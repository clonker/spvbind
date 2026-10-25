#!/usr/bin/env python3
"""Differential fuzzing of a reflection library against spvbind, the oracle.

For each generated module (see generate.py), `spvbind --locations` and the subject (reflect_dump, which wraps
SPIRV-Reflect) print every scalar of every push constant block with its path, offset and type. The properties:

1. Oracle: if spvbind accepts the module, the subject accepts it and prints the same scalars. `Guarantees.generate_correct`
   says that spvbind's output is exactly what the SPIR-V decorations say, so a difference is a bug in the subject, or a
   gap in `Spec` (which is what review of `Spec` is for).
2. Robustness: the subject never crashes, whatever the module. With reflect_dump built with sanitizers, a sanitizer
   report counts as a crash.
3. Totality of spvbind: it exits with 0 or 1, never otherwise.

When spvbind rejects a module the oracle is silent; the reasons are tallied so that the generators can be tuned.
Findings are classified with spirv-val as `valid` or `invalid` SPIR-V and saved under --findings with the module, its
source and disassembly, both outputs and the diff.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import os
import pathlib
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import generate  # noqa: E402

ASAN_EXIT, UBSAN_EXIT = 99, 98


class Run:
    def __init__(self, rc: int, out: str, err: str, crashed: bool, timed_out: bool):
        self.rc, self.out, self.err, self.crashed, self.timed_out = rc, out, err, crashed, timed_out


def run(cmd: list[str], timeout: float) -> Run:
    env = dict(os.environ, ASAN_OPTIONS=f'exitcode={ASAN_EXIT}:allocator_may_return_null=1:detect_leaks=0',
               UBSAN_OPTIONS=f'exitcode={UBSAN_EXIT}:halt_on_error=1:print_stacktrace=1')
    try:
        p = subprocess.run(cmd, capture_output=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired as e:
        return Run(-1, (e.stdout or b'').decode(errors='replace'), (e.stderr or b'').decode(errors='replace'), True, True)
    crashed = p.returncode < 0 or p.returncode in (ASAN_EXIT, UBSAN_EXIT) or p.returncode > 2
    return Run(p.returncode, p.stdout.decode(errors='replace'), p.stderr.decode(errors='replace'), crashed, False)


def normalize_reason(err: str) -> str:
    """A spvbind error message without its path and numbers, to tally."""
    msg = err.strip().split(': ', 1)[-1] if ': ' in err else err.strip()
    return re.sub(r'\d+', '#', msg)[:100]


class Fuzzer:
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.rng = random.Random(args.seed)
        self.tmp = pathlib.Path(tempfile.mkdtemp(prefix='spvbind-fuzz-'))
        self.findings = pathlib.Path(args.findings)
        self.stats: collections.Counter[str] = collections.Counter()
        self.rejections: collections.Counter[str] = collections.Counter()
        self.exotic: collections.Counter[str] = collections.Counter()
        self.saved: dict[str, int] = collections.Counter()
        self.seen: set[str] = set()
        self.corpus: list[bytes] = []
        for d in args.corpus:
            for f in sorted(pathlib.Path(d).rglob('*.spv')):
                self.corpus.append(f.read_bytes())
        self.cfg = generate.Config(exotic=args.exotic, p_weird_name=args.weird_names)

    # --- One module -------------------------------------------------------------------------------------------------

    def module(self, mode: str) -> tuple[bytes | None, dict[str, str]]:
        """A module and what is known about it (source, how it was made)."""
        info: dict[str, str] = {'mode': mode}
        if mode == 'glsl':
            block = generate.random_interface(self.rng, self.cfg, exotic_scalars=self.rng.random() < self.args.exotic)
            source = generate.to_glsl(block, self.rng, self.cfg)
            info['source.comp'] = source
            src, spv = self.tmp / 'module.comp', self.tmp / 'module.spv'
            src.write_text(source)
            p = subprocess.run([self.args.glslc, f'--target-env={self.args.target_env}', '-o', str(spv), str(src)],
                               capture_output=True, text=True)
            if p.returncode != 0:
                self.stats['glslc rejected the GLSL'] += 1
                info['glslc.txt'] = p.stderr
                self.rejections['glslc: ' + normalize_reason(p.stderr.splitlines()[0] if p.stderr else '')] += 1
                return None, info
            return spv.read_bytes(), info
        if mode == 'spirv':
            block = generate.random_interface(self.rng, self.cfg, exotic_scalars=self.rng.random() < self.args.exotic)
            data, exotic = generate.to_spirv(block, self.rng, self.cfg)
            for e in exotic:
                self.exotic[e] += 1
            info['exotic'] = ', '.join(exotic)
            return data, info
        if mode == 'mutate':
            if not self.corpus:
                return None, info
            data, done = generate.mutate(self.rng, self.rng.choice(self.corpus))
            info['mutations'] = '; '.join(done)
            return data, info
        raise ValueError(mode)

    def check(self, data: bytes, info: dict[str, str]) -> None:
        spv = self.tmp / 'module.spv'
        spv.write_bytes(data)
        oracle = run([self.args.spvbind, '--locations', str(spv)], self.args.timeout)
        subject = run([self.args.reflect, str(spv)], self.args.timeout)
        info['spvbind.txt'] = oracle.out + oracle.err
        info['reflect.txt'] = subject.out + subject.err

        if oracle.crashed or oracle.rc not in (0, 1):
            self.save('spvbind-crash', data, info, f'spvbind exited with {oracle.rc}' + (' (timeout)' if oracle.timed_out else ''))
        if subject.crashed:
            self.save('reflect-crash', data, info, f'subject exited with {subject.rc}' + (' (timeout)' if subject.timed_out else ''))
            return
        if oracle.rc == 1:
            self.stats['spvbind rejected'] += 1
            self.rejections[normalize_reason(oracle.err)] += 1
            if subject.rc == 0:
                self.stats['spvbind rejected, subject accepted'] += 1
            return
        if oracle.rc != 0:
            return
        self.stats['spvbind accepted'] += 1
        if subject.rc != 0:
            self.save('reflect-rejects', data, info, 'spvbind accepted, the subject rejected:\n' + subject.err)
            return
        inconsistent = [line for line in subject.out.splitlines() if line.startswith('!') or '\t!' in line]
        if inconsistent:
            self.save('reflect-inconsistent', data, info, 'the subject contradicts itself:\n' + '\n'.join(inconsistent))
        expected = sorted(oracle.out.splitlines())
        actual = sorted(line for line in subject.out.splitlines() if not (line.startswith('!') or '\t!' in line))
        if expected == actual:
            self.stats['agree'] += 1
            if info['mode'] != 'mutate' and len(self.corpus) < 2000:
                self.corpus.append(data)
        else:
            missing = [line for line in expected if line not in actual]
            extra = [line for line in actual if line not in expected]
            diff = '\n'.join(['only spvbind:'] + ['  ' + x for x in missing] + ['only the subject:'] + ['  ' + x for x in extra])
            self.save('mismatch', data, info, diff)

    # --- Findings -----------------------------------------------------------------------------------------------------

    def classify(self, spv: pathlib.Path) -> tuple[str, str]:
        if not self.args.spirv_val:
            return 'unclassified', ''
        p = subprocess.run([self.args.spirv_val, '--target-env', self.args.target_env, str(spv)], capture_output=True,
                           text=True)
        return ('valid' if p.returncode == 0 else 'invalid'), p.stderr + p.stdout

    def save(self, kind: str, data: bytes, info: dict[str, str], what: str) -> None:
        digest = hashlib.sha1(data).hexdigest()[:12]
        self.stats[kind] += 1
        if digest in self.seen:
            return
        self.seen.add(digest)
        spv = self.tmp / 'finding.spv'
        spv.write_bytes(data)
        validity, val_output = self.classify(spv)
        self.stats[f'{kind} ({validity})'] += 1
        if self.saved[kind] >= self.args.max_findings:
            return
        self.saved[kind] += 1
        directory = self.findings / kind / validity / digest
        directory.mkdir(parents=True, exist_ok=True)
        (directory / 'module.spv').write_bytes(data)
        if self.args.spirv_dis:
            p = subprocess.run([self.args.spirv_dis, '--raw-id', str(spv)], capture_output=True, text=True)
            (directory / 'module.spvasm').write_text(p.stdout + p.stderr)
        (directory / 'spirv-val.txt').write_text(f'{validity}\n{val_output}')
        for key in ('source.comp', 'spvbind.txt', 'reflect.txt', 'glslc.txt'):
            if key in info:
                (directory / key).write_text(info[key])
        summary = [f'kind: {kind}', f'spirv-val: {validity}', f'mode: {info.get("mode")}', f'seed: {self.args.seed}']
        for key in ('exotic', 'mutations'):
            if info.get(key):
                summary.append(f'{key}: {info[key]}')
        summary += ['', what, '']
        (directory / 'README.txt').write_text('\n'.join(summary))
        print(f'\n[{kind}, {validity}] {directory}\n{what}', file=sys.stderr)

    # --- The loop -----------------------------------------------------------------------------------------------------

    def loop(self) -> None:
        modes = self.args.mode
        started = time.time()
        try:
            for i in range(self.args.iterations):
                mode = modes[i % len(modes)]
                if mode == 'mutate' and not self.corpus:
                    mode = 'spirv'
                data, info = self.module(mode)
                self.stats[f'generated: {mode}'] += 1
                if data is not None:
                    self.check(data, info)
                if self.args.progress and (i + 1) % self.args.progress == 0:
                    rate = (i + 1) / (time.time() - started)
                    print(f'{i + 1} modules, {rate:.0f}/s, agree {self.stats["agree"]}, '
                          f'spvbind rejected {self.stats["spvbind rejected"]}, '
                          f'findings {sum(self.saved.values())}', file=sys.stderr)
        finally:
            shutil.rmtree(self.tmp, ignore_errors=True)

    def report(self) -> int:
        print('\n== Summary ==')
        for key, count in sorted(self.stats.items()):
            print(f'{count:7}  {key}')
        if self.rejections:
            print('\n== Why spvbind rejected modules (the oracle is silent there) ==')
            for reason, count in self.rejections.most_common(30):
                print(f'{count:7}  {reason}')
        if self.exotic:
            print('\n== Exotic constructs generated ==')
            for name, count in self.exotic.most_common():
                print(f'{count:7}  {name}')
        findings = sum(self.saved.values())
        if findings:
            print(f'\n{findings} findings saved under {self.findings}')
        kinds = ('mismatch', 'reflect-rejects', 'reflect-crash', 'reflect-inconsistent')
        failed = {'none': False,
                  'any': any(k in self.stats for k in kinds),
                  'valid': any(f'{k} (valid)' in self.stats for k in kinds)}[self.args.fail_on]
        return 1 if failed or 'spvbind-crash' in self.stats else 0


def main() -> int:
    here = pathlib.Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--spvbind', default=str(here.parent / '.lake/build/bin/spvbind'), help='the oracle')
    parser.add_argument('--reflect', default=str(here / 'build/reflect_dump'),
                        help='the subject: prints push constant scalars like `spvbind --locations`')
    parser.add_argument('--mode', nargs='+', default=['glsl', 'spirv', 'mutate'], choices=['glsl', 'spirv', 'mutate'],
                        help='how to make modules; several alternate')
    parser.add_argument('-n', '--iterations', type=int, default=300)
    parser.add_argument('--seed', type=int, default=None, help='for reproducible runs; printed')
    parser.add_argument('--exotic', type=float, default=0.1,
                        help='probability of each exotic construct in spirv mode, and of unsupported scalars')
    parser.add_argument('--weird-names', type=float, default=0.005, help='probability of a troublesome name')
    parser.add_argument('--corpus', nargs='*', default=[str(here / 'reproducers')],
                        help='directories of .spv files to mutate, besides the modules both tools agree on')
    parser.add_argument('--findings', default=str(here / 'findings'))
    parser.add_argument('--max-findings', type=int, default=20, help='per kind')
    parser.add_argument('--timeout', type=float, default=20.0, help='seconds per tool run; longer is a hang')
    parser.add_argument('--target-env', default='vulkan1.3')
    parser.add_argument('--glslc', default='glslc')
    parser.add_argument('--spirv-val', default=shutil.which('spirv-val'), help='to classify findings; empty to skip')
    parser.add_argument('--spirv-dis', default=shutil.which('spirv-dis'), help='to disassemble findings; empty to skip')
    parser.add_argument('--progress', type=int, default=100, help='print progress every N modules; 0 for none')
    parser.add_argument('--fail-on', choices=['valid', 'any', 'none'], default='valid',
                        help='exit with 1 on findings on valid modules only (default), on any, or never; a spvbind '
                             'crash always fails')
    args = parser.parse_args()
    if args.seed is None:
        args.seed = random.SystemRandom().randrange(2 ** 32)
    print(f'seed {args.seed}', file=sys.stderr)
    for tool, what in ((args.spvbind, 'spvbind (lake build)'), (args.reflect, 'reflect_dump (see fuzz/README.md)')):
        if not shutil.which(tool):
            print(f'{tool} not found: build {what}', file=sys.stderr)
            return 2
    fuzzer = Fuzzer(args)
    fuzzer.loop()
    return fuzzer.report()


if __name__ == '__main__':
    sys.exit(main())
