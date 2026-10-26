#!/usr/bin/env python3
"""Move the hash pins in workflows/ci.yml to the current heads: the Nix store paths of glslc and spirv-as to those of
nixpkgs' nixos-unstable, and the SPIRV-Headers grammar to main. Prints what moved, as the body of a pull request;
workflows/update-pins.yml runs this weekly and opens it. Needs gh and nix."""

from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys

CI = pathlib.Path(__file__).resolve().parent / 'workflows' / 'ci.yml'
# The nixpkgs outputs pinned as store paths, with the tool whose --version the pull request shows.
PACKAGES = [('shaderc.bin', 'glslc'), ('spirv-tools.out', 'spirv-as')]


def run(*cmd: str) -> str:
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout.strip()


def head(repo: str, branch: str) -> tuple[str, str]:
    """A branch's commit and its date."""
    commit = json.loads(run('gh', 'api', f'repos/{repo}/commits/{branch}'))
    return commit['sha'], commit['commit']['committer']['date'][:10]


class Pins:
    def __init__(self) -> None:
        self.text = CI.read_text()
        self.moves: list[str] = []

    def replace(self, pattern: str, new: str, label: str | None = None) -> None:
        """Replace the single match of `pattern`, recording the move under `label`."""
        matches = list(re.finditer(pattern, self.text))
        if len(matches) != 1:
            sys.exit(f'{CI}: {len(matches)} matches of {pattern!r}, expected one')
        old = matches[0].group()
        self.text = self.text[:matches[0].start()] + new + self.text[matches[0].end():]
        if label and old != new:
            self.moves.append(f'- {label}: `{old}` to `{new}`')


def main() -> None:
    pins = Pins()

    rev, date = head('NixOS/nixpkgs', 'nixos-unstable')
    pins.replace(r'nixpkgs [0-9a-f]{40} \(nixos-unstable, \d{4}-\d{2}-\d{2}\)', f'nixpkgs {rev} (nixos-unstable, {date})',
                 'nixpkgs')
    for package, tool in PACKAGES:
        path = run('nix', 'build', '--no-link', '--print-out-paths', f'github:NixOS/nixpkgs/{rev}#{package}')
        version = ' '.join(run(f'{path}/bin/{tool}', '--version').split()[:2])
        name = package.split('.')[0]
        pins.replace(rf'/nix/store/[0-9a-z]{{32}}-{name}-[\w.+-]+', path, f'{tool} ({version})')

    rev, date = head('KhronosGroup/SPIRV-Headers', 'main')
    pins.replace(r'SPIRV-Headers main as of \d{4}-\d{2}-\d{2}\.', f'SPIRV-Headers main as of {date}.')
    pins.replace(r'SPIRV-Headers/[0-9a-f]{40}/', f'SPIRV-Headers/{rev}/', f'SPIRV-Headers main ({date})')

    if not pins.moves:
        print('Nothing to move.')
        return
    CI.write_text(pins.text)
    print('\n'.join(pins.moves))


if __name__ == '__main__':
    main()
