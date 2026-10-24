import Spvbind

open Spvbind

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: spvbind <module.spv>"; return 2
  let bytes ← IO.FS.readBinFile path
  match words bytes >>= decode >>= fun m => checkVersion m.header *> pure m with
  | .ok m =>
    let h := m.header
    IO.println s!"SPIR-V {h.major}.{h.minor}, generator {h.generator}, bound {h.bound}, \
      {m.instructions.length} instructions"
    for i in m.instructions do
      match i with
      | .name target s => IO.println s!"  %{target} {s.value}"
      | .memberName type member s => IO.println s!"  %{type}.{member} {s.value}"
      | .other .. => pure ()
    return 0
  | .error e =>
    IO.eprintln s!"{path}: {e}"
    return 1
