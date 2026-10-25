import Spvbind

open Spvbind

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: spvbind <module.spv>"; return 2
  let bytes ← IO.FS.readBinFile path
  match words bytes >>= generate >>= print path with
  | .ok header =>
    IO.print header
    return 0
  | .error e =>
    IO.eprintln s!"{path}: {e}"
    return 1
