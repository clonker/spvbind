import Spvbind

open Spvbind

/-- `spvbind <module.spv>` prints the header; `spvbind --locations <module.spv>` prints every scalar of every push
constant block with its path and offset instead, for use as an oracle. -/
def main (args : List String) : IO UInt32 := do
  let usage : IO UInt32 := do IO.eprintln "usage: spvbind [--locations] <module.spv>"; return 2
  let (locations, path) ← match args with
    | ["--locations", path] => pure (true, path)
    | [path] => if path.startsWith "--" then return ← usage else pure (false, path)
    | _ => return ← usage
  let bytes ← try IO.FS.readBinFile path catch e =>
    IO.eprintln s!"{path}: {e}"
    return 1
  let output := words bytes >>= generate >>= fun blocks =>
    if locations then pure (printLocations blocks) else print path blocks
  match output with
  | .ok text =>
    IO.print text
    return 0
  | .error e =>
    IO.eprintln s!"{path}: {e}"
    return 1
