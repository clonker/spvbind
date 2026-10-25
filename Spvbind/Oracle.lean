import Spvbind.Print

/-!
# The oracle as a C function

For the differential fuzzer in `fuzz/`, which links the compiled Lean code of spvbind into a FuzzTest binary and calls
this instead of running the executable for every input.
-/

namespace Spvbind

/-- What `spvbind --locations` prints for the bytes of a module, or `error: ` and the message, which no locations
output starts with (its lines start with a decimal id, or there are none). Exported to C as
`lean_object* spvbind_locations(lean_object* bytes)`, taking the `ByteArray` and returning a `String`. -/
@[export spvbind_locations]
def oracleLocations (bytes : ByteArray) : String :=
  match words bytes >>= generate with
  | .ok blocks => printLocations blocks
  | .error e => "error: " ++ e

end Spvbind
