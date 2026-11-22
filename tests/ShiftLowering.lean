import Lean2C.Lower

private def guarded (x n : UInt64) := if n < 64 then x >>> n else x
private def otherCount (x n m : UInt64) := if m < 64 then x >>> n else x
private def narrow (x n : UInt16) := x <<< n

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, fragment) in [(``guarded, "(x >> n)"), (``otherCount, "(x >> (n % 64))"),
                           (``narrow, "(n % 16)")] do
    let some (.defnInfo d) := env.find? name | throwError "missing shift example"
    let some body := Lean2C.Lower.lower? env name d.type d.value | throwError "missing shift lowering"
    unless body.contains fragment do throwError m!"{name}: expected {fragment} in {body}"
