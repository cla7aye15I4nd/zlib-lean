import ZlibF.Runtime.Monad

namespace C

/-- Address of an automatic variable of type `unsigned char *`. -/
structure BPtrCell where
  id : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Live pointer variables across nested callbacks. Identities survive in caller
    descriptors, and a later activation never reuses an expired identity. -/
structure PointerLocals where
  nextId : Nat := 0
  live : List (BPtrCell × BPtr) := []
  deriving Inhabited

abbrev PointerLocalM := StateT PointerLocals M

def BPtrCell.read (cell : BPtrCell) : PointerLocalM BPtr := fun cells h =>
  match cells.live.lookup cell with
  | some p => .ok ((p, cells), h)
  | none => .error (.ub "read of an expired pointer variable")

def PointerLocals.assign (cells : PointerLocals) (cell : BPtrCell) (p : BPtr) : PointerLocals :=
  { cells with live := cells.live.map fun entry =>
    if entry.1 == cell then (cell, p) else entry }

def BPtrCell.write (cell : BPtrCell) (p : BPtr) : PointerLocalM Unit := fun cells h =>
  if (cells.live.lookup cell).isSome then .ok (((), cells.assign cell p), h)
  else .error (.ub "write to an expired pointer variable")

def PointerLocals.release (cells : PointerLocals) (cell : BPtrCell) : PointerLocals :=
  { cells with live := cells.live.filter fun entry => entry.1 != cell }

/-- An automatic variable consumes no zalloc call or modeled malloc block. Closing
    its scope preserves edits to outer variables made by a nested callback. -/
def withBPtrCell (initial : BPtr) (body : BPtrCell → PointerLocalM α) : PointerLocalM α := do
  let cells ← get
  let cell : BPtrCell := ⟨cells.nextId⟩
  if (cells.live.lookup cell).isSome then
    liftM (ub "automatic pointer variable already live")
  set ({ nextId := cells.nextId + 1, live := (cell, initial) :: cells.live } : PointerLocals)
  let result ← body cell
  modify fun after => after.release cell
  return result

end C
