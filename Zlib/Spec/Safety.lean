import Zlib

/-!
# Whole-Library Safety Specification (`Zlib.Spec.Safety`)

Collects all 86 Verus-style `c_fn` contracts in `Zlib.allContracts` and states
the top-level whole-library safety, bounded termination, frame preservation, and
leak-freedom theorem target `Goal.libz_safety` over `C99.Sem`.
-/

namespace Zlib.Spec

open C99 C99.Sem

/-- The 2 documented permissive C17 pointer-arithmetic exceptions used by patched zlib. -/
def zlibPointerConfig : PointerConfig :=
  { allowAddZeroAny := true, allowNullDiffNull := true }

def isStdLibcSym (sym : String) : Bool :=
  (stdLibcProtos.map Prod.fst).contains sym

/-- External call relation mapping `LSEEK` -> `lseek64`, standard libc/POSIX, and user callbacks. -/
def zlibExt (userExt : ExtHandler) : ExtHandler := fun sym args m os out =>
  if sym == "LSEEK" then Libc.ExtStep "lseek64" args m os out
  else if isStdLibcSym sym then Libc.ExtStep sym args m os out
  else userExt sym args m os out

/-- Initialize patched `libz` globals, string literals, statics, `errno`, and `LSEEK` alias. -/
def initLibz (globBase staticBase strBase : Nat → UInt64) (errnoBase : UInt64) :
    Option (Prog × Env × Mem × OSState) := do
  let (p, env, m, os) ← initProg Zlib.allFiles globBase staticBase strBase errnoBase
  let prog := { p with fnProtos := fun sym =>
    if sym == "LSEEK" then p.fnProtos "lseek64" else p.fnProtos sym }
  return (prog, env, m, os)

/-- Initial small-step execution state calling public symbol `fnName` with ABI arguments `args`. -/
def callState (prog : Prog) (gEnv : Env) (m : Mem) (os : OSState)
    (fnName : String) (args : List Val) : Option RunState := do
  let (retTy, paramTys, variadic) ← prog.fnProtos fnName
  let fnTy := CTy.fnPtr retTy paramTys variadic
  match args.reverse with
  | [] =>
    return .running (.expr (.ret (.rval (.fnPtr fnName) fnTy) [.callFnF []]) .returnVal [])
      gEnv [] m os (.stop retTy)
  | last :: revInit =>
    let done := revInit.reverse.map (·, .void)
    return .running (.expr (.ret (.rval last .void) [.callArgF fnName fnTy done []]) .returnVal [])
      gEnv [] m os (.stop retTy)

/-- Memory blocks protected against client tampering between library API calls. -/
def LibProtected (m0 : Mem) (owned : BlockSet) (os : OSState) (m : Mem) (b : BlockId) : Prop :=
  owned b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ (m0.blocks b).isSome ∨
  ∃ blk, m.blocks b = some blk ∧ blk.kind = .global ∧ blk.perm = .ro

/-- Permitted client mutations between consecutive `libz` calls (buffer updates, budget changes, rebuffering). -/
def ClientFrame (tags : TypeEnv) (m0 : Mem) (v : ClientView) (owned : BlockSet)
    (m m' : Mem) (os os' : OSState) : Prop :=
  os'.errnoBlk = os.errnoBlk ∧
  os'.strerrorBlk = os.strerrorBlk ∧
  (∀ b, LibProtected m0 owned os m b → m'.blocks b = m.blocks b) ∧
  ∀ b k, (b, k) ∈ v.streams →
    (∀ f ∈ ["state", "zalloc", "zfree", "opaque", "adler"],
      readField? tags m' (.ptr b 0) "z_stream_s" f = readField? tags m (.ptr b 0) "z_stream_s" f) ∧
    (k = .inflateBack →
      let st := (readField? tags m (.ptr b 0) "z_stream_s" "state").getD .null
      let win := (readField? tags m st "inflate_state" "window").getD .null
      let wsz := (readNatField? tags m st "inflate_state" "wsize").getD 0
      Writable m' win wsz)

/-- Safety contract required of caller-supplied `inflateBack` `in_func` / `out_func` callbacks. -/
def SafeUserCallbacks (tags : TypeEnv) (m0 : Mem) (v : ClientView)
    (owned userWrite : BlockSet) (userExt : ExtHandler) : Prop :=
  (∀ sym args m os, os.readBudget.isSome → (args.length = 2 ∨ args.length = 3) →
    ∃ ret m' os', userExt sym args m os (.ok ret m' os')) ∧
  ∀ sym args m os out, userExt sym args m os out →
    out ≠ .ub ∧
    ∀ ret m' os', out = .ok ret m' os' →
      os'.errnoBlk = os.errnoBlk ∧
      os'.strerrorBlk = os.strerrorBlk ∧
      FramePreserved m m' (fun b =>
        ¬ LibProtected m0 owned os m b ∧ (∀ k, (b, k) ∉ v.streams) ∧
        (∀ sb, (sb, .inflateBack) ∈ v.streams →
          PtrBlock ((readField? tags m ((readField? tags m (.ptr sb 0) "z_stream_s" "state").getD .null)
            "inflate_state" "window").getD .null) ≠ some b) ∧
        (userWrite b ∨ (m.blocks b).isNone ∨ (∃ op noff, args = [op, .ptr b noff]))) ∧
      NoHeapLeak m m' owned ∧
      (∀ op nb noff, args = [op, .ptr nb noff] →
        ∃ avail : BitVec 32, ret = .int .u32 avail ∧
          (avail.toNat = 0 ∨ ∃ bs pb po, m'.readBytes nb noff 8 = some bs ∧
            Mem.decodePtr bs = some (.ptr pb po) ∧ Readable m' (.ptr pb po) avail.toNat ∧
            ¬ LibProtected m0 owned os m' pb ∧ (∀ k, (pb, k) ∉ v.streams) ∧
            (∀ sb, (sb, .inflateBack) ∈ v.streams →
              PtrBlock ((readField? tags m' ((readField? tags m' (.ptr sb 0) "z_stream_s" "state").getD .null)
                "inflate_state" "window").getD .null) ≠ some pb) ∧
            (∀ blk, m'.blocks pb = some blk → blk.kind ≠ .stack)) ∧
          (∀ k, os.readBudget = some k → ∃ k', os'.readBudget = some k' ∧ (avail.toNat > 0 → k' < k))) ∧
      (∀ op buf len, args = [op, buf, len] →
        (∃ r : BitVec 32, ret = .int .i32 r) ∧ os'.readBudget = os.readBudget)

/-- C ABI well-typedness predicate for incoming arguments passed to `callState`. -/
def ValHasCTy (ty : CTy) (v : Val) : Prop :=
  match ty.unqual with
  | .int k => ∃ bv, v = .int k bv
  | .enumTy _ isU => ∃ bv, v = .int (if isU then .u32 else .i32) bv
  | .ptr _ | .array _ _ => v = .null ∨ ∃ b off, v = .ptr b off
  | .fnPtr _ _ _ => v = .null ∨ ∃ sym, v = .fnPtr sym
  | .vaList => v = .vaList true
  | .void => v = .void
  | _ => True

/-- Arity and fixed-parameter C ABI typing check for `callState` arguments. -/
def ArgsWellTyped (prog : Prog) (paramTys : List CTy) (variadic : Bool) (args : List Val) : Prop :=
  (if variadic then paramTys.length ≤ args.length else args.length = paramTys.length) ∧
  (∀ i (_ : i < paramTys.length),
    match args[i]? with | some v => ValHasCTy paramTys[i] v | none => False) ∧
  ∀ i (_ : i < paramTys.length),
    match paramTys[i].unqual, args[i]? with
    | .fnPtr _ _ _, some (.fnPtr sym) =>
        prog.fns sym = none ∧ sym ≠ "LSEEK" ∧ isStdLibcSym sym = false
    | _, _ => True

/-- Safety, bounded termination, frame, and leak-freedom obligations for one Verus contract `c`. -/
def ContractSafe (prog : Prog) (gEnv : Env) (ext : ExtHandler)
    (Inv : ClientView → BlockSet → Mem → OSState → Prop)
    (userWrite : BlockSet) (c : FnContract ClientView) : Prop :=
  ∀ v owned m os args s0,
    Inv v owned m os →
    c.pre prog.tags owned v m args →
    ArgsWellTyped prog c.paramTys c.variadic args →
    (∀ a ∈ args, DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
    callState prog gEnv m os c.fnName args = some s0 →
    Safe prog zlibPointerConfig ext s0 ∧
    (os.readBudget.isSome → TerminatesSafely prog zlibPointerConfig ext s0) ∧
    (∀ ret m' os', Star (Step prog zlibPointerConfig ext) s0 (.returned ret m' os') →
      ∃ owned' v',
        c.post prog.tags owned v m args ret m' v' ∧
        Inv v' owned' m' os' ∧
        FramePreserved m m' (fun b =>
          owned b ∨ owned' b ∨ c.modSet prog.tags owned v m args b ∨
          userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
        NoHeapLeak m m' owned' ∧
        (v'.isEmpty → ∀ b, ¬ owned' b))

/-- Top-level whole-library safety claim across all 86 Verus-contracted public `zlib.h` APIs. -/
def Goal.libz_safety : Prop :=
  ∀ globBase staticBase strBase errnoBase prog gEnv m0 os0,
    initLibz globBase staticBase strBase errnoBase = some (prog, gEnv, m0, os0) →
    ∃ Inv : ClientView → BlockSet → Mem → OSState → Prop,
      Inv ClientView.empty (fun _ => False) m0 os0 ∧
      (∀ v owned m m' os os', Inv v owned m os →
        ClientFrame prog.tags m0 v owned m m' os os' → Inv v owned m' os') ∧
      (∀ userExt userWrite,
        (∀ v owned, DisjointSets owned userWrite →
          SafeUserCallbacks prog.tags m0 v owned userWrite userExt) →
        ∀ c ∈ Zlib.allContracts, ContractSafe prog gEnv (zlibExt userExt) Inv userWrite c)

end Zlib.Spec
