import ZlibF.Spec.Common.Inflate.InflateTableInvariant
import ZlibF.Proof.«inftrees.c.fixed»
import ZlibF.Proof.«inflate.c.platform»
import ZlibF.Proof.«inflate.c.main.type»
import ZlibF.Proof.«deflate.c.base»
import ZlibF.Proof.«inffast.c.tableok»

/-!
# inflate.c: producers of the guarded data-table invariant

The initial state and the actual fixed-table installation establish this
clause without assuming a decoder-table contract. Dynamic installation and
preservation through all stream operations are separate obligations.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
open Zlib.Inftrees.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- HEAD does not read a data table. Requiring a fully initialized data
table here would give the wrong invariant for successful initialization. -/
theorem dataTableInvariant_head {h : Heap} {s : InflateState} (head : s.mode = HEAD) :
    DataTableInvariant h s := by
  intro mode
  rw [head] at mode
  simp only [DataTableMode] at mode
  rcases mode with a | a | a | a | a | a | a <;> contradiction

set_option maxRecDepth 100000 in
/-- The fixed pointers resolve to the actual reviewed static arrays. -/
theorem fixedState_tables_safe {h : Heap} (s : InflateState) (globals : LibraryGlobals h) :
    DataTablesSafe h (fixedState s) := by
  constructor
  · refine ⟨.st_lenfix, 0, Zlib.InffixedH.lenfix, rfl, ?_, ?_⟩
    · change some h.static.lenfix = some Zlib.InffixedH.lenfix
      rw [globals]
      rfl
    · exact Zlib.Inffast.Proofs.lenfix_tableSafe
  · refine ⟨.st_distfix, 0, Zlib.InffixedH.distfix, rfl, ?_, ?_⟩
    · change some h.static.distfix = some Zlib.InffixedH.distfix
      rw [globals]
      rfl
    · exact Zlib.Inffast.Proofs.distfix_tableSafe
  · intro ref offset ca pointer get
    have fixed : Ptr.ref CodeRef.st_lenfix 0 = .ref ref offset := pointer
    cases fixed
    have known : Space.get h CodeRef.st_lenfix = some Zlib.InffixedH.lenfix := by
      change some h.static.lenfix = some Zlib.InffixedH.lenfix
      rw [globals]
      rfl
    rw [known] at get
    cases get
    exact Zlib.Inffast.Proofs.lenfix_leavesPositive

/-- `case TYPEDO:` with a fixed block and flush other than Z_TREES.
The actual branch enters LEN_ and establishes the now-active data-table
clause. This connects the installer to dispatch rather than only checking
the table arrays independently. -/
theorem typedoTail_fixed_tableInvariant {c : Ctx} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (env : Env c h r zs z s) (globals : LibraryGlobals h) (l : IL)
    (header : l.hold.toNat % 4 = 1) (flush : c.flush ≠ Z_TREES) :
    runX (typedoTail c) l h =
      .ok ((.ok (), { l with hold := l.hold >>> 2, bits := l.bits - 2 }),
        setI h zs { fixedState s with mode := LEN_ }) ∧
      DataTableInvariant (setI h zs { fixedState s with mode := LEN_ })
        { fixedState s with mode := LEN_ } := by
  refine ⟨typedoTail_fixed env l header flush, ?_⟩
  intro _
  have tables := fixedState_tables_safe
    (h := setI h zs { fixedState s with mode := LEN_ }) s globals
  exact ⟨tables.lengthTable, tables.distanceTable, tables.lengthLeaves⟩

end Zlib.Inflate.Proofs
