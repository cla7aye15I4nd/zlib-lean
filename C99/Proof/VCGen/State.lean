import C99.Proof.VCGen.Ops

/-!
# Symbolic State and Scoped Frame Refinement (`C99.Proof.VCGen.State`)

Verus-inspired register-promoted local variable map (`RegEnv`), clean heap/global
state (`SymState`), lexical stack frame refinement (`Refines`), and sequence-point
mod-set tracking (`ModsOK`). 100% zlib-agnostic.
-/

namespace C99.Proof.VCGen

open C99 C99.Sem C99.Proof

/-! ## Pure Functional Register Environment (`RegEnv`) -/

abbrev RegEnv := List (String × Val × CTy)

namespace RegEnv

def lookup : RegEnv → String → Option (Val × CTy)
  | [], _ => none
  | (y, v, ty) :: rest, x => if y == x then some (v, ty) else lookup rest x

def set : RegEnv → String → Val → CTy → RegEnv
  | [], _, _, _ => []
  | (y, ov, oty) :: rest, x, nv, nty =>
    if y == x then (y, nv, nty) :: rest
    else (y, ov, oty) :: set rest x nv nty

@[simp] theorem length_set (r : RegEnv) (x : String) (v : Val) (ty : CTy) :
    (r.set x v ty).length = r.length := by
  induction r with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨y, ov, oty⟩
    unfold set
    by_cases hy : (y == x) = true
    · simp [hy]
    · have hyf : (y == x) = false := Bool.eq_false_iff.mpr hy
      simp [hyf, ih]

@[simp] theorem lookup_nil (x : String) : lookup [] x = none := rfl

@[simp] theorem lookup_cons (y : String) (v : Val) (ty : CTy) (rest : RegEnv) (x : String) :
    lookup ((y, v, ty) :: rest) x = if y == x then some (v, ty) else lookup rest x := rfl

@[simp] theorem set_cons (y : String) (ov nv : Val) (oty nty : CTy) (rest : RegEnv) (x : String) :
    set ((y, ov, oty) :: rest) x nv nty =
      if y == x then (y, nv, nty) :: rest else (y, ov, oty) :: set rest x nv nty := rfl

theorem lookup_set_eq {r : RegEnv} {x : String} {ov : Val} {oty nty : CTy} (nv : Val)
    (hl : r.lookup x = some (ov, oty)) :
    (r.set x nv nty).lookup x = some (nv, nty) := by
  induction r with
  | nil => cases hl
  | cons hd tl ih =>
    rcases hd with ⟨y, v, ty⟩
    by_cases hy : (y == x) = true
    · simp [hy]
    · have hyf : (y == x) = false := Bool.eq_false_iff.mpr hy
      simp only [lookup_cons, hyf, Bool.false_eq_true, ↓reduceIte] at hl
      simp only [set_cons, hyf, Bool.false_eq_true, ↓reduceIte, lookup_cons]
      exact ih hl

theorem lookup_set_ne (r : RegEnv) {x y : String} (v : Val) (ty : CTy) (hne : x ≠ y) :
    (r.set x v ty).lookup y = r.lookup y := by
  induction r with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨z, ov, oty⟩
    by_cases hzx : (z == x) = true
    · have hzx_eq : z = x := eq_of_beq hzx
      have hzy : (z == y) = false := beq_false_of_ne (hzx_eq ▸ hne)
      simp [hzx, hzy]
    · have hzxf : (z == x) = false := Bool.eq_false_iff.mpr hzx
      by_cases hzy : (z == y) = true
      · simp [hzxf, hzy]
      · have hzyf : (z == y) = false := Bool.eq_false_iff.mpr hzy
        simp [hzxf, hzyf, ih]

theorem drop_set_of_not_mem (r1 r2 : RegEnv) {x : String} (v : Val) (ty : CTy)
    (hnot : ∀ e ∈ r1, e.1 ≠ x) :
    ((r1 ++ r2).set x v ty).drop r1.length = r2.set x v ty := by
  induction r1 with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨y, ov, oty⟩
    have hyne : y ≠ x := hnot (y, ov, oty) (.head _)
    have hyf : (y == x) = false := beq_false_of_ne hyne
    simp only [List.cons_append, set_cons, hyf, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, List.drop_succ_cons]
    exact ih (fun e he => hnot e (.tail _ he))

theorem lookup_set_none {r : RegEnv} {x y : String} (v : Val) (ty : CTy)
    (hl : r.lookup y = none) :
    (r.set x v ty).lookup y = none := by
  by_cases hxy : x = y
  · subst hxy
    induction r with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨z, ov, oty⟩
      by_cases hzx : (z == x) = true
      · simp [hzx] at hl
      · have hzf : (z == x) = false := Bool.eq_false_iff.mpr hzx
        simp only [lookup_cons, hzf, Bool.false_eq_true, ↓reduceIte] at hl
        simp [set_cons, hzf, lookup_cons, ih hl]
  · rw [lookup_set_ne r v ty hxy, hl]

theorem lookup_eq_none_of_drop_mem {r1 r2 : RegEnv} {x : String}
    (hl : (r1 ++ r2).lookup x = none) : r2.lookup x = none := by
  induction r1 with
  | nil => exact hl
  | cons hd tl ih =>
    rcases hd with ⟨y, v, ty⟩
    by_cases hy : (y == x) = true
    · simp [hy] at hl
    · have hyf : (y == x) = false := Bool.eq_false_iff.mpr hy
      simp only [List.cons_append, lookup_cons, hyf, Bool.false_eq_true, ↓reduceIte] at hl
      exact ih hl

end RegEnv

structure SymState where
  regs : RegEnv
  stack : Env := []
  mem : Mem
  os : OSState

def SymState.typeEnv (s : SymState) (baseEnv : Env) : Env :=
  s.regs.map (fun p => (p.1, 0, p.2.2)) ++ s.stack ++ baseEnv

def SymState.exitBlock (s : SymState) (regLen0 stkLen0 : Nat) : SymState :=
  let stkDrop := s.stack.length - stkLen0
  let regDrop := s.regs.length - regLen0
  { regs := s.regs.drop regDrop
    stack := s.stack.drop stkDrop
    mem := s.mem.freeStack ((s.stack.take stkDrop).map (·.2.1))
    os := s.os }

def SymState.exitFn (s : SymState) : Mem :=
  s.mem.freeStack (s.stack.map (·.2.1))

@[simp] theorem SymState.exitFn_of_stack_nil (regs : RegEnv) (mem : Mem) (os : OSState) :
    ({ regs := regs, stack := [], mem := mem, os := os } : SymState).exitFn = mem := by
  unfold SymState.exitFn
  cases mem
  rfl

/-! ## Concrete Lexical Stack Frame Overlay (`FrameSlot`, `FrameScope`, `Refines`) -/

inductive SlotKind where
  | reg
  | stk
  deriving DecidableEq, Repr

structure FrameSlot where
  name : String
  blk : BlockId
  ty : CTy
  kind : SlotKind := .reg

abbrev FrameScope := List FrameSlot

def FrameScope.blks (sc : FrameScope) : List BlockId :=
  sc.map (·.blk)

def regSlots (slots : List FrameSlot) : List FrameSlot :=
  slots.filter (·.kind == .reg)

def stkSlots (slots : List FrameSlot) : List FrameSlot :=
  slots.filter (·.kind == .stk)

@[simp] theorem regSlots_nil : regSlots [] = [] := rfl
@[simp] theorem stkSlots_nil : stkSlots [] = [] := rfl

@[simp] theorem regSlots_cons_reg (name : String) (blk : BlockId) (ty : CTy) (rest : List FrameSlot) :
    regSlots (⟨name, blk, ty, .reg⟩ :: rest) = ⟨name, blk, ty, .reg⟩ :: regSlots rest := rfl

@[simp] theorem regSlots_cons_stk (name : String) (blk : BlockId) (ty : CTy) (rest : List FrameSlot) :
    regSlots (⟨name, blk, ty, .stk⟩ :: rest) = regSlots rest := rfl

@[simp] theorem stkSlots_cons_reg (name : String) (blk : BlockId) (ty : CTy) (rest : List FrameSlot) :
    stkSlots (⟨name, blk, ty, .reg⟩ :: rest) = stkSlots rest := rfl

@[simp] theorem stkSlots_cons_stk (name : String) (blk : BlockId) (ty : CTy) (rest : List FrameSlot) :
    stkSlots (⟨name, blk, ty, .stk⟩ :: rest) = ⟨name, blk, ty, .stk⟩ :: stkSlots rest := rfl

theorem regSlots_append (s1 s2 : List FrameSlot) :
    regSlots (s1 ++ s2) = regSlots s1 ++ regSlots s2 := by
  simp [regSlots, List.filter_append]

theorem stkSlots_append (s1 s2 : List FrameSlot) :
    stkSlots (s1 ++ s2) = stkSlots s1 ++ stkSlots s2 := by
  simp [stkSlots, List.filter_append]

def allSlots (cur : FrameScope) (outer : List FrameScope) : List FrameSlot :=
  cur ++ outer.flatten

def allSlotBlks (cur : FrameScope) (outer : List FrameScope) : List BlockId :=
  (allSlots cur outer).map (·.blk)

def allRegSlots (cur : FrameScope) (outer : List FrameScope) : List FrameSlot :=
  regSlots (allSlots cur outer)

def allRegBlks (cur : FrameScope) (outer : List FrameScope) : List BlockId :=
  (allRegSlots cur outer).map (·.blk)

def allStkSlots (cur : FrameScope) (outer : List FrameScope) : List FrameSlot :=
  stkSlots (allSlots cur outer)

def allStkBlks (cur : FrameScope) (outer : List FrameScope) : List BlockId :=
  (allStkSlots cur outer).map (·.blk)

theorem mem_allSlotBlks_of_reg {cur : FrameScope} {outer : List FrameScope} {b : BlockId}
    (hb : b ∈ allRegBlks cur outer) : b ∈ allSlotBlks cur outer := by
  obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hb
  exact List.mem_map.mpr ⟨sl, (List.mem_filter.mp hsl).1, rfl⟩

theorem mem_allSlotBlks_of_stk {cur : FrameScope} {outer : List FrameScope} {b : BlockId}
    (hb : b ∈ allStkBlks cur outer) : b ∈ allSlotBlks cur outer := by
  obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hb
  exact List.mem_map.mpr ⟨sl, (List.mem_filter.mp hsl).1, rfl⟩

theorem allRegBlks_or_allStkBlks_of_allSlotBlks {cur : FrameScope} {outer : List FrameScope}
    {b : BlockId} (hb : b ∈ allSlotBlks cur outer) :
    b ∈ allRegBlks cur outer ∨ b ∈ allStkBlks cur outer := by
  obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hb
  cases hk : sl.kind
  · left; exact List.mem_map.mpr ⟨sl, List.mem_filter.mpr ⟨hsl, by simp [hk]⟩, rfl⟩
  · right; exact List.mem_map.mpr ⟨sl, List.mem_filter.mpr ⟨hsl, by simp [hk]⟩, rfl⟩

theorem not_mem_reg_of_stk_nodup {slots : List FrameSlot} (hnd : (slots.map (·.blk)).Nodup)
    {sl : FrameSlot} (hsl : sl ∈ stkSlots slots) :
    sl.blk ∉ (regSlots slots).map (·.blk) := by
  induction slots with
  | nil => simp at hsl
  | cons hd tl ih =>
    rcases hd with ⟨name, blk, ty, kind⟩
    rcases List.nodup_cons.mp hnd with ⟨hnot, hnd'⟩
    cases kind
    · simp only [stkSlots_cons_reg, regSlots_cons_reg, List.map_cons, List.mem_cons, not_or] at hsl ⊢
      have hsl_in : sl ∈ tl := (List.mem_filter.mp hsl).1
      exact ⟨fun heq => hnot (List.mem_map.mpr ⟨sl, hsl_in, heq⟩), ih hnd' hsl⟩
    · simp only [regSlots_cons_stk, stkSlots_cons_stk, List.mem_cons] at hsl ⊢
      rcases hsl with rfl | hsl_tl
      · exact fun hm => hnot (by
          obtain ⟨s', hs', heq⟩ := List.mem_map.mp hm
          exact List.mem_map.mpr ⟨s', (List.mem_filter.mp hs').1, heq⟩)
      · exact ih hnd' hsl_tl

theorem nodup_regBlks_of_nodup {slots : List FrameSlot} (hnd : (slots.map (·.blk)).Nodup) :
    ((regSlots slots).map (·.blk)).Nodup :=
  (List.Sublist.map _ (List.filter_sublist)).nodup hnd

theorem nodup_stkBlks_of_nodup {slots : List FrameSlot} (hnd : (slots.map (·.blk)).Nodup) :
    ((stkSlots slots).map (·.blk)).Nodup :=
  (List.Sublist.map _ (List.filter_sublist)).nodup hnd

def slotsEnv (slots : List FrameSlot) (baseEnv : Env) : Env :=
  slots.map (fun sl => (sl.name, sl.blk, sl.ty)) ++ baseEnv

def dropBlks (m : Mem) (bs : List BlockId) : Mem :=
  { blocks := fun b => if b ∈ bs then none else m.blocks b
    nextBlock := m.nextBlock
    fresh := by
      intro b hb
      split
      · rfl
      · exact m.fresh b hb }

@[simp] theorem dropBlks_nextBlock (m : Mem) (bs : List BlockId) :
    (dropBlks m bs).nextBlock = m.nextBlock := rfl

theorem dropBlks_blocks_not_mem (m : Mem) (bs : List BlockId) {b : BlockId} (hnot : b ∉ bs) :
    (dropBlks m bs).blocks b = m.blocks b := by
  simp [dropBlks, hnot]

theorem dropBlks_blocks_mem (m : Mem) (bs : List BlockId) {b : BlockId} (hmem : b ∈ bs) :
    (dropBlks m bs).blocks b = none := by
  simp [dropBlks, hmem]

@[simp] theorem dropBlks_nil (m : Mem) : dropBlks m [] = m := by
  cases m; rfl

@[simp] theorem freeStack_nil (m : Mem) : m.freeStack [] = m := by
  cases m; rfl

theorem freeStack_append (m : Mem) (bs1 bs2 : List BlockId) :
    (m.freeStack bs1).freeStack bs2 = m.freeStack (bs1 ++ bs2) := by
  rcases m with ⟨blocks, nextBlock, fresh⟩
  simp only [Mem.freeStack]
  congr 1
  funext b
  by_cases h1 : bs1.contains b = true
  · simp only [h1, ↓reduceIte, List.contains_append, Bool.true_or]
    cases hb : blocks b with
    | none => simp
    | some blk =>
      cases hk : (blk.kind == .stack) <;> simp [hk]
  · have h1f : bs1.contains b = false := Bool.eq_false_iff.mpr h1
    simp only [h1f, Bool.false_eq_true, ↓reduceIte, List.contains_append, Bool.false_or]

@[simp] theorem SymState.exitBlock_same_stk (s : SymState) (regLen0 : Nat) :
    s.exitBlock regLen0 s.stack.length =
      { s with regs := s.regs.drop (s.regs.length - regLen0) } := by
  simp [SymState.exitBlock]

def allocAt (m : Mem) (bid : BlockId) (hle : m.nextBlock ≤ bid)
    (sz al : Nat) (perm : Perm) (kind : AllocKind)
    (base : UInt64) (init : Nat → MemByte)
    (hsz : sz < ptrDiffLimit) (hal : 0 < al) (hba : base.toNat % al = 0) : Mem :=
  let blk : Block :=
    { size := sz, align := al, perm := perm, kind := kind,
      baseAddr := base, bytes := init, sizeLt := hsz, alignPos := hal, baseAligned := hba }
  { blocks := fun x => if x == bid then some blk else m.blocks x
    nextBlock := bid + 1
    fresh := by
      intro x hx
      have hne : (x == bid) = false := beq_false_of_ne (Nat.ne_of_gt hx)
      have hmx : m.nextBlock ≤ x := Nat.le_trans hle (Nat.le_of_lt hx)
      simp [hne, m.fresh x hmx] }

@[simp] theorem allocAt_nextBlock (m : Mem) (bid : BlockId) (hle : m.nextBlock ≤ bid)
    (sz al : Nat) (perm : Perm) (kind : AllocKind) (base : UInt64) (init : Nat → MemByte)
    (hsz : sz < ptrDiffLimit) (hal : 0 < al) (hba : base.toNat % al = 0) :
    (allocAt m bid hle sz al perm kind base init hsz hal hba).nextBlock = bid + 1 := rfl

theorem allocAt_blocks_eq (m : Mem) (bid : BlockId) (hle : m.nextBlock ≤ bid)
    (sz al : Nat) (perm : Perm) (kind : AllocKind) (base : UInt64) (init : Nat → MemByte)
    (hsz : sz < ptrDiffLimit) (hal : 0 < al) (hba : base.toNat % al = 0) :
    (allocAt m bid hle sz al perm kind base init hsz hal hba).blocks bid =
      some ⟨sz, al, perm, kind, base, init, hsz, hal, hba⟩ := by
  simp [allocAt]

theorem allocAt_blocks_ne (m : Mem) (bid : BlockId) (hle : m.nextBlock ≤ bid)
    (sz al : Nat) (perm : Perm) (kind : AllocKind) (base : UInt64) (init : Nat → MemByte)
    (hsz : sz < ptrDiffLimit) (hal : 0 < al) (hba : base.toNat % al = 0)
    {b : BlockId} (hne : b ≠ bid) :
    (allocAt m bid hle sz al perm kind base init hsz hal hba).blocks b = m.blocks b := by
  simp [allocAt, hne]

theorem writeBytes_allocAt_eq {m : Mem} {bid : BlockId} {hle : m.nextBlock ≤ bid}
    {sz al : Nat} {kind : AllocKind} {base : UInt64} {init : Nat → MemByte}
    {hsz : sz < ptrDiffLimit} {hal : 0 < al} {hba : base.toNat % al = 0}
    {bs : List MemByte} (hbs : bs.length ≤ sz) :
    ∃ m', (allocAt m bid hle sz al .rw kind base init hsz hal hba).writeBytes bid 0 bs = some m' ∧
      m'.nextBlock = bid + 1 ∧
      (∀ b, b ≠ bid → m'.blocks b = m.blocks b) ∧
      ∃ blk', m'.blocks bid = some blk' ∧ blk'.kind = kind := by
  have hb := allocAt_blocks_eq m bid hle sz al .rw kind base init hsz hal hba
  have hin : Mem.inBounds ⟨sz, al, .rw, kind, base, init, hsz, hal, hba⟩ 0 bs.length = true := by
    rw [inBounds_iff]
    exact ⟨by decide, by simpa using hbs⟩
  unfold Mem.writeBytes
  split
  · next hnone => rw [hb] at hnone; cases hnone
  · next blk hblk =>
    rw [hb, Option.some.injEq] at hblk
    subst blk
    have hperm : (Perm.rw == Perm.rw && Mem.inBounds ⟨sz, al, .rw, kind, base, init, hsz, hal, hba⟩ 0 bs.length) = true := by
      simp [hin]
    simp only [hperm, ↓reduceIte]
    refine ⟨_, rfl, rfl, ?_, ?_⟩
    · intro b hne
      simp [beq_false_of_ne hne, allocAt_blocks_ne _ _ _ _ _ _ _ _ _ _ _ _ hne]
    · simp only [beq_self_eq_true, ↓reduceIte]
      exact ⟨_, rfl, rfl⟩

theorem readVal_stripConst (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64) (ty : CTy) :
    Sem.readVal tags m b off ty.stripConst = Sem.readVal tags m b off ty := by
  unfold Sem.readVal
  rw [stripConst_unqual]

/-- Lockstep correspondence between concrete stack slots and non-promoted `SymState.stack`. -/
inductive StkMatch (m : Mem) : List FrameSlot → Env → Prop where
  | nil : StkMatch m [] []
  | cons {sl : FrameSlot} {x : String} {b : BlockId} {ty : CTy}
      {restSlots : List FrameSlot} {restStk : Env} :
      sl.name = x →
      sl.blk = b →
      sl.ty = ty →
      (∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      StkMatch m restSlots restStk →
      StkMatch m (sl :: restSlots) ((x, b, ty) :: restStk)

theorem StkMatch.length_eq {m : Mem} {slots : List FrameSlot} {stk : Env}
    (h : StkMatch m slots stk) : slots.length = stk.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ ih => simp [ih]

theorem StkMatch.blocks_some {m : Mem} {slots : List FrameSlot} {stk : Env}
    (hm : StkMatch m slots stk) {sl : FrameSlot} (hsl : sl ∈ slots) :
    ∃ blk, m.blocks sl.blk = some blk ∧ blk.kind = .stack := by
  induction hm with
  | nil => cases hsl
  | cons _ hb _ hblk _ ih =>
    rcases List.mem_cons.mp hsl with rfl | hmem
    · rwa [hb]
    · exact ih hmem

theorem StkMatch.lookup_some {m : Mem} {slots : List FrameSlot} {stk : Env}
    (hm : StkMatch m slots stk) {baseEnv : Env} {x : String} {b : BlockId} {ty : CTy}
    (hl : stk.lookup x = some (b, ty)) :
    ∃ sl ∈ slots, sl.name = x ∧ sl.blk = b ∧ sl.ty = ty ∧
      (slotsEnv slots baseEnv).lookup x = some (b, ty) ∧
      ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack := by
  induction hm with
  | nil => cases hl
  | @cons sl y sb sty restS restStk hn hb hty hblk _ ih =>
    subst y sb sty
    by_cases hname : x = sl.name
    · subst hname
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      refine ⟨sl, .head _, rfl, rfl, rfl, ?_, hblk⟩
      simp [slotsEnv]
    · have hxf : (x == sl.name) = false := beq_false_of_ne hname
      simp only [List.lookup, hxf] at hl
      obtain ⟨sl', hsl', hn', hb', hty', henv', hblk'⟩ := ih hl
      refine ⟨sl', .tail _ hsl', hn', hb', hty', ?_, hblk'⟩
      simpa [slotsEnv, List.lookup, hxf] using henv'

theorem StkMatch.not_mem_of_lookup_none {m : Mem} {slots : List FrameSlot} {stk : Env}
    (hm : StkMatch m slots stk) {x : String} (hl : stk.lookup x = none) :
    ∀ sl ∈ slots, sl.name ≠ x := by
  induction hm with
  | nil => intro _ h; cases h
  | @cons sl y sb sty restS restStk hn _ _ _ _ ih =>
    subst y
    by_cases hname : x = sl.name
    · subst hname
      simp [List.lookup] at hl
    · have hxf : (x == sl.name) = false := beq_false_of_ne hname
      simp only [List.lookup, hxf] at hl
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs_tl
      · exact Ne.symm hname
      · exact ih hl s hs_tl

theorem StkMatch.of_blocks {m1 m2 : Mem} {slots : List FrameSlot} {stk : Env}
    (hm : StkMatch m1 slots stk)
    (hagree : ∀ sl ∈ slots, ∃ blk, m2.blocks sl.blk = some blk ∧ blk.kind = .stack) :
    StkMatch m2 slots stk := by
  induction hm with
  | nil => exact .nil
  | @cons sl x b ty restS restStk hn hb hty _ _ ih =>
    have hblk := hagree sl (.head _)
    rw [hb] at hblk
    exact .cons hn hb hty hblk (ih (fun s hs => hagree s (.tail _ hs)))

theorem StkMatch.of_blocks_agree {m1 m2 : Mem} {slots : List FrameSlot} {stk : Env}
    (hm : StkMatch m1 slots stk)
    (hagree : ∀ sl ∈ slots, m2.blocks sl.blk = m1.blocks sl.blk) :
    StkMatch m2 slots stk :=
  hm.of_blocks (fun sl hsl => by
    obtain ⟨blk, hb, hk⟩ := hm.blocks_some hsl
    exact ⟨blk, (hagree sl hsl).trans hb, hk⟩)

theorem StkMatch.drop {m : Mem} {s1 s2 : List FrameSlot} {stk : Env}
    (hm : StkMatch m (s1 ++ s2) stk) :
    StkMatch m s2 (stk.drop s1.length) := by
  induction s1 generalizing stk with
  | nil => exact hm
  | cons _ _ ih =>
    cases hm with
    | cons _ _ _ _ hrest => simpa using ih hrest

theorem StkMatch.take_blks {m : Mem} {s1 s2 : List FrameSlot} {stk : Env}
    (hm : StkMatch m (s1 ++ s2) stk) :
    (stk.take s1.length).map (·.2.1) = s1.map (·.blk) := by
  induction s1 generalizing stk with
  | nil => simp
  | cons sl tl ih =>
    cases hm with
    | cons _ hb _ _ hrest =>
      simp only [List.length_cons, List.take_succ_cons, List.map_cons, ih hrest, hb]

theorem StkMatch.append_iff {m : Mem} {s1 s2 : List FrameSlot} {stk : Env} :
    StkMatch m (s1 ++ s2) stk ↔
      StkMatch m s1 (stk.take s1.length) ∧ StkMatch m s2 (stk.drop s1.length) := by
  constructor
  · intro h
    induction s1 generalizing stk with
    | nil => exact ⟨.nil, h⟩
    | cons _ _ ih =>
      cases h with
      | cons hn hb hty hblk hrest =>
        obtain ⟨htake, hdrop⟩ := ih hrest
        exact ⟨.cons hn hb hty hblk htake, hdrop⟩
  · rintro ⟨h1, h2⟩
    induction s1 generalizing stk with
    | nil => exact h2
    | cons _ _ ih =>
      cases stk with
      | nil => cases h1
      | cons _ _ =>
        cases h1 with
        | cons hn hb hty hblk htake =>
          exact .cons hn hb hty hblk (ih htake (by simpa using h2))

theorem env_lookup_eq_none_of_drop_mem {e1 e2 : Env} {x : String}
    (hl : (e1 ++ e2).lookup x = none) : e2.lookup x = none := by
  induction e1 with
  | nil => exact hl
  | cons hd tl ih =>
    rcases hd with ⟨y, b, ty⟩
    by_cases hy : (x == y) = true
    · simp [List.lookup, hy] at hl
    · have hyf : (x == y) = false := Bool.eq_false_iff.mpr hy
      simp only [List.cons_append, List.lookup, hyf] at hl
      exact ih hl

/-- Lockstep correspondence between concrete stack slots and register-promoted `RegEnv`. -/
inductive SlotsMatch (tags : TypeEnv) (m : Mem) : List FrameSlot → RegEnv → Prop where
  | nil : SlotsMatch tags m [] []
  | cons {sl : FrameSlot} {x : String} {v : Val} {ty : CTy}
      {restSlots : List FrameSlot} {restRegs : RegEnv} :
      sl.name = x →
      sl.ty = ty →
      (∃ blk, m.blocks sl.blk = some blk ∧ blk.kind = .stack ∧ blk.perm = .rw ∧
        Mem.inBounds blk 0 (sizeofTy tags ty) = true ∧
        (0 < alignofTy tags ty → Mem.isAligned blk 0 (alignofTy tags ty) = true)) →
      (v ≠ .undef → Sem.readVal tags m sl.blk 0 ty = some v) →
      SlotsMatch tags m restSlots restRegs →
      SlotsMatch tags m (sl :: restSlots) ((x, v, ty) :: restRegs)

theorem SlotsMatch.length_eq {tags : TypeEnv} {m : Mem} {slots : List FrameSlot} {regs : RegEnv}
    (h : SlotsMatch tags m slots regs) : slots.length = regs.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ ih => simp [ih]

theorem SlotsMatch.blocks_some {tags : TypeEnv} {m : Mem} {slots : List FrameSlot} {regs : RegEnv}
    (hm : SlotsMatch tags m slots regs) {sl : FrameSlot} (hsl : sl ∈ slots) :
    ∃ blk, m.blocks sl.blk = some blk ∧ blk.kind = .stack ∧ blk.perm = .rw := by
  induction hm with
  | nil => cases hsl
  | cons _ _ hblk _ _ ih =>
    rcases List.mem_cons.mp hsl with rfl | hmem
    · rcases hblk with ⟨blk, hb, hk, hp, _⟩
      exact ⟨blk, hb, hk, hp⟩
    · exact ih hmem

theorem SlotsMatch.of_blocks_agree {tags : TypeEnv} {m1 m2 : Mem}
    {slots : List FrameSlot} {regs : RegEnv}
    (hm : SlotsMatch tags m1 slots regs)
    (hagree : ∀ sl ∈ slots, m2.blocks sl.blk = m1.blocks sl.blk) :
    SlotsMatch tags m2 slots regs := by
  induction hm with
  | nil => exact .nil
  | @cons sl x v ty restS restR hn ht hblk hrd _ ih =>
    have heq := hagree sl (.head _)
    refine .cons hn ht ?_ ?_ (ih (fun s hs => hagree s (.tail _ hs)))
    · rcases hblk with ⟨blk, hb, hk, hp, hin, hal⟩
      exact ⟨blk, heq ▸ hb, hk, hp, hin, hal⟩
    · intro hne
      have hrd1 := hrd hne
      unfold Sem.readVal Mem.readBytes at hrd1 ⊢
      rw [heq]
      exact hrd1

theorem SlotsMatch.lookup {tags : TypeEnv} {m : Mem} {slots : List FrameSlot} {regs : RegEnv}
    (hm : SlotsMatch tags m slots regs) {baseEnv : Env} {x : String} {v : Val} {ty : CTy}
    (hl : regs.lookup x = some (v, ty)) :
    ∃ sl ∈ slots, sl.name = x ∧ sl.ty = ty ∧
      (slotsEnv slots baseEnv).lookup x = some (sl.blk, ty) ∧
      (v ≠ .undef → Sem.readVal tags m sl.blk 0 ty = some v) := by
  induction hm with
  | nil => cases hl
  | @cons sl y ov oty restS restR hn ht hblk hrd _ ih =>
    subst y oty
    by_cases hname : (sl.name == x) = true
    · simp only [RegEnv.lookup_cons, hname, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      have hxs : sl.name = x := eq_of_beq hname
      refine ⟨sl, .head _, hxs, rfl, ?_, hrd⟩
      simp [slotsEnv, hxs]
    · have hnf : (sl.name == x) = false := Bool.eq_false_iff.mpr hname
      simp only [RegEnv.lookup_cons, hnf, Bool.false_eq_true, ↓reduceIte] at hl
      obtain ⟨sl', hsl', hn', hty', henv', hrd'⟩ := ih hl
      have hne : x ≠ sl.name := fun heq => hname (heq ▸ beq_self_eq_true x)
      have hxf : (x == sl.name) = false := beq_false_of_ne hne
      refine ⟨sl', .tail _ hsl', hn', hty', ?_, hrd'⟩
      simpa [slotsEnv, List.lookup, hxf] using henv'

theorem SlotsMatch.drop {tags : TypeEnv} {m : Mem} {s1 s2 : List FrameSlot} {regs : RegEnv}
    (hm : SlotsMatch tags m (s1 ++ s2) regs) :
    SlotsMatch tags m s2 (regs.drop s1.length) := by
  induction s1 generalizing regs with
  | nil => exact hm
  | cons sl tl ih =>
    cases hm with
    | cons _ _ _ _ hrest =>
      simpa using ih hrest

theorem SlotsMatch.append_iff {tags : TypeEnv} {m : Mem} {s1 s2 : List FrameSlot} {regs : RegEnv} :
    SlotsMatch tags m (s1 ++ s2) regs ↔
      SlotsMatch tags m s1 (regs.take s1.length) ∧ SlotsMatch tags m s2 (regs.drop s1.length) := by
  constructor
  · intro h
    induction s1 generalizing regs with
    | nil => exact ⟨.nil, h⟩
    | cons sl tl ih =>
      cases h with
      | cons hn ht hblk hrd hrest =>
        obtain ⟨htake, hdrop⟩ := ih hrest
        exact ⟨.cons hn ht hblk hrd htake, hdrop⟩
  · rintro ⟨h1, h2⟩
    induction s1 generalizing regs with
    | nil => exact h2
    | cons sl tl ih =>
      cases regs with
      | nil => cases h1
      | cons r rs =>
        cases h1 with
        | cons hn ht hblk hrd htake =>
          exact .cons hn ht hblk hrd (ih htake (by simpa using h2))

theorem writePlace_rval_scalar {tags : TypeEnv} {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v : Val} {vty : CTy}
    (ht : ValScalarTyped ty v)
    (hw : Sem.writeVal m b off ty v = some m') :
    Sem.writePlace tags m b off ty (.rval v vty) = some (.rval v ty, m') := by
  have hc := ht.castVal_self m
  unfold Sem.writePlace
  unfold ValScalarTyped at ht
  cases hu : ty.unqual <;> simp [hu] at ht
  case vaList => simp [hw, bind, Option.bind, pure, Pure.pure]
  all_goals simp [hc, hw, bind, Option.bind, pure, Pure.pure]

theorem SlotsMatch.not_mem_of_lookup_none {tags : TypeEnv} {m : Mem}
    {slots : List FrameSlot} {regs : RegEnv}
    (hm : SlotsMatch tags m slots regs) {x : String} (hl : regs.lookup x = none) :
    ∀ sl ∈ slots, sl.name ≠ x := by
  induction hm with
  | nil => intro _ h; cases h
  | @cons sl y ov oty restS restR hn _ _ _ _ ih =>
    subst y
    by_cases hname : (sl.name == x) = true
    · simp [RegEnv.lookup_cons, hname] at hl
    · have hnf : (sl.name == x) = false := Bool.eq_false_iff.mpr hname
      simp only [RegEnv.lookup_cons, hnf, Bool.false_eq_true, ↓reduceIte] at hl
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs_tl
      · exact fun heq => hname (heq ▸ beq_self_eq_true x)
      · exact ih hl s hs_tl

theorem slotsEnv_lookup_filter_reg (slots : List FrameSlot) (baseEnv : Env) {x : String}
    (hnot : ∀ sl ∈ stkSlots slots, sl.name ≠ x) :
    (slotsEnv slots baseEnv).lookup x = (slotsEnv (regSlots slots) baseEnv).lookup x := by
  induction slots with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨name, blk, ty, kind⟩
    cases kind
    · have ih' := ih (fun s hs => hnot s (by simpa [stkSlots_cons_reg] using hs))
      simp only [slotsEnv, List.map_cons, List.cons_append, List.lookup, regSlots_cons_reg]
      by_cases hx : (x == name) = true
      · simp [hx]
      · have hxf : (x == name) = false := Bool.eq_false_iff.mpr hx
        simpa [hxf, slotsEnv] using ih'
    · have hne : name ≠ x := hnot ⟨name, blk, ty, .stk⟩ (by simp [stkSlots_cons_stk])
      have hxf : (x == name) = false := beq_false_of_ne hne.symm
      have ih' := ih (fun s hs => hnot s (by simp [stkSlots_cons_stk, hs]))
      simp only [slotsEnv, List.map_cons, List.cons_append, List.lookup, hxf, regSlots_cons_stk]
      unfold slotsEnv at ih'
      exact ih'

theorem slotsEnv_lookup_filter_stk (slots : List FrameSlot) (baseEnv : Env) {x : String}
    (hnot : ∀ sl ∈ regSlots slots, sl.name ≠ x) :
    (slotsEnv slots baseEnv).lookup x = (slotsEnv (stkSlots slots) baseEnv).lookup x := by
  induction slots with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨name, blk, ty, kind⟩
    cases kind
    · have hne : name ≠ x := hnot ⟨name, blk, ty, .reg⟩ (by simp [regSlots_cons_reg])
      have hxf : (x == name) = false := beq_false_of_ne hne.symm
      have ih' := ih (fun s hs => hnot s (by simp [regSlots_cons_reg, hs]))
      simp only [slotsEnv, List.map_cons, List.cons_append, List.lookup, hxf, stkSlots_cons_reg]
      unfold slotsEnv at ih'
      exact ih'
    · have ih' := ih (fun s hs => hnot s (by simpa [regSlots_cons_stk] using hs))
      simp only [slotsEnv, List.map_cons, List.cons_append, List.lookup, stkSlots_cons_stk]
      by_cases hx : (x == name) = true
      · simp [hx]
      · have hxf : (x == name) = false := Bool.eq_false_iff.mpr hx
        simpa [hxf, slotsEnv] using ih'

theorem slotsEnv_lookup_none (slots : List FrameSlot) (baseEnv : Env) {x : String}
    (hreg : ∀ sl ∈ regSlots slots, sl.name ≠ x)
    (hstk : ∀ sl ∈ stkSlots slots, sl.name ≠ x) :
    (slotsEnv slots baseEnv).lookup x = baseEnv.lookup x := by
  rw [slotsEnv_lookup_filter_reg slots baseEnv hstk]
  generalize regSlots slots = rslots at hreg
  induction rslots with
  | nil => rfl
  | cons hd tl ih =>
    have hne : hd.name ≠ x := hreg hd (.head _)
    have hxf : (x == hd.name) = false := beq_false_of_ne hne.symm
    simp only [slotsEnv, List.map_cons, List.cons_append, List.lookup, hxf]
    exact ih (fun s hs => hreg s (.tail _ hs))

theorem exprType?_congr_env {tags : TypeEnv} {e1 e2 : Env} {fnProtos : String → Option FnSig}
    (hcongr : ∀ x, (e1.lookup x).map Prod.snd = (e2.lookup x).map Prod.snd) :
    ∀ e : CExpr, Sem.exprType? tags e1 fnProtos e = Sem.exprType? tags e2 fnProtos e
  | .paren e => by simp only [Sem.exprType?, exprType?_congr_env hcongr e]
  | .lit _ _ _ _ _ => rfl
  | .strLit _ => rfl
  | .var x => by
    have h := hcongr x
    simp only [Sem.exprType?]
    cases h1 : e1.lookup x <;> cases h2 : e2.lookup x <;> simp [h1, h2] at h ⊢
    exact h
  | .sizeOfTy _ => rfl
  | .sizeOfExpr _ => rfl
  | .cast _ _ => rfl
  | .unary _ e => by simp only [Sem.exprType?, exprType?_congr_env hcongr e]
  | .addrOf e => by simp only [Sem.exprType?, exprType?_congr_env hcongr e]
  | .deref e => by simp only [Sem.exprType?, exprType?_congr_env hcongr e]
  | .index e _ => by simp only [Sem.exprType?, exprType?_congr_env hcongr e]
  | .member e _ => by simp only [Sem.exprType?, exprType?_congr_env hcongr e]
  | .arrow e _ => by simp only [Sem.exprType?, exprType?_congr_env hcongr e]
  | .binary _ l r => by simp only [Sem.exprType?, exprType?_congr_env hcongr l, exprType?_congr_env hcongr r]
  | .logAnd _ _ => rfl
  | .logOr _ _ => rfl
  | .cond _ t _ => by simp only [Sem.exprType?, exprType?_congr_env hcongr t]
  | .comma _ r => by simp only [Sem.exprType?, exprType?_congr_env hcongr r]
  | .assign _ l _ => by simp only [Sem.exprType?, exprType?_congr_env hcongr l]
  | .incDec _ l => by simp only [Sem.exprType?, exprType?_congr_env hcongr l]
  | .call fn _ => by simp only [Sem.exprType?, exprType?_congr_env hcongr fn]
  | .vaStart _ _ => rfl
  | .vaEnd _ => rfl

theorem castVal_of_blocks_agree {m1 m2 : Mem} {target : CTy} {v cv : Val}
    (hagree : ∀ b blk, m1.blocks b = some blk → m2.blocks b = some blk)
    (h : Sem.castVal m1 target v = some cv) :
    Sem.castVal m2 target v = some cv := by
  unfold Sem.castVal at h ⊢
  dsimp only at h ⊢
  by_cases hv : target.unqual.isVoid = true
  · simp only [hv, ↓reduceIte] at h ⊢; exact h
  · have hvf : target.unqual.isVoid = false := Bool.eq_false_iff.mpr hv
    simp only [hvf, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hk : target.unqual.intKind? with
    | none => simp only [hk] at h ⊢; exact h
    | some k =>
      simp only [hk] at h ⊢
      cases v with
      | ptr b off =>
        dsimp only at h ⊢
        unfold Mem.addrOf at h ⊢
        cases hb : m1.blocks b with
        | none => simp [hb] at h
        | some blk =>
          simp only [hb] at h
          rw [hagree b blk hb]
          exact h
      | _ => exact h

/-- Refinement relation between abstract `SymState` and small-step `(env, blks, m)` inside `cur`/`outer`. -/
structure Refines (tags : TypeEnv) (baseEnv : Env) (cur : FrameScope) (outer : List FrameScope)
    (s : SymState) (env : Env) (blks : List BlockId) (m : Mem) : Prop where
  env_eq : env = slotsEnv (allSlots cur outer) baseEnv
  blks_eq : blks = cur.blks
  nodup_blks : (allSlotBlks cur outer).Nodup
  disjoint_names : ∀ x, s.regs.lookup x = none ∨ s.stack.lookup x = none
  nextBlock_le : s.mem.nextBlock ≤ m.nextBlock
  slots_absent : ∀ b ∈ allRegBlks cur outer, s.mem.blocks b = none
  blocks_agree : ∀ b, b ∉ allRegBlks cur outer → m.blocks b = s.mem.blocks b
  regs_match : SlotsMatch tags m (allRegSlots cur outer) s.regs
  stk_match : StkMatch s.mem (allStkSlots cur outer) s.stack

namespace Refines

theorem reg_lt_nextBlock {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {b : BlockId} (hb : b ∈ allRegBlks cur outer) : b < m.nextBlock := by
  obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hb
  obtain ⟨blk, hbm, _⟩ := hr.regs_match.blocks_some hsl
  exact lt_nextBlock_of_some hbm

theorem stk_lt_nextBlock {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {b : BlockId} (hb : b ∈ allStkBlks cur outer) : b < m.nextBlock := by
  obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hb
  obtain ⟨blk, hbs, _⟩ := hr.stk_match.blocks_some hsl
  exact Nat.lt_of_lt_of_le (lt_nextBlock_of_some hbs) hr.nextBlock_le

theorem all_lt_nextBlock {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {b : BlockId} (hb : b ∈ allSlotBlks cur outer) : b < m.nextBlock := by
  rcases allRegBlks_or_allStkBlks_of_allSlotBlks hb with hreg | hstk
  · exact hr.reg_lt_nextBlock hreg
  · exact hr.stk_lt_nextBlock hstk

theorem mem_blocks_some {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m) {b : BlockId} {blk : Block}
    (hb : s.mem.blocks b = some blk) :
    b ∉ allRegBlks cur outer ∧ m.blocks b = some blk := by
  have hnot : b ∉ allRegBlks cur outer := fun hmem => by
    have hnone := hr.slots_absent b hmem
    rw [hb] at hnone
    cases hnone
  exact ⟨hnot, (hr.blocks_agree b hnot).trans hb⟩

theorem lookup_reg {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m) {x : String} {v : Val} {ty : CTy}
    (hl : s.regs.lookup x = some (v, ty)) :
    ∃ sl ∈ allRegSlots cur outer, sl.name = x ∧ sl.ty = ty ∧
      env.lookup x = some (sl.blk, ty) ∧
      (v ≠ .undef → Sem.readVal tags m sl.blk 0 ty = some v) := by
  have hstk_none : s.stack.lookup x = none := by
    rcases hr.disjoint_names x with hnone | hnone
    · rw [hl] at hnone; cases hnone
    · exact hnone
  have hnot_stk := hr.stk_match.not_mem_of_lookup_none hstk_none
  obtain ⟨sl, hsl, hname, hty, henv, hrd⟩ := hr.regs_match.lookup (baseEnv := baseEnv) hl
  have henv' : env.lookup x = some (sl.blk, ty) := by
    rw [hr.env_eq, slotsEnv_lookup_filter_reg _ baseEnv hnot_stk]
    exact henv
  exact ⟨sl, hsl, hname, hty, henv', hrd⟩

theorem lookup_stk {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m) {x : String} {b : BlockId} {ty : CTy}
    (hl : s.stack.lookup x = some (b, ty)) :
    b ∉ allRegBlks cur outer ∧
    env.lookup x = some (b, ty) ∧
    ∃ blk, s.mem.blocks b = some blk ∧ blk.kind = .stack ∧ m.blocks b = some blk := by
  have hreg_none : s.regs.lookup x = none := by
    rcases hr.disjoint_names x with hnone | hnone
    · exact hnone
    · rw [hl] at hnone; cases hnone
  have hnot_reg := hr.regs_match.not_mem_of_lookup_none hreg_none
  obtain ⟨sl, _, _, _, _, henv, blk, hbs, hkind⟩ := hr.stk_match.lookup_some (baseEnv := baseEnv) hl
  have henv' : env.lookup x = some (b, ty) := by
    rw [hr.env_eq, slotsEnv_lookup_filter_stk _ baseEnv hnot_reg]
    exact henv
  obtain ⟨hnot, hbm⟩ := hr.mem_blocks_some hbs
  exact ⟨hnot, henv', blk, hbs, hkind, hbm⟩

theorem lookup_none {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m) {x : String}
    (hreg : s.regs.lookup x = none) (hstk : s.stack.lookup x = none) :
    env.lookup x = baseEnv.lookup x := by
  rw [hr.env_eq]
  exact slotsEnv_lookup_none (allSlots cur outer) baseEnv
    (hr.regs_match.not_mem_of_lookup_none hreg)
    (hr.stk_match.not_mem_of_lookup_none hstk)

private theorem regEnv_lookup_map_zero_some (regs : RegEnv) (rest : Env) {x : String} {v : Val} {ty : CTy}
    (hreg : regs.lookup x = some (v, ty)) :
    (regs.map (fun p => (p.1, (0 : BlockId), p.2.2)) ++ rest).lookup x = some (0, ty) := by
  induction regs with
  | nil => simp at hreg
  | cons hd tl ih =>
    rcases hd with ⟨y, ov, oty⟩
    by_cases hy : (y == x) = true
    · have hyx : x = y := (eq_of_beq hy).symm
      simp only [RegEnv.lookup_cons, hy, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hreg
      rcases hreg with ⟨rfl, rfl⟩
      simp [hyx]
    · have hyf : (y == x) = false := Bool.eq_false_iff.mpr hy
      have hne : x ≠ y := fun heq => hy (heq ▸ beq_self_eq_true x)
      have hxyf : (x == y) = false := beq_false_of_ne hne
      simp only [RegEnv.lookup_cons, hyf, Bool.false_eq_true, ↓reduceIte] at hreg
      simp only [List.map_cons, List.cons_append, List.lookup, hxyf]
      exact ih hreg

private theorem regEnv_lookup_map_zero_none (regs : RegEnv) {x : String}
    (hreg : regs.lookup x = none) :
    (regs.map (fun p => (p.1, (0 : BlockId), p.2.2))).lookup x = none := by
  induction regs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨y, ov, oty⟩
    by_cases hy : (y == x) = true
    · simp [RegEnv.lookup_cons, hy] at hreg
    · have hyf : (y == x) = false := Bool.eq_false_iff.mpr hy
      have hne : x ≠ y := fun heq => hy (heq ▸ beq_self_eq_true x)
      have hxyf : (x == y) = false := beq_false_of_ne hne
      simp only [RegEnv.lookup_cons, hyf, Bool.false_eq_true, ↓reduceIte] at hreg
      simp only [List.map_cons, List.lookup, hxyf]
      exact ih hreg

private theorem env_lookup_append_none (l1 l2 : Env) {x : String} (hl1 : l1.lookup x = none) :
    (l1 ++ l2).lookup x = l2.lookup x := by
  induction l1 with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨y, b, ty⟩
    by_cases hxy : (x == y) = true
    · simp [List.lookup, hxy] at hl1
    · have hxyf : (x == y) = false := Bool.eq_false_iff.mpr hxy
      simp only [List.lookup, hxyf] at hl1
      simp only [List.cons_append, List.lookup, hxyf]
      exact ih hl1

theorem exprType?_eq {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {fnProtos : String → Option FnSig} (e : CExpr) :
    Sem.exprType? tags (s.typeEnv baseEnv) fnProtos e = Sem.exprType? tags env fnProtos e := by
  apply exprType?_congr_env
  intro x
  cases hreg : s.regs.lookup x with
  | some p =>
    obtain ⟨_, _, _, _, henv, _⟩ := hr.lookup_reg hreg
    have htype_lhs : (s.typeEnv baseEnv).lookup x = some (0, p.2) := by
      simp only [SymState.typeEnv, List.append_assoc]
      exact regEnv_lookup_map_zero_some s.regs (s.stack ++ baseEnv) hreg
    rw [htype_lhs, henv]
    rfl
  | none =>
    have hreg_map_none : (s.regs.map (fun p => (p.1, (0 : BlockId), p.2.2))).lookup x = none :=
      regEnv_lookup_map_zero_none s.regs hreg
    cases hstk : s.stack.lookup x with
    | some p =>
      obtain ⟨_, henv, _⟩ := hr.lookup_stk hstk
      have htype_lhs : (s.typeEnv baseEnv).lookup x = some p := by
        simp only [SymState.typeEnv, List.append_assoc]
        rw [env_lookup_append_none _ _ hreg_map_none]
        clear hreg_map_none hreg henv
        let rec go : (stk : Env) → stk.lookup x = some p → (stk ++ baseEnv).lookup x = some p
          | [], h => by simp at h
          | (y, b, ty) :: tl, h => by
            by_cases hxy : (x == y) = true
            · simp only [List.lookup, hxy] at h
              simp only [List.cons_append, List.lookup, hxy]
              exact h
            · have hxyf : (x == y) = false := Bool.eq_false_iff.mpr hxy
              simp only [List.lookup, hxyf] at h
              simp only [List.cons_append, List.lookup, hxyf]
              exact go tl h
        exact go s.stack hstk
      rw [htype_lhs, henv]
    | none =>
      have hnone := hr.lookup_none hreg hstk
      have htype_lhs : (s.typeEnv baseEnv).lookup x = baseEnv.lookup x := by
        simp only [SymState.typeEnv, List.append_assoc]
        rw [env_lookup_append_none _ _ hreg_map_none, env_lookup_append_none _ _ hstk]
      rw [htype_lhs, hnone]

private theorem slotsMatch_set_first {tags : TypeEnv} {m : Mem}
    {slots : List FrameSlot} {regs : RegEnv} {x : String} {ov nv : Val} {ty : CTy}
    (hm : SlotsMatch tags m slots regs)
    (hnodup : (slots.map (·.blk)).Nodup)
    (hl : regs.lookup x = some (ov, ty))
    (hnc : ty.isConst = false)
    (ht : ValScalarTyped ty nv) :
    ∃ (sl : FrameSlot) (m' : Mem),
      sl ∈ slots ∧
      sl.name = x ∧
      sl.ty = ty ∧
      (∀ baseEnv, (slotsEnv slots baseEnv).lookup x = some (sl.blk, ty)) ∧
      Sem.writeVal m sl.blk 0 ty nv = some m' ∧
      SlotsMatch tags m' slots (regs.set x nv ty) ∧
      (∀ b, b ≠ sl.blk → m'.blocks b = m.blocks b) ∧
      m'.nextBlock = m.nextBlock := by
  induction hm with
  | nil => cases hl
  | @cons sl y curV curTy restS restR hn hty hblk hrd hrest ih =>
    subst y curTy
    rcases List.nodup_cons.mp hnodup with ⟨hnot_in, hnodup_rest⟩
    by_cases hx : (sl.name == x) = true
    · have hname_eq : sl.name = x := eq_of_beq hx
      simp only [RegEnv.lookup_cons, hx, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      rcases hblk with ⟨blk, hbm, hkind, hperm, hin, hal⟩
      obtain ⟨hal_pos, _⟩ := ht.align_eq_sizeof
      have hal' : Mem.isAligned blk 0 (alignofTy tags sl.ty) = true := hal hal_pos
      obtain ⟨m', hm', ⟨_, _, hwb⟩, hrd'⟩ :=
        writeVal_scalar_some hnc hbm hperm hin hal' ht
      have hne_all : ∀ s' ∈ restS, s'.blk ≠ sl.blk := fun s' hs' heq =>
        hnot_in (List.mem_map.mpr ⟨s', hs', heq⟩)
      have hne_blocks : ∀ b, b ≠ sl.blk → m'.blocks b = m.blocks b := fun b hne =>
        writeVal_blocks_ne hm' hne
      have henv_fn : ∀ baseEnv, (slotsEnv (sl :: restS) baseEnv).lookup x = some (sl.blk, sl.ty) :=
        fun baseEnv => by simp [slotsEnv, hname_eq]
      refine ⟨sl, m', .head _, hname_eq, rfl, henv_fn, hm', ?_, hne_blocks, writeVal_nextBlock hm'⟩
      simp only [RegEnv.set_cons, hx, ↓reduceIte]
      refine .cons rfl rfl ?_ (fun _ => hrd') ?_
      · exact ⟨_, writeBytes_blocks_eq hbm hwb, hkind, hperm, hin, hal⟩
      · exact hrest.of_blocks_agree (fun s' hs' => hne_blocks s'.blk (hne_all s' hs'))
    · have hxf : (sl.name == x) = false := Bool.eq_false_iff.mpr hx
      simp only [RegEnv.lookup_cons, hxf, Bool.false_eq_true, ↓reduceIte] at hl
      obtain ⟨sl', m', hsl', hn', hty', henv', hm', hrest', hne_blocks, hnext⟩ :=
        ih hnodup_rest hl
      have hne_sl : sl.blk ≠ sl'.blk := fun heq =>
        hnot_in (List.mem_map.mpr ⟨sl', hsl', heq.symm⟩)
      have hagree_sl : m'.blocks sl.blk = m.blocks sl.blk := hne_blocks sl.blk hne_sl
      have hne_xs : x ≠ sl.name := fun heq => hx (heq ▸ beq_self_eq_true x)
      have hxsf : (x == sl.name) = false := beq_false_of_ne hne_xs
      have henv_fn : ∀ baseEnv, (slotsEnv (sl :: restS) baseEnv).lookup x = some (sl'.blk, ty) :=
        fun baseEnv => by simpa [slotsEnv, List.lookup, hxsf] using henv' baseEnv
      refine ⟨sl', m', .tail _ hsl', hn', hty', henv_fn, hm', ?_, hne_blocks, hnext⟩
      simp only [RegEnv.set_cons, hxf, Bool.false_eq_true, ↓reduceIte]
      rcases hblk with ⟨blk, hbm, hkind, hperm, hin, hal⟩
      refine .cons rfl rfl ⟨blk, hagree_sl ▸ hbm, hkind, hperm, hin, hal⟩ (fun hne => ?_) hrest'
      have hrd1 := hrd hne
      unfold Sem.readVal Mem.readBytes at hrd1 ⊢
      rw [hagree_sl]
      exact hrd1

theorem write_reg {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {x : String} {ov nv : Val} {ty : CTy}
    (hl : s.regs.lookup x = some (ov, ty))
    (hnc : ty.isConst = false) (ht : ValScalarTyped ty nv) :
    ∃ sl ∈ allRegSlots cur outer, ∃ m',
      sl.name = x ∧ sl.ty = ty ∧
      env.lookup x = some (sl.blk, ty) ∧
      Sem.writeVal m sl.blk 0 ty nv = some m' ∧
      Sem.writePlace tags m sl.blk 0 ty (.rval nv ty) = some (.rval nv ty, m') ∧
      Refines tags baseEnv cur outer { s with regs := s.regs.set x nv ty } env blks m' := by
  have hnd_reg : (allRegSlots cur outer |>.map (·.blk)).Nodup :=
    nodup_regBlks_of_nodup hr.nodup_blks
  obtain ⟨sl, m', hsl, hname, hty, hfn, hwm, hmatch', hne_blocks, hnext⟩ :=
    slotsMatch_set_first hr.regs_match hnd_reg hl hnc ht
  have hstk_none : s.stack.lookup x = none := by
    rcases hr.disjoint_names x with h | h
    · rw [hl] at h; cases h
    · exact h
  have hwrplace := writePlace_rval_scalar (tags := tags) (vty := ty) ht hwm
  have henv_x : env.lookup x = some (sl.blk, ty) := by
    rw [hr.env_eq, slotsEnv_lookup_filter_reg _ baseEnv (hr.stk_match.not_mem_of_lookup_none hstk_none)]
    exact hfn baseEnv
  refine ⟨sl, hsl, m', hname, hty, henv_x, hwm, hwrplace, ?_⟩
  refine ⟨hr.env_eq, hr.blks_eq, hr.nodup_blks, ?_, by rw [hnext]; exact hr.nextBlock_le,
    hr.slots_absent, ?_, hmatch', hr.stk_match⟩
  · intro y
    rcases hr.disjoint_names y with hnone | hnone
    · left; exact RegEnv.lookup_set_none nv ty hnone
    · right; exact hnone
  · intro b hbnot
    have hne : b ≠ sl.blk := fun heq => hbnot (List.mem_map.mpr ⟨sl, hsl, heq.symm⟩)
    rw [hne_blocks b hne, hr.blocks_agree b hbnot]

theorem alloc_none {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m m1 : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {x : String} {ty : CTy} {base : UInt64} {bid : BlockId}
    (hstk_none : s.stack.lookup x = none)
    (hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy tags ty))
    (hba : base.toNat % max 1 (alignofTy tags ty) = 0)
    (halloc : m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1)) :
    Refines tags baseEnv (⟨x, bid, ty, .reg⟩ :: cur) outer
      { s with regs := (x, .undef, ty) :: s.regs }
      ((x, bid, ty) :: env) (bid :: blks) m1 := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst halloc).symm
  have hm1 : m1 = (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd halloc).symm
  subst hbid hm1
  have hm1_eq : (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base (fun _ => .undef) hsz hal hba).2.blocks m.nextBlock = _ :=
    alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hnot_in_all : m.nextBlock ∉ allSlotBlks cur outer := fun hmem =>
    Nat.lt_irrefl _ (hr.all_lt_nextBlock hmem)
  have hnot_in_reg : m.nextBlock ∉ allRegBlks cur outer := fun hmem =>
    Nat.lt_irrefl _ (hr.reg_lt_nextBlock hmem)
  have hsm_none : s.mem.blocks m.nextBlock = none := s.mem.fresh _ hr.nextBlock_le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [slotsEnv, allSlots] using congrArg (fun e => (x, m.nextBlock, ty) :: e) hr.env_eq
  · simp [FrameScope.blks, hr.blks_eq]
  · simp only [allSlotBlks, allSlots, List.cons_append, List.map_cons, List.nodup_cons]
    exact ⟨hnot_in_all, hr.nodup_blks⟩
  · intro y
    by_cases hy : x = y
    · subst hy; right; exact hstk_none
    · have hxyf : (x == y) = false := beq_false_of_ne hy
      rcases hr.disjoint_names y with hrn | hsn
      · left; simp [RegEnv.lookup_cons, hxyf, hrn]
      · right; exact hsn
  · rw [alloc_snd_nextBlock]
    exact Nat.le_trans hr.nextBlock_le (Nat.le_succ _)
  · intro b hb
    simp only [allRegBlks, allRegSlots, allSlots, List.cons_append, regSlots_cons_reg,
      List.map_cons, List.mem_cons] at hb
    rcases hb with rfl | hmem
    · exact hsm_none
    · exact hr.slots_absent b hmem
  · intro b hbnot
    simp only [allRegBlks, allRegSlots, allSlots, List.cons_append, regSlots_cons_reg,
      List.map_cons, List.mem_cons, not_or] at hbnot
    rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hbnot.1]
    exact hr.blocks_agree b hbnot.2
  · simp only [allRegSlots, allSlots, List.cons_append, regSlots_cons_reg]
    refine .cons rfl rfl ?_ (fun hne => False.elim (hne rfl)) ?_
    · refine ⟨_, hm1_eq, rfl, rfl, ?_, ?_⟩
      · rw [inBounds_iff]
        have hz : (0 : Int64).toInt = 0 := rfl
        have hle_sz : sizeofTy tags ty ≤ max 1 (sizeofTy tags ty) := Nat.le_max_right _ _
        simp [hz, hle_sz]
      · intro hpos
        rw [isAligned_iff]
        have hz : (0 : Int64).toInt = 0 := rfl
        have hmax : max 1 (alignofTy tags ty) = alignofTy tags ty := Nat.max_eq_right hpos
        simp [hz, hpos]
        simpa [hmax] using hba
    · exact hr.regs_match.of_blocks_agree (fun sl hsl =>
        alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (fun heq => hnot_in_reg (heq ▸ List.mem_map.mpr ⟨sl, hsl, rfl⟩)))
  · simpa [allStkSlots, allSlots, stkSlots_cons_reg] using hr.stk_match

theorem alloc_some {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m m1 : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {x : String} {ty vty : CTy} {v : Val} {base : UInt64} {bid : BlockId}
    (hstk_none : s.stack.lookup x = none)
    (ht : ValScalarTyped ty v)
    (hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy tags ty))
    (hba : base.toNat % max 1 (alignofTy tags ty) = 0)
    (halloc : m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1)) :
    ∃ r m2,
      Sem.writePlace tags m1 bid 0 ty.stripConst (.rval v vty) = some (r, m2) ∧
      Refines tags baseEnv (⟨x, bid, ty, .reg⟩ :: cur) outer
        { s with regs := (x, v, ty) :: s.regs }
        ((x, bid, ty) :: env) (bid :: blks) m2 := by
  have hr1 := hr.alloc_none (x := x) hstk_none hsz hal hba halloc
  have hnc : ty.stripConst.isConst = false := stripConst_isConst ty
  have hts : ValScalarTyped ty.stripConst v := by
    unfold ValScalarTyped at ht ⊢
    rwa [stripConst_unqual]
  have hsz_eq : sizeofTy tags ty.stripConst = sizeofTy tags ty := by
    rw [← sizeofTy_unqual, stripConst_unqual, sizeofTy_unqual]
  have hal_eq : alignofTy tags ty.stripConst = alignofTy tags ty := by
    rw [← alignofTy_unqual, stripConst_unqual, alignofTy_unqual]
  obtain ⟨blk1, hm1, hkind, hperm, hin, hal_m1⟩ :=
    match hr1.regs_match with
    | .cons _ _ hblk _ _ => hblk
  have hrest1 : SlotsMatch tags m1 (allRegSlots cur outer) s.regs :=
    match hr1.regs_match with
    | .cons _ _ _ _ hrest => hrest
  obtain ⟨hal_pos, _⟩ := hts.align_eq_sizeof
  have hin' : Mem.inBounds blk1 0 (sizeofTy tags ty.stripConst) = true := by rwa [hsz_eq]
  have hal' : Mem.isAligned blk1 0 (alignofTy tags ty.stripConst) = true := by
    rw [hal_eq]; exact hal_m1 (by rwa [← hal_eq])
  obtain ⟨m2, hwm, _, hrd⟩ := writeVal_scalar_some hnc hm1 hperm hin' hal' hts
  have hwrplace := writePlace_rval_scalar (tags := tags) (vty := vty) hts hwm
  refine ⟨.rval v ty.stripConst, m2, hwrplace, ?_⟩
  have hnext : m2.nextBlock = m1.nextBlock := writeVal_nextBlock hwm
  have hbid : bid = m.nextBlock := (congrArg Prod.fst halloc).symm
  have hnot_in_reg : bid ∉ allRegBlks cur outer := fun hmem =>
    Nat.lt_irrefl _ (hbid ▸ hr.reg_lt_nextBlock hmem)
  refine ⟨hr1.env_eq, hr1.blks_eq, hr1.nodup_blks, ?_, ?_, hr1.slots_absent, ?_, ?_, hr1.stk_match⟩
  · intro y
    by_cases hy : x = y
    · subst hy; right; exact hstk_none
    · have hxyf : (x == y) = false := beq_false_of_ne hy
      rcases hr.disjoint_names y with hrn | hsn
      · left; simp [RegEnv.lookup_cons, hxyf, hrn]
      · right; exact hsn
  · rw [hnext]; exact hr1.nextBlock_le
  · intro b hbnot
    simp only [allRegBlks, allRegSlots, allSlots, List.cons_append, regSlots_cons_reg,
      List.map_cons, List.mem_cons, not_or] at hbnot
    rw [writeVal_blocks_ne hwm hbnot.1]
    exact hr1.blocks_agree b (by
      simp only [allRegBlks, allRegSlots, allSlots, List.cons_append, regSlots_cons_reg,
        List.map_cons, List.mem_cons, not_or]
      exact hbnot)
  · obtain ⟨_, hw_bs⟩ := writeVal_writeBytes hwm
    have hbm2 := writeBytes_blocks_eq hm1 hw_bs
    have hrd_ty : Sem.readVal tags m2 bid 0 ty = some v := by
      rwa [← readVal_stripConst tags m2 bid 0 ty]
    simp only [allRegSlots, allSlots, List.cons_append, regSlots_cons_reg]
    refine .cons rfl rfl ⟨_, hbm2, hkind, hperm, hin, hal_m1⟩ (fun _ => hrd_ty) ?_
    exact hrest1.of_blocks_agree (fun sl hsl =>
      writeVal_blocks_ne hwm (fun heq => hnot_in_reg (List.mem_map.mpr ⟨sl, hsl, heq⟩)))

theorem alloc_stk_none {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m m1 : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {x : String} {ty : CTy} {base : UInt64} {bid : BlockId}
    (hreg_none : s.regs.lookup x = none)
    (hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy tags ty))
    (hba : base.toNat % max 1 (alignofTy tags ty) = 0)
    (halloc : m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1))
    (hle : s.mem.nextBlock ≤ bid := Nat.le_trans hr.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))) :
    Refines tags baseEnv (⟨x, bid, ty, .stk⟩ :: cur) outer
      { s with
        stack := (x, bid, ty) :: s.stack
        mem := allocAt s.mem bid hle
          (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
          .rw .stack base (fun _ => .undef) hsz hal hba }
      ((x, bid, ty) :: env) (bid :: blks) m1 := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst halloc).symm
  have hm1 : m1 = (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd halloc).symm
  subst hbid hm1
  have hm1_eq : (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base (fun _ => .undef) hsz hal hba).2.blocks m.nextBlock = _ :=
    alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hnot_in_all : m.nextBlock ∉ allSlotBlks cur outer := fun hmem =>
    Nat.lt_irrefl _ (hr.all_lt_nextBlock hmem)
  have hnot_in_reg : m.nextBlock ∉ allRegBlks cur outer := fun hmem =>
    Nat.lt_irrefl _ (hr.reg_lt_nextBlock hmem)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [slotsEnv, allSlots] using congrArg (fun e => (x, m.nextBlock, ty) :: e) hr.env_eq
  · simp [FrameScope.blks, hr.blks_eq]
  · simp only [allSlotBlks, allSlots, List.cons_append, List.map_cons, List.nodup_cons]
    exact ⟨hnot_in_all, hr.nodup_blks⟩
  · intro y
    by_cases hy : x = y
    · subst hy; left; exact hreg_none
    · have hxyf : (y == x) = false := beq_false_of_ne (Ne.symm hy)
      rcases hr.disjoint_names y with hrn | hsn
      · left; exact hrn
      · right; simp [List.lookup, hxyf, hsn]
  · simp [allocAt_nextBlock, alloc_snd_nextBlock]
  · intro b hb
    simp only [allRegBlks, allRegSlots, allSlots, List.cons_append, regSlots_cons_stk] at hb
    have hne : b ≠ m.nextBlock := Nat.ne_of_lt (hr.reg_lt_nextBlock hb)
    rw [allocAt_blocks_ne _ _ _ _ _ _ _ _ _ _ _ _ hne]
    exact hr.slots_absent b hb
  · intro b hbnot
    simp only [allRegBlks, allRegSlots, allSlots, List.cons_append, regSlots_cons_stk] at hbnot
    by_cases hbm : b = m.nextBlock
    · subst hbm
      rw [hm1_eq, allocAt_blocks_eq]
    · rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hbm,
        allocAt_blocks_ne _ _ _ _ _ _ _ _ _ _ _ _ hbm]
      exact hr.blocks_agree b hbnot
  · simp only [allRegSlots, allSlots, List.cons_append, regSlots_cons_stk]
    exact hr.regs_match.of_blocks_agree (fun sl hsl =>
      alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (fun heq => hnot_in_reg (heq ▸ List.mem_map.mpr ⟨sl, hsl, rfl⟩)))
  · simp only [allStkSlots, allSlots, List.cons_append, stkSlots_cons_stk]
    refine .cons rfl rfl rfl ⟨_, allocAt_blocks_eq _ _ _ _ _ _ _ _ _ _ _ _, rfl⟩ ?_
    exact hr.stk_match.of_blocks_agree (fun sl hsl =>
      allocAt_blocks_ne _ _ _ _ _ _ _ _ _ _ _ _ (fun heq =>
        hnot_in_all (mem_allSlotBlks_of_stk (List.mem_map.mpr ⟨sl, hsl, heq⟩))))

theorem alloc_strLit {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m m' : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {str : String} {base : UInt64} {bid : BlockId}
    (hsz : str.utf8ByteSize + 1 < ptrDiffLimit)
    (halloc : m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m'))
    (hle : s.mem.nextBlock ≤ bid := Nat.le_trans hr.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))) :
    Refines tags baseEnv cur outer
      { s with mem := (allocAt s.mem bid hle (str.utf8ByteSize + 1) 1 .ro .global base
        (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)) }
      env blks m' := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst halloc).symm
  have hm' : m' = (m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)).2 :=
    (congrArg Prod.snd halloc).symm
  subst hbid hm'
  have hnot_reg : m.nextBlock ∉ allRegBlks cur outer := fun hmem =>
    Nat.lt_irrefl _ (hr.reg_lt_nextBlock hmem)
  refine ⟨hr.env_eq, hr.blks_eq, hr.nodup_blks, hr.disjoint_names, ?_, ?_, ?_, ?_, ?_⟩
  · simp [allocAt_nextBlock, alloc_snd_nextBlock]
  · intro b hb
    have hne : b ≠ m.nextBlock := Nat.ne_of_lt (hr.reg_lt_nextBlock hb)
    rw [allocAt_blocks_ne _ _ _ _ _ _ _ _ _ _ _ _ hne]
    exact hr.slots_absent b hb
  · intro b hbnot
    by_cases hbm : b = m.nextBlock
    · subst hbm; rw [alloc_blocks_eq, allocAt_blocks_eq]
    · rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hbm,
        allocAt_blocks_ne _ _ _ _ _ _ _ _ _ _ _ _ hbm]
      exact hr.blocks_agree b hbnot
  · refine hr.regs_match.of_blocks_agree (fun sl hsl => ?_)
    have hne : sl.blk ≠ m.nextBlock := fun heq => hnot_reg (heq ▸ List.mem_map.mpr ⟨sl, hsl, rfl⟩)
    exact alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne
  · refine hr.stk_match.of_blocks (fun sl hsl => ?_)
    have hne : sl.blk ≠ m.nextBlock := fun heq => by
      have hlt := hr.stk_lt_nextBlock (List.mem_map.mpr ⟨sl, hsl, heq⟩)
      exact Nat.lt_irrefl _ hlt
    rw [allocAt_blocks_ne _ _ _ _ _ _ _ _ _ _ _ _ hne]
    exact hr.stk_match.blocks_some hsl

theorem enter_block {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m) :
    Refines tags baseEnv [] (cur :: outer) s env [] m :=
  ⟨hr.env_eq, rfl, hr.nodup_blks, hr.disjoint_names, hr.nextBlock_le,
    hr.slots_absent, hr.blocks_agree, hr.regs_match, hr.stk_match⟩

private theorem not_mem_fst_of_nodup_append {α : Type} {l1 l2 : List α}
    (hnd : (l1 ++ l2).Nodup) {x : α} (hx : x ∈ l2) : x ∉ l1 := by
  induction l1 with
  | nil => simp
  | cons a tl ih =>
    rcases List.nodup_cons.mp hnd with ⟨hnot, hnd'⟩
    intro hmem
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact hnot (List.mem_append_right _ hx)
    · exact ih hnd' htl

private theorem nodup_snd_of_append {α : Type} {l1 l2 : List α} (hnd : (l1 ++ l2).Nodup) :
    l2.Nodup := by
  induction l1 with
  | nil => exact hnd
  | cons _ _ ih => exact ih (List.nodup_cons.mp hnd).2

theorem exit_block {tags : TypeEnv} {baseEnv : Env} {cur sc : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur (sc :: outer) s env blks m)
    {regLen0 stkLen0 : Nat}
    (hreg0 : regLen0 = (allRegSlots sc outer).length)
    (hstk0 : stkLen0 = (allStkSlots sc outer).length) :
    Refines tags baseEnv sc outer (s.exitBlock regLen0 stkLen0)
      (slotsEnv (allSlots sc outer) baseEnv) sc.blks (m.freeStack cur.blks) := by
  have hall_eq : allSlots cur (sc :: outer) = cur ++ allSlots sc outer := rfl
  have hreg_eq : allRegSlots cur (sc :: outer) = regSlots cur ++ allRegSlots sc outer := by
    simp [allRegSlots, allSlots, regSlots_append]
  have hstk_eq : allStkSlots cur (sc :: outer) = stkSlots cur ++ allStkSlots sc outer := by
    simp [allStkSlots, allSlots, stkSlots_append]
  have hreg_len : s.regs.length - regLen0 = (regSlots cur).length := by
    have hl := hr.regs_match.length_eq
    rw [hreg_eq, List.length_append] at hl
    rw [hreg0, ← hl]
    exact Nat.add_sub_cancel _ _
  have hstk_len : s.stack.length - stkLen0 = (stkSlots cur).length := by
    have hl := hr.stk_match.length_eq
    rw [hstk_eq, List.length_append] at hl
    rw [hstk0, ← hl]
    exact Nat.add_sub_cancel _ _
  have hblks_eq : allSlotBlks cur (sc :: outer) = cur.blks ++ allSlotBlks sc outer := by
    simp [allSlotBlks, FrameScope.blks, allSlots, List.map_append]
  have hnd_full : (cur.blks ++ allSlotBlks sc outer).Nodup := hblks_eq ▸ hr.nodup_blks
  have hdisj : ∀ b ∈ allSlotBlks sc outer, b ∉ cur.blks := fun b hb =>
    not_mem_fst_of_nodup_append hnd_full hb
  have htake_blks : (s.stack.take (stkSlots cur).length).map (·.2.1) = (stkSlots cur).map (·.blk) :=
    StkMatch.take_blks (s1 := stkSlots cur) (s2 := allStkSlots sc outer) (hstk_eq ▸ hr.stk_match)
  have heq_exit : s.exitBlock regLen0 stkLen0 =
      { regs := s.regs.drop (regSlots cur).length
        stack := s.stack.drop (stkSlots cur).length
        mem := s.mem.freeStack ((stkSlots cur).map (·.blk))
        os := s.os } := by
    simp only [SymState.exitBlock, hreg_len, hstk_len, htake_blks]
  rw [heq_exit]
  refine ⟨rfl, rfl, nodup_snd_of_append hnd_full, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    have h1 : s.regs = s.regs.take (regSlots cur).length ++ s.regs.drop (regSlots cur).length :=
      (List.take_append_drop _ _).symm
    have h2 : s.stack = s.stack.take (stkSlots cur).length ++ s.stack.drop (stkSlots cur).length :=
      (List.take_append_drop _ _).symm
    rcases hr.disjoint_names y with h | h
    · left; rw [h1] at h; exact RegEnv.lookup_eq_none_of_drop_mem h
    · right; rw [h2] at h; exact env_lookup_eq_none_of_drop_mem h
  · rw [freeStack_nextBlock, freeStack_nextBlock]; exact hr.nextBlock_le
  · intro b hb
    have hb_in : b ∈ allRegBlks cur (sc :: outer) := by
      rw [allRegBlks, hreg_eq, List.map_append, List.mem_append]; exact .inr hb
    have hnone := hr.slots_absent b hb_in
    by_cases hbs : b ∈ (stkSlots cur).map (·.blk)
    · obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hbs
      have hsl_stk : sl ∈ stkSlots (allSlots cur (sc :: outer)) :=
        List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_filter.mp hsl).1, (List.mem_filter.mp hsl).2⟩
      have hnot := not_mem_reg_of_stk_nodup hr.nodup_blks hsl_stk
      exact False.elim (hnot hb_in)
    · rw [freeStack_blocks_not_mem s.mem _ hbs, hnone]
  · intro b hbnot
    by_cases hcur : b ∈ cur.blks
    · obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hcur
      have hsl_all : sl ∈ allSlots cur (sc :: outer) := List.mem_append_left _ hsl
      cases hk : sl.kind
      · have hsl_reg : sl ∈ allRegSlots cur (sc :: outer) :=
          List.mem_filter.mpr ⟨hsl_all, by simp [hk]⟩
        obtain ⟨blk, hbm, hkind, _⟩ := hr.regs_match.blocks_some hsl_reg
        have hfs := freeStack_blocks_mem_stack m cur.blks hcur hbm hkind
        have hsb : sl.blk ∈ allRegBlks cur (sc :: outer) := List.mem_map.mpr ⟨sl, hsl_reg, rfl⟩
        have hnot_stk : sl.blk ∉ (stkSlots cur).map (·.blk) := by
          intro hsm
          obtain ⟨s2, hs2, heq2⟩ := List.mem_map.mp hsm
          have hs2_stk : s2 ∈ stkSlots (allSlots cur (sc :: outer)) :=
            List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_filter.mp hs2).1, (List.mem_filter.mp hs2).2⟩
          exact (not_mem_reg_of_stk_nodup hr.nodup_blks hs2_stk) (heq2 ▸ hsb)
        rw [hfs, freeStack_blocks_not_mem s.mem _ hnot_stk, hr.slots_absent sl.blk hsb]
      · have hsl_stk_cur : sl ∈ stkSlots cur := List.mem_filter.mpr ⟨hsl, by simp [hk]⟩
        have hsl_stk_all : sl ∈ allStkSlots cur (sc :: outer) :=
          List.mem_filter.mpr ⟨hsl_all, by simp [hk]⟩
        obtain ⟨blks, hbs, hk_s⟩ := hr.stk_match.blocks_some hsl_stk_all
        have hnot_reg : sl.blk ∉ allRegBlks cur (sc :: outer) :=
          not_mem_reg_of_stk_nodup hr.nodup_blks hsl_stk_all
        have hbm : m.blocks sl.blk = some blks := (hr.blocks_agree sl.blk hnot_reg).trans hbs
        have hfs_m := freeStack_blocks_mem_stack m cur.blks hcur hbm hk_s
        have hin_sc : sl.blk ∈ (stkSlots cur).map (·.blk) := List.mem_map.mpr ⟨sl, hsl_stk_cur, rfl⟩
        have hfs_s := freeStack_blocks_mem_stack s.mem _ hin_sc hbs hk_s
        rw [hfs_m, hfs_s]
    · rw [freeStack_blocks_not_mem m cur.blks hcur]
      have hnot_sc : b ∉ (stkSlots cur).map (·.blk) := fun hmem => by
        obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hmem
        exact hcur (List.mem_map.mpr ⟨sl, (List.mem_filter.mp hsl).1, rfl⟩)
      rw [freeStack_blocks_not_mem s.mem _ hnot_sc]
      apply hr.blocks_agree b
      rw [allRegBlks, hreg_eq, List.map_append, List.mem_append, not_or]
      refine ⟨fun hmem => ?_, hbnot⟩
      obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hmem
      exact hcur (List.mem_map.mpr ⟨sl, (List.mem_filter.mp hsl).1, rfl⟩)
  · have hm_drop : SlotsMatch tags m (allRegSlots sc outer) (s.regs.drop (regSlots cur).length) :=
      SlotsMatch.drop (s1 := regSlots cur) (s2 := allRegSlots sc outer) (hreg_eq ▸ hr.regs_match)
    refine hm_drop.of_blocks_agree (fun sl hsl => ?_)
    have hb_in : sl.blk ∈ allSlotBlks sc outer := mem_allSlotBlks_of_reg (List.mem_map.mpr ⟨sl, hsl, rfl⟩)
    exact freeStack_blocks_not_mem m cur.blks (hdisj sl.blk hb_in)
  · have hm_drop : StkMatch s.mem (allStkSlots sc outer) (s.stack.drop (stkSlots cur).length) :=
      StkMatch.drop (s1 := stkSlots cur) (s2 := allStkSlots sc outer) (hstk_eq ▸ hr.stk_match)
    refine hm_drop.of_blocks_agree (fun sl hsl => ?_)
    have hb_in : sl.blk ∈ allSlotBlks sc outer := mem_allSlotBlks_of_stk (List.mem_map.mpr ⟨sl, hsl, rfl⟩)
    have hnot_cur : sl.blk ∉ (stkSlots cur).map (·.blk) := fun hmem => by
      obtain ⟨s2, hs2, heq⟩ := List.mem_map.mp hmem
      exact hdisj sl.blk hb_in (List.mem_map.mpr ⟨s2, (List.mem_filter.mp hs2).1, heq⟩)
    exact freeStack_blocks_not_mem s.mem _ hnot_cur

def freeAllScopes (m : Mem) (cur : FrameScope) : List FrameScope → Mem
  | [] => m.freeStack cur.blks
  | sc :: rest => freeAllScopes (m.freeStack cur.blks) sc rest

theorem free_all_scopes {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope}
    {outer : List FrameScope} {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m) :
    (freeAllScopes m cur outer).nextBlock = m.nextBlock ∧
    s.mem.nextBlock ≤ m.nextBlock ∧
    ∀ b, (freeAllScopes m cur outer).blocks b = s.exitFn.blocks b := by
  induction outer generalizing cur s env blks m with
  | nil =>
    refine ⟨freeStack_nextBlock m cur.blks, hr.nextBlock_le, fun b => ?_⟩
    dsimp only [freeAllScopes, SymState.exitFn]
    have hstk_eq : s.stack.map (·.2.1) = (stkSlots cur).map (·.blk) := by
      have hlen := hr.stk_match.length_eq
      have hm := StkMatch.take_blks (s1 := allStkSlots cur []) (s2 := []) (by simpa using hr.stk_match)
      have htake : s.stack.take (allStkSlots cur []).length = s.stack := by
        rw [hlen, List.take_length]
      rw [htake] at hm
      simpa [allStkSlots, allSlots] using hm
    rw [hstk_eq]
    by_cases hcur : b ∈ cur.blks
    · obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hcur
      have hsl_all : sl ∈ allSlots cur [] := List.mem_append_left _ hsl
      cases hk : sl.kind
      · have hsl_reg : sl ∈ allRegSlots cur [] := List.mem_filter.mpr ⟨hsl_all, by simp [hk]⟩
        obtain ⟨blk, hbm, hkind, _⟩ := hr.regs_match.blocks_some hsl_reg
        have hfs := freeStack_blocks_mem_stack m cur.blks hcur hbm hkind
        have hsb : sl.blk ∈ allRegBlks cur [] := List.mem_map.mpr ⟨sl, hsl_reg, rfl⟩
        have hnot_stk : sl.blk ∉ (stkSlots cur).map (·.blk) := by
          intro hsm
          obtain ⟨s2, hs2, heq2⟩ := List.mem_map.mp hsm
          have hs2_stk : s2 ∈ stkSlots (allSlots cur []) := by simpa [allSlots] using hs2
          exact (not_mem_reg_of_stk_nodup hr.nodup_blks hs2_stk) (heq2 ▸ hsb)
        rw [hfs, freeStack_blocks_not_mem s.mem _ hnot_stk, hr.slots_absent sl.blk hsb]
      · have hsl_stk_cur : sl ∈ stkSlots cur := List.mem_filter.mpr ⟨hsl, by simp [hk]⟩
        have hsl_stk_all : sl ∈ allStkSlots cur [] := by simpa [allStkSlots, allSlots] using hsl_stk_cur
        obtain ⟨blks, hbs, hk_s⟩ := hr.stk_match.blocks_some hsl_stk_all
        have hnot_reg : sl.blk ∉ allRegBlks cur [] := not_mem_reg_of_stk_nodup hr.nodup_blks hsl_stk_all
        have hbm : m.blocks sl.blk = some blks := (hr.blocks_agree sl.blk hnot_reg).trans hbs
        have hfs_m := freeStack_blocks_mem_stack m cur.blks hcur hbm hk_s
        have hin_sc : sl.blk ∈ (stkSlots cur).map (·.blk) := List.mem_map.mpr ⟨sl, hsl_stk_cur, rfl⟩
        have hfs_s := freeStack_blocks_mem_stack s.mem _ hin_sc hbs hk_s
        rw [hfs_m, hfs_s]
    · rw [freeStack_blocks_not_mem m cur.blks hcur]
      have hnot_sc : b ∉ (stkSlots cur).map (·.blk) := fun hmem => by
        obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hmem
        exact hcur (List.mem_map.mpr ⟨sl, (List.mem_filter.mp hsl).1, rfl⟩)
      rw [freeStack_blocks_not_mem s.mem _ hnot_sc]
      apply hr.blocks_agree b
      intro hmem
      obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hmem
      simp only [allRegSlots, allSlots, List.flatten_nil, List.append_nil] at hsl
      exact hcur (List.mem_map.mpr ⟨sl, (List.mem_filter.mp hsl).1, rfl⟩)
  | cons sc rest ih =>
    have hr_ex := hr.exit_block rfl rfl
    obtain ⟨hnb, _, heq⟩ := ih hr_ex
    refine ⟨hnb.trans (freeStack_nextBlock m cur.blks), hr.nextBlock_le, fun b => ?_⟩
    rw [freeAllScopes, heq b]
    have hstk_eq : allStkSlots cur (sc :: rest) = stkSlots cur ++ allStkSlots sc rest := by
      simp [allStkSlots, allSlots, stkSlots_append]
    have hreg_eq : allRegSlots cur (sc :: rest) = regSlots cur ++ allRegSlots sc rest := by
      simp [allRegSlots, allSlots, regSlots_append]
    have hex_mem : (s.exitBlock (allRegSlots sc rest).length (allStkSlots sc rest).length).exitFn = s.exitFn := by
      have hreg_len : s.regs.length - (allRegSlots sc rest).length = (regSlots cur).length := by
        have hl := hr.regs_match.length_eq
        rw [hreg_eq, List.length_append] at hl
        rw [← hl]; exact Nat.add_sub_cancel _ _
      have hstk_len : s.stack.length - (allStkSlots sc rest).length = (stkSlots cur).length := by
        have hl := hr.stk_match.length_eq
        rw [hstk_eq, List.length_append] at hl
        rw [← hl]; exact Nat.add_sub_cancel _ _
      simp only [SymState.exitBlock, SymState.exitFn, hreg_len, hstk_len, freeStack_append]
      congr 1
      rw [← List.map_append, List.take_append_drop]
    rw [hex_mem]

theorem roExt_of_blocks_eq {m0 m_clean m_out : Mem}
    (hro : ROExt m0 m_clean)
    (heq : ∀ b, m_out.blocks b = m_clean.blocks b)
    (hle : m_clean.nextBlock ≤ m_out.nextBlock) :
    ROExt m0 m_out := by
  refine ⟨Nat.le_trans hro.1 hle, ?_, ?_⟩
  · intro b hb
    rw [heq b, hro.2.1 b hb]
  · intro b blk hle' hbm
    rw [heq b] at hbm
    exact hro.2.2 b blk hle' hbm

theorem roExt_dropBlks {m_clean m m_after : Mem} {bs : List BlockId}
    (hle : m_clean.nextBlock ≤ m.nextBlock)
    (habs : ∀ b ∈ bs, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (hro : ROExt m m_after) :
    ROExt m_clean (dropBlks m_after bs) := by
  refine ⟨Nat.le_trans hle (by rw [dropBlks_nextBlock]; exact hro.1), ?_, ?_⟩
  · intro b hb
    have hbm : m_after.blocks b = m.blocks b := hro.2.1 b (Nat.lt_of_lt_of_le hb hle)
    by_cases hbs : b ∈ bs
    · rw [dropBlks_blocks_mem _ _ hbs, habs b hbs]
    · rw [dropBlks_blocks_not_mem _ _ hbs, hbm, hagree b hbs]
  · intro b blk hle_c hbm
    by_cases hbs : b ∈ bs
    · rw [dropBlks_blocks_mem _ _ hbs] at hbm; cases hbm
    · rw [dropBlks_blocks_not_mem _ _ hbs] at hbm
      by_cases hlt : b < m.nextBlock
      · exfalso
        have heq1 : m_after.blocks b = m.blocks b := hro.2.1 b hlt
        have heq2 : m.blocks b = m_clean.blocks b := hagree b hbs
        have hnone := m_clean.fresh b hle_c
        rw [heq1, heq2, hnone] at hbm
        cases hbm
      · exact hro.2.2 b blk (Nat.le_of_not_lt hlt) hbm

theorem init (tags : TypeEnv) (baseEnv : Env) (m : Mem) (os : OSState) :
    Refines tags baseEnv [] [] { regs := [], stack := [], mem := m, os := os } baseEnv [] m :=
  ⟨rfl, rfl, List.nodup_nil, (fun _ => .inl rfl), Nat.le_refl _,
    (fun _ hb => by cases hb), (fun _ _ => rfl), .nil, .nil⟩

end Refines

theorem readVal_of_blocks_eq {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId} {off : Int64} {ty : CTy}
    (heq : m2.blocks b = m1.blocks b) :
    Sem.readVal tags m2 b off ty = Sem.readVal tags m1 b off ty := by
  have hrb : ∀ len, m2.readBytes b off len = m1.readBytes b off len := fun len => by
    unfold Mem.readBytes; simp only [heq]
  unfold Sem.readVal
  cases ty.unqual with
  | int _ | enumTy _ _ =>
    simp only [heq, bind, Option.bind]
    cases m1.blocks b <;> cases h : CTy.intKind? _ <;> simp only [hrb] <;> rfl
  | ptr _ =>
    simp only [heq, bind, Option.bind]
    cases m1.blocks b with
    | none => rfl
    | some blk => simp only [hrb]
  | fnPtr _ _ _ =>
    simp only [heq, bind, Option.bind]
    cases m1.blocks b with
    | none => rfl
    | some blk => simp only [hrb]
  | vaList => simp only [hrb]
  | array _ _ | void | const_ _ | structTy _ | unionTy _ | anonStruct _ | anonUnion _ | typedef _ _ => rfl

theorem readPlace_of_blocks_eq {tags : TypeEnv} {m1 m2 : Mem} {mods : ModSet} {w : Want}
    {b : BlockId} {off : Int64} {ty : CTy}
    (heq : m2.blocks b = m1.blocks b) :
    Sem.readPlace tags m2 mods w b off ty = Sem.readPlace tags m1 mods w b off ty := by
  unfold Sem.readPlace
  cases w with
  | lval => rfl
  | rval =>
    have hrb : ∀ len, m2.readBytes b off len = m1.readBytes b off len := fun len => by
      unfold Mem.readBytes; simp only [heq]
    have hrv := readVal_of_blocks_eq (tags := tags) (off := off) (ty := ty) heq
    cases ty.unqual <;> simp only [hrb, hrv]

namespace Refines

theorem read_mem {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {b : BlockId} {off : Int64} {ty : CTy} {blk : Block}
    (hb : s.mem.blocks b = some blk) :
    b ∉ allRegBlks cur outer ∧
    m.blocks b = some blk ∧
    Sem.readVal tags m b off ty = Sem.readVal tags s.mem b off ty := by
  obtain ⟨hnot, hbm⟩ := hr.mem_blocks_some hb
  exact ⟨hnot, hbm, readVal_of_blocks_eq (hbm.trans hb.symm)⟩

theorem readPlace_mem {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {mods : ModSet} {w : Want} {b : BlockId} {off : Int64} {ty : CTy} {blk : Block}
    (hb : s.mem.blocks b = some blk) :
    b ∉ allRegBlks cur outer ∧
    Sem.readPlace tags m mods w b off ty = Sem.readPlace tags s.mem mods w b off ty := by
  obtain ⟨hnot, hbm⟩ := hr.mem_blocks_some hb
  exact ⟨hnot, readPlace_of_blocks_eq (hbm.trans hb.symm)⟩

theorem evalPtrAdd_mem {cfg : PointerConfig} {tags : TypeEnv} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {p : Val} {el : CTy} {idx : Int} {pv : Val}
    (h : Sem.evalPtrAdd cfg tags s.mem p el idx = some pv) :
    Sem.evalPtrAdd cfg tags m p el idx = some pv := by
  unfold Sem.evalPtrAdd at h ⊢
  by_cases hkz : (idx == 0 && cfg.allowAddZeroAny) = true
  · simp only [hkz, ↓reduceIte] at h ⊢; exact h
  · have hkzf : (idx == 0 && cfg.allowAddZeroAny) = false := Bool.eq_false_iff.mpr hkz
    simp only [hkzf, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases p with
    | ptr b off =>
      dsimp only [bind, Option.bind] at h ⊢
      cases hb : s.mem.blocks b with
      | none => simp [hb] at h
      | some blk =>
        simp only [hb] at h
        rw [(hr.mem_blocks_some hb).2]
        exact h
    | _ => simp at h

theorem evalPtrDiff_mem {cfg : PointerConfig} {tags : TypeEnv} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {p q : Val} {el : CTy} {dv : Val}
    (h : Sem.evalPtrDiff cfg tags s.mem p q el = some dv) :
    Sem.evalPtrDiff cfg tags m p q el = some dv := by
  unfold Sem.evalPtrDiff at h ⊢
  cases p <;> cases q <;> try exact h
  next b1 o1 b2 o2 =>
    dsimp only [bind, Option.bind, guard, Pure.pure] at h ⊢
    by_cases hbeq : (b1 == b2) = true
    · simp only [hbeq, ↓reduceIte] at h ⊢
      cases hb : s.mem.blocks b1 with
      | none => simp [hb] at h
      | some blk =>
        simp only [hb] at h
        rw [(hr.mem_blocks_some hb).2]
        exact h
    · have hbf : (b1 == b2) = false := Bool.eq_false_iff.mpr hbeq
      simp only [hbf, Bool.false_eq_true, ↓reduceIte] at h
      cases h

theorem evalPtrCmp_mem {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {op : BinOp} {p q rv : Val}
    (h : Sem.evalPtrCmp s.mem op p q = some rv) :
    Sem.evalPtrCmp m op p q = some rv := by
  unfold Sem.evalPtrCmp at h ⊢
  cases op with
  | lt | le | gt | ge =>
    cases p <;> cases q <;> try exact h
    next b1 o1 b2 o2 =>
      dsimp only [bind, Option.bind, guard, Pure.pure] at h ⊢
      by_cases hbeq : (b1 == b2) = true
      · simp only [hbeq, ↓reduceIte] at h ⊢
        cases hb : s.mem.blocks b1 with
        | none => simp [hb] at h
        | some blk =>
          simp only [hb] at h
          rw [(hr.mem_blocks_some hb).2]
          exact h
      · have hbf : (b1 == b2) = false := Bool.eq_false_iff.mpr hbeq
        simp only [hbf, Bool.false_eq_true, ↓reduceIte] at h
        cases h
  | _ => exact h

theorem applyBinary_mem {cfg : PointerConfig} {tags : TypeEnv} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {op : BinOp} {v1 : Val} {t1 : CTy} {v2 : Val} {t2 : CTy} {res : Val × CTy}
    (h : Sem.applyBinary cfg tags s.mem op v1 t1 v2 t2 = some res) :
    Sem.applyBinary cfg tags m op v1 t1 v2 t2 = some res := by
  unfold Sem.applyBinary at h ⊢
  dsimp only at h ⊢
  split
  · next hptr =>
    simp only [hptr, ↓reduceIte] at h ⊢
    cases op with
    | add =>
      by_cases ht1 : t1.isPtr = true
      · simp only [ht1, ↓reduceIte] at h ⊢
        cases hvi : Sem.valAsInt? v2 with
        | none => cases hu1 : t1.unqual <;> simp [hu1, hvi] at h
        | some p =>
          cases hu1 : t1.unqual <;> simp only [hu1, hvi] at h ⊢
          all_goals try cases h
          next el =>
            cases hv : Sem.evalPtrAdd cfg tags s.mem v1 el p.2 with
            | none => simp [hv] at h
            | some pv =>
              rw [hr.evalPtrAdd_mem hv]
              simpa [hv] using h
      · have ht1f : t1.isPtr = false := Bool.eq_false_iff.mpr ht1
        simp only [ht1f, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hvi : Sem.valAsInt? v1 with
        | none => cases hu2 : t2.unqual <;> simp [hu2, hvi] at h
        | some p =>
          cases hu2 : t2.unqual <;> simp only [hu2, hvi] at h ⊢
          all_goals try cases h
          next el =>
            cases hv : Sem.evalPtrAdd cfg tags s.mem v2 el p.2 with
            | none => simp [hv] at h
            | some pv =>
              rw [hr.evalPtrAdd_mem hv]
              simpa [hv] using h
    | sub =>
      by_cases h12 : (t1.isPtr && t2.isPtr) = true
      · simp only [h12, ↓reduceIte] at h ⊢
        cases hu1 : t1.unqual <;> simp only [hu1] at h ⊢
        all_goals try cases h
        next el =>
          cases hv : Sem.evalPtrDiff cfg tags s.mem v1 v2 el with
          | none => simp [hv] at h
          | some dv =>
            rw [hr.evalPtrDiff_mem hv]
            simpa [hv] using h
      · have h12f : (t1.isPtr && t2.isPtr) = false := Bool.eq_false_iff.mpr h12
        simp only [h12f, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases ht1 : t1.isPtr = true
        · simp only [ht1, ↓reduceIte] at h ⊢
          cases hvi : Sem.valAsInt? v2 with
          | none => cases hu1 : t1.unqual <;> simp [hu1, hvi] at h
          | some p =>
            cases hu1 : t1.unqual <;> simp only [hu1, hvi] at h ⊢
            all_goals try cases h
            next el =>
              cases hv : Sem.evalPtrAdd cfg tags s.mem v1 el (-p.2) with
              | none => simp [hv] at h
              | some pv =>
                rw [hr.evalPtrAdd_mem hv]
                simpa [hv] using h
        · have ht1f : t1.isPtr = false := Bool.eq_false_iff.mpr ht1
          simp only [ht1f, Bool.false_eq_true, ↓reduceIte] at h
          cases h
    | eq =>
      cases hv : Sem.evalPtrCmp s.mem .eq v1 v2 with
      | none => simp [hv] at h
      | some rv => rw [hr.evalPtrCmp_mem hv]; simpa [hv] using h
    | ne =>
      cases hv : Sem.evalPtrCmp s.mem .ne v1 v2 with
      | none => simp [hv] at h
      | some rv => rw [hr.evalPtrCmp_mem hv]; simpa [hv] using h
    | lt =>
      cases hv : Sem.evalPtrCmp s.mem .lt v1 v2 with
      | none => simp [hv] at h
      | some rv => rw [hr.evalPtrCmp_mem hv]; simpa [hv] using h
    | le =>
      cases hv : Sem.evalPtrCmp s.mem .le v1 v2 with
      | none => simp [hv] at h
      | some rv => rw [hr.evalPtrCmp_mem hv]; simpa [hv] using h
    | gt =>
      cases hv : Sem.evalPtrCmp s.mem .gt v1 v2 with
      | none => simp [hv] at h
      | some rv => rw [hr.evalPtrCmp_mem hv]; simpa [hv] using h
    | ge =>
      cases hv : Sem.evalPtrCmp s.mem .ge v1 v2 with
      | none => simp [hv] at h
      | some rv => rw [hr.evalPtrCmp_mem hv]; simpa [hv] using h
    | _ => cases h
  · next hptr =>
    simp only [hptr, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact h

theorem castVal_mem {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {target : CTy} {v cv : Val}
    (h : Sem.castVal s.mem target v = some cv) :
    Sem.castVal m target v = some cv := by
  unfold Sem.castVal at h ⊢
  dsimp only at h ⊢
  by_cases hv : target.unqual.isVoid = true
  · simp only [hv, ↓reduceIte] at h ⊢; exact h
  · have hvf : target.unqual.isVoid = false := Bool.eq_false_iff.mpr hv
    simp only [hvf, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hk : target.unqual.intKind? with
    | none => simp only [hk] at h ⊢; exact h
    | some k =>
      simp only [hk] at h ⊢
      cases v with
      | ptr b off =>
        dsimp only at h ⊢
        unfold Mem.addrOf at h ⊢
        cases hb : s.mem.blocks b with
        | none => simp [hb] at h
        | some blk =>
          simp only [hb] at h
          rw [(hr.mem_blocks_some hb).2]
          exact h
      | _ => exact h

end Refines

private theorem writeBytes_eq_of_blocks_eq {m1 m2 m1' : Mem} {b : BlockId} {off : Int64} {bs : List MemByte}
    (heq : m2.blocks b = m1.blocks b) (hw : m1.writeBytes b off bs = some m1') :
    ∃ m2', m2.writeBytes b off bs = some m2' ∧
      m2'.blocks b = m1'.blocks b ∧
      (∀ b', b' ≠ b → m2'.blocks b' = m2.blocks b') ∧
      m2'.nextBlock = m2.nextBlock := by
  unfold Mem.writeBytes at hw ⊢
  split at hw
  · cases hw
  · next blk1 hblk1 =>
    have hb2 : m2.blocks b = some blk1 := heq.trans hblk1
    split at hw
    · next hperm =>
      cases hw
      split
      · next hblk2 => rw [hb2] at hblk2; cases hblk2
      · next blk2 hblk2 =>
        rw [hb2, Option.some.injEq] at hblk2
        subst blk2
        simp only [hperm, ↓reduceIte]
        refine ⟨_, rfl, ?_, ?_, rfl⟩
        · simp
        · intro b' hne; simp [hne]
    · cases hw

theorem writeVal_eq_of_blocks_eq {m1 m2 m1' : Mem} {b : BlockId} {off : Int64} {ty : CTy} {v : Val}
    (heq : m2.blocks b = m1.blocks b) (hw : Sem.writeVal m1 b off ty v = some m1') :
    ∃ m2', Sem.writeVal m2 b off ty v = some m2' ∧
      m2'.blocks b = m1'.blocks b ∧
      (∀ b', b' ≠ b → m2'.blocks b' = m2.blocks b') ∧
      m2'.nextBlock = m2.nextBlock := by
  unfold Sem.writeVal at hw ⊢
  by_cases hnc : ty.isConst = true
  · simp [hnc, bind, Option.bind, guard] at hw
  · have hncf : ty.isConst = false := Bool.eq_false_iff.mpr hnc
    simp only [hncf, Bool.not_false, guard_true, bind, Option.bind] at hw ⊢
    cases hb : m1.blocks b with
    | none => simp [hb] at hw
    | some blk =>
      have hb2 : m2.blocks b = some blk := heq.trans hb
      simp only [hb] at hw
      simp only [hb2]
      cases hu : ty.unqual with
      | int k =>
        simp only [hu, CTy.unqual, CTy.intKind?] at hw ⊢
        by_cases ha : Mem.isAligned blk off k.align = true
        · simp only [ha, guard_true] at hw ⊢
          cases hvi : Sem.valAsInt? v with
          | none => simp [hvi] at hw
          | some p =>
            simp only [hvi] at hw
            exact writeBytes_eq_of_blocks_eq heq hw
        · have haf : Mem.isAligned blk off k.align = false := Bool.eq_false_iff.mpr ha
          simp only [haf, Bool.false_eq_true, guard, ↓reduceIte] at hw
          cases hw
      | enumTy tag isU =>
        simp only [hu, CTy.unqual, CTy.intKind?] at hw ⊢
        by_cases ha : Mem.isAligned blk off (if isU = true then IntKind.u32 else IntKind.i32).align = true
        · simp only [ha, guard_true] at hw ⊢
          cases hvi : Sem.valAsInt? v with
          | none => simp [hvi] at hw
          | some p =>
            simp only [hvi] at hw
            exact writeBytes_eq_of_blocks_eq heq hw
        · have haf : Mem.isAligned blk off (if isU = true then IntKind.u32 else IntKind.i32).align = false :=
            Bool.eq_false_iff.mpr ha
          simp only [haf, Bool.false_eq_true, guard, ↓reduceIte] at hw
          cases hw
      | ptr _ | fnPtr _ _ _ =>
        simp only [hu] at hw ⊢
        by_cases ha : Mem.isAligned blk off 8 = true
        · simp only [ha, guard_true] at hw ⊢
          cases v with
          | null => exact writeBytes_eq_of_blocks_eq heq hw
          | ptr pb poff =>
            simp only at hw ⊢
            first | cases hw | exact writeBytes_eq_of_blocks_eq heq hw
          | fnPtr s =>
            simp only at hw ⊢
            first | cases hw | exact writeBytes_eq_of_blocks_eq heq hw
          | int _ bv =>
            by_cases hz : (bv.toNat == 0) = true
            · simp only [hz, ↓reduceIte] at hw ⊢
              exact writeBytes_eq_of_blocks_eq heq hw
            · have hzf : (bv.toNat == 0) = false := Bool.eq_false_iff.mpr hz
              simp [hzf] at hw
          | _ => cases hw
        · have haf : Mem.isAligned blk off 8 = false := Bool.eq_false_iff.mpr ha
          simp only [haf, Bool.false_eq_true, guard, ↓reduceIte] at hw
          cases hw
      | vaList =>
        simp only [hu] at hw ⊢
        cases v with
        | vaList bflag =>
          cases bflag
          · cases hw
          · exact writeBytes_eq_of_blocks_eq heq hw
        | _ => cases hw
      | void | const_ _ | array _ _ | structTy _ | unionTy _ | anonStruct _ | anonUnion _ | typedef _ _ =>
        simp [hu] at hw

namespace Refines

private theorem writeBytes_preserves_stack_kind {m m' : Mem} {b : BlockId} {off : Int64}
    {bs : List MemByte} (hw : m.writeBytes b off bs = some m')
    {b' : BlockId} {blk : Block} (hb : m.blocks b' = some blk) (hk : blk.kind = .stack) :
    ∃ blk', m'.blocks b' = some blk' ∧ blk'.kind = .stack := by
  by_cases hbb : b' = b
  · subst hbb
    unfold Mem.writeBytes at hw
    split at hw
    · cases hw
    · next blk1 hblk1 =>
      rw [hb, Option.some.injEq] at hblk1
      subst blk1
      split at hw
      · cases hw
        simp only [beq_self_eq_true, ↓reduceIte]
        exact ⟨_, rfl, hk⟩
      · cases hw
  · rw [writeBytes_blocks_ne hw hbb]
    exact ⟨blk, hb, hk⟩

theorem alloc_stk_some_scalar {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m m1 : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {x : String} {ty vty : CTy} {v cv : Val} {base : UInt64} {bid : BlockId}
    (hreg_none : s.regs.lookup x = none)
    (hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy tags ty))
    (hba : base.toNat % max 1 (alignofTy tags ty) = 0)
    (hc : Sem.castVal s.mem ty.stripConst v = some cv)
    (ht : ValScalarTyped ty.stripConst cv)
    (halloc : m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1))
    (hle : s.mem.nextBlock ≤ bid := Nat.le_trans hr.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))) :
    ∃ r m2 ms2,
      Sem.writePlace tags m1 bid 0 ty.stripConst (.rval v vty) = some (r, m2) ∧
      Sem.writeVal
        (allocAt s.mem bid hle
          (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
          .rw .stack base (fun _ => .undef) hsz hal hba)
        bid 0 ty.stripConst cv = some ms2 ∧
      Refines tags baseEnv (⟨x, bid, ty, .stk⟩ :: cur) outer
        { s with stack := (x, bid, ty) :: s.stack, mem := ms2 }
        ((x, bid, ty) :: env) (bid :: blks) m2 := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst halloc).symm
  subst hbid
  have hr1 := hr.alloc_stk_none hreg_none hsz hal hba halloc hle
  let ms1 := allocAt s.mem m.nextBlock hle
    (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
    .rw .stack base (fun _ => .undef) hsz hal hba
  have hnc : ty.stripConst.isConst = false := stripConst_isConst ty
  have hsz_eq : sizeofTy tags ty.stripConst = sizeofTy tags ty := by
    rw [← sizeofTy_unqual, stripConst_unqual, sizeofTy_unqual]
  have hal_eq : alignofTy tags ty.stripConst = alignofTy tags ty := by
    rw [← alignofTy_unqual, stripConst_unqual, alignofTy_unqual]
  have hms1_eq : ms1.blocks m.nextBlock =
      some ⟨max 1 (sizeofTy tags ty), max 1 (alignofTy tags ty), .rw, .stack, base,
        (fun _ => .undef), hsz, hal, hba⟩ :=
    allocAt_blocks_eq _ _ _ _ _ _ _ _ _ _ _ _
  have hin : Mem.inBounds ⟨max 1 (sizeofTy tags ty), max 1 (alignofTy tags ty), .rw, .stack, base,
      (fun _ => .undef), hsz, hal, hba⟩ 0 (sizeofTy tags ty.stripConst) = true := by
    rw [inBounds_iff]
    exact ⟨by decide, by simpa [hsz_eq] using Nat.le_max_right 1 (sizeofTy tags ty)⟩
  obtain ⟨hal_pos, _⟩ := ht.align_eq_sizeof
  have hal_blk : Mem.isAligned ⟨max 1 (sizeofTy tags ty), max 1 (alignofTy tags ty), .rw, .stack, base,
      (fun _ => .undef), hsz, hal, hba⟩ 0 (alignofTy tags ty.stripConst) = true := by
    rw [isAligned_iff]
    have hal_ty_pos : 0 < alignofTy tags ty := by rwa [← hal_eq]
    have hmax : max 1 (alignofTy tags ty) = alignofTy tags ty := Nat.max_eq_right hal_ty_pos
    exact ⟨by decide, hal_pos, by simpa [hal_eq, hmax] using hba⟩
  obtain ⟨ms2, hwms, ⟨_, _, hwbs⟩, _⟩ := writeVal_scalar_some hnc hms1_eq rfl hin hal_blk ht
  have hm1_eq : m1.blocks m.nextBlock = ms1.blocks m.nextBlock := by
    have hm1s : m1 = (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
        .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd halloc).symm
    rw [hm1s, alloc_blocks_eq, hms1_eq]
  obtain ⟨m2, hwm2, hbeq, hne_m2, hnext_m2⟩ := writeVal_eq_of_blocks_eq hm1_eq hwms
  have hc_m1 : Sem.castVal m1 ty.stripConst v = some cv := by
    refine castVal_of_blocks_agree (fun b blk hb => ?_) hc
    have hlt_m : b < m.nextBlock := Nat.lt_of_lt_of_le (lt_nextBlock_of_some hb) hr.nextBlock_le
    have hne : b ≠ m.nextBlock := Nat.ne_of_lt hlt_m
    have hm1s : m1 = (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
        .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd halloc).symm
    rw [hm1s, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne]
    exact (hr.mem_blocks_some hb).2
  have hwrplace : Sem.writePlace tags m1 m.nextBlock 0 ty.stripConst (.rval v vty) = some (.rval cv ty.stripConst, m2) := by
    unfold Sem.writePlace
    unfold ValScalarTyped at ht
    cases hu : ty.stripConst.unqual <;> simp [hu] at ht
    case int | enumTy | ptr | fnPtr =>
      simp only [hc_m1, bind, Option.bind, hwm2, pure, Pure.pure]
    case vaList =>
      subst ht
      unfold Sem.castVal at hc
      simp only [hu, CTy.unqual, CTy.isVoid, CTy.intKind?, Bool.false_eq_true, ↓reduceIte] at hc
      cases v <;> simp at hc
      case vaList bf =>
        cases bf <;> simp at hc
        simp only [bind, Option.bind, hwm2, pure, Pure.pure]
  have hnext_ms2 : ms2.nextBlock = ms1.nextBlock := writeVal_nextBlock hwms
  have hne_ms2 : ∀ b, b ≠ m.nextBlock → ms2.blocks b = ms1.blocks b := fun b hne =>
    writeVal_blocks_ne hwms hne
  have hnot_in_reg : m.nextBlock ∉ allRegBlks cur outer := fun hmem =>
    Nat.lt_irrefl _ (hr.reg_lt_nextBlock hmem)
  refine ⟨.rval cv ty.stripConst, m2, ms2, hwrplace, hwms, ?_⟩
  refine ⟨hr1.env_eq, hr1.blks_eq, hr1.nodup_blks, hr1.disjoint_names, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnext_ms2, hnext_m2]; exact hr1.nextBlock_le
  · intro b hb
    have hb' : b ∈ allRegBlks cur outer := by
      simpa [allRegBlks, allRegSlots, allSlots, regSlots_cons_stk] using hb
    have hne : b ≠ m.nextBlock := Nat.ne_of_lt (hr.reg_lt_nextBlock hb')
    rw [hne_ms2 b hne]
    exact hr1.slots_absent b hb
  · intro b hbnot
    by_cases hbm : b = m.nextBlock
    · subst hbm; exact hbeq
    · rw [hne_m2 b hbm, hne_ms2 b hbm]
      exact hr1.blocks_agree b hbnot
  · refine hr1.regs_match.of_blocks_agree (fun sl hsl => ?_)
    have hsl' : sl ∈ allRegSlots cur outer := by
      simpa [allRegSlots, allSlots, regSlots_cons_stk] using hsl
    have hne : sl.blk ≠ m.nextBlock := fun heq => hnot_in_reg (heq ▸ List.mem_map.mpr ⟨sl, hsl', rfl⟩)
    exact hne_m2 sl.blk hne
  · refine hr1.stk_match.of_blocks (fun sl hsl => ?_)
    by_cases hbm : sl.blk = m.nextBlock
    · rw [hbm]
      exact ⟨_, writeBytes_blocks_eq hms1_eq hwbs, rfl⟩
    · rw [hne_ms2 sl.blk hbm]
      exact hr1.stk_match.blocks_some hsl

theorem alloc_stk_some_agg {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m m1 : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {x : String} {ty sty : CTy} {bs : List MemByte} {base : UInt64} {bid : BlockId}
    (hreg_none : s.regs.lookup x = none)
    (hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy tags ty))
    (hba : base.toNat % max 1 (alignofTy tags ty) = 0)
    (hbs : bs.length = sizeofTy tags ty)
    (halloc : m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1))
    (hle : s.mem.nextBlock ≤ bid := Nat.le_trans hr.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))) :
    ∃ r m2 ms2,
      Sem.writePlace tags m1 bid 0 ty.stripConst (.structVal bs sty) = some (r, m2) ∧
      (allocAt s.mem bid hle
          (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
          .rw .stack base (fun _ => .undef) hsz hal hba).writeBytes bid 0 bs = some ms2 ∧
      Refines tags baseEnv (⟨x, bid, ty, .stk⟩ :: cur) outer
        { s with stack := (x, bid, ty) :: s.stack, mem := ms2 }
        ((x, bid, ty) :: env) (bid :: blks) m2 := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst halloc).symm
  subst hbid
  have hr1 := hr.alloc_stk_none hreg_none hsz hal hba halloc hle
  have hbs_le : bs.length ≤ max 1 (sizeofTy tags ty) := hbs ▸ Nat.le_max_right _ _
  obtain ⟨ms2, hwms, hnext_ms2, hne_ms2, blk', hblk_ms2, hkind_ms2⟩ :=
    writeBytes_allocAt_eq (m := s.mem) (bid := m.nextBlock) (hle := hle)
      (kind := .stack) (base := base) (init := fun _ => .undef) (hsz := hsz) (hal := hal) (hba := hba) hbs_le
  have hm1_eq : m1.blocks m.nextBlock =
      (allocAt s.mem m.nextBlock hle (max 1 (sizeofTy tags ty))
        (max 1 (alignofTy tags ty)) .rw .stack base (fun _ => .undef) hsz hal hba).blocks m.nextBlock := by
    have hm1s : m1 = (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
        .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd halloc).symm
    rw [hm1s, alloc_blocks_eq, allocAt_blocks_eq]
  obtain ⟨m2, hwb2, hbeq2, hne_m2, hnext_m2⟩ := writeBytes_eq_of_blocks_eq hm1_eq hwms
  have hsz_eq : sizeofTy tags ty.stripConst = sizeofTy tags ty := by
    rw [← sizeofTy_unqual, stripConst_unqual, sizeofTy_unqual]
  have hwrplace : Sem.writePlace tags m1 m.nextBlock 0 ty.stripConst (.structVal bs sty) =
      some (.structVal bs ty.stripConst, m2) := by
    simp [Sem.writePlace, hbs, hsz_eq, hwb2]
  have hnot_in_reg : m.nextBlock ∉ allRegBlks cur outer := fun hmem =>
    Nat.lt_irrefl _ (hr.reg_lt_nextBlock hmem)
  refine ⟨.structVal bs ty.stripConst, m2, ms2, hwrplace, hwms, ?_⟩
  refine ⟨hr1.env_eq, hr1.blks_eq, hr1.nodup_blks, hr1.disjoint_names, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnext_ms2, hnext_m2]; exact hr1.nextBlock_le
  · intro b hb
    have hb' : b ∈ allRegBlks cur outer := by
      simpa [allRegBlks, allRegSlots, allSlots, regSlots_cons_stk] using hb
    have hne : b ≠ m.nextBlock := Nat.ne_of_lt (hr.reg_lt_nextBlock hb')
    have hne_s : ms2.blocks b = s.mem.blocks b := hne_ms2 b hne
    rw [hne_s]
    exact hr.slots_absent b hb'
  · intro b hbnot
    by_cases hbm : b = m.nextBlock
    · subst hbm; exact hbeq2
    · have hb' : b ∉ allRegBlks cur outer := by
        simpa [allRegBlks, allRegSlots, allSlots, regSlots_cons_stk] using hbnot
      rw [hne_m2 b hbm, hne_ms2 b hbm]
      have hm1s : m1 = (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
          .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd halloc).symm
      rw [hm1s, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hbm]
      exact hr.blocks_agree b hb'
  · refine hr1.regs_match.of_blocks_agree (fun sl hsl => ?_)
    have hsl' : sl ∈ allRegSlots cur outer := by
      simpa [allRegSlots, allSlots, regSlots_cons_stk] using hsl
    have hne : sl.blk ≠ m.nextBlock := fun heq => hnot_in_reg (heq ▸ List.mem_map.mpr ⟨sl, hsl', rfl⟩)
    exact hne_m2 sl.blk hne
  · refine hr1.stk_match.of_blocks (fun sl hsl => ?_)
    by_cases hbm : sl.blk = m.nextBlock
    · rw [hbm]; exact ⟨blk', hblk_ms2, hkind_ms2⟩
    · simp only [allStkSlots, allSlots, List.cons_append, stkSlots_cons_stk, List.mem_cons] at hsl
      rcases hsl with rfl | hsl_tl
      · exact False.elim (hbm rfl)
      · rw [hne_ms2 sl.blk hbm]
        exact hr.stk_match.blocks_some hsl_tl

theorem write_mem {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m m_clean' : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {b : BlockId} {off : Int64} {ty : CTy} {v : Val}
    (hw : Sem.writeVal s.mem b off ty v = some m_clean') :
    ∃ m', b ∉ allRegBlks cur outer ∧
      Sem.writeVal m b off ty v = some m' ∧
      (∀ vty, ValScalarTyped ty v → Sem.writePlace tags m b off ty (.rval v vty) = some (.rval v ty, m')) ∧
      Refines tags baseEnv cur outer { s with mem := m_clean' } env blks m' := by
  obtain ⟨bs, hbs⟩ := writeVal_writeBytes hw
  have hblk_ex : ∃ blk, s.mem.blocks b = some blk := by
    unfold Mem.writeBytes at hbs
    split at hbs
    · cases hbs
    · next blk hblk => exact ⟨blk, hblk⟩
  obtain ⟨blk, hb⟩ := hblk_ex
  obtain ⟨hnot, hbm⟩ := hr.mem_blocks_some hb
  obtain ⟨m', hwm, hbeq, hne_m, hnext_m⟩ := writeVal_eq_of_blocks_eq (hbm.trans hb.symm) hw
  have hne_clean : ∀ b', b' ≠ b → m_clean'.blocks b' = s.mem.blocks b' := fun b' hne =>
    writeVal_blocks_ne hw hne
  have hnext_c : m_clean'.nextBlock = s.mem.nextBlock := writeVal_nextBlock hw
  refine ⟨m', hnot, hwm, (fun vty ht => writePlace_rval_scalar ht hwm), ?_⟩
  refine ⟨hr.env_eq, hr.blks_eq, hr.nodup_blks, hr.disjoint_names, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnext_c, hnext_m]; exact hr.nextBlock_le
  · intro sb hsb
    have hne : sb ≠ b := fun heq => hnot (heq ▸ hsb)
    rw [hne_clean sb hne]
    exact hr.slots_absent sb hsb
  · intro b' hbnot
    by_cases heq : b' = b
    · subst b'; exact hbeq
    · rw [hne_m b' heq, hne_clean b' heq]
      exact hr.blocks_agree b' hbnot
  · refine hr.regs_match.of_blocks_agree (fun sl hsl => ?_)
    have hne : sl.blk ≠ b := fun heq => hnot (heq ▸ List.mem_map.mpr ⟨sl, hsl, rfl⟩)
    exact hne_m sl.blk hne
  · refine hr.stk_match.of_blocks (fun sl hsl => ?_)
    obtain ⟨sblk, hsb, hsk⟩ := hr.stk_match.blocks_some hsl
    exact writeBytes_preserves_stack_kind hbs hsb hsk

theorem writeBytes_mem {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m m_clean' : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {b : BlockId} {off : Int64} {bs : List MemByte}
    (hw : s.mem.writeBytes b off bs = some m_clean') :
    ∃ m', b ∉ allRegBlks cur outer ∧
      m.writeBytes b off bs = some m' ∧
      (∀ ty sty, bs.length = sizeofTy tags ty →
        Sem.writePlace tags m b off ty (.structVal bs sty) = some (.structVal bs ty, m')) ∧
      Refines tags baseEnv cur outer { s with mem := m_clean' } env blks m' := by
  have hblk_ex : ∃ blk, s.mem.blocks b = some blk := by
    unfold Mem.writeBytes at hw
    split at hw
    · cases hw
    · next blk hblk => exact ⟨blk, hblk⟩
  obtain ⟨blk, hb⟩ := hblk_ex
  obtain ⟨hnot, hbm⟩ := hr.mem_blocks_some hb
  obtain ⟨m', hwm, hbeq, hne_m, hnext_m⟩ := writeBytes_eq_of_blocks_eq (hbm.trans hb.symm) hw
  have hne_clean : ∀ b', b' ≠ b → m_clean'.blocks b' = s.mem.blocks b' := fun b' hne =>
    writeBytes_blocks_ne hw hne
  have hnext_c : m_clean'.nextBlock = s.mem.nextBlock := writeBytes_nextBlock hw
  refine ⟨m', hnot, hwm, (fun ty sty hbs => by simp [Sem.writePlace, hbs, hwm]), ?_⟩
  refine ⟨hr.env_eq, hr.blks_eq, hr.nodup_blks, hr.disjoint_names, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnext_c, hnext_m]; exact hr.nextBlock_le
  · intro sb hsb
    have hne : sb ≠ b := fun heq => hnot (heq ▸ hsb)
    rw [hne_clean sb hne]
    exact hr.slots_absent sb hsb
  · intro b' hbnot
    by_cases heq : b' = b
    · subst b'; exact hbeq
    · rw [hne_m b' heq, hne_clean b' heq]
      exact hr.blocks_agree b' hbnot
  · refine hr.regs_match.of_blocks_agree (fun sl hsl => ?_)
    have hne : sl.blk ≠ b := fun heq => hnot (heq ▸ List.mem_map.mpr ⟨sl, hsl, rfl⟩)
    exact hne_m sl.blk hne
  · refine hr.stk_match.of_blocks (fun sl hsl => ?_)
    obtain ⟨sblk, hsb, hsk⟩ := hr.stk_match.blocks_some hsl
    exact writeBytes_preserves_stack_kind hw hsb hsk

theorem after_call {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m m_after : Mem} {os' : OSState}
    (hr : Refines tags baseEnv cur outer s env blks m)
    (hregs : ∀ b ∈ allRegBlks cur outer, ∀ blk, m.blocks b = some blk → m_after.blocks b = some blk)
    (hstack : ∀ b blk, m.blocks b = some blk → blk.kind = .stack →
      ∃ blk', m_after.blocks b = some blk' ∧ blk'.kind = .stack) :
    Refines tags baseEnv cur outer
      { regs := s.regs, stack := s.stack, mem := dropBlks m_after (allRegBlks cur outer), os := os' }
      env blks m_after := by
  refine ⟨hr.env_eq, hr.blks_eq, hr.nodup_blks, hr.disjoint_names, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dropBlks_nextBlock]; exact Nat.le_refl _
  · intro b hb
    exact dropBlks_blocks_mem _ _ hb
  · intro b hbnot
    exact (dropBlks_blocks_not_mem _ _ hbnot).symm
  · refine hr.regs_match.of_blocks_agree (fun sl hsl => ?_)
    obtain ⟨blk, hbm, _, _⟩ := hr.regs_match.blocks_some hsl
    have hmem : sl.blk ∈ allRegBlks cur outer := List.mem_map.mpr ⟨sl, hsl, rfl⟩
    exact (hregs sl.blk hmem blk hbm).trans hbm.symm
  · refine hr.stk_match.of_blocks (fun sl hsl => ?_)
    have hsl_all : sl ∈ stkSlots (allSlots cur outer) := hsl
    have hnot : sl.blk ∉ allRegBlks cur outer := not_mem_reg_of_stk_nodup hr.nodup_blks hsl_all
    obtain ⟨blk, hbs, hk⟩ := hr.stk_match.blocks_some hsl
    have hbm : m.blocks sl.blk = some blk := (hr.blocks_agree sl.blk hnot).trans hbs
    obtain ⟨blk', hbm', hk'⟩ := hstack sl.blk blk hbm hk
    rw [dropBlks_blocks_not_mem _ _ hnot]
    exact ⟨blk', hbm', hk'⟩

theorem castVal_unqual_eq (m : Mem) {t1 t2 : CTy} (hu : t1.unqual = t2.unqual) (v : Val) :
    Sem.castVal m t1 v = Sem.castVal m t2 v := by
  unfold Sem.castVal
  simp only [hu]

private theorem mapM_loop_castVal_unqual {m : Mem}
    (ps1 ps2 : List CTy) (args : List (Val × CTy))
    (hmap : ps1.map CTy.unqual = ps2.map CTy.unqual) (acc : List Val) :
    List.mapM.loop (m := Option) (fun (p : CTy × Val × CTy) => Sem.castVal m p.1 p.2.1) (ps1.zip args) acc =
    List.mapM.loop (m := Option) (fun (p : CTy × Val × CTy) => Sem.castVal m p.1 p.2.1) (ps2.zip args) acc := by
  induction ps1 generalizing ps2 args acc with
  | nil =>
    cases ps2 with
    | nil => rfl
    | cons _ _ => cases hmap
  | cons p1 t1 ih =>
    cases ps2 with
    | nil => cases hmap
    | cons p2 t2 =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      cases args with
      | nil => rfl
      | cons arg rest =>
        simp only [List.zip_cons_cons, List.mapM.loop, bind, Option.bind]
        rw [castVal_unqual_eq m hmap.1 arg.1]
        cases Sem.castVal m p2 arg.1 with
        | none => rfl
        | some cv => exact ih t2 rest hmap.2 (cv :: acc)

theorem coerceCallArgs_of_map_unqual {m : Mem} {ps1 ps2 : List CTy} {variadic : Bool}
    {args : List (Val × CTy)} (hmap : ps1.map CTy.unqual = ps2.map CTy.unqual) :
    Sem.coerceCallArgs m ps1 variadic args = Sem.coerceCallArgs m ps2 variadic args := by
  have hlen : ps1.length = ps2.length := by
    have := congrArg List.length hmap
    simpa using this
  unfold Sem.coerceCallArgs
  simp only [hlen]
  by_cases hv : variadic = true
  · simp only [hv, ↓reduceIte, bind, Option.bind]
    by_cases hle : ps2.length ≤ args.length
    · simp only [guard, pure, Pure.pure, hle, ↓reduceIte]
      have hm := mapM_loop_castVal_unqual (m := m) ps1 ps2 (args.take ps2.length) hmap []
      simp only [List.mapM] at hm ⊢
      rw [hm]
    · simp [guard, failure, hle]
  · have hvf : variadic = false := Bool.eq_false_iff.mpr hv
    simp only [hvf, Bool.false_eq_true, ↓reduceIte, bind, Option.bind]
    by_cases heq : args.length = ps2.length
    · simp only [guard, pure, Pure.pure, beq_iff_eq, heq, ↓reduceIte]
      have hm := mapM_loop_castVal_unqual (m := m) ps1 ps2 args hmap []
      simp only [List.mapM] at hm ⊢
      rw [hm]
    · simp [guard, failure, heq]

private theorem mapM_loop_castVal_mem {tags : TypeEnv} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    (l : List (CTy × Val × CTy)) (acc out : List Val)
    (h : List.mapM.loop (m := Option) (fun (p : CTy × Val × CTy) => Sem.castVal s.mem p.1 p.2.1) l acc = some out) :
    List.mapM.loop (m := Option) (fun (p : CTy × Val × CTy) => Sem.castVal m p.1 p.2.1) l acc = some out := by
  induction l generalizing acc with
  | nil => exact h
  | cons hd tl ih =>
    unfold List.mapM.loop at h ⊢
    simp only [bind, Option.bind] at h ⊢
    cases hc : Sem.castVal s.mem hd.1 hd.2.1 with
    | none => simp [hc] at h
    | some cv =>
      simp only [hc] at h
      rw [hr.castVal_mem hc]
      exact ih (cv :: acc) h

theorem coerceCallArgs_mem {tags : TypeEnv} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {paramTys : List CTy} {variadic : Bool} {args : List (Val × CTy)} {out : List Val}
    (h : Sem.coerceCallArgs s.mem paramTys variadic args = some out) :
    Sem.coerceCallArgs m paramTys variadic args = some out := by
  unfold Sem.coerceCallArgs at h ⊢
  simp only [bind, Option.bind, pure, Pure.pure] at h ⊢
  by_cases hv : variadic = true
  · simp only [hv, ↓reduceIte] at h ⊢
    by_cases hlen : paramTys.length ≤ args.length
    · simp only [hlen, guard_true] at h ⊢
      cases hm : (paramTys.zip (args.take paramTys.length)).mapM (fun (pty, (v, _)) => Sem.castVal s.mem pty v) with
      | none => simp [hm] at h
      | some fx =>
        simp only [hm] at h
        have hm' : (paramTys.zip (args.take paramTys.length)).mapM (fun (pty, (v, _)) => Sem.castVal m pty v) = some fx :=
          mapM_loop_castVal_mem hr _ [] fx hm
        rw [hm']; exact h
    · simp [hlen, guard] at h
  · have hvf : variadic = false := Bool.eq_false_iff.mpr hv
    simp only [hvf, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hlen : (args.length == paramTys.length) = true
    · simp only [hlen, guard_true] at h ⊢
      exact mapM_loop_castVal_mem hr (paramTys.zip args) [] out h
    · have hlf : (args.length == paramTys.length) = false := Bool.eq_false_iff.mpr hlen
      simp [hlf, guard] at h

theorem alloc_some_writeVal {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m m1 : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {x : String} {ty : CTy} {v : Val} {base : UInt64} {bid : BlockId}
    (hstk_none : s.stack.lookup x = none)
    (ht : ValScalarTyped ty v)
    (hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy tags ty))
    (hba : base.toNat % max 1 (alignofTy tags ty) = 0)
    (halloc : m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1)) :
    ∃ m2,
      Sem.writeVal m1 bid 0 ty.stripConst v = some m2 ∧
      Refines tags baseEnv (⟨x, bid, ty, .reg⟩ :: cur) outer
        { s with regs := (x, v, ty) :: s.regs }
        ((x, bid, ty) :: env) (bid :: blks) m2 := by
  obtain ⟨r, m2, hwp, hr2⟩ := hr.alloc_some (vty := ty) hstk_none ht hsz hal hba halloc
  have hts : ValScalarTyped ty.stripConst v := by
    unfold ValScalarTyped at ht ⊢
    rwa [stripConst_unqual]
  have hwm : Sem.writeVal m1 bid 0 ty.stripConst v = some m2 := by
    unfold Sem.writePlace at hwp
    have hc := hts.castVal_self m1
    unfold ValScalarTyped at hts
    cases hu : ty.stripConst.unqual <;> simp [hu] at hts
    case vaList =>
      subst hts
      simp only [hu, bind, Option.bind, pure, Pure.pure] at hwp
      cases hw : Sem.writeVal m1 bid 0 ty.stripConst (.vaList true) with
      | none => rw [hw] at hwp; cases hwp
      | some mw => rw [hw] at hwp; cases hwp; rfl
    all_goals
      simp only [hu, hc, bind, Option.bind, pure, Pure.pure] at hwp
      cases hw : Sem.writeVal m1 bid 0 ty.stripConst v with
      | none => rw [hw] at hwp; cases hwp
      | some mw => rw [hw] at hwp; cases hwp; rfl
  exact ⟨m2, hwm, hr2⟩

end Refines

theorem ValScalarTyped.size_lt_ptrDiffLimit {tags : TypeEnv} {ty : CTy} {v : Val}
    (h : ValScalarTyped ty v) :
    max 1 (sizeofTy tags ty) < ptrDiffLimit := by
  unfold ValScalarTyped at h
  rw [← sizeofTy_unqual, ptrDiffLimit_val]
  cases hu : ty.unqual with
  | int k =>
    simp only [sizeofTy_int]
    cases k <;> decide
  | enumTy tag isU =>
    have hsz : sizeofTy tags (.enumTy tag isU) = 4 := by unfold sizeofTy sizeofAux; rfl
    rw [hsz]; decide
  | ptr _ =>
    simp only [sizeofTy_ptr]; decide
  | fnPtr r ps var =>
    have hsz : sizeofTy tags (.fnPtr r ps var) = 8 := by unfold sizeofTy sizeofAux; rfl
    rw [hsz]; decide
  | vaList =>
    have hsz : sizeofTy tags .vaList = 24 := by unfold sizeofTy sizeofAux; rfl
    rw [hsz]; decide
  | void | const_ _ | array _ _ | structTy _ | unionTy _ | anonStruct _ | anonUnion _ | typedef _ _ =>
    simp [hu] at h

theorem ValScalarTyped.align_pos {tags : TypeEnv} {ty : CTy} {v : Val}
    (_h : ValScalarTyped ty v) :
    0 < max 1 (alignofTy tags ty) :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem pushCallParams_exists_of_scalar (tags : TypeEnv) (baseEnv : Env)
    (cur : FrameScope) (s : SymState) (env : Env) (blks : List BlockId) (m : Mem) (idx : Nat)
    (hr : Refines tags baseEnv cur [] s env blks m)
    (hstk : s.stack = [])
    (pvs : List (Param × Val))
    (ht : ∀ pv ∈ pvs, ValScalarTyped pv.1.ty pv.2) :
    ∃ callEnv callBlks m',
      pushCallParams tags m (fun _ => 0) idx pvs env blks = some (callEnv, callBlks, m') := by
  induction pvs generalizing cur s env blks m idx with
  | nil => exact ⟨env, blks, m, rfl⟩
  | cons hd tl ih =>
    rcases hd with ⟨p, v⟩
    have hpv : ValScalarTyped p.ty v := ht (p, v) (.head _)
    have hsz : max 1 (sizeofTy tags p.ty) < ptrDiffLimit := hpv.size_lt_ptrDiffLimit
    have hal : 0 < max 1 (alignofTy tags p.ty) := hpv.align_pos
    have hba : ((fun _ : Nat => (0 : UInt64)) idx).toNat % max 1 (alignofTy tags p.ty) = 0 := Nat.zero_mod _
    obtain ⟨m2, hwm, hr2⟩ := hr.alloc_some_writeVal (x := p.name) (ty := p.ty) (v := v)
      (base := (fun _ : Nat => (0 : UInt64)) idx) (bid := m.nextBlock)
      (m1 := (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
        .rw .stack ((fun _ : Nat => (0 : UInt64)) idx) (fun _ => .undef) hsz hal hba).2)
      (by rw [hstk]; rfl) hpv hsz hal hba rfl
    obtain ⟨cEnv, cBlks, cm', hc⟩ := ih _ _ _ _ m2 (idx + 1) hr2 hstk (fun pv hp => ht pv (.tail _ hp))
    refine ⟨cEnv, cBlks, cm', ?_⟩
    rw [pushCallParams_cons (base := fun _ : Nat => (0 : UInt64)) (idx := idx) hsz hal hba hwm]
    exact hc

theorem Refines.of_pushCallParams {tags : TypeEnv} {baseEnv : Env}
    {cur : FrameScope} {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    {base : Nat → UInt64} {idx : Nat} {pvs : List (Param × Val)}
    {callEnv : Env} {callBlks : List BlockId} {m' : Mem}
    (hr : Refines tags baseEnv cur [] s env blks m)
    (hstk : s.stack = [])
    (ht : ∀ pv ∈ pvs, ValScalarTyped pv.1.ty pv.2)
    (hpush : pushCallParams tags m base idx pvs env blks = some (callEnv, callBlks, m')) :
    ∃ cur', Refines tags baseEnv cur' []
      { s with regs := pvs.reverse.map (fun pv => (pv.1.name, pv.2, pv.1.ty)) ++ s.regs }
      callEnv callBlks m' := by
  induction pvs generalizing cur s env blks m idx with
  | nil =>
    cases hpush
    exact ⟨cur, hr⟩
  | cons hd tl ih =>
    rcases hd with ⟨p, v⟩
    have hpv : ValScalarTyped p.ty v := ht (p, v) (.head _)
    obtain ⟨hsz, hal, hba, m2, hw2, hrest⟩ := pushCallParams_cons_inv hpush
    obtain ⟨m2', hwm', hr2⟩ := hr.alloc_some_writeVal (x := p.name) (ty := p.ty) (v := v)
      (base := base idx) (bid := m.nextBlock)
      (m1 := (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
        .rw .stack (base idx) (fun _ => .undef) hsz hal hba).2)
      (by rw [hstk]; rfl) hpv hsz hal hba rfl
    have heq_m2 : m2' = m2 := by
      rw [hwm'] at hw2
      cases hw2
      rfl
    subst heq_m2
    obtain ⟨cur', hrc⟩ := ih hr2 hstk (fun pv hp => ht pv (.tail _ hp)) hrest
    refine ⟨cur', ?_⟩
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using hrc

/-! ## Sequence-Point Modification Tracking (`ModsOK`) -/

def ModsOK (cur : FrameScope) (outer : List FrameScope) (modVars : List String)
    (modHeap : List (BlockId × Int64 × Nat)) (mods : ModSet) : Prop :=
  ∀ e ∈ mods,
    (∃ sl ∈ allRegSlots cur outer, sl.blk = e.bid ∧ sl.name ∈ modVars) ∨
    (∃ p ∈ modHeap, e.bid = p.1 ∧ e.off = p.2.1 ∧ e.len = p.2.2 ∧ p.1 ∉ allRegBlks cur outer)

private theorem slot_inj_of_nodup {slots : List FrameSlot} (hnd : (slots.map (·.blk)).Nodup)
    {s1 s2 : FrameSlot} (h1 : s1 ∈ slots) (h2 : s2 ∈ slots) (heq : s1.blk = s2.blk) :
    s1 = s2 := by
  induction slots with
  | nil => cases h1
  | cons hd tl ih =>
    rcases List.nodup_cons.mp hnd with ⟨hnot, hnd'⟩
    rcases List.mem_cons.mp h1 with rfl | ht1 <;> rcases List.mem_cons.mp h2 with rfl | ht2
    · rfl
    · exfalso; exact hnot (List.mem_map.mpr ⟨s2, ht2, heq.symm⟩)
    · exfalso; exact hnot (List.mem_map.mpr ⟨s1, ht1, heq⟩)
    · exact ih hnd' ht1 ht2

namespace ModsOK

theorem nil (cur : FrameScope) (outer : List FrameScope)
    (modVars : List String) (modHeap : List (BlockId × Int64 × Nat)) :
    ModsOK cur outer modVars modHeap [] := fun _ h => by cases h

theorem no_conflict_var {cur : FrameScope} {outer : List FrameScope}
    {modVars : List String} {modHeap : List (BlockId × Int64 × Nat)} {mods : ModSet}
    (hm : ModsOK cur outer modVars modHeap mods)
    (hnd : (allRegBlks cur outer).Nodup)
    {sl : FrameSlot} (hsl : sl ∈ allRegSlots cur outer) (hnot : sl.name ∉ modVars)
    (off : Int64) (sz : Nat) :
    mods.conflicts sl.blk off sz = false := by
  unfold ModSet.conflicts
  cases h : List.any mods (fun e => e.bid == sl.blk && !(e.off.toInt + ↑e.len ≤ off.toInt || off.toInt + ↑sz ≤ e.off.toInt)) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨e, he, hc⟩ := List.any_eq_true.mp h
    have hbid : e.bid = sl.blk := eq_of_beq (Bool.and_eq_true _ _ |>.mp hc).1
    rcases hm e he with ⟨sl', hsl', hblk', hname'⟩ | ⟨p, _, hp_b, _, _, hp_not⟩
    · have heq := slot_inj_of_nodup hnd hsl hsl' (hbid.symm.trans hblk'.symm)
      subst heq
      exact hnot hname'
    · exact hp_not (hp_b ▸ hbid ▸ List.mem_map.mpr ⟨sl, hsl, rfl⟩)

theorem no_conflict_heap {cur : FrameScope} {outer : List FrameScope}
    {modVars : List String} {modHeap : List (BlockId × Int64 × Nat)} {mods : ModSet}
    (hm : ModsOK cur outer modVars modHeap mods)
    {b : BlockId} (hb_not : b ∉ allRegBlks cur outer)
    (off : Int64) (sz : Nat)
    (hdisj : ∀ p ∈ modHeap, p.1 ≠ b ∨ p.2.1.toInt + (p.2.2 : Int) ≤ off.toInt ∨ off.toInt + (sz : Int) ≤ p.2.1.toInt) :
    mods.conflicts b off sz = false := by
  unfold ModSet.conflicts
  cases h : List.any mods (fun e => e.bid == b && !(e.off.toInt + ↑e.len ≤ off.toInt || off.toInt + ↑sz ≤ e.off.toInt)) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨e, he, hc⟩ := List.any_eq_true.mp h
    rcases Bool.and_eq_true _ _ |>.mp hc with ⟨hbeq, hnot_or⟩
    have hbid : e.bid = b := eq_of_beq hbeq
    rcases hm e he with ⟨sl, hsl, hblk, _⟩ | ⟨p, hp, hpb, hpo, hpl, _⟩
    · exact hb_not (hbid ▸ hblk ▸ List.mem_map.mpr ⟨sl, hsl, rfl⟩)
    · have hne_or := hdisj p hp
      have hbad : (e.off.toInt + ↑e.len ≤ off.toInt || off.toInt + ↑sz ≤ e.off.toInt) = false := by
        simpa [Bool.not_eq_true'] using hnot_or
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hbad
      rw [hpb] at hbid
      rw [hpo, hpl] at hbad
      rcases hne_or with hne | hle1 | hle2
      · exact hne hbid
      · exact hbad.1 hle1
      · exact hbad.2 hle2

theorem cons_var {cur : FrameScope} {outer : List FrameScope}
    {modVars : List String} {modHeap : List (BlockId × Int64 × Nat)} {mods : ModSet}
    (hm : ModsOK cur outer modVars modHeap mods)
    {sl : FrameSlot} (hsl : sl ∈ allRegSlots cur outer) (off : Int64) (sz : Nat) :
    ModsOK cur outer (sl.name :: modVars) modHeap (⟨sl.blk, off, sz⟩ :: mods) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he'
  · exact Or.inl ⟨sl, hsl, rfl, .head _⟩
  · rcases hm e he' with ⟨sl', hsl', hblk', hm'⟩ | ⟨p, hp, h1, h2, h3, h4⟩
    · exact Or.inl ⟨sl', hsl', hblk', .tail _ hm'⟩
    · exact Or.inr ⟨p, hp, h1, h2, h3, h4⟩

theorem cons_heap {cur : FrameScope} {outer : List FrameScope}
    {modVars : List String} {modHeap : List (BlockId × Int64 × Nat)} {mods : ModSet}
    (hm : ModsOK cur outer modVars modHeap mods)
    {b : BlockId} (hnot : b ∉ allRegBlks cur outer) (off : Int64) (sz : Nat) :
    ModsOK cur outer modVars ((b, off, sz) :: modHeap) (⟨b, off, sz⟩ :: mods) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he'
  · exact Or.inr ⟨(b, off, sz), .head _, rfl, rfl, rfl, hnot⟩
  · rcases hm e he' with ⟨sl', hsl', hblk', hm'⟩ | ⟨p, hp, h1, h2, h3, h4⟩
    · exact Or.inl ⟨sl', hsl', hblk', hm'⟩
    · exact Or.inr ⟨p, .tail _ hp, h1, h2, h3, h4⟩

end ModsOK

end C99.Proof.VCGen
