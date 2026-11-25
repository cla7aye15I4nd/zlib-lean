import C99.Proof.VCGen.Solve

/-!
# Verified VCGen Specifications for Standard Libc & POSIX Externals (`C99.Proof.VCGen.LibcSpecs`)

Provides generic external call contract constructors (`CallSpec.of_ext`, `CallSafeSpec.of_ext`)
and verified VCGen contracts (`CallSpec` / `CallSafeSpec`) for every external function in
`C99.Sem.stdLibcProtos` against `C99.Libc.ExtStep`. Strictly 100% domain-agnostic.
-/

namespace C99.Proof.VCGen

open C99 C99.Sem C99.Proof

/-! ## Generic External Call Contract Builders -/

/-- Build a terminating `CallSpec` for external symbol `sym` implemented by `Libc.ExtStep targetSym`.
Using distinct `sym` and `targetSym` supports symbol aliasing cleanly. -/
def CallSpec.of_ext {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (sym targetSym : String)
    (paramTys : List CTy) (retTy : CTy) (variadic : Bool := false)
    (pre : Mem → OSState → List Val → Prop)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop)
    (hnfn : prog.fns sym = none)
    (hext : ∀ args m os out, ext sym args m os out ↔ Libc.ExtStep targetSym args m os out)
    (hpre_mono : ∀ {m_clean m : Mem} {os : OSState} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args → pre m os args)
    (hpost_stack : ∀ {m_clean m m' : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack))
    (hpost_drop : ∀ {m_clean m m_after : Mem} {os os' : OSState} {args : List Val} {rv : Val}
      (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m_after os' →
      post m_clean os args rv (dropBlks m_after bs) os')
    (hstep_ok : ∀ m os args, pre m os args →
      (∃ ret m' os', Libc.ExtOk targetSym args m os ret m' os') ∧
      (∀ ret m' os', Libc.ExtOk targetSym args m os ret m' os' → post m os args ret m' os')) :
    CallSpec prog cfg ext where
  sym := sym
  paramTys := paramTys
  retTy := retTy
  variadic := variadic
  pre := pre
  post := post
  pre_mono := hpre_mono
  post_stack := hpost_stack
  post_drop := hpost_drop
  sound := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q hd hsig hptys hco hpre hcont
    have hco' : Sem.coerceCallArgs m ptys variadic argVals = some args :=
      (Refines.coerceCallArgs_of_map_unqual hptys).trans hco
    obtain ⟨⟨ret0, m0', os0', hok0⟩, hpost_of⟩ := hstep_ok m os args hpre
    have hex : ∃ ret m' os', ext sym args m os (.ok ret m' os') :=
      ⟨ret0, m0', os0', (hext args m os (.ok ret0 m0' os0')).mpr hok0⟩
    have hnoub : ¬ ext sym args m os .ub := fun hub =>
      ((hext args m os .ub).mp hub) ⟨ret0, m0', os0', hok0⟩
    exact WPTerm.of_call_ext hd hnfn hsig hco' hex hnoub fun ret m' os' hext' =>
      hcont ret m' os' (hpost_of ret m' os' ((hext args m os (.ok ret m' os')).mp hext'))
  sound_safe := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q R hd hsig hptys hco hpre hcont
    have hco' : Sem.coerceCallArgs m ptys variadic argVals = some args :=
      (Refines.coerceCallArgs_of_map_unqual hptys).trans hco
    obtain ⟨⟨ret0, m0', os0', hok0⟩, hpost_of⟩ := hstep_ok m os args hpre
    have hnoub : ¬ ext sym args m os .ub := fun hub =>
      ((hext args m os .ub).mp hub) ⟨ret0, m0', os0', hok0⟩
    exact SafeUntil.of_call_ext hd hnfn hsig hco' hnoub fun ret m' os' hext' =>
      hcont ret m' os' (hpost_of ret m' os' ((hext args m os (.ok ret m' os')).mp hext'))

/-- Build a conditionally terminating `CallSafeSpec` for external symbol `sym` implemented by
`Libc.ExtStep targetSym`, where `hstep_term` may use `os.readBudget.isSome = true`. -/
def CallSafeSpec.of_ext {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (sym targetSym : String)
    (paramTys : List CTy) (retTy : CTy) (variadic : Bool := false)
    (pre : Mem → OSState → List Val → Prop)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop)
    (hnfn : prog.fns sym = none)
    (hext : ∀ args m os out, ext sym args m os out ↔ Libc.ExtStep targetSym args m os out)
    (hpre_mono : ∀ {m_clean m : Mem} {os : OSState} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args → pre m os args)
    (hpost_stack : ∀ {m_clean m m' : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack))
    (hpost_drop : ∀ {m_clean m m_after : Mem} {os os' : OSState} {args : List Val} {rv : Val}
      (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m_after os' →
      post m_clean os args rv (dropBlks m_after bs) os')
    (hstep_safe : ∀ m os args, pre m os args →
      (∃ ret m' os', Libc.ExtOk targetSym args m os ret m' os') ∧
      (∀ ret m' os', Libc.ExtOk targetSym args m os ret m' os' → post m os args ret m' os'))
    (hstep_term : ∀ m os args, os.readBudget.isSome = true → pre m os args →
      (∃ ret m' os', Libc.ExtOk targetSym args m os ret m' os') ∧
      (∀ ret m' os', Libc.ExtOk targetSym args m os ret m' os' → post m os args ret m' os') :=
      fun m os args _ hpre => hstep_safe m os args hpre) :
    CallSafeSpec prog cfg ext where
  sym := sym
  paramTys := paramTys
  retTy := retTy
  variadic := variadic
  pre := pre
  post := post
  pre_mono := hpre_mono
  post_stack := hpost_stack
  post_drop := hpost_drop
  sound_safe := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q R hd hsig hptys hco hpre hcont
    have hco' : Sem.coerceCallArgs m ptys variadic argVals = some args :=
      (Refines.coerceCallArgs_of_map_unqual hptys).trans hco
    obtain ⟨⟨ret0, m0', os0', hok0⟩, hpost_of⟩ := hstep_safe m os args hpre
    have hnoub : ¬ ext sym args m os .ub := fun hub =>
      ((hext args m os .ub).mp hub) ⟨ret0, m0', os0', hok0⟩
    exact SafeUntil.of_call_ext hd hnfn hsig hco' hnoub fun ret m' os' hext' =>
      hcont ret m' os' (hpost_of ret m' os' ((hext args m os (.ok ret m' os')).mp hext'))
  sound_term := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q hbud hd hsig hptys hco hpre hcont
    have hco' : Sem.coerceCallArgs m ptys variadic argVals = some args :=
      (Refines.coerceCallArgs_of_map_unqual hptys).trans hco
    obtain ⟨⟨ret0, m0', os0', hok0⟩, hpost_of⟩ := hstep_term m os args hbud hpre
    have hex : ∃ ret m' os', ext sym args m os (.ok ret m' os') :=
      ⟨ret0, m0', os0', (hext args m os (.ok ret0 m0' os0')).mpr hok0⟩
    have hnoub : ¬ ext sym args m os .ub := fun hub =>
      ((hext args m os .ub).mp hub) ⟨ret0, m0', os0', hok0⟩
    exact WPTerm.of_call_ext hd hnfn hsig hco' hex hnoub fun ret m' os' hext' =>
      hcont ret m' os' (hpost_of ret m' os' ((hext args m os (.ok ret m' os')).mp hext'))

/-! ## Generic Block Mutation, `errno`, Bounds, and String Helpers -/

/-- Preservation of non-byte block metadata (`size`, `align`, `perm`, `kind`, `baseAddr`). -/
def BlockMetaEq (blk blk' : Block) : Prop :=
  blk'.size = blk.size ∧
  blk'.align = blk.align ∧
  blk'.perm = blk.perm ∧
  blk'.kind = blk.kind ∧
  blk'.baseAddr = blk.baseAddr

theorem BlockMetaEq.refl (blk : Block) : BlockMetaEq blk blk :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem BlockMetaEq.trans {b1 b2 b3 : Block} (h12 : BlockMetaEq b1 b2) (h23 : BlockMetaEq b2 b3) :
    BlockMetaEq b1 b3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
    h23.2.2.2.1.trans h12.2.2.2.1, h23.2.2.2.2.trans h12.2.2.2.2⟩

/-- Exact byte-level characterization of overwriting `[off, off + bytes.length)` in `blk`. -/
def BlockWrittenAt (blk blk' : Block) (off : Int64) (bytes : List MemByte) : Prop :=
  BlockMetaEq blk blk' ∧
  ∀ i, blk'.bytes i =
    if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + bytes.length
    then bytes[i - off.toInt.toNat]?.getD .undef
    else blk.bytes i

theorem BlockWrittenAt.metaEq {blk blk' : Block} {off : Int64} {bytes : List MemByte}
    (h : BlockWrittenAt blk blk' off bytes) : BlockMetaEq blk blk' := h.1

theorem BlockWrittenAt.inBounds {blk blk' : Block} {off off' : Int64} {bytes : List MemByte} {n : Nat}
    (h : BlockWrittenAt blk blk' off bytes) :
    Mem.inBounds blk' off' n = Mem.inBounds blk off' n := by
  simp [Mem.inBounds, h.1.1]

theorem BlockWrittenAt.isAligned {blk blk' : Block} {off off' : Int64} {bytes : List MemByte} {al : Nat}
    (h : BlockWrittenAt blk blk' off bytes) :
    Mem.isAligned blk' off' al = Mem.isAligned blk off' al := by
  simp [Mem.isAligned, h.1.2.2.2.2]

theorem BlockWrittenAt.readBytes_same {m : Mem} {b : BlockId} {blk blk' : Block} {off : Int64}
    {bytes : List MemByte} (hb : m.blocks b = some blk') (hw : BlockWrittenAt blk blk' off bytes)
    (hin : Mem.inBounds blk off bytes.length = true) :
    m.readBytes b off bytes.length = some bytes := by
  have hin' : Mem.inBounds blk' off bytes.length = true := hw.inBounds.trans hin
  rw [readBytes_of_bounds hb hin']
  apply congrArg some
  apply List.ext_getElem
  · simp
  · intro i hi1 _
    have hi : i < bytes.length := by simpa using hi1
    simp [List.getElem_map, List.getElem_range, hw.2, hi, Nat.add_sub_cancel_left, Option.getD]

theorem BlockWrittenAt.bufSlice {m : Mem} {b : BlockId} {blk blk' : Block} {off : Int64}
    {bs : List UInt8} (hb : m.blocks b = some blk')
    (hw : BlockWrittenAt blk blk' off (bs.map MemByte.byte))
    (hin : Mem.inBounds blk off bs.length = true) :
    BufSlice m b off bs.length := by
  refine ⟨blk', hb, hw.inBounds.trans hin, fun i hi => ?_⟩
  refine ⟨bs[i], ?_⟩
  have hlen : (bs.map MemByte.byte).length = bs.length := by simp
  have hbyte := hw.2 (off.toInt.toNat + i)
  have hcond : off.toInt.toNat ≤ off.toInt.toNat + i ∧
      off.toInt.toNat + i < off.toInt.toNat + (bs.map MemByte.byte).length := by omega
  simp only [hcond, and_self, ↓reduceIte, Nat.add_sub_cancel_left] at hbyte
  rw [hbyte, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

private theorem strlenAt_go_of_mem_zero (blk : Block) (start len : Nat) (outBytes : List UInt8)
    (hlen : outBytes.length = len) (hsz : start + len ≤ blk.size)
    (hbytes : ∀ i < len, blk.bytes (start + i) = .byte (outBytes[i]?.getD 0)) :
    ∀ k, k ≤ len → (∃ j, len - k ≤ j ∧ j < len ∧ outBytes[j]? = some 0) →
      ∃ slen < len, len - k ≤ slen ∧ Mem.strlenAt.go blk start (start + (len - k)) = some slen := by
  intro k hk hex
  induction k with
  | zero =>
    rcases hex with ⟨j, hge, hlt, _⟩
    omega
  | succ k' ih =>
    have hidx_lt : len - (k' + 1) < len := by omega
    have hlt_blk : start + (len - (k' + 1)) < blk.size := by omega
    have hb_eq := hbytes (len - (k' + 1)) hidx_lt
    have hget : outBytes[len - (k' + 1)]? = some (outBytes[len - (k' + 1)]?.getD 0) := by
      have hidx_len : len - (k' + 1) < outBytes.length := hlen ▸ hidx_lt
      simp [List.getElem?_eq_getElem hidx_len, Option.getD]
    by_cases hz : outBytes[len - (k' + 1)]?.getD 0 = 0
    · refine ⟨len - (k' + 1), hidx_lt, Nat.le_refl _, ?_⟩
      rw [Mem.strlenAt.go]
      simp only [hlt_blk, ↓reduceDIte, hb_eq, hz]
      simp [Nat.add_sub_cancel_left]
    · have hex' : ∃ j, len - k' ≤ j ∧ j < len ∧ outBytes[j]? = some 0 := by
        rcases hex with ⟨j, hge, hlt, hj⟩
        by_cases hj_idx : j = len - (k' + 1)
        · subst hj_idx
          rw [hget, Option.some.injEq] at hj
          exact False.elim (hz hj)
        · exact ⟨j, by omega, hlt, hj⟩
      obtain ⟨slen, hslen_lt, hslen_ge, hgo⟩ := ih (by omega) hex'
      refine ⟨slen, hslen_lt, by omega, ?_⟩
      rw [Mem.strlenAt.go]
      simp only [hlt_blk, ↓reduceDIte, hb_eq]
      have hnext : start + (len - (k' + 1)) + 1 = start + (len - k') := by omega
      rwa [hnext]

theorem BlockWrittenAt.strlenAt_lt_of_zero_mem {m : Mem} {b : BlockId} {blk blk' : Block}
    {off : Int64} {outBytes : List UInt8}
    (hb : m.blocks b = some blk')
    (hw : BlockWrittenAt blk blk' off (outBytes.map MemByte.byte))
    (hin : Mem.inBounds blk off outBytes.length = true)
    (hnul : (0 : UInt8) ∈ outBytes) :
    ∃ slen < outBytes.length, m.strlenAt b off = some slen := by
  obtain ⟨h0, hlen_blk⟩ := inBounds_iff.mp hin
  have hlen_map : (outBytes.map MemByte.byte).length = outBytes.length := by simp
  have hsz : off.toInt.toNat + outBytes.length ≤ blk'.size := by rw [hw.1.1]; exact hlen_blk
  have hbytes : ∀ i < outBytes.length, blk'.bytes (off.toInt.toNat + i) = .byte (outBytes[i]?.getD 0) := by
    intro i hi
    have hcond : off.toInt.toNat ≤ off.toInt.toNat + i ∧
        off.toInt.toNat + i < off.toInt.toNat + (outBytes.map MemByte.byte).length := by omega
    have hbw := hw.2 (off.toInt.toNat + i)
    simp only [hcond, and_self, ↓reduceIte, Nat.add_sub_cancel_left] at hbw
    rw [hbw, List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  obtain ⟨j, hj_lt, hj_eq⟩ := List.mem_iff_getElem.mp hnul
  have hex : ∃ j0, outBytes.length - outBytes.length ≤ j0 ∧ j0 < outBytes.length ∧
      outBytes[j0]? = some 0 :=
    ⟨j, by omega, hj_lt, by rw [List.getElem?_eq_getElem hj_lt, hj_eq]⟩
  obtain ⟨slen, hslen_lt, _, hgo⟩ :=
    strlenAt_go_of_mem_zero blk' off.toInt.toNat outBytes.length outBytes rfl hsz hbytes
      outBytes.length (Nat.le_refl _) hex
  refine ⟨slen, hslen_lt, ?_⟩
  unfold Mem.strlenAt
  simp only [hb, h0, Nat.le_of_add_right_le hsz, bind, Option.bind]
  simpa [Nat.sub_self, Nat.add_zero] using hgo

private theorem strlenAt_go_of_nonnul_tail (blk : Block) (bs : List UInt8)
    (hsz : blk.size = bs.length + 1)
    (hbytes : ∀ i, blk.bytes i = .byte (if i < bs.length then bs[i]?.getD 0 else 0))
    (hnonnul : (0 : UInt8) ∉ bs) :
    ∀ k, k ≤ bs.length → Mem.strlenAt.go blk 0 (bs.length - k) = some bs.length := by
  intro k hk
  induction k with
  | zero =>
    rw [Nat.sub_zero, Mem.strlenAt.go]
    have hlt : bs.length < blk.size := by omega
    simp only [hlt, ↓reduceDIte, hbytes, Nat.lt_irrefl, ↓reduceIte, Nat.sub_zero]
  | succ k' ih =>
    have hlt : bs.length - (k' + 1) < bs.length := by omega
    have hlt1 : bs.length - (k' + 1) < blk.size := by omega
    have hnz : bs[bs.length - (k' + 1)]?.getD 0 ≠ 0 := fun hz => by
      have heq : bs[bs.length - (k' + 1)] = 0 := by
        simpa [List.getElem?_eq_getElem hlt, Option.getD] using hz
      exact hnonnul (heq ▸ List.getElem_mem hlt)
    have hsub : bs.length - (k' + 1) + 1 = bs.length - k' := by omega
    rw [Mem.strlenAt.go]
    simp only [hlt1, ↓reduceDIte, hbytes, hlt, ↓reduceIte]
    rw [hsub]
    first
    | exact ih (by omega)
    | (split
       · exfalso; apply hnz; simp_all
       · exact ih (by omega)
       · exfalso; rename_i _ hne; exact hne _ rfl)

theorem strlenAt_of_nonnul_bytes {m : Mem} {bid : BlockId} {blk : Block} {bs : List UInt8}
    (hb : m.blocks bid = some blk) (hsz : blk.size = bs.length + 1)
    (hbytes : ∀ i, blk.bytes i = .byte (if i < bs.length then bs[i]?.getD 0 else 0))
    (hnonnul : (0 : UInt8) ∉ bs) :
    m.strlenAt bid 0 = some bs.length := by
  have hgo := strlenAt_go_of_nonnul_tail blk bs hsz hbytes hnonnul bs.length (Nat.le_refl _)
  rw [Nat.sub_self] at hgo
  unfold Mem.strlenAt
  have hz : (0 : Int64).toInt = 0 := rfl
  simp only [hb, hz, Int.le_refl, Int.toNat_zero, Nat.zero_le, bind, Option.bind]
  exact hgo

theorem bitVec64_toNat_of_lt {k : Nat} {n : BitVec 64} (heq : BitVec.ofNat 64 k = n)
    (hlt : k < ptrDiffLimit) : n.toNat = k := by
  subst n
  have hlt64 : k < 2 ^ 64 := Nat.lt_trans hlt (by decide)
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]

theorem bitVec64_mul_toNat_of_lt {k0 n0 : Nat} {k n : BitVec 64}
    (hk : BitVec.ofNat 64 k0 = k) (hn : BitVec.ofNat 64 n0 = n)
    (hsz : k0 * n0 < ptrDiffLimit) : k.toNat * n.toNat = k0 * n0 := by
  by_cases hk0 : k0 = 0
  · subst hk0; simp [← hk]
  · by_cases hn0 : n0 = 0
    · subst hn0; simp [← hn]
    · have hklt : k0 < ptrDiffLimit :=
        Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right k0 (Nat.pos_of_ne_zero hn0)) hsz
      have hnlt : n0 < ptrDiffLimit :=
        Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left n0 (Nat.pos_of_ne_zero hk0)) hsz
      rw [bitVec64_toNat_of_lt hk hklt, bitVec64_toNat_of_lt hn hnlt]

theorem readBytes_spec {m : Mem} {b : BlockId} {off : Int64} {len : Nat} {bytes : List MemByte}
    (h : m.readBytes b off len = some bytes) :
    ∃ blk, m.blocks b = some blk ∧ Mem.inBounds blk off len = true ∧
      len < ptrDiffLimit ∧ bytes.length = len := by
  have ⟨blk, hblk⟩ : ∃ blk, m.blocks b = some blk := by
    unfold Mem.readBytes at h
    cases hb : m.blocks b with
    | none => simp [hb] at h
    | some blk => exact ⟨blk, rfl⟩
  have h1 := h
  unfold Mem.readBytes at h1
  simp only [hblk, bind, Option.bind, guard, Pure.pure] at h1
  by_cases hin : Mem.inBounds blk off len = true
  · simp only [hin, ↓reduceIte, Option.some.injEq] at h1
    obtain ⟨_, hlen⟩ := inBounds_iff.mp hin
    have hlt : len < ptrDiffLimit := Nat.lt_of_le_of_lt (by omega) blk.sizeLt
    exact ⟨blk, hblk, hin, hlt, by rw [← h1]; simp⟩
  · simp [hin] at h1

theorem writeBytes_spec {m m' : Mem} {b : BlockId} {off : Int64} {bs : List MemByte}
    (h : m.writeBytes b off bs = some m') :
    m'.nextBlock = m.nextBlock ∧
    (∀ x, x ≠ b → m'.blocks x = m.blocks x) ∧
    bs.length < ptrDiffLimit ∧
    ∃ blk blk', m.blocks b = some blk ∧ blk.perm = .rw ∧ Mem.inBounds blk off bs.length = true ∧
      m'.blocks b = some blk' ∧ BlockWrittenAt blk blk' off bs := by
  have hnext := writeBytes_nextBlock h
  have hne : ∀ x, x ≠ b → m'.blocks x = m.blocks x := fun x hx => writeBytes_blocks_ne h hx
  have h1 := h
  unfold Mem.writeBytes at h1
  split at h1
  · cases h1
  · next blk hb =>
    split at h1
    · next hcond =>
      have hperm : blk.perm = .rw := by simpa using (Bool.and_eq_true _ _).mp hcond |>.1
      have hin : Mem.inBounds blk off bs.length = true := (Bool.and_eq_true _ _).mp hcond |>.2
      obtain ⟨_, hlen⟩ := inBounds_iff.mp hin
      have hlt : bs.length < ptrDiffLimit := Nat.lt_of_le_of_lt (by omega) blk.sizeLt
      have hbe := writeBytes_blocks_eq hb h
      exact ⟨hnext, hne, hlt, blk, _, hb, hperm, hin, hbe, BlockMetaEq.refl blk, fun _ => rfl⟩
    · cases h1

theorem validWritableRange_iff {m : Mem} {b : BlockId} {off : Int64} {n : Nat} :
    Libc.validWritableRange m b off n = true ↔
      ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧ Mem.inBounds blk off n = true := by
  unfold Libc.validWritableRange
  cases hb : m.blocks b with
  | none => simp
  | some blk => simp

theorem validWritableRange_lt {m : Mem} {b : BlockId} {off : Int64} {n : Nat}
    (h : Libc.validWritableRange m b off n = true) : n < ptrDiffLimit := by
  obtain ⟨blk, _, _, hin⟩ := validWritableRange_iff.mp h
  obtain ⟨_, hlen⟩ := inBounds_iff.mp hin
  exact Nat.lt_of_le_of_lt (by omega) blk.sizeLt

theorem validReadableRange_iff {m : Mem} {b : BlockId} {off : Int64} {n : Nat} :
    Libc.validReadableRange m b off n = true ↔
      ∃ blk, m.blocks b = some blk ∧ Mem.inBounds blk off n = true := by
  unfold Libc.validReadableRange
  cases hb : m.blocks b with
  | none => simp
  | some blk => simp

theorem validReadableRange_lt {m : Mem} {b : BlockId} {off : Int64} {n : Nat}
    (h : Libc.validReadableRange m b off n = true) : n < ptrDiffLimit := by
  obtain ⟨blk, _, hin⟩ := validReadableRange_iff.mp h
  obtain ⟨_, hlen⟩ := inBounds_iff.mp hin
  exact Nat.lt_of_le_of_lt (by omega) blk.sizeLt

theorem validWritableRange_of_blocks_eq {m1 m2 : Mem} {b : BlockId} {off : Int64} {n : Nat}
    (heq : m2.blocks b = m1.blocks b) :
    Libc.validWritableRange m1 b off n = true → Libc.validWritableRange m2 b off n = true := by
  intro h
  obtain ⟨blk, hb, hperm, hin⟩ := validWritableRange_iff.mp h
  exact validWritableRange_iff.mpr ⟨blk, heq ▸ hb, hperm, hin⟩

theorem validReadableRange_of_blocks_eq {m1 m2 : Mem} {b : BlockId} {off : Int64} {n : Nat}
    (heq : m2.blocks b = m1.blocks b) :
    Libc.validReadableRange m1 b off n = true → Libc.validReadableRange m2 b off n = true := by
  intro h
  obtain ⟨blk, hb, hin⟩ := validReadableRange_iff.mp h
  exact validReadableRange_iff.mpr ⟨blk, heq ▸ hb, hin⟩

theorem readBytes_of_blocks_eq {m1 m2 : Mem} {b : BlockId} {off : Int64} {n : Nat}
    (heq : m2.blocks b = m1.blocks b) :
    m2.readBytes b off n = m1.readBytes b off n := by
  unfold Mem.readBytes
  simp only [heq]

private theorem strlenAt_go_lt (blk : Block) (start : Nat) :
    ∀ k i len, blk.size - i = k → start ≤ i →
      Mem.strlenAt.go blk start i = some len → start + len < blk.size := by
  intro k
  induction k with
  | zero =>
    intro i len hk _ hgo
    have hge : ¬ (i < blk.size) := by omega
    rw [Mem.strlenAt.go] at hgo
    simp [hge] at hgo
  | succ k' ih =>
    intro i len hk hsi hgo
    have hlt : i < blk.size := by omega
    rw [Mem.strlenAt.go] at hgo
    simp only [hlt, ↓reduceDIte] at hgo
    cases hcb : blk.bytes i with
    | byte u =>
      rw [hcb] at hgo
      split at hgo
      · cases hgo; omega
      · exact ih (i + 1) len (by omega) (by omega) hgo
      · cases hgo
    | undef | ptrFrag _ _ _ | fnFrag _ _ => simp [hcb] at hgo

theorem strlenAt_spec {m : Mem} {b : BlockId} {off : Int64} {len : Nat}
    (h : m.strlenAt b off = some len) :
    ∃ blk, m.blocks b = some blk ∧ 0 ≤ off.toInt ∧ off.toInt.toNat + len < blk.size ∧
      len < ptrDiffLimit := by
  have ⟨blk, hb⟩ : ∃ blk, m.blocks b = some blk := by
    have h1 := h
    unfold Mem.strlenAt at h1
    cases hmb : m.blocks b with
    | none => simp [hmb] at h1
    | some blk => exact ⟨blk, rfl⟩
  have h1 := h
  unfold Mem.strlenAt at h1
  rw [hb] at h1
  dsimp only [bind, Option.bind, guard, Pure.pure] at h1
  by_cases hcond : (0 ≤ off.toInt && off.toInt.toNat ≤ blk.size) = true
  · simp only [hcond, ↓reduceIte] at h1
    have h0 : 0 ≤ off.toInt := by simpa using (Bool.and_eq_true _ _).mp hcond |>.1
    have hlt := strlenAt_go_lt blk off.toInt.toNat (blk.size - off.toInt.toNat)
      off.toInt.toNat len rfl (Nat.le_refl _) h1
    exact ⟨blk, hb, h0, hlt, Nat.lt_of_lt_of_le (by omega) blk.sizeLt⟩
  · have hf : (0 ≤ off.toInt && off.toInt.toNat ≤ blk.size) = false := Bool.eq_false_iff.mpr hcond
    simp only [hf, Bool.false_eq_true, ↓reduceIte, failure, Alternative.failure] at h1
    cases h1

private theorem memchrStep_go_result (b : BlockId) (off : Int64) (target : UInt8) (n : Nat)
    (blk : Block) :
    ∀ k i ret, i = n - k → k ≤ n →
      Libc.memchrStep.go b off target n blk off.toInt.toNat i = some ret →
      ret = Val.null ∨
        ∃ idx < n, ret = Val.ptr b (Int64.ofInt (off.toInt + idx)) ∧
          blk.bytes (off.toInt.toNat + idx) = .byte target := by
  intro k
  induction k with
  | zero =>
    intro i ret hi _ hgo
    rw [hi, Nat.sub_zero, Libc.memchrStep.go] at hgo
    simp at hgo
    exact .inl hgo.symm
  | succ k' ih =>
    intro i ret hi hk hgo
    have hlt : i < n := by omega
    rw [Libc.memchrStep.go] at hgo
    simp only [hlt, ↓reduceDIte] at hgo
    split at hgo
    · next u _ =>
      by_cases heq : (u == target) = true
      · simp only [heq, ↓reduceIte, Option.some.injEq] at hgo
        refine .inr ⟨i, hlt, hgo.symm, ?_⟩
        rw [← eq_of_beq heq]
        assumption
      · have hne : (u == target) = false := Bool.eq_false_iff.mpr heq
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hgo
        exact ih (i + 1) ret (by omega) (by omega) hgo
    · cases hgo

theorem memchrStep_spec {m : Mem} {b : BlockId} {off : Int64} {target : UInt8} {n : Nat}
    {ret : Val} (h : Libc.memchrStep m b off target n = some ret) :
    ∃ blk, m.blocks b = some blk ∧ Mem.inBounds blk off n = true ∧ n < ptrDiffLimit ∧
      (ret = .null ∨
        ∃ i < n, ret = .ptr b (Int64.ofInt (off.toInt + i)) ∧
          blk.bytes (off.toInt.toNat + i) = .byte target) := by
  have ⟨blk, hb⟩ : ∃ blk, m.blocks b = some blk := by
    have h1 := h
    unfold Libc.memchrStep at h1
    cases hmb : m.blocks b with
    | none => simp [hmb] at h1
    | some blk => exact ⟨blk, rfl⟩
  have h0 := h
  unfold Libc.memchrStep at h0
  rw [hb] at h0
  dsimp only [bind, Option.bind, guard, Pure.pure] at h0
  by_cases hcond : (0 ≤ off.toInt && off.toInt.toNat + n ≤ blk.size) = true
  · simp only [hcond, ↓reduceIte] at h0
    have hoff0 : 0 ≤ off.toInt := by simpa using (Bool.and_eq_true _ _).mp hcond |>.1
    have hlen : off.toInt.toNat + n ≤ blk.size := by
      simpa using (Bool.and_eq_true _ _).mp hcond |>.2
    have hin : Mem.inBounds blk off n = true := inBounds_iff.mpr ⟨hoff0, hlen⟩
    have hlt : n < ptrDiffLimit := Nat.lt_of_le_of_lt (by omega) blk.sizeLt
    have hres := memchrStep_go_result b off target n blk n 0 ret (Nat.sub_self n).symm (Nat.le_refl _) h0
    exact ⟨blk, hb, hin, hlt, hres⟩
  · have hf : (0 ≤ off.toInt && off.toInt.toNat + n ≤ blk.size) = false := Bool.eq_false_iff.mpr hcond
    simp only [hf, Bool.false_eq_true, ↓reduceIte, failure, Alternative.failure] at h0
    cases h0

/-! ## `errno` Validity & Mutation Framing -/

/-- Valid, writable, non-stack `int errno` block in OS state. -/
def ValidErrno (m : Mem) (os : OSState) : Prop :=
  ∃ eblk, m.blocks os.errnoBlk = some eblk ∧ eblk.perm = .rw ∧ eblk.kind ≠ .stack ∧ 4 ≤ eblk.size

theorem ValidErrno.of_blocks_eq {m1 m2 : Mem} {os : OSState}
    (heq : m2.blocks os.errnoBlk = m1.blocks os.errnoBlk) (h : ValidErrno m1 os) :
    ValidErrno m2 os := by
  obtain ⟨eblk, hb, hp, hk, hs⟩ := h
  exact ⟨eblk, heq ▸ hb, hp, hk, hs⟩

theorem ValidErrno.writeErrno_some {m : Mem} {os : OSState} (h : ValidErrno m os) (e : Int32) :
    ∃ m', Libc.writeErrno m os e = some m' := by
  obtain ⟨eblk, hb, hp, _, hs⟩ := h
  have hlen : (Mem.encodeInt .i32 (BitVec.ofInt IntKind.i32.bits e.toInt)).length = 4 :=
    encodeInt_length .i32 _
  have hin : Mem.inBounds eblk 0 (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt)).length = true := by
    rw [inBounds_iff]
    refine ⟨by decide, ?_⟩
    change 0 + (Mem.encodeInt .i32 (BitVec.ofInt IntKind.i32.bits e.toInt)).length ≤ eblk.size
    rw [hlen]
    omega
  exact writeBytes_eq_some hb hp hin

theorem ValidErrno.of_writeBytes {m m' : Mem} {os : OSState} {b : BlockId} {off : Int64}
    {bs : List MemByte} (h : ValidErrno m os) (hw : m.writeBytes b off bs = some m') :
    ValidErrno m' os := by
  obtain ⟨eblk, hb, hp, hk, hs⟩ := h
  by_cases hbe : os.errnoBlk = b
  · subst hbe
    obtain ⟨_, _, _, blk0, blk', hb0, _, _, hbe', hwa⟩ := writeBytes_spec hw
    rw [hb] at hb0
    cases hb0
    exact ⟨blk', hbe', hwa.1.2.2.1 ▸ hp, hwa.1.2.2.2.1 ▸ hk, hwa.1.1 ▸ hs⟩
  · rw [← writeBytes_blocks_ne hw hbe] at hb
    exact ⟨eblk, hb, hp, hk, hs⟩

/-- Postcondition fragment for external calls that mutate only `os.errnoBlk`. -/
def ErrnoOnlyPost (m : Mem) (os : OSState) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧ m.nextBlock ≤ m'.nextBlock ∧
  (∀ x, x ≠ os.errnoBlk → m'.blocks x = m.blocks x) ∧
  (∀ eblk, m.blocks os.errnoBlk = some eblk →
    ∃ (eblk' : Block) (e : Int32), m'.blocks os.errnoBlk = some eblk' ∧
      BlockWrittenAt eblk eblk' 0 (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt)))

theorem ErrnoOnlyPost.of_writeErrno {m m' : Mem} {os : OSState} {e : Int32}
    (herr : Libc.writeErrno m os e = some m') : ErrnoOnlyPost m os m' os := by
  obtain ⟨hnext, hne, _, blk, blk', hb, _, _, hbe, hwa⟩ := writeBytes_spec herr
  refine ⟨rfl, by rw [hnext]; exact Nat.le_refl _, hne, fun eblk hbe0 => ?_⟩
  rw [hb] at hbe0
  cases hbe0
  exact ⟨blk', e, hbe, hwa⟩

theorem ErrnoOnlyPost.post_stack {m_clean m m' : Mem} {os os' : OSState}
    (herr_pre : ValidErrno m_clean os) (bs : List BlockId)
    (habs : ∀ b ∈ bs, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (hp : ErrnoOnlyPost m os m' os') :
    m.nextBlock ≤ m'.nextBlock ∧
    (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
    (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
      ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack) := by
  obtain ⟨eblk0, he0, _, hk0, _⟩ := herr_pre
  have henot : os.errnoBlk ∉ bs := fun hmem => by
    have hn := habs _ hmem
    rw [he0] at hn
    cases hn
  have hm_e : m.blocks os.errnoBlk = some eblk0 := (hagree os.errnoBlk henot).trans he0
  rcases hp with ⟨_, hle, hother, _⟩
  refine ⟨hle, ?_, ?_⟩
  · intro b hb blk hbm _
    have hne : b ≠ os.errnoBlk := fun heq => henot (heq ▸ hb)
    rw [hother b hne, hbm]
  · intro b blk hbm hstk
    by_cases hbe : b = os.errnoBlk
    · subst hbe
      rw [hm_e] at hbm
      cases hbm
      exact False.elim (hk0 hstk)
    · rw [hother b hbe]
      exact ⟨blk, hbm, hstk⟩

theorem ErrnoOnlyPost.post_drop {m_clean m m_after : Mem} {os os' : OSState} (bs : List BlockId)
    (hnb : m_clean.nextBlock ≤ m.nextBlock)
    (habs : ∀ b ∈ bs, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (hp : ErrnoOnlyPost m os m_after os') :
    ErrnoOnlyPost m_clean os (dropBlks m_after bs) os' := by
  rcases hp with ⟨hos, hle, hother, herr⟩
  refine ⟨hos, by rw [dropBlks_nextBlock]; exact Nat.le_trans hnb hle, ?_, ?_⟩
  · intro x hx
    by_cases hxb : x ∈ bs
    · rw [dropBlks_blocks_mem _ _ hxb, habs x hxb]
    · rw [dropBlks_blocks_not_mem _ _ hxb, hother x hx, hagree x hxb]
  · intro eblk hce
    have henot : os.errnoBlk ∉ bs := fun hmem => by
      have hn := habs _ hmem
      rw [hce] at hn
      cases hn
    have hme : m.blocks os.errnoBlk = some eblk := (hagree os.errnoBlk henot).trans hce
    obtain ⟨eblk', e, hae, hwa⟩ := herr eblk hme
    exact ⟨eblk', e, by rw [dropBlks_blocks_not_mem _ _ henot]; exact hae, hwa⟩

private theorem dropBlks_blocks_eq_of_eq {m_clean m m_after : Mem} {bs : List BlockId}
    (habs : ∀ b ∈ bs, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (hother : ∀ b, m_after.blocks b = m.blocks b) :
    ∀ b, (dropBlks m_after bs).blocks b = m_clean.blocks b :=
  roExt_dropBlks_blocks_eq habs hagree hother

private theorem or_str_ne_absurd {s a b c : String} (hor : s = a ∨ s = b) (heq : s = c)
    (h1 : c ≠ a) (h2 : c ≠ b) : False := by
  subst heq
  rcases hor with rfl | rfl <;> contradiction

private theorem or_str_disj_absurd {s a b c d : String}
    (h1 : s = a ∨ s = b) (h2 : s = c ∨ s = d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : False := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> contradiction

private theorem str_disj_lit_absurd {s a b : String}
    (h : s = a ∨ s = b) (ha : s ≠ a) (hb : s ≠ b) : False := by
  rcases h with rfl | rfl <;> contradiction

local macro "close_ext_mismatch" : tactic =>
  `(tactic| all_goals (
      intro hfn _
      first
      | exact False.elim (or_str_ne_absurd ‹_ = "lseek" ∨ _ = "lseek64"› hfn (by decide) (by decide))
      | exact False.elim (or_str_ne_absurd ‹_ = "snprintf" ∨ _ = "vsnprintf"› hfn (by decide) (by decide))
      | exact absurd hfn (by decide)))

/-! ## 1. `malloc` -/

def MallocPre (_ : Mem) (_ : OSState) (args : List Val) : Prop :=
  ∃ n : BitVec 64, args = [.int .u64 n]

def MallocPost (m : Mem) (os : OSState) (args : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧ m.nextBlock ≤ m'.nextBlock ∧
  ((rv = .null ∧ ∀ b, m'.blocks b = m.blocks b) ∨
   (∃ (n : BitVec 64) (bid : BlockId) (blk : Block),
     args = [.int .u64 n] ∧ rv = .ptr bid 0 ∧
     n.toNat < ptrDiffLimit ∧
     m.nextBlock ≤ bid ∧ bid < m'.nextBlock ∧
     m.blocks bid = none ∧ m'.blocks bid = some blk ∧
     blk.size = n.toNat ∧ blk.align = 16 ∧ blk.perm = .rw ∧ blk.kind = .heap ∧
     blk.baseAddr.toNat % 16 = 0 ∧
     (∀ b, b ≠ bid → m'.blocks b = m.blocks b)))

private theorem extOk_malloc_inv {n : BitVec 64} {m : Mem} {os : OSState}
    {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "malloc" [.int .u64 n] m os ret m' os') :
    (ret = .null ∧ m' = m ∧ os' = os) ∨
    (∃ (n0 : Nat) (hsz : n0 < ptrDiffLimit) (base : UInt64) (hba : base.toNat % 16 = 0) (bid : BlockId),
      BitVec.ofNat 64 n0 = n ∧ ret = .ptr bid 0 ∧ os' = os ∧
      m.alloc n0 16 .rw .heap base (fun _ => .undef) hsz (by decide) hba = (bid, m')) := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "malloc" → args = [.int .u64 n] →
      (retA = .null ∧ mB = mA ∧ osB = osA) ∨
      (∃ (n0 : Nat) (hsz : n0 < ptrDiffLimit) (base : UInt64) (hba : base.toNat % 16 = 0) (bid : BlockId),
        BitVec.ofNat 64 n0 = n ∧ retA = .ptr bid 0 ∧ osB = osA ∧
        mA.alloc n0 16 .rw .heap base (fun _ => .undef) hsz (by decide) hba = (bid, mB)) := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case malloc_null _ =>
      intro _ _
      exact .inl ⟨rfl, rfl, rfl⟩
    case malloc_ok n0 hsz base hba bid halloc =>
      intro _ hargs
      injection hargs with hhead
      injection hhead with _ hbv
      exact .inr ⟨n0, hsz, base, hba, bid, hbv, rfl, rfl, halloc⟩
    close_ext_mismatch
  exact h hok rfl rfl

def mallocSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "malloc" = none)
    (hext : ∀ args m os out, ext "malloc" args m os out ↔ Libc.ExtStep "malloc" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "malloc" "malloc" [.int .u64] (.ptr .void) false MallocPre MallocPost
    hnfn hext
    (fun _ _ _ _ _ _ hpre => hpre)
    (fun {_ m m' _ _ _ _} _ _ _ _ _ _ _ hpost => by
      rcases hpost with ⟨_, hle, ⟨_, hblocks⟩ | ⟨_, bid, _, _, _, _, _, _, hnone, _, _, _, _, _, _, hne⟩⟩
      · exact ⟨hle, fun b _ blk hbm _ => (hblocks b).trans hbm,
          fun b blk hbm hk => ⟨blk, (hblocks b).trans hbm, hk⟩⟩
      · refine ⟨hle, ?_, ?_⟩
        · intro b _ blk hbm _
          have hbne : b ≠ bid := fun heq => by rw [heq, hnone] at hbm; cases hbm
          rw [hne b hbne, hbm]
        · intro b blk hbm hk
          have hbne : b ≠ bid := fun heq => by rw [heq, hnone] at hbm; cases hbm
          exact ⟨blk, (hne b hbne).trans hbm, hk⟩)
    (fun {m_clean m m_after os os' args rv} bs hnb habs hagree hlt _ _ hpost => by
      rcases hpost with ⟨hos, hle, ⟨hrv, hblocks⟩ |
          ⟨n, bid, blk, hargs, hrv, hsz, hbid_ge, hbid_lt, _, hmb, hblksz, hal, hp, hk, hba, hne⟩⟩
      · exact ⟨hos, by rw [dropBlks_nextBlock]; exact Nat.le_trans hnb hle,
          .inl ⟨hrv, dropBlks_blocks_eq_of_eq habs hagree hblocks⟩⟩
      · have hnot_mem : bid ∉ bs := fun hmem => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt bid hmem) hbid_ge)
        have hclean_ge : m_clean.nextBlock ≤ bid := Nat.le_trans hnb hbid_ge
        refine ⟨hos, by rw [dropBlks_nextBlock]; exact Nat.le_trans hnb hle,
          .inr ⟨n, bid, blk, hargs, hrv, hsz, hclean_ge, by rw [dropBlks_nextBlock]; exact hbid_lt,
            m_clean.fresh bid hclean_ge, by rw [dropBlks_blocks_not_mem _ _ hnot_mem]; exact hmb,
            hblksz, hal, hp, hk, hba, fun b hneb => ?_⟩⟩
        by_cases hbm : b ∈ bs
        · rw [dropBlks_blocks_mem _ _ hbm, habs b hbm]
        · rw [dropBlks_blocks_not_mem _ _ hbm, hne b hneb, hagree b hbm])
    (fun m os args hpre => by
      rcases hpre with ⟨n, rfl⟩
      refine ⟨⟨.null, m, os, ?_⟩, fun ret m' os' hok => ?_⟩
      · simpa using Libc.ExtOk.malloc_null n.toNat m os
      · rcases extOk_malloc_inv hok with ⟨rfl, rfl, rfl⟩ | ⟨n0, hsz, base, hba, bid, hn, rfl, rfl, halloc⟩
        · exact ⟨rfl, Nat.le_refl _, .inl ⟨rfl, fun _ => rfl⟩⟩
        · have hbid : bid = m.nextBlock := (congrArg Prod.fst halloc).symm
          have hm' : m' = (m.alloc n0 16 .rw .heap base (fun _ => .undef) hsz (by decide) hba).2 :=
            (congrArg Prod.snd halloc).symm
          subst hbid hm'
          have hnt : n.toNat = n0 := bitVec64_toNat_of_lt hn hsz
          exact ⟨rfl, Nat.le_succ _, .inr ⟨n, m.nextBlock, _, rfl, rfl, hnt ▸ hsz, Nat.le_refl _,
            Nat.lt_succ_self _, m.fresh m.nextBlock (Nat.le_refl _),
            alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, hnt.symm, rfl, rfl, rfl, hba,
            fun b hb => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hb⟩⟩)

/-! ## 2. `calloc` -/

def CallocPre (_ : Mem) (_ : OSState) (args : List Val) : Prop :=
  ∃ k n : BitVec 64, args = [.int .u64 k, .int .u64 n]

def CallocPost (m : Mem) (os : OSState) (args : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧ m.nextBlock ≤ m'.nextBlock ∧
  ((rv = .null ∧ ∀ b, m'.blocks b = m.blocks b) ∨
   (∃ (k n : BitVec 64) (bid : BlockId) (blk : Block),
     args = [.int .u64 k, .int .u64 n] ∧ rv = .ptr bid 0 ∧
     k.toNat * n.toNat < ptrDiffLimit ∧
     m.nextBlock ≤ bid ∧ bid < m'.nextBlock ∧
     m.blocks bid = none ∧ m'.blocks bid = some blk ∧
     blk.size = k.toNat * n.toNat ∧ blk.align = 16 ∧ blk.perm = .rw ∧ blk.kind = .heap ∧
     blk.baseAddr.toNat % 16 = 0 ∧
     (∀ i, blk.bytes i = .byte 0) ∧
     (∀ b, b ≠ bid → m'.blocks b = m.blocks b)))

private theorem extOk_calloc_inv {k n : BitVec 64} {m : Mem} {os : OSState}
    {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "calloc" [.int .u64 k, .int .u64 n] m os ret m' os') :
    (ret = .null ∧ m' = m ∧ os' = os) ∨
    (∃ (k0 n0 : Nat) (hsz : k0 * n0 < ptrDiffLimit) (base : UInt64) (hba : base.toNat % 16 = 0)
        (bid : BlockId),
      BitVec.ofNat 64 k0 = k ∧ BitVec.ofNat 64 n0 = n ∧ ret = .ptr bid 0 ∧ os' = os ∧
      m.alloc (k0 * n0) 16 .rw .heap base (fun _ => .byte 0) hsz (by decide) hba = (bid, m')) := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "calloc" → args = [.int .u64 k, .int .u64 n] →
      (retA = .null ∧ mB = mA ∧ osB = osA) ∨
      (∃ (k0 n0 : Nat) (hsz : k0 * n0 < ptrDiffLimit) (base : UInt64) (hba : base.toNat % 16 = 0)
          (bid : BlockId),
        BitVec.ofNat 64 k0 = k ∧ BitVec.ofNat 64 n0 = n ∧ retA = .ptr bid 0 ∧ osB = osA ∧
        mA.alloc (k0 * n0) 16 .rw .heap base (fun _ => .byte 0) hsz (by decide) hba = (bid, mB)) := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case calloc_null _ _ =>
      intro _ _
      exact .inl ⟨rfl, rfl, rfl⟩
    case calloc_ok k0 n0 hsz base hba bid halloc =>
      intro _ hargs
      injection hargs with hhead htail
      injection hhead with _ hk
      injection htail with hhead2
      injection hhead2 with _ hn
      exact .inr ⟨k0, n0, hsz, base, hba, bid, hk, hn, rfl, rfl, halloc⟩
    close_ext_mismatch
  exact h hok rfl rfl

def callocSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "calloc" = none)
    (hext : ∀ args m os out, ext "calloc" args m os out ↔ Libc.ExtStep "calloc" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "calloc" "calloc" [.int .u64, .int .u64] (.ptr .void) false CallocPre CallocPost
    hnfn hext
    (fun _ _ _ _ _ _ hpre => hpre)
    (fun {_ m m' _ _ _ _} _ _ _ _ _ _ _ hpost => by
      rcases hpost with ⟨_, hle, ⟨_, hblocks⟩ | ⟨_, _, bid, _, _, _, _, _, _, hnone, _, _, _, _, _, _, _, hne⟩⟩
      · exact ⟨hle, fun b _ blk hbm _ => (hblocks b).trans hbm,
          fun b blk hbm hk => ⟨blk, (hblocks b).trans hbm, hk⟩⟩
      · refine ⟨hle, ?_, ?_⟩
        · intro b _ blk hbm _
          have hbne : b ≠ bid := fun heq => by rw [heq, hnone] at hbm; cases hbm
          rw [hne b hbne, hbm]
        · intro b blk hbm hk
          have hbne : b ≠ bid := fun heq => by rw [heq, hnone] at hbm; cases hbm
          exact ⟨blk, (hne b hbne).trans hbm, hk⟩)
    (fun {m_clean m m_after os os' args rv} bs hnb habs hagree hlt _ _ hpost => by
      rcases hpost with ⟨hos, hle, ⟨hrv, hblocks⟩ |
          ⟨k, n, bid, blk, hargs, hrv, hsz, hbid_ge, hbid_lt, _, hmb, hblksz, hal, hp, hk, hba, hzero, hne⟩⟩
      · exact ⟨hos, by rw [dropBlks_nextBlock]; exact Nat.le_trans hnb hle,
          .inl ⟨hrv, dropBlks_blocks_eq_of_eq habs hagree hblocks⟩⟩
      · have hnot_mem : bid ∉ bs := fun hmem => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt bid hmem) hbid_ge)
        have hclean_ge : m_clean.nextBlock ≤ bid := Nat.le_trans hnb hbid_ge
        refine ⟨hos, by rw [dropBlks_nextBlock]; exact Nat.le_trans hnb hle,
          .inr ⟨k, n, bid, blk, hargs, hrv, hsz, hclean_ge, by rw [dropBlks_nextBlock]; exact hbid_lt,
            m_clean.fresh bid hclean_ge, by rw [dropBlks_blocks_not_mem _ _ hnot_mem]; exact hmb,
            hblksz, hal, hp, hk, hba, hzero, fun b hneb => ?_⟩⟩
        by_cases hbm : b ∈ bs
        · rw [dropBlks_blocks_mem _ _ hbm, habs b hbm]
        · rw [dropBlks_blocks_not_mem _ _ hbm, hne b hneb, hagree b hbm])
    (fun m os args hpre => by
      rcases hpre with ⟨k, n, rfl⟩
      refine ⟨⟨.null, m, os, ?_⟩, fun ret m' os' hok => ?_⟩
      · simpa using Libc.ExtOk.calloc_null k.toNat n.toNat m os
      · rcases extOk_calloc_inv hok with ⟨rfl, rfl, rfl⟩ | ⟨k0, n0, hsz, base, hba, bid, hk, hn, rfl, rfl, halloc⟩
        · exact ⟨rfl, Nat.le_refl _, .inl ⟨rfl, fun _ => rfl⟩⟩
        · have hbid : bid = m.nextBlock := (congrArg Prod.fst halloc).symm
          have hm' : m' = (m.alloc (k0 * n0) 16 .rw .heap base (fun _ => .byte 0) hsz (by decide) hba).2 :=
            (congrArg Prod.snd halloc).symm
          subst hbid hm'
          have hmul : k.toNat * n.toNat = k0 * n0 := bitVec64_mul_toNat_of_lt hk hn hsz
          exact ⟨rfl, Nat.le_succ _, .inr ⟨k, n, m.nextBlock, _, rfl, rfl, hmul ▸ hsz, Nat.le_refl _,
            Nat.lt_succ_self _, m.fresh m.nextBlock (Nat.le_refl _),
            alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, hmul.symm, rfl, rfl, rfl, hba, fun _ => rfl,
            fun b hb => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hb⟩⟩)

/-! ## 3. `free` -/

def FreePre (m : Mem) (_ : OSState) (args : List Val) : Prop :=
  args = [.null] ∨ ∃ b : BlockId, args = [.ptr b 0] ∧ ∃ blk : Block, m.blocks b = some blk ∧ blk.kind = .heap

def FreePost (m : Mem) (os : OSState) (args : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  rv = .void ∧ os' = os ∧ m.nextBlock ≤ m'.nextBlock ∧
  (args = [.null] → ∀ x, m'.blocks x = m.blocks x) ∧
  (∀ b, args = [.ptr b 0] →
    m'.blocks b = none ∧ (∀ x, x ≠ b → m'.blocks x = m.blocks x))

private theorem extOk_free_null_inv {m : Mem} {os : OSState}
    {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "free" [.null] m os ret m' os') :
    ret = .void ∧ m' = m ∧ os' = os := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "free" → args = [.null] → retA = .void ∧ mB = mA ∧ osB = osA := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case free_null => intro _ _; exact ⟨rfl, rfl, rfl⟩
    case free_ok _ _ => intro _ hargs; cases hargs
    close_ext_mismatch
  exact h hok rfl rfl

private theorem extOk_free_ptr_inv {b : BlockId} {m : Mem} {os : OSState}
    {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "free" [.ptr b 0] m os ret m' os') :
    ret = .void ∧ os' = os ∧ m.free b = some m' := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "free" → args = [.ptr b 0] → retA = .void ∧ osB = osA ∧ mA.free b = some mB := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case free_null => intro _ hargs; cases hargs
    case free_ok b' hfree =>
      intro _ hargs
      injection hargs with hhead
      injection hhead with hb
      exact ⟨rfl, rfl, hb ▸ hfree⟩
    close_ext_mismatch
  exact h hok rfl rfl

def freeSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "free" = none)
    (hext : ∀ args m os out, ext "free" args m os out ↔ Libc.ExtStep "free" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "free" "free" [.ptr .void] .void false FreePre FreePost
    hnfn hext
    (fun {_ m _ _} bs _ habs hagree _ _ hpre => by
      rcases hpre with rfl | ⟨b, rfl, blk, hbm, hk⟩
      · exact .inl rfl
      · have hnot : b ∉ bs := fun hmem => by
          have hn := habs _ hmem
          rw [hbm] at hn
          cases hn
        exact .inr ⟨b, rfl, blk, (hagree b hnot).trans hbm, hk⟩)
    (fun {_ m m' _ _ args _} bs _ habs hagree _ _ hpre hpost => by
      rcases hpost with ⟨_, _, hle, hnull, hptr⟩
      rcases hpre with rfl | ⟨b, rfl, blk0, hbc, hk0⟩
      · have hblocks := hnull rfl
        exact ⟨hle, fun x _ blk hbm _ => (hblocks x).trans hbm,
          fun x blk hbm hk => ⟨blk, (hblocks x).trans hbm, hk⟩⟩
      · have hnot : b ∉ bs := fun hmem => by
          have hn := habs _ hmem
          rw [hbc] at hn
          cases hn
        have hm_b : m.blocks b = some blk0 := (hagree b hnot).trans hbc
        obtain ⟨_, hne⟩ := hptr b rfl
        refine ⟨hle, ?_, ?_⟩
        · intro x hx blk hbm _
          have hxne : x ≠ b := fun heq => hnot (heq ▸ hx)
          rw [hne x hxne, hbm]
        · intro x blk hbm hstk
          by_cases hxb : x = b
          · subst hxb
            rw [hm_b] at hbm
            cases hbm
            rw [hk0] at hstk
            cases hstk
          · rw [hne x hxb]
            exact ⟨blk, hbm, hstk⟩)
    (fun {m_clean m m_after os os' args rv} bs hnb habs hagree _ _ _ hpost => by
      rcases hpost with ⟨hrv, hos, hle, hnull, hptr⟩
      refine ⟨hrv, hos, by rw [dropBlks_nextBlock]; exact Nat.le_trans hnb hle, ?_, ?_⟩
      · intro hargs
        exact dropBlks_blocks_eq_of_eq habs hagree (hnull hargs)
      · intro b hargs
        obtain ⟨hnone, hne⟩ := hptr b hargs
        refine ⟨?_, fun x hxb => ?_⟩
        · by_cases hmem : b ∈ bs
          · exact dropBlks_blocks_mem _ _ hmem
          · rw [dropBlks_blocks_not_mem _ _ hmem, hnone]
        · by_cases hmem : x ∈ bs
          · rw [dropBlks_blocks_mem _ _ hmem, habs x hmem]
          · rw [dropBlks_blocks_not_mem _ _ hmem, hne x hxb, hagree x hmem])
    (fun m os args hpre => by
      rcases hpre with rfl | ⟨b, rfl, blk, hb, hk⟩
      · refine ⟨⟨.void, m, os, Libc.ExtOk.free_null m os⟩, fun ret m' os' hok => ?_⟩
        obtain ⟨rfl, rfl, rfl⟩ := extOk_free_null_inv hok
        exact ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, fun _ h => by cases h⟩
      · have hfree_ex : ∃ m', m.free b = some m' := by
          unfold Mem.free
          simp [hb, hk]
        obtain ⟨m0', hfree0⟩ := hfree_ex
        refine ⟨⟨.void, m0', os, Libc.ExtOk.free_ok b m m0' os hfree0⟩, fun ret m' os' hok => ?_⟩
        obtain ⟨rfl, rfl, hfree⟩ := extOk_free_ptr_inv hok
        simp [Mem.free, hb, hk] at hfree
        cases hfree
        refine ⟨rfl, rfl, Nat.le_refl _, ?_, ?_⟩
        · intro h; cases h
        · intro b0 h0
          injection h0 with h0'
          injection h0' with h0''
          subst h0''
          exact ⟨by simp, fun x hx => by simp [hx]⟩)

/-! ## 4 & 5. `memcpy` & `memmove` -/

private def MemCopyPost (m : Mem) (os : OSState) (args : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  ∃ (bd bs : BlockId) (od os_ : Int64) (n : BitVec 64),
    args = [.ptr bd od, .ptr bs os_, .int .u64 n] ∧
    rv = .ptr bd od ∧ os' = os ∧ m.nextBlock ≤ m'.nextBlock ∧
    (∀ x, x ≠ bd → m'.blocks x = m.blocks x) ∧
    (∀ blk bytes, m.blocks bd = some blk → m.readBytes bs os_ n.toNat = some bytes →
      ∃ blk', m'.blocks bd = some blk' ∧ BlockWrittenAt blk blk' od bytes)

def MemcpyPre (m : Mem) (_ : OSState) (args : List Val) : Prop :=
  ∃ (bd bs : BlockId) (od os_ : Int64) (n : BitVec 64) (bytes : List MemByte),
    args = [.ptr bd od, .ptr bs os_, .int .u64 n] ∧
    Libc.ptrDisjointOrEq bd od bs os_ n.toNat = true ∧
    m.readBytes bs os_ n.toNat = some bytes ∧
    Libc.validWritableRange m bd od n.toNat = true

def MemcpyPost : Mem → OSState → List Val → Val → Mem → OSState → Prop := MemCopyPost

def MemmovePre (m : Mem) (_ : OSState) (args : List Val) : Prop :=
  ∃ (bd bs : BlockId) (od os_ : Int64) (n : BitVec 64) (bytes : List MemByte),
    args = [.ptr bd od, .ptr bs os_, .int .u64 n] ∧
    m.readBytes bs os_ n.toNat = some bytes ∧
    Libc.validWritableRange m bd od n.toNat = true

def MemmovePost : Mem → OSState → List Val → Val → Mem → OSState → Prop := MemCopyPost

private theorem memCopy_post_stack {m_clean m m' : Mem} {os os' : OSState} {args : List Val}
    {rv : Val} (bsReg : List BlockId)
    (habs : ∀ b ∈ bsReg, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bsReg → m.blocks b = m_clean.blocks b)
    (hmem_pre : ∃ (bd bsrc : BlockId) (od os_ : Int64) (n : BitVec 64) (bytes : List MemByte),
      args = [.ptr bd od, .ptr bsrc os_, .int .u64 n] ∧
      m_clean.readBytes bsrc os_ n.toNat = some bytes ∧
      Libc.validWritableRange m_clean bd od n.toNat = true)
    (hpost : MemCopyPost m os args rv m' os') :
    m.nextBlock ≤ m'.nextBlock ∧
    (∀ b ∈ bsReg, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
    (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
      ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack) := by
  rcases hpost with ⟨bd, bsrc, od, os_, n, hargs, _, _, hle, hother, hwr⟩
  rcases hmem_pre with ⟨bd0, bsrc0, od0, os0, n0, bytes0, hargs0, hrd0, hwr0⟩
  rw [hargs] at hargs0
  cases hargs0
  obtain ⟨blk_d, hbd_clean, _, _⟩ := validWritableRange_iff.mp hwr0
  obtain ⟨blk_s, hbs_clean, _, _, _⟩ := readBytes_spec hrd0
  have hbd_not : bd ∉ bsReg := fun hmem => by
    have hn := habs _ hmem; rw [hbd_clean] at hn; cases hn
  have hbs_not : bsrc ∉ bsReg := fun hmem => by
    have hn := habs _ hmem; rw [hbs_clean] at hn; cases hn
  have hrd_m : m.readBytes bsrc os_ n.toNat = some bytes0 := by
    rwa [readBytes_of_blocks_eq (hagree bsrc hbs_not)]
  refine ⟨hle, ?_, ?_⟩
  · intro b hb blk hbm _
    have hne : b ≠ bd := fun heq => hbd_not (heq ▸ hb)
    rw [hother b hne, hbm]
  · intro b blk hbm hstk
    by_cases hbb : b = bd
    · subst hbb
      obtain ⟨blk', hbm', hwa⟩ := hwr blk bytes0 hbm hrd_m
      exact ⟨blk', hbm', hwa.1.2.2.2.1 ▸ hstk⟩
    · rw [hother b hbb]
      exact ⟨blk, hbm, hstk⟩

private theorem memCopy_post_drop {m_clean m m_after : Mem} {os os' : OSState} {args : List Val}
    {rv : Val} (bsReg : List BlockId)
    (hnb : m_clean.nextBlock ≤ m.nextBlock)
    (habs : ∀ b ∈ bsReg, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bsReg → m.blocks b = m_clean.blocks b)
    (hpost : MemCopyPost m os args rv m_after os') :
    MemCopyPost m_clean os args rv (dropBlks m_after bsReg) os' := by
  rcases hpost with ⟨bd, bsrc, od, os_, n, hargs, hrv, hos, hle, hother, hwr⟩
  refine ⟨bd, bsrc, od, os_, n, hargs, hrv, hos,
    by rw [dropBlks_nextBlock]; exact Nat.le_trans hnb hle, ?_, ?_⟩
  · intro x hx
    by_cases hmem : x ∈ bsReg
    · rw [dropBlks_blocks_mem _ _ hmem, habs x hmem]
    · rw [dropBlks_blocks_not_mem _ _ hmem, hother x hx, hagree x hmem]
  · intro blk bytes hbd_c hrd_c
    obtain ⟨blk_s, hbs_c, _, _, _⟩ := readBytes_spec hrd_c
    have hbd_not : bd ∉ bsReg := fun hmem => by
      have hn := habs _ hmem; rw [hbd_c] at hn; cases hn
    have hbs_not : bsrc ∉ bsReg := fun hmem => by
      have hn := habs _ hmem; rw [hbs_c] at hn; cases hn
    have hbd_m : m.blocks bd = some blk := (hagree bd hbd_not).trans hbd_c
    have hrd_m : m.readBytes bsrc os_ n.toNat = some bytes := by
      rwa [readBytes_of_blocks_eq (hagree bsrc hbs_not)]
    obtain ⟨blk', hba, hwa⟩ := hwr blk bytes hbd_m hrd_m
    exact ⟨blk', by rw [dropBlks_blocks_not_mem _ _ hbd_not]; exact hba, hwa⟩

private theorem extOk_memcpy_inv {bd bsrc : BlockId} {od os_ : Int64} {n : BitVec 64}
    {m : Mem} {os : OSState} {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "memcpy" [.ptr bd od, .ptr bsrc os_, .int .u64 n] m os ret m' os') :
    ∃ (n0 : Nat) (bytes : List MemByte),
      BitVec.ofNat 64 n0 = n ∧ ret = .ptr bd od ∧ os' = os ∧
      m.readBytes bsrc os_ n0 = some bytes ∧ m.writeBytes bd od bytes = some m' := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "memcpy" → args = [.ptr bd od, .ptr bsrc os_, .int .u64 n] →
      ∃ (n0 : Nat) (bytes : List MemByte),
        BitVec.ofNat 64 n0 = n ∧ retA = .ptr bd od ∧ osB = osA ∧
        mA.readBytes bsrc os_ n0 = some bytes ∧ mA.writeBytes bd od bytes = some mB := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case memcpy_ok bd' bsrc' od' os_' n0 bytes _ hrd hwr =>
      intro _ hargs
      injection hargs with h0 h12
      injection h0 with hbd hod
      injection h12 with h1 h23
      injection h1 with hbs hos_
      injection h23 with h2
      injection h2 with _ hn
      subst hbd hod hbs hos_
      exact ⟨n0, bytes, hn, rfl, rfl, hrd, hwr⟩
    close_ext_mismatch
  exact h hok rfl rfl

private theorem extOk_memmove_inv {bd bsrc : BlockId} {od os_ : Int64} {n : BitVec 64}
    {m : Mem} {os : OSState} {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "memmove" [.ptr bd od, .ptr bsrc os_, .int .u64 n] m os ret m' os') :
    ∃ (n0 : Nat) (bytes : List MemByte),
      BitVec.ofNat 64 n0 = n ∧ ret = .ptr bd od ∧ os' = os ∧
      m.readBytes bsrc os_ n0 = some bytes ∧ m.writeBytes bd od bytes = some m' := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "memmove" → args = [.ptr bd od, .ptr bsrc os_, .int .u64 n] →
      ∃ (n0 : Nat) (bytes : List MemByte),
        BitVec.ofNat 64 n0 = n ∧ retA = .ptr bd od ∧ osB = osA ∧
        mA.readBytes bsrc os_ n0 = some bytes ∧ mA.writeBytes bd od bytes = some mB := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case memmove_ok bd' bsrc' od' os_' n0 bytes hrd hwr =>
      intro _ hargs
      injection hargs with h0 h12
      injection h0 with hbd hod
      injection h12 with h1 h23
      injection h1 with hbs hos_
      injection h23 with h2
      injection h2 with _ hn
      subst hbd hod hbs hos_
      exact ⟨n0, bytes, hn, rfl, rfl, hrd, hwr⟩
    close_ext_mismatch
  exact h hok rfl rfl

def memcpySpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "memcpy" = none)
    (hext : ∀ args m os out, ext "memcpy" args m os out ↔ Libc.ExtStep "memcpy" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "memcpy" "memcpy" [.ptr .void, .ptr (.const_ .void), .int .u64] (.ptr .void) false
    MemcpyPre MemcpyPost hnfn hext
    (fun {_ m _ _} bs _ habs hagree _ _ hpre => by
      rcases hpre with ⟨bd, bsrc, od, os_, n, bytes, rfl, hdis, hrd, hwr⟩
      obtain ⟨_, hbs_c, _, _, _⟩ := readBytes_spec hrd
      obtain ⟨_, hbd_c, _, _⟩ := validWritableRange_iff.mp hwr
      have hbs_not : bsrc ∉ bs := fun hm => by have hn := habs _ hm; rw [hbs_c] at hn; cases hn
      have hbd_not : bd ∉ bs := fun hm => by have hn := habs _ hm; rw [hbd_c] at hn; cases hn
      exact ⟨bd, bsrc, od, os_, n, bytes, rfl, hdis,
        by rwa [readBytes_of_blocks_eq (hagree bsrc hbs_not)],
        validWritableRange_of_blocks_eq (hagree bd hbd_not) hwr⟩)
    (fun bs _ habs hagree _ _ ⟨bd, bsrc, od, os_, n, bytes, hargs, _, hrd, hwr⟩ hpost =>
      memCopy_post_stack bs habs hagree ⟨bd, bsrc, od, os_, n, bytes, hargs, hrd, hwr⟩ hpost)
    (fun bs hnb habs hagree _ _ _ hpost => memCopy_post_drop bs hnb habs hagree hpost)
    (fun m os args hpre => by
      rcases hpre with ⟨bd, bsrc, od, os_, n, bytes, rfl, hdis, hrd, hwr⟩
      obtain ⟨_, _, _, _, hlen_eq⟩ := readBytes_spec hrd
      obtain ⟨blk, hb, hperm, hin⟩ := validWritableRange_iff.mp hwr
      obtain ⟨m0', hm0'⟩ := writeBytes_eq_some hb hperm (by rw [hlen_eq]; exact hin)
      refine ⟨⟨.ptr bd od, m0', os, ?_⟩, fun ret m' os' hok => ?_⟩
      · simpa using Libc.ExtOk.memcpy_ok bd bsrc od os_ n.toNat bytes m m0' os hdis hrd hm0'
      · obtain ⟨n0, bytes', hn, rfl, rfl, hrd', hwr'⟩ := extOk_memcpy_inv hok
        obtain ⟨_, _, _, hlt', _⟩ := readBytes_spec hrd'
        have hn0 : n.toNat = n0 := bitVec64_toNat_of_lt hn hlt'
        obtain ⟨hnext, hne, _, blk0, blk', hb0, _, _, hbe', hwa⟩ := writeBytes_spec hwr'
        refine ⟨bd, bsrc, od, os_, n, rfl, rfl, rfl, by rw [hnext]; exact Nat.le_refl _, hne, ?_⟩
        intro blk1 bytes1 hb1 hrd1
        rw [hb0] at hb1; cases hb1
        rw [hn0, hrd'] at hrd1; cases hrd1
        exact ⟨blk', hbe', hwa⟩)

def memmoveSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "memmove" = none)
    (hext : ∀ args m os out, ext "memmove" args m os out ↔ Libc.ExtStep "memmove" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "memmove" "memmove" [.ptr .void, .ptr (.const_ .void), .int .u64] (.ptr .void) false
    MemmovePre MemmovePost hnfn hext
    (fun {_ m _ _} bs _ habs hagree _ _ hpre => by
      rcases hpre with ⟨bd, bsrc, od, os_, n, bytes, rfl, hrd, hwr⟩
      obtain ⟨_, hbs_c, _, _, _⟩ := readBytes_spec hrd
      obtain ⟨_, hbd_c, _, _⟩ := validWritableRange_iff.mp hwr
      have hbs_not : bsrc ∉ bs := fun hm => by have hn := habs _ hm; rw [hbs_c] at hn; cases hn
      have hbd_not : bd ∉ bs := fun hm => by have hn := habs _ hm; rw [hbd_c] at hn; cases hn
      exact ⟨bd, bsrc, od, os_, n, bytes, rfl,
        by rwa [readBytes_of_blocks_eq (hagree bsrc hbs_not)],
        validWritableRange_of_blocks_eq (hagree bd hbd_not) hwr⟩)
    (fun bs _ habs hagree _ _ ⟨bd, bsrc, od, os_, n, bytes, hargs, hrd, hwr⟩ hpost =>
      memCopy_post_stack bs habs hagree ⟨bd, bsrc, od, os_, n, bytes, hargs, hrd, hwr⟩ hpost)
    (fun bs hnb habs hagree _ _ _ hpost => memCopy_post_drop bs hnb habs hagree hpost)
    (fun m os args hpre => by
      rcases hpre with ⟨bd, bsrc, od, os_, n, bytes, rfl, hrd, hwr⟩
      obtain ⟨_, _, _, _, hlen_eq⟩ := readBytes_spec hrd
      obtain ⟨blk, hb, hperm, hin⟩ := validWritableRange_iff.mp hwr
      obtain ⟨m0', hm0'⟩ := writeBytes_eq_some hb hperm (by rw [hlen_eq]; exact hin)
      refine ⟨⟨.ptr bd od, m0', os, ?_⟩, fun ret m' os' hok => ?_⟩
      · simpa using Libc.ExtOk.memmove_ok bd bsrc od os_ n.toNat bytes m m0' os hrd hm0'
      · obtain ⟨n0, bytes', hn, rfl, rfl, hrd', hwr'⟩ := extOk_memmove_inv hok
        obtain ⟨_, _, _, hlt', _⟩ := readBytes_spec hrd'
        have hn0 : n.toNat = n0 := bitVec64_toNat_of_lt hn hlt'
        obtain ⟨hnext, hne, _, blk0, blk', hb0, _, _, hbe', hwa⟩ := writeBytes_spec hwr'
        refine ⟨bd, bsrc, od, os_, n, rfl, rfl, rfl, by rw [hnext]; exact Nat.le_refl _, hne, ?_⟩
        intro blk1 bytes1 hb1 hrd1
        rw [hb0] at hb1; cases hb1
        rw [hn0, hrd'] at hrd1; cases hrd1
        exact ⟨blk', hbe', hwa⟩)

/-! ## 6. `memset` -/

def MemsetPre (m : Mem) (_ : OSState) (args : List Val) : Prop :=
  ∃ (bd : BlockId) (od : Int64) (c : BitVec 32) (n : BitVec 64),
    args = [.ptr bd od, .int .i32 c, .int .u64 n] ∧
    Libc.validWritableRange m bd od n.toNat = true

def MemsetPost (m : Mem) (os : OSState) (args : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  ∃ (bd : BlockId) (od : Int64) (c : BitVec 32) (n : BitVec 64),
    args = [.ptr bd od, .int .i32 c, .int .u64 n] ∧
    rv = .ptr bd od ∧ os' = os ∧ m.nextBlock ≤ m'.nextBlock ∧
    (∀ x, x ≠ bd → m'.blocks x = m.blocks x) ∧
    (∀ blk, m.blocks bd = some blk →
      ∃ blk', m'.blocks bd = some blk' ∧
        BlockWrittenAt blk blk' od (List.replicate n.toNat (.byte (UInt8.ofNat (c.toNat % 256)))))

private theorem extOk_memset_inv {bd : BlockId} {od : Int64} {c : BitVec 32} {n : BitVec 64}
    {m : Mem} {os : OSState} {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "memset" [.ptr bd od, .int .i32 c, .int .u64 n] m os ret m' os') :
    ∃ n0 : Nat, BitVec.ofNat 64 n0 = n ∧ ret = .ptr bd od ∧ os' = os ∧
      m.writeBytes bd od (List.replicate n0 (.byte (UInt8.ofNat (c.toNat % 256)))) = some m' := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "memset" → args = [.ptr bd od, .int .i32 c, .int .u64 n] →
      ∃ n0 : Nat, BitVec.ofNat 64 n0 = n ∧ retA = .ptr bd od ∧ osB = osA ∧
        mA.writeBytes bd od (List.replicate n0 (.byte (UInt8.ofNat (c.toNat % 256)))) = some mB := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case memset_ok bd' od' c' n0 hwr =>
      intro _ hargs
      injection hargs with h0 h12
      injection h0 with hbd hod
      injection h12 with h1 h23
      injection h1 with _ hc
      injection h23 with h2
      injection h2 with _ hn
      subst hbd hod hc
      exact ⟨n0, hn, rfl, rfl, hwr⟩
    close_ext_mismatch
  exact h hok rfl rfl

def memsetSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "memset" = none)
    (hext : ∀ args m os out, ext "memset" args m os out ↔ Libc.ExtStep "memset" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "memset" "memset" [.ptr .void, .int .i32, .int .u64] (.ptr .void) false
    MemsetPre MemsetPost hnfn hext
    (fun {_ m _ _} bs _ habs hagree _ _ hpre => by
      rcases hpre with ⟨bd, od, c, n, rfl, hwr⟩
      obtain ⟨_, hbd_c, _, _⟩ := validWritableRange_iff.mp hwr
      have hbd_not : bd ∉ bs := fun hm => by have hn := habs _ hm; rw [hbd_c] at hn; cases hn
      exact ⟨bd, od, c, n, rfl, validWritableRange_of_blocks_eq (hagree bd hbd_not) hwr⟩)
    (fun {_ m m' _ _ _ _} bs _ habs hagree _ _ ⟨bd0, od0, c0, n0, hargs0, hwr0⟩
        ⟨bd, od, c, n, hargs, _, _, hle, hother, hwr⟩ => by
      rw [hargs] at hargs0
      injection hargs0 with h0 _
      injection h0 with hbd _
      obtain ⟨_, hbd_c, _, _⟩ := validWritableRange_iff.mp (hbd ▸ hwr0)
      have hbd_not : bd ∉ bs := fun hm => by have hn := habs _ hm; rw [hbd_c] at hn; cases hn
      refine ⟨hle, ?_, ?_⟩
      · intro b hb blk hbm _
        have hne : b ≠ bd := fun heq => hbd_not (heq ▸ hb)
        rw [hother b hne, hbm]
      · intro b blk hbm hstk
        by_cases hbb : b = bd
        · subst hbb
          obtain ⟨blk', hbm', hwa⟩ := hwr blk hbm
          exact ⟨blk', hbm', hwa.1.2.2.2.1 ▸ hstk⟩
        · rw [hother b hbb]
          exact ⟨blk, hbm, hstk⟩)
    (fun {m_clean m m_after os os' args rv} bs hnb habs hagree _ _ _
        ⟨bd, od, c, n, hargs, hrv, hos, hle, hother, hwr⟩ => by
      refine ⟨bd, od, c, n, hargs, hrv, hos,
        by rw [dropBlks_nextBlock]; exact Nat.le_trans hnb hle, ?_, ?_⟩
      · intro x hx
        by_cases hmem : x ∈ bs
        · rw [dropBlks_blocks_mem _ _ hmem, habs x hmem]
        · rw [dropBlks_blocks_not_mem _ _ hmem, hother x hx, hagree x hmem]
      · intro blk hbd_c
        have hbd_not : bd ∉ bs := fun hm => by have hn := habs _ hm; rw [hbd_c] at hn; cases hn
        obtain ⟨blk', hba, hwa⟩ := hwr blk ((hagree bd hbd_not).trans hbd_c)
        exact ⟨blk', by rw [dropBlks_blocks_not_mem _ _ hbd_not]; exact hba, hwa⟩)
    (fun m os args hpre => by
      rcases hpre with ⟨bd, od, c, n, rfl, hwr⟩
      obtain ⟨blk, hb, hperm, hin⟩ := validWritableRange_iff.mp hwr
      have hin' : Mem.inBounds blk od
          (List.replicate n.toNat (MemByte.byte (UInt8.ofNat (c.toNat % 256)))).length = true := by
        rw [List.length_replicate]
        exact hin
      obtain ⟨m0', hm0'⟩ := writeBytes_eq_some hb hperm hin'
      refine ⟨⟨.ptr bd od, m0', os, ?_⟩, fun ret m' os' hok => ?_⟩
      · simpa using Libc.ExtOk.memset_ok bd od c n.toNat m m0' os hm0'
      · obtain ⟨n0, hn, rfl, rfl, hwr'⟩ := extOk_memset_inv hok
        obtain ⟨hnext, hne, hlt, blk0, blk', hb0, _, _, hbe', hwa⟩ := writeBytes_spec hwr'
        have hlt0 : n0 < ptrDiffLimit := by simpa [List.length_replicate] using hlt
        have hn0 : n.toNat = n0 := bitVec64_toNat_of_lt hn hlt0
        refine ⟨bd, od, c, n, rfl, rfl, rfl, by rw [hnext]; exact Nat.le_refl _, hne, ?_⟩
        intro blk1 hb1
        rw [hb0] at hb1; cases hb1
        exact ⟨blk', hbe', hn0 ▸ hwa⟩)

/-! ## 7. `memcmp` -/

def MemcmpPre (m : Mem) (_ : OSState) (args : List Val) : Prop :=
  ∃ (b1 b2 : BlockId) (o1 o2 : Int64) (n : BitVec 64)
    (raw1 raw2 : List MemByte) (bs1 bs2 : List UInt8),
    args = [.ptr b1 o1, .ptr b2 o2, .int .u64 n] ∧
    m.readBytes b1 o1 n.toNat = some raw1 ∧ Libc.allConcreteBytes raw1 = some bs1 ∧
    m.readBytes b2 o2 n.toNat = some raw2 ∧ Libc.allConcreteBytes raw2 = some bs2

def MemcmpPost (m : Mem) (os : OSState) (args : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  MemUnchanged m m' ∧ os' = os ∧
  ∃ (b1 b2 : BlockId) (o1 o2 : Int64) (n : BitVec 64),
    args = [.ptr b1 o1, .ptr b2 o2, .int .u64 n] ∧
    (∃ i : BitVec 32, rv = .int .i32 i) ∧
    (∀ raw1 raw2 bs1 bs2,
      m.readBytes b1 o1 n.toNat = some raw1 → Libc.allConcreteBytes raw1 = some bs1 →
      m.readBytes b2 o2 n.toNat = some raw2 → Libc.allConcreteBytes raw2 = some bs2 →
      rv = .int .i32 (BitVec.ofInt 32 (Libc.memcmpBytes bs1 bs2).toInt))

private theorem extOk_memcmp_inv {b1 b2 : BlockId} {o1 o2 : Int64} {n : BitVec 64}
    {m : Mem} {os : OSState} {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "memcmp" [.ptr b1 o1, .ptr b2 o2, .int .u64 n] m os ret m' os') :
    ∃ (n0 : Nat) (raw1 raw2 : List MemByte) (bs1 bs2 : List UInt8),
      BitVec.ofNat 64 n0 = n ∧ m = m' ∧ os = os' ∧
      m.readBytes b1 o1 n0 = some raw1 ∧ Libc.allConcreteBytes raw1 = some bs1 ∧
      m.readBytes b2 o2 n0 = some raw2 ∧ Libc.allConcreteBytes raw2 = some bs2 ∧
      ret = .int .i32 (BitVec.ofInt 32 (Libc.memcmpBytes bs1 bs2).toInt) := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "memcmp" → args = [.ptr b1 o1, .ptr b2 o2, .int .u64 n] →
      ∃ (n0 : Nat) (raw1 raw2 : List MemByte) (bs1 bs2 : List UInt8),
        BitVec.ofNat 64 n0 = n ∧ mA = mB ∧ osA = osB ∧
        mA.readBytes b1 o1 n0 = some raw1 ∧ Libc.allConcreteBytes raw1 = some bs1 ∧
        mA.readBytes b2 o2 n0 = some raw2 ∧ Libc.allConcreteBytes raw2 = some bs2 ∧
        retA = .int .i32 (BitVec.ofInt 32 (Libc.memcmpBytes bs1 bs2).toInt) := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case memcmp_ok b1' b2' o1' o2' n0 raw1 raw2 bs1 bs2 hc1 hc2 hr1 hr2 =>
      intro _ hargs
      injection hargs with h0 h12
      injection h0 with hb1 ho1
      injection h12 with h1 h23
      injection h1 with hb2 ho2
      injection h23 with h2
      injection h2 with _ hn
      subst hb1 ho1 hb2 ho2
      exact ⟨n0, raw1, raw2, bs1, bs2, hn, rfl, rfl, hr1, hc1, hr2, hc2, rfl⟩
    close_ext_mismatch
  exact h hok rfl rfl

def memcmpSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "memcmp" = none)
    (hext : ∀ args m os out, ext "memcmp" args m os out ↔ Libc.ExtStep "memcmp" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "memcmp" "memcmp" [.ptr (.const_ .void), .ptr (.const_ .void), .int .u64]
    (.int .i32) false MemcmpPre MemcmpPost hnfn hext
    (fun {_ m _ _} bs _ habs hagree _ _ hpre => by
      rcases hpre with ⟨b1, b2, o1, o2, n, raw1, raw2, bs1, bs2, rfl, hr1, hc1, hr2, hc2⟩
      obtain ⟨_, hb1, _, _, _⟩ := readBytes_spec hr1
      obtain ⟨_, hb2, _, _, _⟩ := readBytes_spec hr2
      have h1 : b1 ∉ bs := fun hm => by have hn := habs _ hm; rw [hb1] at hn; cases hn
      have h2 : b2 ∉ bs := fun hm => by have hn := habs _ hm; rw [hb2] at hn; cases hn
      exact ⟨b1, b2, o1, o2, n, raw1, raw2, bs1, bs2, rfl,
        by rwa [readBytes_of_blocks_eq (hagree b1 h1)], hc1,
        by rwa [readBytes_of_blocks_eq (hagree b2 h2)], hc2⟩)
    (fun _ _ _ _ _ _ _ ⟨hmem, _⟩ =>
      ⟨hmem.post_stack.1, fun b _ blk hbm hk => hmem.post_stack.2 b blk hbm hk,
       fun b blk hbm hk => ⟨blk, hmem.post_stack.2 b blk hbm hk, hk⟩⟩)
    (fun {m_clean m m_after os os' args rv} bs hnb habs hagree _ _ _
        ⟨hmem, hos, b1, b2, o1, o2, n, hargs, hirv, hres⟩ => by
      refine ⟨MemUnchanged.post_drop hnb habs hagree hmem, hos, b1, b2, o1, o2, n, hargs, hirv, ?_⟩
      intro raw1 raw2 bs1 bs2 hr1 hc1 hr2 hc2
      obtain ⟨_, hb1, _, _, _⟩ := readBytes_spec hr1
      obtain ⟨_, hb2, _, _, _⟩ := readBytes_spec hr2
      have h1 : b1 ∉ bs := fun hm => by have hn := habs _ hm; rw [hb1] at hn; cases hn
      have h2 : b2 ∉ bs := fun hm => by have hn := habs _ hm; rw [hb2] at hn; cases hn
      exact hres raw1 raw2 bs1 bs2
        (by rwa [readBytes_of_blocks_eq (hagree b1 h1)]) hc1
        (by rwa [readBytes_of_blocks_eq (hagree b2 h2)]) hc2)
    (fun m os args hpre => by
      rcases hpre with ⟨b1, b2, o1, o2, n, raw1, raw2, bs1, bs2, rfl, hr1, hc1, hr2, hc2⟩
      refine ⟨⟨.int .i32 (BitVec.ofInt 32 (Libc.memcmpBytes bs1 bs2).toInt), m, os, ?_⟩,
        fun ret m' os' hok => ?_⟩
      · simpa using Libc.ExtOk.memcmp_ok b1 b2 o1 o2 n.toNat raw1 raw2 bs1 bs2 m os hr1 hc1 hr2 hc2
      · obtain ⟨n0, _, _, _, _, hn, rfl, rfl, hr1', hc1', hr2', hc2', rfl⟩ := extOk_memcmp_inv hok
        obtain ⟨_, _, _, hlt1, _⟩ := readBytes_spec hr1'
        have hn0 : n.toNat = n0 := bitVec64_toNat_of_lt hn hlt1
        refine ⟨MemUnchanged.refl m, rfl, b1, b2, o1, o2, n, rfl, ⟨_, rfl⟩, ?_⟩
        intro r1 r2 s1 s2 hr1a hc1a hr2a hc2a
        rw [hn0, hr1'] at hr1a; cases hr1a
        rw [hc1'] at hc1a; cases hc1a
        rw [hn0, hr2'] at hr2a; cases hr2a
        rw [hc2'] at hc2a; cases hc2a
        rfl)

/-! ## 8. `strlen` -/

def StrlenPre (m : Mem) (_ : OSState) (args : List Val) : Prop :=
  ∃ (b : BlockId) (off : Int64) (len : Nat), args = [.ptr b off] ∧ m.strlenAt b off = some len

def StrlenPost (m : Mem) (os : OSState) (args : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  MemUnchanged m m' ∧ os' = os ∧
  ∃ (b : BlockId) (off : Int64),
    args = [.ptr b off] ∧
    (∃ v : BitVec 64, rv = .int .u64 v) ∧
    (∀ len, m.strlenAt b off = some len → rv = .int .u64 (BitVec.ofNat 64 len))

private theorem extOk_strlen_inv {b : BlockId} {off : Int64} {m : Mem} {os : OSState}
    {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "strlen" [.ptr b off] m os ret m' os') :
    ∃ len : Nat, m = m' ∧ os = os' ∧ m.strlenAt b off = some len ∧
      ret = .int .u64 (BitVec.ofNat 64 len) := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "strlen" → args = [.ptr b off] →
      ∃ len : Nat, mA = mB ∧ osA = osB ∧ mA.strlenAt b off = some len ∧
        retA = .int .u64 (BitVec.ofNat 64 len) := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case strlen_ok b' off' len hlen =>
      intro _ hargs
      injection hargs with h0
      injection h0 with hb hoff
      subst hb hoff
      exact ⟨len, rfl, rfl, hlen, rfl⟩
    close_ext_mismatch
  exact h hok rfl rfl

def strlenSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "strlen" = none)
    (hext : ∀ args m os out, ext "strlen" args m os out ↔ Libc.ExtStep "strlen" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "strlen" "strlen" [.ptr (.const_ (.int .i8))] (.int .u64) false
    StrlenPre StrlenPost hnfn hext
    (fun {_ m _ _} bs _ habs hagree _ _ hpre => by
      rcases hpre with ⟨b, off, len, rfl, hlen⟩
      obtain ⟨_, hb, _, _, _⟩ := strlenAt_spec hlen
      have hnot : b ∉ bs := fun hm => by have hn := habs _ hm; rw [hb] at hn; cases hn
      exact ⟨b, off, len, rfl, by rwa [strlenAt_of_blocks_eq (hagree b hnot)]⟩)
    (fun _ _ _ _ _ _ _ ⟨hmem, _⟩ =>
      ⟨hmem.post_stack.1, fun b _ blk hbm hk => hmem.post_stack.2 b blk hbm hk,
       fun b blk hbm hk => ⟨blk, hmem.post_stack.2 b blk hbm hk, hk⟩⟩)
    (fun {m_clean m m_after os os' args rv} bs hnb habs hagree _ _ _
        ⟨hmem, hos, b, off, hargs, hv, hlen⟩ => by
      refine ⟨MemUnchanged.post_drop hnb habs hagree hmem, hos, b, off, hargs, hv, ?_⟩
      intro len hclean
      obtain ⟨_, hb, _, _, _⟩ := strlenAt_spec hclean
      have hnot : b ∉ bs := fun hm => by have hn := habs _ hm; rw [hb] at hn; cases hn
      exact hlen len (by rwa [strlenAt_of_blocks_eq (hagree b hnot)]))
    (fun m os args hpre => by
      rcases hpre with ⟨b, off, len, rfl, hlen⟩
      refine ⟨⟨.int .u64 (BitVec.ofNat 64 len), m, os, Libc.ExtOk.strlen_ok b off len m os hlen⟩,
        fun ret m' os' hok => ?_⟩
      obtain ⟨len', rfl, rfl, hlen', rfl⟩ := extOk_strlen_inv hok
      refine ⟨MemUnchanged.refl m, rfl, b, off, rfl, ⟨_, rfl⟩, fun len0 hlen0 => ?_⟩
      rw [hlen'] at hlen0
      cases hlen0
      rfl)

/-! ## 9. `memchr` -/

def MemchrPre (m : Mem) (_ : OSState) (args : List Val) : Prop :=
  ∃ (b : BlockId) (off : Int64) (c : BitVec 32) (n : BitVec 64) (ret : Val),
    args = [.ptr b off, .int .i32 c, .int .u64 n] ∧
    Libc.memchrStep m b off (UInt8.ofNat (c.toNat % 256)) n.toNat = some ret

def MemchrPost (m : Mem) (os : OSState) (args : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  MemUnchanged m m' ∧ os' = os ∧
  ∃ (b : BlockId) (off : Int64) (c : BitVec 32) (n : BitVec 64),
    args = [.ptr b off, .int .i32 c, .int .u64 n] ∧
    (∀ ret, Libc.memchrStep m b off (UInt8.ofNat (c.toNat % 256)) n.toNat = some ret → rv = ret) ∧
    (rv = .null ∨ ∃ i < n.toNat, rv = .ptr b (Int64.ofInt (off.toInt + i)))

private theorem extOk_memchr_inv {b : BlockId} {off : Int64} {c : BitVec 32} {n : BitVec 64}
    {m : Mem} {os : OSState} {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "memchr" [.ptr b off, .int .i32 c, .int .u64 n] m os ret m' os') :
    ∃ n0 : Nat, BitVec.ofNat 64 n0 = n ∧ m = m' ∧ os = os' ∧
      Libc.memchrStep m b off (UInt8.ofNat (c.toNat % 256)) n0 = some ret := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "memchr" → args = [.ptr b off, .int .i32 c, .int .u64 n] →
      ∃ n0 : Nat, BitVec.ofNat 64 n0 = n ∧ mA = mB ∧ osA = osB ∧
        Libc.memchrStep mA b off (UInt8.ofNat (c.toNat % 256)) n0 = some retA := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case memchr_ok b' off' c' n0 hres =>
      intro _ hargs
      injection hargs with h0 h12
      injection h0 with hb hoff
      injection h12 with h1 h23
      injection h1 with _ hc
      injection h23 with h2
      injection h2 with _ hn
      subst hb hoff hc
      exact ⟨n0, hn, rfl, rfl, hres⟩
    close_ext_mismatch
  exact h hok rfl rfl

def memchrSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "memchr" = none)
    (hext : ∀ args m os out, ext "memchr" args m os out ↔ Libc.ExtStep "memchr" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "memchr" "memchr" [.ptr (.const_ .void), .int .i32, .int .u64] (.ptr .void)
    false MemchrPre MemchrPost hnfn hext
    (fun {_ m _ _} bs _ habs hagree _ _ hpre => by
      rcases hpre with ⟨b, off, c, n, ret, rfl, hres⟩
      obtain ⟨_, hb, _, _, _⟩ := memchrStep_spec hres
      have hnot : b ∉ bs := fun hm => by have hn := habs _ hm; rw [hb] at hn; cases hn
      exact ⟨b, off, c, n, ret, rfl, by rwa [memchrStep_of_blocks_eq (hagree b hnot)]⟩)
    (fun _ _ _ _ _ _ _ ⟨hmem, _⟩ =>
      ⟨hmem.post_stack.1, fun b _ blk hbm hk => hmem.post_stack.2 b blk hbm hk,
       fun b blk hbm hk => ⟨blk, hmem.post_stack.2 b blk hbm hk, hk⟩⟩)
    (fun {m_clean m m_after os os' args rv} bs hnb habs hagree _ _ _
        ⟨hmem, hos, b, off, c, n, hargs, hdet, hshape⟩ => by
      refine ⟨MemUnchanged.post_drop hnb habs hagree hmem, hos, b, off, c, n, hargs, ?_, hshape⟩
      intro ret hclean
      obtain ⟨_, hb, _, _, _⟩ := memchrStep_spec hclean
      have hnot : b ∉ bs := fun hm => by have hn := habs _ hm; rw [hb] at hn; cases hn
      exact hdet ret (by rwa [memchrStep_of_blocks_eq (hagree b hnot)]))
    (fun m os args hpre => by
      rcases hpre with ⟨b, off, c, n, ret, rfl, hres⟩
      refine ⟨⟨ret, m, os, ?_⟩, fun ret' m' os' hok => ?_⟩
      · simpa using Libc.ExtOk.memchr_ok b off c n.toNat ret m os hres
      · obtain ⟨n0, hn, rfl, rfl, hres'⟩ := extOk_memchr_inv hok
        obtain ⟨_, _, _, hlt', hshape⟩ := memchrStep_spec hres'
        have hn0 : n.toNat = n0 := bitVec64_toNat_of_lt hn hlt'
        have hshape' : ret' = .null ∨ ∃ i < n.toNat, ret' = .ptr b (Int64.ofInt (off.toInt + i)) := by
          rcases hshape with hnull | ⟨i, hi, hptr, _⟩
          · exact .inl hnull
          · exact .inr ⟨i, hn0 ▸ hi, hptr⟩
        refine ⟨MemUnchanged.refl m, rfl, b, off, c, n, rfl, ?_, hshape'⟩
        intro ret1 hres1
        rw [hn0, hres'] at hres1
        cases hres1
        rfl)

/-! ## 10. `open` (`variadic := true`) -/

def OpenPre (m : Mem) (os : OSState) (args : List Val) : Prop :=
  ValidErrno m os ∧
  ∃ (b : BlockId) (off : Int64) (plen : Nat) (flags : BitVec 32) (rest : List Val),
    args = .ptr b off :: .int .i32 flags :: rest ∧ m.strlenAt b off = some plen

def OpenPost (m : Mem) (os : OSState) (_ : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  ErrnoOnlyPost m os m' os' ∧
  ∃ fd : Int32, -1 ≤ fd.toInt ∧ rv = .int .i32 (BitVec.ofInt 32 fd.toInt)

private theorem extOk_open_inv {b : BlockId} {off : Int64} {flags : BitVec 32} {rest : List Val}
    {m : Mem} {os : OSState} {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "open" (.ptr b off :: .int .i32 flags :: rest) m os ret m' os') :
    ∃ fd e : Int32, -1 ≤ fd.toInt ∧ os' = os ∧
      ret = .int .i32 (BitVec.ofInt 32 fd.toInt) ∧ Libc.writeErrno m os e = some m' := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "open" → args = .ptr b off :: .int .i32 flags :: rest →
      ∃ fd e : Int32, -1 ≤ fd.toInt ∧ osB = osA ∧
        retA = .int .i32 (BitVec.ofInt 32 fd.toInt) ∧ Libc.writeErrno mA osA e = some mB := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case open_ok =>
      intro _ _
      exact ⟨_, _, ‹-1 ≤ (_ : Int32).toInt›, rfl, rfl, ‹Libc.writeErrno _ _ _ = some _›⟩
    close_ext_mismatch
  exact h hok rfl rfl

def openSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "open" = none)
    (hext : ∀ args m os out, ext "open" args m os out ↔ Libc.ExtStep "open" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "open" "open" [.ptr (.const_ (.int .i8)), .int .i32] (.int .i32) true
    OpenPre OpenPost hnfn hext
    (fun {_ m os _} bs _ habs hagree _ _ hpre => by
      rcases hpre with ⟨herr, b, off, plen, flags, rest, rfl, hpath⟩
      obtain ⟨_, hb, _, _, _⟩ := strlenAt_spec hpath
      have hnot : b ∉ bs := fun hm => by have hn := habs _ hm; rw [hb] at hn; cases hn
      obtain ⟨eblk, he, hp, hk, hs⟩ := herr
      have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [he] at hn; cases hn
      exact ⟨⟨eblk, (hagree os.errnoBlk henot).trans he, hp, hk, hs⟩,
        b, off, plen, flags, rest, rfl, by rwa [strlenAt_of_blocks_eq (hagree b hnot)]⟩)
    (fun bs _ habs hagree _ _ ⟨herr_pre, _⟩ ⟨herr, _⟩ =>
      ErrnoOnlyPost.post_stack herr_pre bs habs hagree herr)
    (fun bs hnb habs hagree _ _ _ ⟨herr, hfd⟩ =>
      ⟨ErrnoOnlyPost.post_drop bs hnb habs hagree herr, hfd⟩)
    (fun m os args hpre => by
      rcases hpre with ⟨herr, b, off, plen, flags, rest, rfl, hpath⟩
      obtain ⟨m0', hm0'⟩ := herr.writeErrno_some 0
      refine ⟨⟨.int .i32 (BitVec.ofInt 32 (-1 : Int32).toInt), m0', os,
          Libc.ExtOk.open_ok b off plen flags rest (-1) 0 m m0' os hpath (by decide) hm0'⟩,
        fun ret m' os' hok => ?_⟩
      obtain ⟨fd, e, hfd, rfl, rfl, herr'⟩ := extOk_open_inv hok
      exact ⟨ErrnoOnlyPost.of_writeErrno herr', fd, hfd, rfl⟩)

/-! ## 11. `close` -/

def ClosePre (m : Mem) (os : OSState) (args : List Val) : Prop :=
  ValidErrno m os ∧ ∃ fd : BitVec 32, args = [.int .i32 fd]

def ClosePost (m : Mem) (os : OSState) (_ : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  ErrnoOnlyPost m os m' os' ∧
  ∃ ret : Int32, (ret = 0 ∨ ret = -1) ∧ rv = .int .i32 (BitVec.ofInt 32 ret.toInt)

private theorem extOk_close_inv {fd : BitVec 32} {m : Mem} {os : OSState}
    {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "close" [.int .i32 fd] m os ret m' os') :
    ∃ r e : Int32, (r = 0 ∨ r = -1) ∧ os' = os ∧
      ret = .int .i32 (BitVec.ofInt 32 r.toInt) ∧ Libc.writeErrno m os e = some m' := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "close" → args = [.int .i32 fd] →
      ∃ r e : Int32, (r = 0 ∨ r = -1) ∧ osB = osA ∧
        retA = .int .i32 (BitVec.ofInt 32 r.toInt) ∧ Libc.writeErrno mA osA e = some mB := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case close_ok _ r e hr herr =>
      intro _ _
      exact ⟨r, e, hr, rfl, rfl, herr⟩
    close_ext_mismatch
  exact h hok rfl rfl

def closeSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "close" = none)
    (hext : ∀ args m os out, ext "close" args m os out ↔ Libc.ExtStep "close" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "close" "close" [.int .i32] (.int .i32) false
    ClosePre ClosePost hnfn hext
    (fun {_ m os _} bs _ habs hagree _ _ ⟨herr, hfd⟩ => by
      obtain ⟨eblk, he, hp, hk, hs⟩ := herr
      have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [he] at hn; cases hn
      exact ⟨⟨eblk, (hagree os.errnoBlk henot).trans he, hp, hk, hs⟩, hfd⟩)
    (fun bs _ habs hagree _ _ ⟨herr_pre, _⟩ ⟨herr, _⟩ =>
      ErrnoOnlyPost.post_stack herr_pre bs habs hagree herr)
    (fun bs hnb habs hagree _ _ _ ⟨herr, hret⟩ =>
      ⟨ErrnoOnlyPost.post_drop bs hnb habs hagree herr, hret⟩)
    (fun m os args hpre => by
      rcases hpre with ⟨herr, fd, rfl⟩
      obtain ⟨m0', hm0'⟩ := herr.writeErrno_some 0
      refine ⟨⟨.int .i32 (BitVec.ofInt 32 (0 : Int32).toInt), m0', os,
          Libc.ExtOk.close_ok fd 0 0 m m0' os (.inl rfl) hm0'⟩, fun ret m' os' hok => ?_⟩
      obtain ⟨r, e, hr, rfl, rfl, herr'⟩ := extOk_close_inv hok
      exact ⟨ErrnoOnlyPost.of_writeErrno herr', r, hr, rfl⟩)

/-! ## 12. `fcntl` (`variadic := true`) -/

def FcntlPre (m : Mem) (os : OSState) (args : List Val) : Prop :=
  ValidErrno m os ∧ ∃ (fd cmd : BitVec 32) (rest : List Val), args = .int .i32 fd :: .int .i32 cmd :: rest

def FcntlPost (m : Mem) (os : OSState) (_ : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  ErrnoOnlyPost m os m' os' ∧ ∃ ret : Int32, rv = .int .i32 (BitVec.ofInt 32 ret.toInt)

private theorem extOk_fcntl_inv {fd cmd : BitVec 32} {rest : List Val}
    {m : Mem} {os : OSState} {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "fcntl" (.int .i32 fd :: .int .i32 cmd :: rest) m os ret m' os') :
    ∃ r e : Int32, os' = os ∧
      ret = .int .i32 (BitVec.ofInt 32 r.toInt) ∧ Libc.writeErrno m os e = some m' := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "fcntl" → args = .int .i32 fd :: .int .i32 cmd :: rest →
      ∃ r e : Int32, osB = osA ∧
        retA = .int .i32 (BitVec.ofInt 32 r.toInt) ∧ Libc.writeErrno mA osA e = some mB := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case fcntl_ok _ _ _ r e herr =>
      intro _ _
      exact ⟨r, e, rfl, rfl, herr⟩
    close_ext_mismatch
  exact h hok rfl rfl

def fcntlSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "fcntl" = none)
    (hext : ∀ args m os out, ext "fcntl" args m os out ↔ Libc.ExtStep "fcntl" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "fcntl" "fcntl" [.int .i32, .int .i32] (.int .i32) true
    FcntlPre FcntlPost hnfn hext
    (fun {_ m os _} bs _ habs hagree _ _ ⟨herr, hargs⟩ => by
      obtain ⟨eblk, he, hp, hk, hs⟩ := herr
      have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [he] at hn; cases hn
      exact ⟨⟨eblk, (hagree os.errnoBlk henot).trans he, hp, hk, hs⟩, hargs⟩)
    (fun bs _ habs hagree _ _ ⟨herr_pre, _⟩ ⟨herr, _⟩ =>
      ErrnoOnlyPost.post_stack herr_pre bs habs hagree herr)
    (fun bs hnb habs hagree _ _ _ ⟨herr, hret⟩ =>
      ⟨ErrnoOnlyPost.post_drop bs hnb habs hagree herr, hret⟩)
    (fun m os args hpre => by
      rcases hpre with ⟨herr, fd, cmd, rest, rfl⟩
      obtain ⟨m0', hm0'⟩ := herr.writeErrno_some 0
      refine ⟨⟨.int .i32 (BitVec.ofInt 32 (0 : Int32).toInt), m0', os,
          Libc.ExtOk.fcntl_ok fd cmd rest 0 0 m m0' os hm0'⟩, fun ret m' os' hok => ?_⟩
      obtain ⟨r, e, rfl, rfl, herr'⟩ := extOk_fcntl_inv hok
      exact ⟨ErrnoOnlyPost.of_writeErrno herr', r, rfl⟩)

/-! ## 13. `lseek`, `lseek64`, and Generic Alias Constructor -/

def LseekPre (m : Mem) (os : OSState) (args : List Val) : Prop :=
  ValidErrno m os ∧
  ∃ (fd : BitVec 32) (off : BitVec 64) (whence : BitVec 32),
    args = [.int .i32 fd, .int .i64 off, .int .i32 whence]

def LseekPost (m : Mem) (os : OSState) (_ : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  ErrnoOnlyPost m os m' os' ∧ ∃ ret : Int64, rv = .int .i64 (BitVec.ofInt 64 ret.toInt)

private theorem extOk_lseek_inv {targetSym : String} (htgt : targetSym = "lseek" ∨ targetSym = "lseek64")
    {fd : BitVec 32} {off : BitVec 64} {whence : BitVec 32}
    {m : Mem} {os : OSState} {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk targetSym [.int .i32 fd, .int .i64 off, .int .i32 whence] m os ret m' os') :
    ∃ (r : Int64) (e : Int32), os' = os ∧
      ret = .int .i64 (BitVec.ofInt 64 r.toInt) ∧ Libc.writeErrno m os e = some m' := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      (fn = "lseek" ∨ fn = "lseek64") → args = [.int .i32 fd, .int .i64 off, .int .i32 whence] →
      ∃ (r : Int64) (e : Int32), osB = osA ∧
        retA = .int .i64 (BitVec.ofInt 64 r.toInt) ∧ Libc.writeErrno mA osA e = some mB := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case lseek_ok =>
      intro _ _
      exact ⟨_, _, rfl, rfl, ‹Libc.writeErrno _ _ _ = some _›⟩
    all_goals
      intro hfn _
      first
      | exact False.elim (or_str_disj_absurd hfn ‹_ = "snprintf" ∨ _ = "vsnprintf"›
          (by decide) (by decide) (by decide) (by decide))
      | exact False.elim (str_disj_lit_absurd hfn (by decide) (by decide))
  exact h hok htgt rfl

/-- Generic `lseek` / `lseek64` / symbol-alias specification builder. -/
def lseekAliasSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (sym targetSym : String) (htgt : targetSym = "lseek" ∨ targetSym = "lseek64")
    (hnfn : prog.fns sym = none)
    (hext : ∀ args m os out, ext sym args m os out ↔ Libc.ExtStep targetSym args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext sym targetSym [.int .i32, .int .i64, .int .i32] (.int .i64) false
    LseekPre LseekPost hnfn hext
    (fun {_ m os _} bs _ habs hagree _ _ ⟨herr, hargs⟩ => by
      obtain ⟨eblk, he, hp, hk, hs⟩ := herr
      have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [he] at hn; cases hn
      exact ⟨⟨eblk, (hagree os.errnoBlk henot).trans he, hp, hk, hs⟩, hargs⟩)
    (fun bs _ habs hagree _ _ ⟨herr_pre, _⟩ ⟨herr, _⟩ =>
      ErrnoOnlyPost.post_stack herr_pre bs habs hagree herr)
    (fun bs hnb habs hagree _ _ _ ⟨herr, hret⟩ =>
      ⟨ErrnoOnlyPost.post_drop bs hnb habs hagree herr, hret⟩)
    (fun m os args hpre => by
      rcases hpre with ⟨herr, fd, off, whence, rfl⟩
      obtain ⟨m0', hm0'⟩ := herr.writeErrno_some 0
      refine ⟨⟨.int .i64 (BitVec.ofInt 64 (0 : Int64).toInt), m0', os,
          Libc.ExtOk.lseek_ok targetSym htgt fd off whence 0 0 m m0' os hm0'⟩,
        fun ret m' os' hok => ?_⟩
      obtain ⟨r, e, rfl, rfl, herr'⟩ := extOk_lseek_inv htgt hok
      exact ⟨ErrnoOnlyPost.of_writeErrno herr', r, rfl⟩)

def lseekSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "lseek" = none)
    (hext : ∀ args m os out, ext "lseek" args m os out ↔ Libc.ExtStep "lseek" args m os out) :
    CallSpec prog cfg ext :=
  lseekAliasSpec "lseek" "lseek" (.inl rfl) hnfn hext

def lseek64Spec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "lseek64" = none)
    (hext : ∀ args m os out, ext "lseek64" args m os out ↔ Libc.ExtStep "lseek64" args m os out) :
    CallSpec prog cfg ext :=
  lseekAliasSpec "lseek64" "lseek64" (.inr rfl) hnfn hext

/-! ## 14. `read` (`CallSafeSpec`) -/

def ReadPre (m : Mem) (os : OSState) (args : List Val) : Prop :=
  ValidErrno m os ∧
  ∃ (fd : BitVec 32) (b : BlockId) (off : Int64) (cnt : BitVec 64),
    args = [.int .i32 fd, .ptr b off, .int .u64 cnt] ∧
    Libc.validWritableRange m b off cnt.toNat = true

def ReadPost (m : Mem) (os : OSState) (args : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  m.nextBlock ≤ m'.nextBlock ∧
  os'.errnoBlk = os.errnoBlk ∧ os'.strerrorBlk = os.strerrorBlk ∧
  ∃ (fd : BitVec 32) (b : BlockId) (off : Int64) (cnt : BitVec 64),
    args = [.int .i32 fd, .ptr b off, .int .u64 cnt] ∧
    (∀ x, x ≠ b → x ≠ os.errnoBlk → m'.blocks x = m.blocks x) ∧
    (∀ eblk, m.blocks os.errnoBlk = some eblk →
      ∃ (eblk' : Block) (e : Int32), m'.blocks os.errnoBlk = some eblk' ∧ BlockMetaEq eblk eblk' ∧
        (∀ i < 4, eblk'.bytes i = (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt))[i]?.getD .undef)) ∧
    (b ≠ os.errnoBlk → ∀ eblk, m.blocks os.errnoBlk = some eblk →
      ∃ (eblk' : Block) (e : Int32), m'.blocks os.errnoBlk = some eblk' ∧
        BlockWrittenAt eblk eblk' 0 (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt))) ∧
    ((rv = .int .i64 (BitVec.ofInt 64 (-1)) ∧
      os'.readBudget = os.readBudget ∧
      (b ≠ os.errnoBlk → ∀ blk, m.blocks b = some blk → m'.blocks b = some blk)) ∨
     (∃ (k : Nat) (bs : List UInt8),
       k ≤ min cnt.toNat (2 ^ 63 - 1) ∧
       bs.length = k ∧
       (∀ rem, os.readBudget = some rem → k ≤ rem) ∧
       rv = .int .i64 (BitVec.ofNat 64 k) ∧
       os'.readBudget = os.readBudget.map (· - k) ∧
       (b ≠ os.errnoBlk → ∀ blk, m.blocks b = some blk →
         ∃ blk', m'.blocks b = some blk' ∧ BlockWrittenAt blk blk' off (bs.map MemByte.byte))))

theorem ReadPost.readBudget_isSome {m m' : Mem} {os os' : OSState} {args : List Val} {rv : Val}
    (hp : ReadPost m os args rv m' os') (hbud : os.readBudget.isSome = true) :
    os'.readBudget.isSome = true := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, hres⟩
  rcases hres with ⟨_, hrb, _⟩ | ⟨k, _, _, _, _, _, hrb, _⟩
  · rwa [hrb]
  · cases ho : os.readBudget with
    | none => simp [ho] at hbud
    | some rem => simp [hrb, ho]

private theorem extOk_read_inv {fd : BitVec 32} {b : BlockId} {off : Int64} {cnt : BitVec 64}
    {m : Mem} {os : OSState} {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "read" [.int .i32 fd, .ptr b off, .int .u64 cnt] m os ret m' os') :
    (∃ (cnt0 : Nat) (e : Int32),
      BitVec.ofNat 64 cnt0 = cnt ∧ ret = .int .i64 (BitVec.ofInt 64 (-1)) ∧ os' = os ∧
      Libc.validWritableRange m b off cnt0 = true ∧ Libc.writeErrno m os e = some m') ∨
    (∃ (cnt0 k : Nat) (bs : List UInt8) (e : Int32) (m1 : Mem),
      BitVec.ofNat 64 cnt0 = cnt ∧
      Libc.validWritableRange m b off cnt0 = true ∧
      k ≤ min cnt0 (2 ^ 63 - 1) ∧ bs.length = k ∧
      (∀ rem, os.readBudget = some rem → k ≤ rem) ∧
      m.writeBytes b off (bs.map MemByte.byte) = some m1 ∧
      Libc.writeErrno m1 os e = some m' ∧
      ret = .int .i64 (BitVec.ofNat 64 k) ∧
      os' = { os with readBudget := os.readBudget.map (· - k) }) := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "read" → args = [.int .i32 fd, .ptr b off, .int .u64 cnt] →
      (∃ (cnt0 : Nat) (e : Int32),
        BitVec.ofNat 64 cnt0 = cnt ∧ retA = .int .i64 (BitVec.ofInt 64 (-1)) ∧ osB = osA ∧
        Libc.validWritableRange mA b off cnt0 = true ∧ Libc.writeErrno mA osA e = some mB) ∨
      (∃ (cnt0 k : Nat) (bs : List UInt8) (e : Int32) (m1 : Mem),
        BitVec.ofNat 64 cnt0 = cnt ∧
        Libc.validWritableRange mA b off cnt0 = true ∧
        k ≤ min cnt0 (2 ^ 63 - 1) ∧ bs.length = k ∧
        (∀ rem, osA.readBudget = some rem → k ≤ rem) ∧
        mA.writeBytes b off (bs.map MemByte.byte) = some m1 ∧
        Libc.writeErrno m1 osA e = some mB ∧
        retA = .int .i64 (BitVec.ofNat 64 k) ∧
        osB = { osA with readBudget := osA.readBudget.map (· - k) }) := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case read_fail _ b' off' cnt0 e hbuf herr =>
      intro _ hargs
      injection hargs with _ h12
      injection h12 with h1 h23
      injection h1 with hb hoff
      injection h23 with h2
      injection h2 with _ hcnt
      subst hb hoff
      exact .inl ⟨cnt0, e, hcnt, rfl, rfl, hbuf, herr⟩
    case read_ok _ b' off' cnt0 k bs e m1 hk hlen hbuf hwr hbud herr =>
      intro _ hargs
      injection hargs with _ h12
      injection h12 with h1 h23
      injection h1 with hb hoff
      injection h23 with h2
      injection h2 with _ hcnt
      subst hb hoff
      exact .inr ⟨cnt0, k, bs, e, m1, hcnt, hbuf, hk, hlen,
        (fun rem hrem => by simpa [hrem] using hbud), hwr, herr, rfl, rfl⟩
    close_ext_mismatch
  exact h hok rfl rfl

def readSafeSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "read" = none)
    (hext : ∀ args m os out, ext "read" args m os out ↔ Libc.ExtStep "read" args m os out) :
    CallSafeSpec prog cfg ext :=
  CallSafeSpec.of_ext "read" "read" [.int .i32, .ptr .void, .int .u64] (.int .i64) false
    ReadPre ReadPost hnfn hext
    (fun {_ m os _} bs _ habs hagree _ _ hpre => by
      rcases hpre with ⟨herr, fd, b, off, cnt, rfl, hbuf⟩
      obtain ⟨eblk, he, hp, hk, hs⟩ := herr
      obtain ⟨_, hb, _, _⟩ := validWritableRange_iff.mp hbuf
      have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [he] at hn; cases hn
      have hbnot : b ∉ bs := fun hm => by have hn := habs _ hm; rw [hb] at hn; cases hn
      exact ⟨⟨eblk, (hagree os.errnoBlk henot).trans he, hp, hk, hs⟩,
        fd, b, off, cnt, rfl, validWritableRange_of_blocks_eq (hagree b hbnot) hbuf⟩)
    (fun {_ m m' os _ _ _} bs _ habs hagree _ _ ⟨herr_pre, fd0, b0, off0, cnt0, hargs0, hbuf0⟩
        ⟨hle, _, _, fd, b, off, cnt, hargs, hother, _, _, hres⟩ => by
      rw [hargs] at hargs0
      injection hargs0 with _ h12
      injection h12 with h1 _
      injection h1 with hb_eq _
      obtain ⟨eblk0, he0, _, hk_e0, _⟩ := herr_pre
      obtain ⟨_, hb0, _, _⟩ := validWritableRange_iff.mp (hb_eq ▸ hbuf0)
      have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [he0] at hn; cases hn
      have hbnot : b ∉ bs := fun hm => by have hn := habs _ hm; rw [hb0] at hn; cases hn
      have hm_e : m.blocks os.errnoBlk = some eblk0 := (hagree os.errnoBlk henot).trans he0
      refine ⟨hle, ?_, ?_⟩
      · intro x hx blk hbm _
        have hxe : x ≠ os.errnoBlk := fun heq => henot (heq ▸ hx)
        have hxb : x ≠ b := fun heq => hbnot (heq ▸ hx)
        rw [hother x hxb hxe, hbm]
      · intro x blk hbm hstk
        by_cases hxe : x = os.errnoBlk
        · subst hxe
          rw [hm_e] at hbm; cases hbm
          exact False.elim (hk_e0 hstk)
        · by_cases hxb : x = b
          · subst hxb
            rcases hres with ⟨_, _, hsame⟩ | ⟨_, _, _, _, _, _, _, hwr⟩
            · exact ⟨blk, hsame hxe blk hbm, hstk⟩
            · obtain ⟨blk', hbm', hwa⟩ := hwr hxe blk hbm
              exact ⟨blk', hbm', hwa.1.2.2.2.1 ▸ hstk⟩
          · rw [hother x hxb hxe]
            exact ⟨blk, hbm, hstk⟩)
    (fun {m_clean m m_after os os' args rv} bs hnb habs hagree _ _ _
        ⟨hle, hos_e, hos_s, fd, b, off, cnt, hargs, hother, herr_meta, herr_wr, hres⟩ => by
      refine ⟨by rw [dropBlks_nextBlock]; exact Nat.le_trans hnb hle, hos_e, hos_s,
        fd, b, off, cnt, hargs, ?_, ?_, ?_, ?_⟩
      · intro x hxb hxe
        by_cases hmem : x ∈ bs
        · rw [dropBlks_blocks_mem _ _ hmem, habs x hmem]
        · rw [dropBlks_blocks_not_mem _ _ hmem, hother x hxb hxe, hagree x hmem]
      · intro eblk hce
        have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [hce] at hn; cases hn
        obtain ⟨eblk', e, hae, hmeta, hbytes⟩ := herr_meta eblk ((hagree os.errnoBlk henot).trans hce)
        exact ⟨eblk', e, by rw [dropBlks_blocks_not_mem _ _ henot]; exact hae, hmeta, hbytes⟩
      · intro hne eblk hce
        have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [hce] at hn; cases hn
        obtain ⟨eblk', e, hae, hwa⟩ := herr_wr hne eblk ((hagree os.errnoBlk henot).trans hce)
        exact ⟨eblk', e, by rw [dropBlks_blocks_not_mem _ _ henot]; exact hae, hwa⟩
      · rcases hres with ⟨hrv, hrb, hsame⟩ | ⟨k, bs0, hk, hlen, hbud, hrv, hrb, hwr⟩
        · exact .inl ⟨hrv, hrb, fun hne blk hcb => by
            have hbnot : b ∉ bs := fun hm => by have hn := habs _ hm; rw [hcb] at hn; cases hn
            rw [dropBlks_blocks_not_mem _ _ hbnot]
            exact hsame hne blk ((hagree b hbnot).trans hcb)⟩
        · exact .inr ⟨k, bs0, hk, hlen, hbud, hrv, hrb, fun hne blk hcb => by
            have hbnot : b ∉ bs := fun hm => by have hn := habs _ hm; rw [hcb] at hn; cases hn
            obtain ⟨blk', hba, hwa⟩ := hwr hne blk ((hagree b hbnot).trans hcb)
            exact ⟨blk', by rw [dropBlks_blocks_not_mem _ _ hbnot]; exact hba, hwa⟩⟩)
    (fun m os args hpre => by
      rcases hpre with ⟨herr, fd, b, off, cnt, rfl, hbuf⟩
      obtain ⟨m0', hm0'⟩ := herr.writeErrno_some 0
      refine ⟨⟨.int .i64 (BitVec.ofInt 64 (-1)), m0', os, ?_⟩, fun ret m' os' hok => ?_⟩
      · simpa using Libc.ExtOk.read_fail fd b off cnt.toNat 0 m m0' os hbuf hm0'
      · rcases extOk_read_inv hok with
            ⟨cnt0, e, _, rfl, rfl, _, herr'⟩ |
            ⟨cnt0, k, bs0, e, m1, hcnt, hbuf', hk, hlen, hbud, hwr, herr', rfl, rfl⟩
        · obtain ⟨hnext, hne_e, _, eblk0, eblk', hb_e0, _, _, hbe_e, hwa_e⟩ := writeBytes_spec herr'
          refine ⟨by rw [hnext]; exact Nat.le_refl _, rfl, rfl, fd, b, off, cnt, rfl, ?_, ?_, ?_, .inl ⟨rfl, rfl, ?_⟩⟩
          · intro x _ hxe
            exact hne_e x hxe
          · intro eblk hbe
            rw [hb_e0] at hbe; cases hbe
            refine ⟨eblk', e, hbe_e, hwa_e.metaEq, fun i hi => ?_⟩
            have hbw := hwa_e.2 i
            have hcond : (0 : Int64).toInt.toNat ≤ i ∧
                i < (0 : Int64).toInt.toNat + (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt)).length := by
              change 0 ≤ i ∧ i < 0 + 4; omega
            simp only [hcond, and_self, ↓reduceIte] at hbw
            exact hbw
          · intro _ eblk hbe
            rw [hb_e0] at hbe; cases hbe
            exact ⟨eblk', e, hbe_e, hwa_e⟩
          · intro hne blk hb
            exact (hne_e b hne).trans hb
        · have hcnt0 : cnt.toNat = cnt0 := bitVec64_toNat_of_lt hcnt (validWritableRange_lt hbuf')
          obtain ⟨hnext1, hne1, _, blk0, blk1, hb0, _, _, hbe1, hwa1⟩ := writeBytes_spec hwr
          obtain ⟨hnext2, hne2, _, eblk1, eblk2, hb_e1, _, _, hbe_e2, hwa_e2⟩ := writeBytes_spec herr'
          refine ⟨by rw [hnext2, hnext1]; exact Nat.le_refl _, rfl, rfl, fd, b, off, cnt, rfl,
            ?_, ?_, ?_, .inr ⟨k, bs0, hcnt0 ▸ hk, hlen, hbud, rfl, rfl, ?_⟩⟩
          · intro x hxb hxe
            rw [hne2 x hxe, hne1 x hxb]
          · intro eblk hbe
            by_cases hbe_eq : b = os.errnoBlk
            · subst hbe_eq
              rw [hb0] at hbe; cases hbe
              rw [hbe1] at hb_e1; cases hb_e1
              refine ⟨eblk2, e, hbe_e2, hwa1.metaEq.trans hwa_e2.metaEq, fun i hi => ?_⟩
              have hbw := hwa_e2.2 i
              have hcond : (0 : Int64).toInt.toNat ≤ i ∧
                  i < (0 : Int64).toInt.toNat + (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt)).length := by
                change 0 ≤ i ∧ i < 0 + 4; omega
              simp only [hcond, and_self, ↓reduceIte] at hbw
              exact hbw
            · have hm1_e : m1.blocks os.errnoBlk = some eblk := (hne1 os.errnoBlk (Ne.symm hbe_eq)).trans hbe
              rw [hm1_e] at hb_e1; cases hb_e1
              refine ⟨eblk2, e, hbe_e2, hwa_e2.metaEq, fun i hi => ?_⟩
              have hbw := hwa_e2.2 i
              have hcond : (0 : Int64).toInt.toNat ≤ i ∧
                  i < (0 : Int64).toInt.toNat + (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt)).length := by
                change 0 ≤ i ∧ i < 0 + 4; omega
              simp only [hcond, and_self, ↓reduceIte] at hbw
              exact hbw
          · intro hne eblk hbe
            have hm1_e : m1.blocks os.errnoBlk = some eblk := (hne1 os.errnoBlk (Ne.symm hne)).trans hbe
            rw [hm1_e] at hb_e1; cases hb_e1
            exact ⟨eblk2, e, hbe_e2, hwa_e2⟩
          · intro hne blk hb
            rw [hb0] at hb; cases hb
            exact ⟨blk1, (hne2 b hne).trans hbe1, hwa1⟩)

/-! ## 15. `write` -/

def WritePre (m : Mem) (os : OSState) (args : List Val) : Prop :=
  ValidErrno m os ∧
  ∃ (fd : BitVec 32) (b : BlockId) (off : Int64) (cnt : BitVec 64),
    args = [.int .i32 fd, .ptr b off, .int .u64 cnt] ∧
    Libc.validReadableRange m b off cnt.toNat = true

def WritePost (m : Mem) (os : OSState) (args : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  ErrnoOnlyPost m os m' os' ∧
  ∃ (fd : BitVec 32) (b : BlockId) (off : Int64) (cnt : BitVec 64),
    args = [.int .i32 fd, .ptr b off, .int .u64 cnt] ∧
    (rv = .int .i64 (BitVec.ofInt 64 (-1)) ∨
     ∃ k : Nat,
       (cnt.toNat = 0 → k = 0) ∧
       (cnt.toNat > 0 → 1 ≤ k ∧ k ≤ min cnt.toNat (2 ^ 63 - 1)) ∧
       rv = .int .i64 (BitVec.ofNat 64 k))

private theorem extOk_write_inv {fd : BitVec 32} {b : BlockId} {off : Int64} {cnt : BitVec 64}
    {m : Mem} {os : OSState} {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "write" [.int .i32 fd, .ptr b off, .int .u64 cnt] m os ret m' os') :
    (∃ (cnt0 : Nat) (e : Int32),
      BitVec.ofNat 64 cnt0 = cnt ∧ ret = .int .i64 (BitVec.ofInt 64 (-1)) ∧ os' = os ∧
      Libc.validReadableRange m b off cnt0 = true ∧ Libc.writeErrno m os e = some m') ∨
    (∃ (cnt0 k : Nat) (e : Int32),
      BitVec.ofNat 64 cnt0 = cnt ∧
      Libc.validReadableRange m b off cnt0 = true ∧
      ((cnt0 = 0 → k = 0) ∧ (cnt0 > 0 → 1 ≤ k ∧ k ≤ min cnt0 (2 ^ 63 - 1))) ∧
      Libc.writeErrno m os e = some m' ∧
      ret = .int .i64 (BitVec.ofNat 64 k) ∧ os' = os) := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "write" → args = [.int .i32 fd, .ptr b off, .int .u64 cnt] →
      (∃ (cnt0 : Nat) (e : Int32),
        BitVec.ofNat 64 cnt0 = cnt ∧ retA = .int .i64 (BitVec.ofInt 64 (-1)) ∧ osB = osA ∧
        Libc.validReadableRange mA b off cnt0 = true ∧ Libc.writeErrno mA osA e = some mB) ∨
      (∃ (cnt0 k : Nat) (e : Int32),
        BitVec.ofNat 64 cnt0 = cnt ∧
        Libc.validReadableRange mA b off cnt0 = true ∧
        ((cnt0 = 0 → k = 0) ∧ (cnt0 > 0 → 1 ≤ k ∧ k ≤ min cnt0 (2 ^ 63 - 1))) ∧
        Libc.writeErrno mA osA e = some mB ∧
        retA = .int .i64 (BitVec.ofNat 64 k) ∧ osB = osA) := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case write_fail _ b' off' cnt0 e hbuf herr =>
      intro _ hargs
      injection hargs with _ h12
      injection h12 with h1 h23
      injection h1 with hb hoff
      injection h23 with h2
      injection h2 with _ hcnt
      subst hb hoff
      exact .inl ⟨cnt0, e, hcnt, rfl, rfl, hbuf, herr⟩
    case write_ok =>
      intro _ hargs
      injection hargs with _ h12
      injection h12 with h1 h23
      injection h1 with hb hoff
      injection h23 with h2
      injection h2 with _ hcnt
      subst hb hoff
      exact .inr ⟨_, _, _, hcnt,
        ‹Libc.validReadableRange _ _ _ _ = true›,
        ‹(_ = 0 → _ = 0) ∧ (_ > 0 → _)›,
        ‹Libc.writeErrno _ _ _ = some _›,
        rfl, rfl⟩
    close_ext_mismatch
  exact h hok rfl rfl

def writeSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "write" = none)
    (hext : ∀ args m os out, ext "write" args m os out ↔ Libc.ExtStep "write" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "write" "write" [.int .i32, .ptr (.const_ .void), .int .u64] (.int .i64) false
    WritePre WritePost hnfn hext
    (fun {_ m os _} bs _ habs hagree _ _ hpre => by
      rcases hpre with ⟨herr, fd, b, off, cnt, rfl, hbuf⟩
      obtain ⟨eblk, he, hp, hk, hs⟩ := herr
      obtain ⟨_, hb, _⟩ := validReadableRange_iff.mp hbuf
      have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [he] at hn; cases hn
      have hbnot : b ∉ bs := fun hm => by have hn := habs _ hm; rw [hb] at hn; cases hn
      exact ⟨⟨eblk, (hagree os.errnoBlk henot).trans he, hp, hk, hs⟩,
        fd, b, off, cnt, rfl, validReadableRange_of_blocks_eq (hagree b hbnot) hbuf⟩)
    (fun bs _ habs hagree _ _ ⟨herr_pre, _⟩ ⟨herr, _⟩ =>
      ErrnoOnlyPost.post_stack herr_pre bs habs hagree herr)
    (fun bs hnb habs hagree _ _ _ ⟨herr, hres⟩ =>
      ⟨ErrnoOnlyPost.post_drop bs hnb habs hagree herr, hres⟩)
    (fun m os args hpre => by
      rcases hpre with ⟨herr, fd, b, off, cnt, rfl, hbuf⟩
      obtain ⟨m0', hm0'⟩ := herr.writeErrno_some 0
      refine ⟨⟨.int .i64 (BitVec.ofInt 64 (-1)), m0', os, ?_⟩, fun ret m' os' hok => ?_⟩
      · simpa using Libc.ExtOk.write_fail fd b off cnt.toNat 0 m m0' os hbuf hm0'
      · rcases extOk_write_inv hok with
            ⟨_, _, _, rfl, rfl, _, herr'⟩ | ⟨cnt0, k, _, hcnt, hbuf', hk, herr', rfl, rfl⟩
        · exact ⟨ErrnoOnlyPost.of_writeErrno herr', fd, b, off, cnt, rfl, .inl rfl⟩
        · have hcnt0 : cnt.toNat = cnt0 := bitVec64_toNat_of_lt hcnt (validReadableRange_lt hbuf')
          exact ⟨ErrnoOnlyPost.of_writeErrno herr', fd, b, off, cnt, rfl,
            .inr ⟨k, hcnt0 ▸ hk.1, hcnt0 ▸ hk.2, rfl⟩⟩)

/-! ## 16. `strerror` -/

def StrerrorPre (m : Mem) (os : OSState) (args : List Val) : Prop :=
  (∃ ev : BitVec 32, args = [.int .i32 ev]) ∧
  (∀ old, os.strerrorBlk = some old → ∃ sblk, m.blocks old = some sblk ∧ sblk.kind ≠ .stack)

def StrerrorPost (m : Mem) (os : OSState) (_ : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  m.nextBlock ≤ m'.nextBlock ∧
  ∃ (bid : BlockId) (blk : Block) (bs : List UInt8),
    rv = .ptr bid 0 ∧
    os' = { os with strerrorBlk := some bid } ∧
    m.nextBlock ≤ bid ∧ bid < m'.nextBlock ∧
    m.blocks bid = none ∧ m'.blocks bid = some blk ∧
    blk.size = bs.length + 1 ∧ blk.align = 1 ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    (0 : UInt8) ∉ bs ∧
    (∀ i, blk.bytes i = .byte (if i < bs.length then bs[i]?.getD 0 else 0)) ∧
    m'.strlenAt bid 0 = some bs.length ∧
    (∀ old, os.strerrorBlk = some old → m'.blocks old = none) ∧
    (∀ b, b ≠ bid → (∀ old, os.strerrorBlk = some old → b ≠ old) → m'.blocks b = m.blocks b)

private theorem extOk_strerror_inv {ev : BitVec 32} {m : Mem} {os : OSState}
    {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk "strerror" [.int .i32 ev] m os ret m' os') :
    ∃ (n0 : Nat) (bs0 : List UInt8) (base : UInt64) (hsz : n0 + 1 < ptrDiffLimit) (bid : BlockId),
      bs0.length = n0 ∧ (0 : UInt8) ∉ bs0 ∧ ret = .ptr bid 0 ∧
      os' = { os with strerrorBlk := some bid } ∧
      (match os.strerrorBlk with | some old => m.dropBlock old | none => m).alloc
        (n0 + 1) 1 .ro .global base (fun i => .byte (if i < n0 then bs0[i]?.getD 0 else 0))
        hsz (by decide) (Nat.mod_one _) = (bid, m') := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "strerror" → args = [.int .i32 ev] →
      ∃ (n0 : Nat) (bs0 : List UInt8) (base : UInt64) (hsz : n0 + 1 < ptrDiffLimit) (bid : BlockId),
        bs0.length = n0 ∧ (0 : UInt8) ∉ bs0 ∧ retA = .ptr bid 0 ∧
        osB = { osA with strerrorBlk := some bid } ∧
        (match osA.strerrorBlk with | some old => mA.dropBlock old | none => mA).alloc
          (n0 + 1) 1 .ro .global base (fun i => .byte (if i < n0 then bs0[i]?.getD 0 else 0))
          hsz (by decide) (Nat.mod_one _) = (bid, mB) := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case strerror_ok _ n0 bs0 base hsz bid hlen hnonnul halloc =>
      intro _ _
      exact ⟨n0, bs0, base, hsz, bid, hlen, hnonnul, rfl, rfl, halloc⟩
    close_ext_mismatch
  exact h hok rfl rfl

def strerrorSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "strerror" = none)
    (hext : ∀ args m os out, ext "strerror" args m os out ↔ Libc.ExtStep "strerror" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "strerror" "strerror" [.int .i32] (.ptr (.int .i8)) false
    StrerrorPre StrerrorPost hnfn hext
    (fun {_ m _ _} bs _ habs hagree _ _ ⟨hargs, hold⟩ => by
      refine ⟨hargs, fun old hsome => ?_⟩
      obtain ⟨sblk, hbc, hk⟩ := hold old hsome
      have hnot : old ∉ bs := fun hm => by have hn := habs _ hm; rw [hbc] at hn; cases hn
      exact ⟨sblk, (hagree old hnot).trans hbc, hk⟩)
    (fun {_ m m' os _ _ _} bs _ habs hagree _ _ ⟨_, hold_pre⟩
        ⟨hle, bid, blk, bytes, _, _, _, _, hnone, _, _, _, _, _, _, _, _, _, hother⟩ => by
      refine ⟨hle, ?_, ?_⟩
      · intro b hb blk0 hbm _
        have hne_bid : b ≠ bid := fun heq => by rw [heq, hnone] at hbm; cases hbm
        have hne_old : ∀ old, os.strerrorBlk = some old → b ≠ old := fun old hold heq => by
          obtain ⟨sblk, hbc, _⟩ := hold_pre old hold
          have hn := habs b hb
          rw [heq, hbc] at hn
          cases hn
        rw [hother b hne_bid hne_old, hbm]
      · intro b blk0 hbm hstk
        have hne_bid : b ≠ bid := fun heq => by rw [heq, hnone] at hbm; cases hbm
        have hne_old : ∀ old, os.strerrorBlk = some old → b ≠ old := fun old hold heq => by
          obtain ⟨sblk, hbc, hk_old⟩ := hold_pre old hold
          have hnot : old ∉ bs := fun hm => by have hn := habs _ hm; rw [hbc] at hn; cases hn
          have hm_old : m.blocks old = some sblk := (hagree old hnot).trans hbc
          rw [heq, hm_old] at hbm
          cases hbm
          exact hk_old hstk
        rw [hother b hne_bid hne_old]
        exact ⟨blk0, hbm, hstk⟩)
    (fun {m_clean m m_after os os' args rv} bs hnb habs hagree hlt _ _
        ⟨hle, bid, blk, bytes, hrv, hos, hbid_ge, hbid_lt, _, hmb, hsz, hal, hp, hk, hnn, hby, _, hdrop_old, hother⟩ => by
      have hnot_bid : bid ∉ bs := fun hm => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt bid hm) hbid_ge)
      have hclean_ge : m_clean.nextBlock ≤ bid := Nat.le_trans hnb hbid_ge
      have hd_bid : (dropBlks m_after bs).blocks bid = some blk := by
        rw [dropBlks_blocks_not_mem _ _ hnot_bid]; exact hmb
      refine ⟨by rw [dropBlks_nextBlock]; exact Nat.le_trans hnb hle, bid, blk, bytes, hrv, hos,
        hclean_ge, by rw [dropBlks_nextBlock]; exact hbid_lt, m_clean.fresh bid hclean_ge, hd_bid,
        hsz, hal, hp, hk, hnn, hby, ?_, ?_, ?_⟩
      · exact strlenAt_of_nonnul_bytes hd_bid hsz hby hnn
      · intro old hold
        by_cases hmem : old ∈ bs
        · exact dropBlks_blocks_mem _ _ hmem
        · rw [dropBlks_blocks_not_mem _ _ hmem, hdrop_old old hold]
      · intro b hne_bid hne_old
        by_cases hmem : b ∈ bs
        · rw [dropBlks_blocks_mem _ _ hmem, habs b hmem]
        · rw [dropBlks_blocks_not_mem _ _ hmem, hother b hne_bid hne_old, hagree b hmem])
    (fun m os args hpre => by
      rcases hpre with ⟨⟨ev, rfl⟩, hold⟩
      let mBase := match os.strerrorBlk with | some old => m.dropBlock old | none => m
      obtain ⟨res1, res2, halloc0⟩ : ∃ res1 res2, mBase.alloc 1 1 .ro .global 0
          (fun i => .byte (if i < 0 then ([] : List UInt8)[i]?.getD 0 else 0))
          (by decide) (by decide) (Nat.mod_one _) = (res1, res2) := by
        cases h0 : mBase.alloc 1 1 .ro .global 0
            (fun i => .byte (if i < 0 then ([] : List UInt8)[i]?.getD 0 else 0))
            (by decide) (by decide) (Nat.mod_one _)
        exact ⟨_, _, rfl⟩
      refine ⟨⟨.ptr res1 0, res2, { os with strerrorBlk := some res1 },
          Libc.ExtOk.strerror_ok ev 0 [] 0 (by decide) m res2 res1 os rfl (by decide) halloc0⟩,
        fun ret m' os' hok => ?_⟩
      obtain ⟨n0, bs0, base, hsz, bid', hlen, hnonnul, rfl, rfl, halloc⟩ := extOk_strerror_inv hok
      let mBase' := match os.strerrorBlk with | some old => m.dropBlock old | none => m
      have hbase_next : mBase'.nextBlock = m.nextBlock := by
        dsimp [mBase']
        cases os.strerrorBlk <;> rfl
      have hbid : bid' = m.nextBlock := by
        have := (congrArg Prod.fst halloc).symm
        change _ = (mBase'.alloc _ _ _ _ _ _ _ _ _).1 at this
        simpa [alloc_fst, hbase_next] using this
      have hm' : m' = (mBase'.alloc (n0 + 1) 1 .ro .global base
          (fun i => .byte (if i < n0 then bs0[i]?.getD 0 else 0)) hsz (by decide) (Nat.mod_one _)).2 :=
        (congrArg Prod.snd halloc).symm
      subst hbid hm'
      let blk : Block := ⟨n0 + 1, 1, .ro, .global, base,
        fun i => .byte (if i < n0 then bs0[i]?.getD 0 else 0), hsz, by decide, Nat.mod_one _⟩
      have hbm' : (mBase'.alloc (n0 + 1) 1 .ro .global base
          (fun i => .byte (if i < n0 then bs0[i]?.getD 0 else 0)) hsz (by decide) (Nat.mod_one _)).2.blocks m.nextBlock =
          some blk := by
        have h := alloc_blocks_eq mBase' (n0 + 1) 1 .ro .global base
          (fun i => .byte (if i < n0 then bs0[i]?.getD 0 else 0)) hsz (by decide) (Nat.mod_one _)
        simpa [hbase_next] using h
      have hstrlen : ((mBase'.alloc (n0 + 1) 1 .ro .global base
          (fun i => .byte (if i < n0 then bs0[i]?.getD 0 else 0)) hsz (by decide) (Nat.mod_one _)).2).strlenAt m.nextBlock 0 =
          some bs0.length := by
        apply strlenAt_of_nonnul_bytes hbm' (by simp [blk, hlen]) (fun i => by simp [blk, hlen]) hnonnul
      have hold_none : ∀ old, os.strerrorBlk = some old →
          (mBase'.alloc (n0 + 1) 1 .ro .global base
            (fun i => .byte (if i < n0 then bs0[i]?.getD 0 else 0)) hsz (by decide) (Nat.mod_one _)).2.blocks old = none := by
        intro old hold_eq
        obtain ⟨sblk, hmo, _⟩ := hold old hold_eq
        have hlt_old : old < m.nextBlock := lt_nextBlock_of_some hmo
        have hne_old : old ≠ m.nextBlock := Nat.ne_of_lt hlt_old
        rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (by simpa [hbase_next] using hne_old)]
        simp [mBase', hold_eq, Mem.dropBlock]
      have hother_eq : ∀ b, b ≠ m.nextBlock → (∀ old, os.strerrorBlk = some old → b ≠ old) →
          (mBase'.alloc (n0 + 1) 1 .ro .global base
            (fun i => .byte (if i < n0 then bs0[i]?.getD 0 else 0)) hsz (by decide) (Nat.mod_one _)).2.blocks b = m.blocks b := by
        intro b hne_bid hne_old
        rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (by simpa [hbase_next] using hne_bid)]
        cases hst : os.strerrorBlk with
        | none => simp [mBase', hst]
        | some old =>
          have hbo : b ≠ old := hne_old old hst
          simp [mBase', hst, Mem.dropBlock, hbo]
      exact ⟨by simp [alloc_snd_nextBlock, hbase_next], m.nextBlock, blk, bs0, rfl, rfl, Nat.le_refl _,
        by simp [alloc_snd_nextBlock, hbase_next], m.fresh m.nextBlock (Nat.le_refl _), hbm',
        by simp [blk, hlen], rfl, rfl, rfl, hnonnul, fun i => by simp [blk, hlen], hstrlen, hold_none, hother_eq⟩)

/-! ## 17 & 18. `snprintf` & `vsnprintf` -/

def PrintfPre (isV : Bool) (m : Mem) (os : OSState) (args : List Val) : Prop :=
  ValidErrno m os ∧
  ∃ (buf : Val) (sz : BitVec 64) (bf : BlockId) (of_ : Int64) (rest : List Val),
    args = buf :: .int .u64 sz :: .ptr bf of_ :: rest ∧
    (isV = true → ∃ rest', rest = .vaList true :: rest') ∧
    Libc.printfFmtOk m bf of_ ∧
    (sz.toNat = 0 ∨ ∃ (bb : BlockId) (ob : Int64),
      buf = .ptr bb ob ∧ Libc.validWritableRange m bb ob sz.toNat = true)

def PrintfPost (m : Mem) (os : OSState) (args : List Val)
    (rv : Val) (m' : Mem) (os' : OSState) : Prop :=
  m.nextBlock ≤ m'.nextBlock ∧
  os' = os ∧
  ∃ (buf : Val) (sz : BitVec 64) (bf : BlockId) (of_ : Int64) (rest : List Val) (ret : Int32),
    args = buf :: .int .u64 sz :: .ptr bf of_ :: rest ∧
    rv = .int .i32 (BitVec.ofInt 32 ret.toInt) ∧
    ((sz.toNat = 0 ∧ ErrnoOnlyPost m os m' os') ∨
     (sz.toNat > 0 ∧
      ∃ (bb : BlockId) (ob : Int64) (outBytes : List UInt8),
        buf = .ptr bb ob ∧
        outBytes.length = sz.toNat ∧
        (0 : UInt8) ∈ outBytes ∧
        (∀ x, x ≠ bb → x ≠ os.errnoBlk → m'.blocks x = m.blocks x) ∧
        (∀ eblk, m.blocks os.errnoBlk = some eblk →
          ∃ (eblk' : Block) (e : Int32), m'.blocks os.errnoBlk = some eblk' ∧ BlockMetaEq eblk eblk' ∧
            (∀ i < 4, eblk'.bytes i = (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt))[i]?.getD .undef)) ∧
        (bb ≠ os.errnoBlk → ∀ eblk, m.blocks os.errnoBlk = some eblk →
          ∃ (eblk' : Block) (e : Int32), m'.blocks os.errnoBlk = some eblk' ∧
            BlockWrittenAt eblk eblk' 0 (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt))) ∧
        (bb ≠ os.errnoBlk → ∀ blk, m.blocks bb = some blk →
          ∃ blk', m'.blocks bb = some blk' ∧
            BlockWrittenAt blk blk' ob (outBytes.map MemByte.byte) ∧
            (Mem.inBounds blk ob sz.toNat = true → ∃ slen < sz.toNat, m'.strlenAt bb ob = some slen))))

private theorem printfPre_mono (isV : Bool) {m_clean m : Mem} {os : OSState} {args : List Val}
    (bs : List BlockId) (habs : ∀ b ∈ bs, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (hpre : PrintfPre isV m_clean os args) :
    PrintfPre isV m os args := by
  rcases hpre with ⟨herr, buf, sz, bf, of_, rest, rfl, hva, hfmt, hbuf⟩
  obtain ⟨eblk, he, hp, hk, hs⟩ := herr
  have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [he] at hn; cases hn
  obtain ⟨flen, rawFmt, fmtBytes, hslen, hrf, hcf, hpn⟩ := hfmt
  obtain ⟨_, hbf, _, _, _⟩ := strlenAt_spec hslen
  have hbf_not : bf ∉ bs := fun hm => by have hn := habs _ hm; rw [hbf] at hn; cases hn
  have hfmt' : Libc.printfFmtOk m bf of_ :=
    printfFmtOk_of_blocks_eq (hagree bf hbf_not) ⟨flen, rawFmt, fmtBytes, hslen, hrf, hcf, hpn⟩
  refine ⟨⟨eblk, (hagree os.errnoBlk henot).trans he, hp, hk, hs⟩, buf, sz, bf, of_, rest, rfl, hva, hfmt', ?_⟩
  rcases hbuf with hz | ⟨bb, ob, rfl, hwr⟩
  · exact .inl hz
  · obtain ⟨_, hbb, _, _⟩ := validWritableRange_iff.mp hwr
    have hbb_not : bb ∉ bs := fun hm => by have hn := habs _ hm; rw [hbb] at hn; cases hn
    exact .inr ⟨bb, ob, rfl, validWritableRange_of_blocks_eq (hagree bb hbb_not) hwr⟩

private theorem printfPost_stack (isV : Bool) {m_clean m m' : Mem} {os os' : OSState}
    {args : List Val} {rv : Val} (bs : List BlockId)
    (habs : ∀ b ∈ bs, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (hpre : PrintfPre isV m_clean os args) (hpost : PrintfPost m os args rv m' os') :
    m.nextBlock ≤ m'.nextBlock ∧
    (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
    (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
      ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack) := by
  rcases hpost with ⟨hle, _, buf, sz, bf, of_, rest, ret, hargs, _, hbody⟩
  rcases hpre with ⟨herr_pre, buf0, sz0, bf0, of0, rest0, hargs0, _, _, hbuf0⟩
  rw [hargs] at hargs0
  injection hargs0 with hbuf_a h12
  injection h12 with hsz_a _
  injection hsz_a with _ hsz_eq
  rcases hbody with ⟨_, herr_only⟩ | ⟨hsz_pos, bb, ob, _, hbuf_eq, _, _, hother, _, _, hbb_wr⟩
  · exact ErrnoOnlyPost.post_stack herr_pre bs habs hagree herr_only
  · obtain ⟨eblk0, he0, _, hk_e0, _⟩ := herr_pre
    have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [he0] at hn; cases hn
    have hm_e : m.blocks os.errnoBlk = some eblk0 := (hagree os.errnoBlk henot).trans he0
    rcases hbuf0 with hz | ⟨bb0, ob0, hbuf0_eq, hwr0⟩
    · have : sz.toNat = sz0.toNat := congrArg BitVec.toNat hsz_eq
      omega
    · have hbb_eq : Val.ptr bb ob = Val.ptr bb0 ob0 := hbuf_eq.symm.trans (hbuf_a.trans hbuf0_eq)
      injection hbb_eq with hbb_id _
      obtain ⟨_, hbb0, _, _⟩ := validWritableRange_iff.mp (hbb_id ▸ hwr0)
      have hbb_not : bb ∉ bs := fun hm => by have hn := habs _ hm; rw [hbb0] at hn; cases hn
      refine ⟨hle, ?_, ?_⟩
      · intro x hx blk hbm _
        have hxe : x ≠ os.errnoBlk := fun heq => henot (heq ▸ hx)
        have hxb : x ≠ bb := fun heq => hbb_not (heq ▸ hx)
        rw [hother x hxb hxe, hbm]
      · intro x blk hbm hstk
        by_cases hxe : x = os.errnoBlk
        · subst hxe
          rw [hm_e] at hbm; cases hbm
          exact False.elim (hk_e0 hstk)
        · by_cases hxb : x = bb
          · subst hxb
            obtain ⟨blk', hbm', hwa, _⟩ := hbb_wr hxe blk hbm
            exact ⟨blk', hbm', hwa.1.2.2.2.1 ▸ hstk⟩
          · rw [hother x hxb hxe]
            exact ⟨blk, hbm, hstk⟩

private theorem printfPost_drop {m_clean m m_after : Mem} {os os' : OSState}
    {args : List Val} {rv : Val} (bs : List BlockId)
    (hnb : m_clean.nextBlock ≤ m.nextBlock)
    (habs : ∀ b ∈ bs, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (hpost : PrintfPost m os args rv m_after os') :
    PrintfPost m_clean os args rv (dropBlks m_after bs) os' := by
  rcases hpost with ⟨hle, hos, buf, sz, bf, of_, rest, ret, hargs, hrv, hbody⟩
  refine ⟨by rw [dropBlks_nextBlock]; exact Nat.le_trans hnb hle, hos, buf, sz, bf, of_, rest, ret, hargs, hrv, ?_⟩
  rcases hbody with ⟨hz, herr_only⟩ | ⟨hsz_pos, bb, ob, outBytes, hbuf_eq, hlen, hnul, hother, herr_m, herr_wr, hbb_wr⟩
  · exact .inl ⟨hz, ErrnoOnlyPost.post_drop bs hnb habs hagree herr_only⟩
  · refine .inr ⟨hsz_pos, bb, ob, outBytes, hbuf_eq, hlen, hnul, ?_, ?_, ?_, ?_⟩
    · intro x hxbb hxe
      by_cases hmem : x ∈ bs
      · rw [dropBlks_blocks_mem _ _ hmem, habs x hmem]
      · rw [dropBlks_blocks_not_mem _ _ hmem, hother x hxbb hxe, hagree x hmem]
    · intro eblk hce
      have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [hce] at hn; cases hn
      obtain ⟨eblk', e, hae, hmeta, hbytes⟩ := herr_m eblk ((hagree os.errnoBlk henot).trans hce)
      exact ⟨eblk', e, by rw [dropBlks_blocks_not_mem _ _ henot]; exact hae, hmeta, hbytes⟩
    · intro hne eblk hce
      have henot : os.errnoBlk ∉ bs := fun hm => by have hn := habs _ hm; rw [hce] at hn; cases hn
      obtain ⟨eblk', e, hae, hwa⟩ := herr_wr hne eblk ((hagree os.errnoBlk henot).trans hce)
      exact ⟨eblk', e, by rw [dropBlks_blocks_not_mem _ _ henot]; exact hae, hwa⟩
    · intro hne blk hcb
      have hbb_not : bb ∉ bs := fun hm => by have hn := habs _ hm; rw [hcb] at hn; cases hn
      obtain ⟨blk', hba, hwa, hslen⟩ := hbb_wr hne blk ((hagree bb hbb_not).trans hcb)
      refine ⟨blk', by rw [dropBlks_blocks_not_mem _ _ hbb_not]; exact hba, hwa, fun hin => ?_⟩
      obtain ⟨slen, hsl_lt, hsl_eq⟩ := hslen hin
      exact ⟨slen, hsl_lt, by rwa [strlenAt_of_blocks_eq (dropBlks_blocks_not_mem m_after bs hbb_not)]⟩

private theorem extOk_printf_inv {fn0 : String} (hfn0 : fn0 = "snprintf" ∨ fn0 = "vsnprintf")
    {buf : Val} {sz : BitVec 64} {bf : BlockId} {of_ : Int64} {rest : List Val}
    {m : Mem} {os : OSState} {ret : Val} {m' : Mem} {os' : OSState}
    (hok : Libc.ExtOk fn0 (buf :: .int .u64 sz :: .ptr bf of_ :: rest) m os ret m' os') :
    (∃ ret0 e : Int32, sz = 0 ∧ os = os' ∧
      ret = .int .i32 (BitVec.ofInt 32 ret0.toInt) ∧ Libc.writeErrno m os e = some m') ∨
    (∃ (bb : BlockId) (ob : Int64) (sz0 : Nat) (outBytes : List UInt8) (ret0 e : Int32) (m1 : Mem),
      buf = .ptr bb ob ∧ BitVec.ofNat 64 sz0 = sz ∧ sz0 > 0 ∧
      Libc.validWritableRange m bb ob sz0 = true ∧
      outBytes.length = sz0 ∧ (0 : UInt8) ∈ outBytes ∧
      m.writeBytes bb ob (outBytes.map MemByte.byte) = some m1 ∧
      Libc.writeErrno m1 os e = some m' ∧
      ret = .int .i32 (BitVec.ofInt 32 ret0.toInt) ∧ os = os') := by
  have h : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      (fn = "snprintf" ∨ fn = "vsnprintf") →
      args = buf :: .int .u64 sz :: .ptr bf of_ :: rest →
      (∃ ret0 e : Int32, sz = 0 ∧ osA = osB ∧
        retA = .int .i32 (BitVec.ofInt 32 ret0.toInt) ∧ Libc.writeErrno mA osA e = some mB) ∨
      (∃ (bb : BlockId) (ob : Int64) (sz0 : Nat) (outBytes : List UInt8) (ret0 e : Int32) (m1 : Mem),
        buf = .ptr bb ob ∧ BitVec.ofNat 64 sz0 = sz ∧ sz0 > 0 ∧
        Libc.validWritableRange mA bb ob sz0 = true ∧
        outBytes.length = sz0 ∧ (0 : UInt8) ∈ outBytes ∧
        mA.writeBytes bb ob (outBytes.map MemByte.byte) = some m1 ∧
        Libc.writeErrno m1 osA e = some mB ∧
        retA = .int .i32 (BitVec.ofInt 32 ret0.toInt) ∧ osA = osB) := by
    intro fn args mA osA retA mB osB hext
    cases hext
    case printf_zero =>
      intro _ hargs
      injection hargs with _ h12
      injection h12 with h1 _
      injection h1 with _ hsz
      exact .inl ⟨_, _, hsz.symm, rfl, rfl, ‹Libc.writeErrno _ _ _ = some _›⟩
    case printf_ok =>
      intro _ hargs
      injection hargs with h0 h12
      injection h12 with h1 _
      injection h1 with _ hsz
      exact .inr ⟨_, _, _, _, _, _, _, h0.symm, hsz,
        ‹(_ : Nat) > 0›,
        ‹Libc.validWritableRange _ _ _ _ = true›,
        ‹(_ : List UInt8).length = _›,
        ‹(0 : UInt8) ∈ _›,
        ‹Mem.writeBytes _ _ _ _ = some _›,
        ‹Libc.writeErrno _ _ _ = some _›,
        rfl, rfl⟩
    all_goals
      intro hfn _
      first
      | exact False.elim (or_str_disj_absurd hfn ‹_ = "lseek" ∨ _ = "lseek64"›
          (by decide) (by decide) (by decide) (by decide))
      | exact False.elim (str_disj_lit_absurd hfn (by decide) (by decide))
  exact h hok hfn0 rfl

private theorem printf_step_ok (fn : String) (hfn : fn = "snprintf" ∨ fn = "vsnprintf")
    (isV : Bool) (hisV : fn = "vsnprintf" → isV = true)
    (m : Mem) (os : OSState) (args : List Val) (hpre : PrintfPre isV m os args) :
    (∃ ret m' os', Libc.ExtOk fn args m os ret m' os') ∧
    (∀ ret m' os', Libc.ExtOk fn args m os ret m' os' → PrintfPost m os args ret m' os') := by
  rcases hpre with ⟨herr, buf, sz, bf, of_, rest, rfl, hva, hfmt, hbuf⟩
  have hva_fn : fn = "vsnprintf" → ∃ rest', rest = .vaList true :: rest' := fun hf => hva (hisV hf)
  have hex : ∃ ret m' os', Libc.ExtOk fn (buf :: .int .u64 sz :: .ptr bf of_ :: rest) m os ret m' os' := by
    rcases hbuf with hz | ⟨bb, ob, rfl, hwr⟩
    · have hsz0 : sz = 0 := BitVec.eq_of_toNat_eq (by simpa using hz)
      subst hsz0
      obtain ⟨m0', hm0'⟩ := herr.writeErrno_some 0
      exact ⟨.int .i32 (BitVec.ofInt 32 (0 : Int32).toInt), m0', os,
        Libc.ExtOk.printf_zero fn hfn buf bf of_ rest 0 0 m m0' os hva_fn hfmt hm0'⟩
    · by_cases hsz0 : sz.toNat = 0
      · have hsz_eq : sz = 0 := BitVec.eq_of_toNat_eq (by simpa using hsz0)
        subst hsz_eq
        obtain ⟨m0', hm0'⟩ := herr.writeErrno_some 0
        exact ⟨.int .i32 (BitVec.ofInt 32 (0 : Int32).toInt), m0', os,
          Libc.ExtOk.printf_zero fn hfn (.ptr bb ob) bf of_ rest 0 0 m m0' os hva_fn hfmt hm0'⟩
      · have hsz_pos : 0 < sz.toNat := Nat.pos_of_ne_zero hsz0
        obtain ⟨blk, hb, hperm, hin⟩ := validWritableRange_iff.mp hwr
        let outBytes : List UInt8 := List.replicate sz.toNat 0
        have hlen : outBytes.length = sz.toNat := List.length_replicate
        have hnul : (0 : UInt8) ∈ outBytes := List.mem_replicate.mpr ⟨hsz0, rfl⟩
        have hin' : Mem.inBounds blk ob (outBytes.map MemByte.byte).length = true := by
          rw [List.length_map, hlen]
          exact hin
        obtain ⟨m1, hm1⟩ := writeBytes_eq_some hb hperm hin'
        obtain ⟨m2, hm2⟩ := (herr.of_writeBytes hm1).writeErrno_some 0
        refine ⟨.int .i32 (BitVec.ofInt 32 (0 : Int32).toInt), m2, os, ?_⟩
        simpa using Libc.ExtOk.printf_ok fn hfn bb ob sz.toNat bf of_ rest outBytes 0 0 m m1 m2 os
          hva_fn hsz_pos hfmt hwr hlen hnul hm1 hm2
  refine ⟨hex, fun ret m' os' hok => ?_⟩
  rcases extOk_printf_inv hfn hok with
      ⟨ret0, e, rfl, rfl, rfl, herr'⟩ |
      ⟨bb, ob, sz0, outBytes, ret0, e, m1, hbuf_eq, hsz_eq0, hsz0, hbuf', hlen, hnul, hwr, herr', rfl, rfl⟩
  · exact ⟨by rw [writeBytes_nextBlock herr']; exact Nat.le_refl _, rfl,
      buf, 0, bf, of_, rest, ret0, rfl, rfl, .inl ⟨rfl, ErrnoOnlyPost.of_writeErrno herr'⟩⟩
  · have hsz_eq : sz.toNat = sz0 := bitVec64_toNat_of_lt hsz_eq0 (validWritableRange_lt hbuf')
    obtain ⟨hnext1, hne1, _, blk0, blk1, hb0, _, _, hbe1, hwa1⟩ := writeBytes_spec hwr
    obtain ⟨hnext2, hne2, _, eblk1, eblk2, hb_e1, _, _, hbe_e2, hwa_e2⟩ := writeBytes_spec herr'
    refine ⟨by rw [hnext2, hnext1]; exact Nat.le_refl _, rfl,
      buf, sz, bf, of_, rest, ret0, rfl, rfl,
      .inr ⟨hsz_eq ▸ hsz0, bb, ob, outBytes, hbuf_eq, hsz_eq ▸ hlen, hnul, ?_, ?_, ?_, ?_⟩⟩
    · intro x hxbb hxe
      rw [hne2 x hxe, hne1 x hxbb]
    · intro eblk hbe
      by_cases hbe_eq : bb = os.errnoBlk
      · subst hbe_eq
        rw [hb0] at hbe; cases hbe
        rw [hbe1] at hb_e1; cases hb_e1
        refine ⟨eblk2, e, hbe_e2, hwa1.metaEq.trans hwa_e2.metaEq, fun i hi => ?_⟩
        have hbw := hwa_e2.2 i
        have hcond : (0 : Int64).toInt.toNat ≤ i ∧
            i < (0 : Int64).toInt.toNat + (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt)).length := by
          change 0 ≤ i ∧ i < 0 + 4; omega
        simp only [hcond, and_self, ↓reduceIte] at hbw
        exact hbw
      · have hm1_e : m1.blocks os.errnoBlk = some eblk := (hne1 os.errnoBlk (Ne.symm hbe_eq)).trans hbe
        rw [hm1_e] at hb_e1; cases hb_e1
        refine ⟨eblk2, e, hbe_e2, hwa_e2.metaEq, fun i hi => ?_⟩
        have hbw := hwa_e2.2 i
        have hcond : (0 : Int64).toInt.toNat ≤ i ∧
            i < (0 : Int64).toInt.toNat + (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt)).length := by
          change 0 ≤ i ∧ i < 0 + 4; omega
        simp only [hcond, and_self, ↓reduceIte] at hbw
        exact hbw
    · intro hne eblk hbe
      have hm1_e : m1.blocks os.errnoBlk = some eblk := (hne1 os.errnoBlk (Ne.symm hne)).trans hbe
      rw [hm1_e] at hb_e1; cases hb_e1
      exact ⟨eblk2, e, hbe_e2, hwa_e2⟩
    · intro hne blk hb
      rw [hb0] at hb; cases hb
      have hbm2 : m'.blocks bb = some blk1 := (hne2 bb hne).trans hbe1
      refine ⟨blk1, hbm2, hwa1, fun hin => ?_⟩
      obtain ⟨slen, hsl_lt, hsl_eq⟩ :=
        BlockWrittenAt.strlenAt_lt_of_zero_mem hbm2 hwa1 (by rw [hlen, ← hsz_eq]; exact hin) hnul
      exact ⟨slen, hsz_eq ▸ (hlen ▸ hsl_lt), hsl_eq⟩

def snprintfSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "snprintf" = none)
    (hext : ∀ args m os out, ext "snprintf" args m os out ↔ Libc.ExtStep "snprintf" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "snprintf" "snprintf"
    [.ptr (.int .i8), .int .u64, .ptr (.const_ (.int .i8))] (.int .i32) true
    (PrintfPre false) PrintfPost hnfn hext
    (fun bs _ habs hagree _ _ hpre => printfPre_mono false bs habs hagree hpre)
    (fun bs _ habs hagree _ _ hpre hpost => printfPost_stack false bs habs hagree hpre hpost)
    (fun bs hnb habs hagree _ _ _ hpost => printfPost_drop bs hnb habs hagree hpost)
    (fun m os args hpre => printf_step_ok "snprintf" (.inl rfl) false (fun h => absurd h (by decide)) m os args hpre)

def vsnprintfSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : prog.fns "vsnprintf" = none)
    (hext : ∀ args m os out, ext "vsnprintf" args m os out ↔ Libc.ExtStep "vsnprintf" args m os out) :
    CallSpec prog cfg ext :=
  CallSpec.of_ext "vsnprintf" "vsnprintf"
    [.ptr (.int .i8), .int .u64, .ptr (.const_ (.int .i8)), .vaList] (.int .i32) false
    (PrintfPre true) PrintfPost hnfn hext
    (fun bs _ habs hagree _ _ hpre => printfPre_mono true bs habs hagree hpre)
    (fun bs _ habs hagree _ _ hpre hpost => printfPost_stack true bs habs hagree hpre hpost)
    (fun bs hnb habs hagree _ _ _ hpost => printfPost_drop bs hnb habs hagree hpost)
    (fun m os args hpre => printf_step_ok "vsnprintf" (.inr rfl) true (fun _ => rfl) m os args hpre)

/-! ## Complete `stdLibcProtos` Spec Environment -/

/-- All external symbol names registered in `C99.Sem.stdLibcProtos`. -/
def stdLibcNames : List String := stdLibcProtos.map (·.1)

/-- Ready-to-use `SafeSpecEnv` covering all 19 external functions in `stdLibcProtos`. -/
def stdLibcSafeSpecEnv {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : ∀ s ∈ stdLibcNames, prog.fns s = none)
    (hext : ∀ s ∈ stdLibcNames, ∀ args m os out, ext s args m os out ↔ Libc.ExtStep s args m os out) :
    SafeSpecEnv prog cfg ext
  | "malloc"    => some (mallocSpec (hnfn "malloc" (by decide)) (hext "malloc" (by decide))).toSafeSpec
  | "calloc"    => some (callocSpec (hnfn "calloc" (by decide)) (hext "calloc" (by decide))).toSafeSpec
  | "free"      => some (freeSpec (hnfn "free" (by decide)) (hext "free" (by decide))).toSafeSpec
  | "memcpy"    => some (memcpySpec (hnfn "memcpy" (by decide)) (hext "memcpy" (by decide))).toSafeSpec
  | "memmove"   => some (memmoveSpec (hnfn "memmove" (by decide)) (hext "memmove" (by decide))).toSafeSpec
  | "memset"    => some (memsetSpec (hnfn "memset" (by decide)) (hext "memset" (by decide))).toSafeSpec
  | "memcmp"    => some (memcmpSpec (hnfn "memcmp" (by decide)) (hext "memcmp" (by decide))).toSafeSpec
  | "strlen"    => some (strlenSpec (hnfn "strlen" (by decide)) (hext "strlen" (by decide))).toSafeSpec
  | "memchr"    => some (memchrSpec (hnfn "memchr" (by decide)) (hext "memchr" (by decide))).toSafeSpec
  | "open"      => some (openSpec (hnfn "open" (by decide)) (hext "open" (by decide))).toSafeSpec
  | "close"     => some (closeSpec (hnfn "close" (by decide)) (hext "close" (by decide))).toSafeSpec
  | "fcntl"     => some (fcntlSpec (hnfn "fcntl" (by decide)) (hext "fcntl" (by decide))).toSafeSpec
  | "lseek"     => some (lseekSpec (hnfn "lseek" (by decide)) (hext "lseek" (by decide))).toSafeSpec
  | "lseek64"   => some (lseek64Spec (hnfn "lseek64" (by decide)) (hext "lseek64" (by decide))).toSafeSpec
  | "read"      => some (readSafeSpec (hnfn "read" (by decide)) (hext "read" (by decide)))
  | "write"     => some (writeSpec (hnfn "write" (by decide)) (hext "write" (by decide))).toSafeSpec
  | "strerror"  => some (strerrorSpec (hnfn "strerror" (by decide)) (hext "strerror" (by decide))).toSafeSpec
  | "snprintf"  => some (snprintfSpec (hnfn "snprintf" (by decide)) (hext "snprintf" (by decide))).toSafeSpec
  | "vsnprintf" => some (vsnprintfSpec (hnfn "vsnprintf" (by decide)) (hext "vsnprintf" (by decide))).toSafeSpec
  | _           => none

theorem stdLibcSafeSpecEnv_sym {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (hnfn : ∀ s ∈ stdLibcNames, prog.fns s = none)
    (hext : ∀ s ∈ stdLibcNames, ∀ args m os out, ext s args m os out ↔ Libc.ExtStep s args m os out)
    {s : String} {sp : CallSafeSpec prog cfg ext}
    (h : stdLibcSafeSpecEnv hnfn hext s = some sp) : sp.sym = s := by
  unfold stdLibcSafeSpecEnv at h
  split at h <;> cases h <;> rfl

end C99.Proof.VCGen
