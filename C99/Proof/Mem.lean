import C99.Semantics

/-!
# Generic Memory & Value Representation Lemmas (`C99.Proof.Mem`)

Zlib-agnostic lemmas for `C99.Mem`, LP64 integer/pointer encoding,
`readVal`/`writeVal`/`castVal`, and stack-only/read-only memory
extension frames (`ROExt`, `LocalFrameMem`).
-/

namespace C99.Proof

open C99 C99.Sem

@[simp] theorem guard_true : (guard True : Option Unit) = some () := rfl

@[simp] theorem guard_eq_some {p : Prop} [Decidable p] :
    (guard p : Option Unit) = some () ↔ p := by
  by_cases h : p <;> simp [guard, Pure.pure, h]

/-! ## `Int64`, `BitVec`, and `IntKind` Arithmetic -/

theorem int64_ofInt_toInt {x : Int} (hlo : -(2 ^ 63 : Int) ≤ x) (hhi : x < (2 ^ 63 : Int)) :
    (Int64.ofInt x).toInt = x := by
  change (BitVec.ofInt 64 x).toInt = x
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem uint64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  change (BitVec.ofNat 64 n).toNat = n
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem ptrDiffLimit_val : ptrDiffLimit = 2 ^ 63 := rfl

@[simp] theorem promote_i8 : IntKind.i8.promote = .i32 := rfl
@[simp] theorem promote_u8 : IntKind.u8.promote = .i32 := rfl
@[simp] theorem promote_i16 : IntKind.i16.promote = .i32 := rfl
@[simp] theorem promote_u16 : IntKind.u16.promote = .i32 := rfl
@[simp] theorem promote_i32 : IntKind.i32.promote = .i32 := rfl
@[simp] theorem promote_u32 : IntKind.u32.promote = .u32 := rfl
@[simp] theorem promote_i64 : IntKind.i64.promote = .i64 := rfl
@[simp] theorem promote_u64 : IntKind.u64.promote = .u64 := rfl

@[simp] theorem valAsInt?_int (k : IntKind) (v : BitVec k.bits) :
    valAsInt? (.int k v) = some (k, if k.signed then v.toInt else (v.toNat : Int)) := rfl

theorem ofIntExact_unsigned {k : IntKind} (hk : k.signed = false) (v : Int) :
    ofIntExact k v = some (.int k (BitVec.ofInt k.bits v)) := by
  simp [ofIntExact, hk]

theorem ofIntExact_signed {k : IntKind} (hk : k.signed = true) {v : Int}
    (hr : k.inRange v = true) :
    ofIntExact k v = some (.int k (BitVec.ofInt k.bits v)) := by
  simp [ofIntExact, hk, hr]

/-! ## Little-Endian Integer & Pointer Byte Codecs -/

@[simp] theorem encodeInt_length (k : IntKind) (v : BitVec k.bits) :
    (Mem.encodeInt k v).length = k.bytes := by
  simp [Mem.encodeInt]

@[simp] theorem encodePtr_length (b : BlockId) (off : Int64) :
    (Mem.encodePtr b off).length = 8 := by
  simp [Mem.encodePtr]

@[simp] theorem encodeFnPtr_length (sym : SymId) :
    (Mem.encodeFnPtr sym).length = 8 := by
  simp [Mem.encodeFnPtr]

@[simp] theorem encodeNull_length : Mem.encodeNull.length = 8 := by
  simp [Mem.encodeNull]

private theorem decodeInt_go_encode_aux (n bytes : Nat) (acc : Nat)
    (hacc : acc < 2 ^ (8 * n)) (x : Nat) (hx : x < 2 ^ (8 * bytes)) :
    Mem.decodeInt.go acc (8 * n)
      ((List.range bytes).map (fun j => MemByte.byte (UInt8.ofNat ((x >>> (8 * j)) % 256)))) =
      some (acc ||| (x <<< (8 * n))) := by
  induction bytes generalizing n acc x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp [Mem.decodeInt.go]
  | succ b ih =>
    have hcons : List.range (b + 1) = 0 :: (List.range b).map Nat.succ :=
      List.range_succ_eq_map
    rw [hcons, List.map_cons, List.map_map, Mem.decodeInt.go]
    have hbyte : (UInt8.ofNat (x % 256)).toNat = x % 256 := by
      change (BitVec.ofNat 8 (x % 256)).toNat = x % 256
      have hpos : (0 : Nat) < 256 := by decide
      simp [Nat.mod_eq_of_lt (Nat.mod_lt x hpos)]
    have hmap : ((List.range b).map (fun j => MemByte.byte (UInt8.ofNat ((x >>> (8 * j.succ)) % 256)))) =
        ((List.range b).map (fun j => MemByte.byte (UInt8.ofNat (((x >>> 8) >>> (8 * j)) % 256)))) := by
      apply List.map_congr_left
      intro j _
      have hsh : x >>> (8 * j.succ) = (x >>> 8) >>> (8 * j) := by
        rw [Nat.mul_succ, Nat.add_comm (8 * j) 8, Nat.shiftRight_add]
      rw [hsh]
    simp only [Function.comp_def, Nat.mul_zero, Nat.shiftRight_zero]
    rw [hmap]
    have hx8 : x >>> 8 < 2 ^ (8 * b) := by
      rw [Nat.shiftRight_eq_div_pow]
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add] at hx
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hx
    have hacc1 : acc ||| (UInt8.ofNat (x % 256)).toNat <<< (8 * n) < 2 ^ (8 * (n + 1)) := by
      rw [hbyte]
      have hpos : (0 : Nat) < 256 := by decide
      have h1 : (x % 256) <<< (8 * n) < 2 ^ (8 * n + 8) := by
        rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm (2 ^ (8 * n)) (2 ^ 8)]
        exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt x hpos) (Nat.two_pow_pos (8 * n))
      have h2 : acc < 2 ^ (8 * n + 8) :=
        Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.or_lt_two_pow h2 h1
    have ihcall := ih (n + 1) (acc ||| (UInt8.ofNat (x % 256)).toNat <<< (8 * n)) hacc1 (x >>> 8) hx8
    have hshift : 8 * n + 8 = 8 * (n + 1) := by omega
    rw [← hshift] at ihcall
    rw [ihcall, hbyte]
    apply congrArg some
    apply Nat.eq_of_testBit_eq
    intro i
    have h256 : (256 : Nat) = 2 ^ 8 := by decide
    rw [h256]
    simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      Nat.testBit_mod_two_pow]
    by_cases hi1 : i < 8 * n
    · have ha1 : ¬ 8 * n ≤ i := by omega
      have ha2 : ¬ 8 * n + 8 ≤ i := by omega
      simp [ha1, ha2]
    · by_cases hi2 : i < 8 * n + 8
      · have ha1 : 8 * n ≤ i := by omega
        have ha2 : ¬ 8 * n + 8 ≤ i := by omega
        have ha3 : i - 8 * n < 8 := by omega
        simp [ha1, ha2, ha3]
      · have ha1 : 8 * n ≤ i := by omega
        have ha2 : 8 * n + 8 ≤ i := by omega
        have ha3 : ¬ i - 8 * n < 8 := by omega
        have hsum : 8 + (i - (8 * n + 8)) = i - 8 * n := by omega
        simp [ha1, ha2, ha3, hsum]

theorem decodeInt_encodeInt (k : IntKind) (v : BitVec k.bits) :
    Mem.decodeInt k (Mem.encodeInt k v) = some v := by
  have hkbits : 8 * k.bytes = k.bits := by cases k <;> rfl
  have hvlt : v.toNat < 2 ^ (8 * k.bytes) := by rw [hkbits]; exact v.isLt
  have hgo := decodeInt_go_encode_aux 0 k.bytes 0 (by decide) v.toNat hvlt
  simp only [Nat.mul_zero, Nat.zero_or, Nat.shiftLeft_zero] at hgo
  unfold Mem.decodeInt Mem.encodeInt
  simp only [List.length_map, List.length_range, beq_self_eq_true, guard_true, bind, Option.bind]
  rw [hgo]
  simp

theorem decodeInt_go_concrete :
    ∀ (bs : List MemByte) (acc shift : Nat),
      (∀ x ∈ bs, ∃ u : UInt8, x = .byte u) →
      ∃ n, Mem.decodeInt.go acc shift bs = some n := by
  intro bs
  induction bs with
  | nil => intro acc shift _; exact ⟨acc, rfl⟩
  | cons x xs ih =>
    intro acc shift hx
    obtain ⟨u, rfl⟩ := hx x (.head _)
    exact ih (acc ||| (u.toNat <<< shift)) (shift + 8) fun y hy => hx y (.tail _ hy)

theorem decodeInt_concrete_some (k : IntKind) (bs : List MemByte)
    (hlen : bs.length = k.bytes)
    (hbytes : ∀ x ∈ bs, ∃ u : UInt8, x = .byte u) :
    ∃ bv, Mem.decodeInt k bs = some bv := by
  obtain ⟨n, hn⟩ := decodeInt_go_concrete bs 0 0 hbytes
  refine ⟨BitVec.ofNat k.bits n, ?_⟩
  unfold Mem.decodeInt
  simp [hlen, hn, bind, Option.bind]

@[simp] theorem decodeInt_u8_byte (u : UInt8) :
    Mem.decodeInt .u8 [.byte u] = some u.toBitVec := by
  unfold Mem.decodeInt
  simp only [List.length_singleton, IntKind.bytes, IntKind.bits, beq_self_eq_true, guard_true,
    Mem.decodeInt.go, Nat.shiftLeft_zero, Nat.zero_or, bind, Option.bind]
  change some (BitVec.ofNat 8 u.toNat) = some u.toBitVec
  apply congrArg some
  apply BitVec.eq_of_toNat_eq
  have hu : u.toNat < 2 ^ 8 := u.toBitVec.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
  rfl

@[simp] theorem decodePtr_encodePtr (b : BlockId) (off : Int64) :
    Mem.decodePtr (Mem.encodePtr b off) = some (.ptr b off) := by
  have he : Mem.encodePtr b off =
      [ .ptrFrag b off 0, .ptrFrag b off 1, .ptrFrag b off 2, .ptrFrag b off 3,
        .ptrFrag b off 4, .ptrFrag b off 5, .ptrFrag b off 6, .ptrFrag b off 7 ] := rfl
  rw [he]
  unfold Mem.decodePtr
  dsimp [bind, Option.bind, pure, guard, Pure.pure]
  split
  · next heq => cases heq; simp
  · next heq => cases heq
  · next h1 h2 => exact False.elim (h1 b off (by decide) b off (by decide) b off (by decide) b off (by decide) b off (by decide) b off (by decide) b off (by decide) b off (by decide) rfl)

@[simp] theorem decodePtr_encodeNull :
    Mem.decodePtr Mem.encodeNull = some .null := by
  decide

@[simp] theorem decodePtr_encodeFnPtr (sym : SymId) :
    Mem.decodePtr (Mem.encodeFnPtr sym) = some (.fnPtr sym) := by
  have he : Mem.encodeFnPtr sym =
      [ .fnFrag sym 0, .fnFrag sym 1, .fnFrag sym 2, .fnFrag sym 3,
        .fnFrag sym 4, .fnFrag sym 5, .fnFrag sym 6, .fnFrag sym 7 ] := rfl
  rw [he]
  unfold Mem.decodePtr
  dsimp [bind, Option.bind, pure, guard, Pure.pure]
  split
  · next heq => cases heq
  · next heq => cases heq; simp
  · next h1 h2 => exact False.elim (h2 sym (by decide) sym (by decide) sym (by decide) sym (by decide) sym (by decide) sym (by decide) sym (by decide) sym (by decide) rfl)

/-! ## Bounds, Alignment, Allocation, Read/Write, and Stack Freeing -/

theorem inBounds_iff {blk : Block} {off : Int64} {len : Nat} :
    Mem.inBounds blk off len = true ↔ 0 ≤ off.toInt ∧ off.toInt.toNat + len ≤ blk.size := by
  simp [Mem.inBounds]

theorem inBounds_mono {blk : Block} {off : Int64} {len len' : Nat}
    (hb : Mem.inBounds blk off len = true) (hle : len' ≤ len) :
    Mem.inBounds blk off len' = true := by
  rw [inBounds_iff] at hb ⊢
  omega

theorem inBounds_add {blk : Block} {off : Int64} {len k len' : Nat}
    (hb : Mem.inBounds blk off len = true) (hle : k + len' ≤ len) :
    Mem.inBounds blk (Int64.ofInt (off.toInt + k)) len' = true := by
  rw [inBounds_iff] at hb ⊢
  have hlt : off.toInt + (k : Int) < 2 ^ 63 := by
    have := blk.sizeLt
    rw [ptrDiffLimit_val] at this
    omega
  have hoff : (Int64.ofInt (off.toInt + k)).toInt = off.toInt + k :=
    int64_ofInt_toInt (by omega) hlt
  rw [hoff]
  omega

theorem isAligned_iff {blk : Block} {off : Int64} {al : Nat} :
    Mem.isAligned blk off al = true ↔
      0 ≤ off.toInt ∧ 0 < al ∧ (blk.baseAddr.toNat + off.toInt.toNat) % al = 0 := by
  simp [Mem.isAligned, and_assoc]

theorem isAligned_one {blk : Block} {off : Int64} (ho : 0 ≤ off.toInt) :
    Mem.isAligned blk off 1 = true := by
  rw [isAligned_iff]
  exact ⟨ho, Nat.zero_lt_one, Nat.mod_one _⟩

theorem isAligned_add {blk : Block} {off : Int64} {k al : Nat}
    (ha : Mem.isAligned blk off al = true) (hdiv : al ∣ k)
    (hbound : off.toInt + (k : Int) < 2 ^ 63) :
    Mem.isAligned blk (Int64.ofInt (off.toInt + k)) al = true := by
  rw [isAligned_iff] at ha ⊢
  have hoff : (Int64.ofInt (off.toInt + k)).toInt = off.toInt + k :=
    int64_ofInt_toInt (by omega) hbound
  rw [hoff]
  refine ⟨by omega, ha.2.1, ?_⟩
  have hk : (off.toInt + (k : Int)).toNat = off.toInt.toNat + k := by omega
  rw [hk, ← Nat.add_assoc, Nat.add_mod, ha.2.2, Nat.mod_eq_zero_of_dvd hdiv]
  simp

theorem addrOf_some {m : Mem} {b : BlockId} {off : Int64} {blk : Block}
    (hb : m.blocks b = some blk) (h0 : 0 ≤ off.toInt) (hle : off.toInt ≤ blk.size) :
    m.addrOf b off = some (blk.baseAddr + UInt64.ofNat off.toInt.toNat) := by
  simp [Mem.addrOf, hb, h0, hle]

theorem isAligned_4_of_addr_and_3 {m : Mem} {b : BlockId} {off : Int64} {blk : Block} {addr : UInt64}
    (hb : m.blocks b = some blk) (h0 : 0 ≤ off.toInt) (hle : off.toInt ≤ blk.size)
    (haddr : m.addrOf b off = some addr) (hand : (addr.toNat &&& 3) = 0) :
    Mem.isAligned blk off 4 = true := by
  rw [addrOf_some hb h0 hle, Option.some.injEq] at haddr
  subst addr
  rw [isAligned_iff]
  refine ⟨h0, by decide, ?_⟩
  have hsum : (blk.baseAddr + UInt64.ofNat off.toInt.toNat).toNat =
      (blk.baseAddr.toNat + (UInt64.ofNat off.toInt.toNat).toNat) % 2 ^ 64 := rfl
  have hofflt : off.toInt.toNat < 2 ^ 64 := by
    have := blk.sizeLt
    rw [ptrDiffLimit_val] at this
    omega
  have hoffeq : (UInt64.ofNat off.toInt.toNat).toNat = off.toInt.toNat :=
    uint64_ofNat_toNat hofflt
  have handmod : ∀ x : Nat, (x &&& 3) = x % 4 := fun x => by
    change x &&& (2 ^ 2 - 1) = x % 2 ^ 2
    exact Nat.and_two_pow_sub_one_eq_mod x 2
  rw [handmod] at hand
  rw [hsum, hoffeq] at hand
  have h4div : 4 ∣ 2 ^ 64 := by decide
  rw [Nat.mod_mod_of_dvd _ h4div] at hand
  exact hand

@[simp] theorem alloc_fst (m : Mem) (sz al : Nat) (p : Perm) (k : AllocKind) (ba : UInt64)
    (init : Nat → MemByte) (h1 : sz < ptrDiffLimit) (h2 : 0 < al) (h3 : ba.toNat % al = 0) :
    (m.alloc sz al p k ba init h1 h2 h3).1 = m.nextBlock := rfl

@[simp] theorem alloc_snd_nextBlock (m : Mem) (sz al : Nat) (p : Perm) (k : AllocKind) (ba : UInt64)
    (init : Nat → MemByte) (h1 : sz < ptrDiffLimit) (h2 : 0 < al) (h3 : ba.toNat % al = 0) :
    (m.alloc sz al p k ba init h1 h2 h3).2.nextBlock = m.nextBlock + 1 := rfl

theorem alloc_blocks_eq (m : Mem) (sz al : Nat) (p : Perm) (k : AllocKind) (ba : UInt64)
    (init : Nat → MemByte) (h1 : sz < ptrDiffLimit) (h2 : 0 < al) (h3 : ba.toNat % al = 0) :
    (m.alloc sz al p k ba init h1 h2 h3).2.blocks m.nextBlock =
      some ⟨sz, al, p, k, ba, init, h1, h2, h3⟩ := by
  simp [Mem.alloc]

theorem alloc_blocks_ne (m : Mem) (sz al : Nat) (p : Perm) (k : AllocKind) (ba : UInt64)
    (init : Nat → MemByte) (h1 : sz < ptrDiffLimit) (h2 : 0 < al) (h3 : ba.toNat % al = 0)
    {b : BlockId} (hne : b ≠ m.nextBlock) :
    (m.alloc sz al p k ba init h1 h2 h3).2.blocks b = m.blocks b := by
  simp [Mem.alloc, hne]

theorem lt_nextBlock_of_some {m : Mem} {b : BlockId} {blk : Block} (h : m.blocks b = some blk) :
    b < m.nextBlock := by
  rcases Nat.lt_or_ge b m.nextBlock with hlt | hge
  · exact hlt
  · have hnone := m.fresh b hge
    rw [hnone] at h
    cases h

theorem readBytes_of_bounds {m : Mem} {b : BlockId} {off : Int64} {len : Nat} {blk : Block}
    (hb : m.blocks b = some blk) (hin : Mem.inBounds blk off len = true) :
    m.readBytes b off len = some ((List.range len).map fun i => blk.bytes (off.toInt.toNat + i)) := by
  unfold Mem.readBytes
  simp [hb, hin, bind, Option.bind]

theorem writeBytes_eq_some {m : Mem} {b : BlockId} {off : Int64} {bs : List MemByte} {blk : Block}
    (hb : m.blocks b = some blk) (hrw : blk.perm = .rw) (hin : Mem.inBounds blk off bs.length = true) :
    ∃ m', m.writeBytes b off bs = some m' := by
  unfold Mem.writeBytes
  split
  · next hblk => rw [hb] at hblk; cases hblk
  · next blk1 hblk =>
    rw [hb, Option.some.injEq] at hblk
    subst blk1
    simp [hrw, hin]

theorem writeBytes_nextBlock {m m' : Mem} {b : BlockId} {off : Int64} {bs : List MemByte}
    (h : m.writeBytes b off bs = some m') : m'.nextBlock = m.nextBlock := by
  unfold Mem.writeBytes at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h

theorem writeBytes_blocks_eq {m m' : Mem} {b : BlockId} {off : Int64} {bs : List MemByte} {blk : Block}
    (hb : m.blocks b = some blk) (h : m.writeBytes b off bs = some m') :
    m'.blocks b = some { blk with bytes := (fun i =>
      if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + bs.length then bs[i - off.toInt.toNat]?.getD .undef
      else blk.bytes i) } := by
  unfold Mem.writeBytes at h
  split at h
  · cases h
  · next blk1 heq =>
    rw [hb, Option.some.injEq] at heq
    subst blk1
    split at h
    · cases h; simp
    · cases h

theorem writeBytes_blocks_ne {m m' : Mem} {b b' : BlockId} {off : Int64} {bs : List MemByte}
    (h : m.writeBytes b off bs = some m') (hne : b' ≠ b) :
    m'.blocks b' = m.blocks b' := by
  unfold Mem.writeBytes at h
  split at h
  · cases h
  · split at h
    · cases h
      have hbeq : (b' == b) = false := beq_false_of_ne hne
      simp [hbeq]
    · cases h

theorem readBytes_writeBytes_same {m m' : Mem} {b : BlockId} {off : Int64} {bs : List MemByte}
    {blk : Block} (hb : m.blocks b = some blk) (hw : m.writeBytes b off bs = some m') :
    m'.readBytes b off bs.length = some bs := by
  have h1 := hw
  unfold Mem.writeBytes at hw
  split at hw
  · cases hw
  · next blk1 heq =>
    rw [hb, Option.some.injEq] at heq
    subst blk1
    split at hw
    · next hperm =>
      cases hw
      have hin : Mem.inBounds blk off bs.length = true := (Bool.and_eq_true _ _).mp hperm |>.2
      have h0 : 0 ≤ off.toInt := (inBounds_iff.mp hin).1
      have hlen : off.toInt.toNat + bs.length ≤ blk.size := (inBounds_iff.mp hin).2
      rw [readBytes_of_bounds (writeBytes_blocks_eq hb h1)]
      · apply congrArg some
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          have hi : i < bs.length := by simpa using hi1
          simp [hi, Nat.add_sub_cancel_left, Option.getD]
      · simp [Mem.inBounds, h0]
        exact hlen
    · cases hw

@[simp] theorem freeStack_nextBlock (m : Mem) (bids : List BlockId) :
    (m.freeStack bids).nextBlock = m.nextBlock := rfl

theorem freeStack_blocks_not_mem (m : Mem) (bids : List BlockId) {b : BlockId}
    (hnot : b ∉ bids) : (m.freeStack bids).blocks b = m.blocks b := by
  simp [Mem.freeStack, hnot]

theorem freeStack_blocks_mem_stack (m : Mem) (bids : List BlockId) {b : BlockId} {blk : Block}
    (hmem : b ∈ bids) (hb : m.blocks b = some blk) (hk : blk.kind = .stack) :
    (m.freeStack bids).blocks b = none := by
  simp [Mem.freeStack, hmem, hb, hk]

theorem freeStack_blocks_mem_nonstack (m : Mem) (bids : List BlockId) {b : BlockId} {blk : Block}
    (hb : m.blocks b = some blk) (hk : blk.kind ≠ .stack) :
    (m.freeStack bids).blocks b = some blk := by
  by_cases hmem : b ∈ bids
  · simp [Mem.freeStack, hmem, hb, hk]
  · rw [freeStack_blocks_not_mem m bids hmem, hb]

/-! ## Scalar `readVal`, `writeVal`, `castVal` -/

theorem readVal_int_of_bytes (tags : TypeEnv) {m : Mem} {b : BlockId} {off : Int64} {blk : Block}
    {k : IntKind} (hb : m.blocks b = some blk)
    (hal : Mem.isAligned blk off k.align = true)
    (hin : Mem.inBounds blk off k.bytes = true)
    (hconcr : ∀ i < k.bytes, ∃ u : UInt8, blk.bytes (off.toInt.toNat + i) = .byte u) :
    ∃ bv, Sem.readVal tags m b off (.int k) = some (.int k bv) := by
  have hrd : m.readBytes b off k.bytes =
      some ((List.range k.bytes).map fun i => blk.bytes (off.toInt.toNat + i)) :=
    readBytes_of_bounds hb hin
  have hlen : ((List.range k.bytes).map fun i => blk.bytes (off.toInt.toNat + i)).length = k.bytes := by
    simp
  have hmap : ∀ x ∈ ((List.range k.bytes).map fun i => blk.bytes (off.toInt.toNat + i)),
      ∃ u : UInt8, x = .byte u := by
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨i, hi, rfl⟩
    exact hconcr i (List.mem_range.mp hi)
  obtain ⟨bv, hdec⟩ := decodeInt_concrete_some k _ hlen hmap
  refine ⟨bv, ?_⟩
  unfold Sem.readVal
  simp only [CTy.unqual, CTy.intKind?, hb, hal, guard_true, bind, Option.bind]
  rw [hrd]
  dsimp [pure]
  rw [hdec]

theorem readVal_writeVal_same_int (tags : TypeEnv) {m m' : Mem} {b : BlockId} {off : Int64}
    {blk : Block} {k : IntKind} {v : BitVec k.bits}
    (hb : m.blocks b = some blk)
    (hwr : Sem.writeVal m b off (.int k) (.int k v) = some m') :
    Sem.readVal tags m' b off (.int k) = some (.int k v) := by
  unfold Sem.writeVal at hwr
  simp only [CTy.isConst, hb, CTy.unqual, CTy.intKind?, valAsInt?, bind, Option.bind,
    guard, Pure.pure] at hwr
  dsimp at hwr
  have hal : Mem.isAligned blk off k.align = true := by
    cases hg : Mem.isAligned blk off k.align
    · simp [hg] at hwr
    · rfl
  simp only [hal, ↓reduceIte] at hwr
  have hwb : m.writeBytes b off (Mem.encodeInt k v) = some m' := by
    have heq : BitVec.ofInt k.bits (if k.signed then v.toInt else (v.toNat : Int)) = v := by
      by_cases hs : k.signed <;> simp [hs]
    simpa [heq] using hwr
  have hrd := readBytes_writeBytes_same hb hwb
  have hblk' := writeBytes_blocks_eq hb hwb
  have hal' : Mem.isAligned { blk with bytes := (fun i =>
      if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + (Mem.encodeInt k v).length then
        (Mem.encodeInt k v)[i - off.toInt.toNat]?.getD .undef
      else blk.bytes i) } off k.align = true := by
    simpa [Mem.isAligned] using hal
  unfold Sem.readVal
  simp only [CTy.unqual, CTy.intKind?, hblk', hal', guard_true, bind, Option.bind]
  rw [← encodeInt_length k v, hrd]
  dsimp [pure]
  rw [decodeInt_encodeInt]

theorem writeVal_int_some {m : Mem} {b : BlockId} {off : Int64} {blk : Block} {ty : CTy}
    {k : IntKind} {v : Val} {iv : Int}
    (hnc : ty.isConst = false) (hk : ty.unqual = .int k)
    (hb : m.blocks b = some blk) (hrw : blk.perm = .rw)
    (hal : Mem.isAligned blk off k.align = true)
    (hin : Mem.inBounds blk off k.bytes = true)
    (hvi : valAsInt? v = some (k, iv)) :
    ∃ m', Sem.writeVal m b off ty v = some m' := by
  have hin2 : Mem.inBounds blk off (Mem.encodeInt k (BitVec.ofInt k.bits iv)).length = true := by
    simpa [encodeInt_length] using hin
  obtain ⟨m', hm'⟩ := writeBytes_eq_some hb hrw hin2
  refine ⟨m', ?_⟩
  unfold Sem.writeVal
  simp [hnc, hb, hk, CTy.unqual, CTy.intKind?, hal, hvi, hm', bind, Option.bind]

theorem writeVal_ptr_some {m : Mem} {b : BlockId} {off : Int64} {blk : Block} {ty el : CTy} {v : Val}
    (hnc : ty.isConst = false) (hptr : ty.unqual = .ptr el)
    (hb : m.blocks b = some blk) (hrw : blk.perm = .rw)
    (hal : Mem.isAligned blk off 8 = true)
    (hin : Mem.inBounds blk off 8 = true)
    (hv : v = .null ∨ ∃ pb poff, v = .ptr pb poff) :
    ∃ m', Sem.writeVal m b off ty v = some m' := by
  rcases hv with rfl | ⟨pb, poff, rfl⟩
  · have hin2 : Mem.inBounds blk off Mem.encodeNull.length = true := by simpa using hin
    obtain ⟨m', hm'⟩ := writeBytes_eq_some hb hrw hin2
    refine ⟨m', ?_⟩
    unfold Sem.writeVal
    simp [hnc, hb, hptr, hal, hm', bind, Option.bind]
  · have hin2 : Mem.inBounds blk off (Mem.encodePtr pb poff).length = true := by simpa using hin
    obtain ⟨m', hm'⟩ := writeBytes_eq_some hb hrw hin2
    refine ⟨m', ?_⟩
    unfold Sem.writeVal
    simp [hnc, hb, hptr, hal, hm', bind, Option.bind]

@[simp] theorem castVal_int (m : Mem) (k k1 : IntKind) (bv : BitVec k1.bits) :
    castVal m (.int k) (.int k1 bv) =
      some (ofIntCast k (if k1.signed then bv.toInt else (bv.toNat : Int))) := by
  simp [castVal, CTy.unqual, CTy.isVoid, CTy.intKind?]

@[simp] theorem castVal_int_self (m : Mem) (k : IntKind) (bv : BitVec k.bits) :
    castVal m (.int k) (.int k bv) = some (.int k bv) := by
  simp only [castVal_int, ofIntCast]
  by_cases hs : k.signed
  · simp [hs, BitVec.ofInt_toInt]
  · simp [hs]

@[simp] theorem castVal_ptr_ptr (m : Mem) (to : CTy) (b : BlockId) (off : Int64) :
    castVal m (.ptr to) (.ptr b off) = some (.ptr b off) := by
  simp [castVal, CTy.unqual, CTy.isVoid, CTy.intKind?]

@[simp] theorem castVal_ptr_null (m : Mem) (to : CTy) :
    castVal m (.ptr to) .null = some .null := by
  simp [castVal, CTy.unqual, CTy.isVoid, CTy.intKind?]

@[simp] theorem castVal_fnPtr_fnPtr (m : Mem) (r : CTy) (ps : List CTy) (v : Bool) (s : SymId) :
    castVal m (.fnPtr r ps v) (.fnPtr s) = some (.fnPtr s) := by
  simp [castVal, CTy.unqual, CTy.isVoid, CTy.intKind?]

@[simp] theorem castVal_fnPtr_null (m : Mem) (r : CTy) (ps : List CTy) (v : Bool) :
    castVal m (.fnPtr r ps v) .null = some .null := by
  simp [castVal, CTy.unqual, CTy.isVoid, CTy.intKind?]

@[simp] theorem castVal_vaList (m : Mem) :
    castVal m .vaList (.vaList true) = some (.vaList true) := by
  simp [castVal, CTy.unqual, CTy.isVoid, CTy.intKind?]

/-! ## String Literals -/

private theorem strlenAt_go_str (blk : Block) (str : String) (hsz : blk.size = str.utf8ByteSize + 1)
    (hbytes : ∀ i, blk.bytes i = .byte ((str.toUTF8[i]?).getD 0))
    (hnonnul : ∀ i < str.utf8ByteSize, (str.toUTF8[i]?).getD 0 ≠ 0)
    (hend : (str.toUTF8[str.utf8ByteSize]?).getD 0 = 0) :
    ∀ k, k ≤ str.utf8ByteSize →
      Mem.strlenAt.go blk 0 (str.utf8ByteSize - k) = some str.utf8ByteSize := by
  intro k hk
  induction k with
  | zero =>
    rw [Nat.sub_zero, Mem.strlenAt.go]
    have hlt : str.utf8ByteSize < blk.size := by omega
    split
    · rw [hbytes, hend]; simp
    · next h => exact False.elim (h hlt)
  | succ k' ih =>
    let idx := str.utf8ByteSize - (k' + 1)
    have hlt : idx < str.utf8ByteSize := by omega
    have hlt1 : idx < blk.size := by omega
    have hnz : (str.toUTF8[idx]?).getD 0 ≠ 0 := hnonnul idx hlt
    rw [Mem.strlenAt.go]
    split
    · rw [hbytes]
      cases hbv : (str.toUTF8[idx]?).getD 0 with
      | ofBitVec v =>
        match hnat : v.toNat with
        | 0 =>
          exfalso
          apply hnz
          rw [hbv]
          apply UInt8.eq_of_toBitVec_eq
          apply BitVec.eq_of_toNat_eq
          exact hnat
        | n + 1 =>
          have hnot0 : UInt8.ofBitVec v ≠ 0 := fun heq => by
            have h0 : v = 0 := congrArg UInt8.toBitVec heq
            simp [h0] at hnat
          have hm : (match MemByte.byte (UInt8.ofBitVec v) with
              | .byte 0 => some (idx - 0)
              | .byte _ => Mem.strlenAt.go blk 0 (idx + 1)
              | _ => none) = Mem.strlenAt.go blk 0 (idx + 1) := by
            rcases h0 : UInt8.ofBitVec v with _
            cases hvn : (⟨v⟩ : UInt8) == 0 <;> simp_all
          change (match MemByte.byte (UInt8.ofBitVec v) with
            | .byte 0 => some (idx - 0)
            | .byte _ => Mem.strlenAt.go blk 0 (idx + 1)
            | _ => none) = some str.utf8ByteSize
          rw [hm]
          have hsub : idx + 1 = str.utf8ByteSize - k' := by omega
          rw [hsub]
          exact ih (by omega)
    · next h => exact False.elim (h hlt1)

theorem strlenAt_alloc_strLit {m m' : Mem} {bid : BlockId} {base : UInt64} {str : String}
    (hsz : str.utf8ByteSize + 1 < ptrDiffLimit)
    (halloc : m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m'))
    (hnonnul : ∀ i < str.utf8ByteSize, (str.toUTF8[i]?).getD 0 ≠ 0)
    (hend : (str.toUTF8[str.utf8ByteSize]?).getD 0 = 0) :
    m'.strlenAt bid 0 = some str.utf8ByteSize := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst halloc).symm
  have hm' : m' = (m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)).2 :=
    (congrArg Prod.snd halloc).symm
  subst hbid hm'
  let blk : Block := ⟨str.utf8ByteSize + 1, 1, .ro, .global, base,
    fun i => .byte ((str.toUTF8[i]?).getD 0), hsz, by decide, Nat.mod_one _⟩
  have hblk : (m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)).2.blocks m.nextBlock =
      some blk := alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hgo := strlenAt_go_str blk str rfl (fun _ => rfl) hnonnul hend str.utf8ByteSize (Nat.le_refl _)
  rw [Nat.sub_self] at hgo
  unfold Mem.strlenAt
  rw [show (m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)).2.blocks m.nextBlock =
      some blk from hblk]
  simpa [Int64.toInt, bind, Option.bind] using hgo

/-! ## Read-Only & Stack-Only Frame Invariants (`ROExt`, `LocalFrameMem`) -/

/-- Read-only memory extension: pre-existing blocks are byte-identical and any new blocks
are read-only globals (string literals). -/
def ROExt (m m' : Mem) : Prop :=
  m.nextBlock ≤ m'.nextBlock ∧
  (∀ b, b < m.nextBlock → m'.blocks b = m.blocks b) ∧
  (∀ b blk, m.nextBlock ≤ b → m'.blocks b = some blk → blk.kind = .global ∧ blk.perm = .ro)

theorem ROExt.refl (m : Mem) : ROExt m m :=
  ⟨Nat.le_refl _, fun _ _ => rfl, (fun b blk hle hs => by
    exfalso
    rw [m.fresh b hle] at hs
    cases hs)⟩

theorem ROExt.trans {m1 m2 m3 : Mem} (h12 : ROExt m1 m2) (h23 : ROExt m2 m3) : ROExt m1 m3 := by
  refine ⟨Nat.le_trans h12.1 h23.1, ?_, ?_⟩
  · intro b hb
    rw [h23.2.1 b (Nat.lt_of_lt_of_le hb h12.1), h12.2.1 b hb]
  · intro b blk hle hs
    by_cases hm2 : b < m2.nextBlock
    · rw [h23.2.1 b hm2] at hs
      exact h12.2.2 b blk hle hs
    · exact h23.2.2 b blk (Nat.le_of_not_lt hm2) hs

theorem ROExt.of_strLit {m m' : Mem} {bid : BlockId} {base : UInt64} {str : String}
    (hsz : str.utf8ByteSize + 1 < ptrDiffLimit)
    (halloc : m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m')) :
    ROExt m m' := by
  have hm' : m' = (m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)).2 :=
    (congrArg Prod.snd halloc).symm
  subst hm'
  refine ⟨Nat.le_succ _, ?_, ?_⟩
  · intro b hb
    exact alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hb)
  · intro b blk hle hs
    by_cases heq : b = m.nextBlock
    · subst b
      rw [alloc_blocks_eq] at hs
      cases hs
      exact ⟨rfl, rfl⟩
    · rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ heq, m.fresh b hle] at hs
      cases hs

/-- Continuation stack block list across all enclosing blocks and call frames. -/
def contStackBlks : Cont → List BlockId
  | .stop _ => []
  | .stmts _ k | .loop _ _ _ _ k | .switchCont k => contStackBlks k
  | .blockEnd _ blks k => blks ++ contStackBlks k
  | .callFrame _ blks _ _ _ _ k => blks ++ contStackBlks k

/-- All blocks below `m0.nextBlock` are untouched; every live stack block above `m0.nextBlock`
belongs to `localBlks`; any other block above `m0.nextBlock` is a read-only global (string literal). -/
def LocalFrameMem (m0 m : Mem) (localBlks : List BlockId) : Prop :=
  m0.nextBlock ≤ m.nextBlock ∧
  (∀ b, b < m0.nextBlock → m.blocks b = m0.blocks b) ∧
  localBlks.Nodup ∧
  (∀ b, b ∈ localBlks → m0.nextBlock ≤ b ∧ ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) ∧
  (∀ b blk, m0.nextBlock ≤ b → m.blocks b = some blk →
    (blk.kind = .stack ∧ b ∈ localBlks) ∨ (blk.kind = .global ∧ blk.perm = .ro))

theorem LocalFrameMem.init (m0 : Mem) : LocalFrameMem m0 m0 [] := by
  refine ⟨Nat.le_refl _, fun _ _ => rfl, List.nodup_nil, (fun _ h => by cases h), fun b blk hle hs => ?_⟩
  rw [m0.fresh b hle] at hs
  cases hs

theorem LocalFrameMem.alloc_stack {m0 m m' : Mem} {blks : List BlockId}
    {sz al : Nat} {ba : UInt64} {init : Nat → MemByte}
    {h1 : sz < ptrDiffLimit} {h2 : 0 < al} {h3 : ba.toNat % al = 0} {bid : BlockId}
    (hf : LocalFrameMem m0 m blks)
    (ha : m.alloc sz al .rw .stack ba init h1 h2 h3 = (bid, m')) :
    LocalFrameMem m0 m' (bid :: blks) := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst ha).symm
  have hm' : m' = (m.alloc sz al .rw .stack ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  subst bid hm'
  have hnot : m.nextBlock ∉ blks := fun hmem => by
    obtain ⟨_, blk, hb, _⟩ := hf.2.2.2.1 m.nextBlock hmem
    have hlt := lt_nextBlock_of_some hb
    exact Nat.lt_irrefl _ hlt
  refine ⟨Nat.le_trans hf.1 (Nat.le_succ _), ?_, List.nodup_cons.mpr ⟨hnot, hf.2.2.1⟩, ?_, ?_⟩
  · intro b hb
    have hltm : b < m.nextBlock := Nat.lt_of_lt_of_le hb hf.1
    rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hltm), hf.2.1 b hb]
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hmem
    · exact ⟨hf.1, _, alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, rfl⟩
    · obtain ⟨hge, blk, hblk, hk⟩ := hf.2.2.2.1 b hmem
      have hlt := lt_nextBlock_of_some hblk
      exact ⟨hge, blk, by rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hlt)]; exact hblk, hk⟩
  · intro b blk hle hs
    by_cases heq : b = m.nextBlock
    · subst b
      rw [alloc_blocks_eq] at hs
      cases hs
      exact Or.inl ⟨rfl, .head _⟩
    · rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ heq] at hs
      rcases hf.2.2.2.2 b blk hle hs with ⟨hk, hmem⟩ | hro
      · exact Or.inl ⟨hk, .tail _ hmem⟩
      · exact Or.inr hro

theorem LocalFrameMem.write_stack {m0 m m' : Mem} {blks : List BlockId}
    {b : BlockId} {off : Int64} {bs : List MemByte} {blk : Block}
    (hf : LocalFrameMem m0 m blks) (hmem : b ∈ blks)
    (hb : m.blocks b = some blk) (hwr : m.writeBytes b off bs = some m') :
    LocalFrameMem m0 m' blks := by
  obtain ⟨hbge, blk0, hb0, hk0⟩ := hf.2.2.2.1 b hmem
  rw [hb] at hb0
  cases hb0
  refine ⟨by rw [writeBytes_nextBlock hwr]; exact hf.1, ?_, hf.2.2.1, ?_, ?_⟩
  · intro x hx
    have hne : x ≠ b := Nat.ne_of_lt (Nat.lt_of_lt_of_le hx hbge)
    rw [writeBytes_blocks_ne hwr hne, hf.2.1 x hx]
  · intro x hx
    by_cases hxb : x = b
    · subst x
      exact ⟨hbge, _, writeBytes_blocks_eq hb hwr, hk0⟩
    · rw [writeBytes_blocks_ne hwr hxb]
      exact hf.2.2.2.1 x hx
  · intro x blk' hx hs
    by_cases hxb : x = b
    · subst x
      rw [writeBytes_blocks_eq hb hwr] at hs
      cases hs
      exact Or.inl ⟨hk0, hmem⟩
    · rw [writeBytes_blocks_ne hwr hxb] at hs
      exact hf.2.2.2.2 x blk' hx hs

theorem LocalFrameMem.of_strLit {m0 m m' : Mem} {blks : List BlockId}
    {bid : BlockId} {base : UInt64} {str : String}
    (hf : LocalFrameMem m0 m blks)
    (hsz : str.utf8ByteSize + 1 < ptrDiffLimit)
    (ha : m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m')) :
    LocalFrameMem m0 m' blks := by
  have hm' : m' = (m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)).2 :=
    (congrArg Prod.snd ha).symm
  subst hm'
  refine ⟨Nat.le_trans hf.1 (Nat.le_succ _), ?_, hf.2.2.1, ?_, ?_⟩
  · intro b hb
    have hltm : b < m.nextBlock := Nat.lt_of_lt_of_le hb hf.1
    rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hltm), hf.2.1 b hb]
  · intro b hmem
    obtain ⟨hge, blk, hblk, hk⟩ := hf.2.2.2.1 b hmem
    have hlt := lt_nextBlock_of_some hblk
    exact ⟨hge, blk, by rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hlt)]; exact hblk, hk⟩
  · intro b blk hle hs
    by_cases heq : b = m.nextBlock
    · subst b
      rw [alloc_blocks_eq] at hs
      cases hs
      exact Or.inr ⟨rfl, rfl⟩
    · rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ heq] at hs
      exact hf.2.2.2.2 b blk hle hs

theorem LocalFrameMem.of_roExt {m0 m m' : Mem} {blks : List BlockId}
    (hf : LocalFrameMem m0 m blks) (hro : ROExt m m') :
    LocalFrameMem m0 m' blks := by
  refine ⟨Nat.le_trans hf.1 hro.1, ?_, hf.2.2.1, ?_, ?_⟩
  · intro b hb
    rw [hro.2.1 b (Nat.lt_of_lt_of_le hb hf.1), hf.2.1 b hb]
  · intro b hmem
    obtain ⟨hge, blk, hblk, hk⟩ := hf.2.2.2.1 b hmem
    exact ⟨hge, blk, by rw [hro.2.1 b (lt_nextBlock_of_some hblk)]; exact hblk, hk⟩
  · intro b blk hle hs
    by_cases hm : b < m.nextBlock
    · rw [hro.2.1 b hm] at hs
      exact hf.2.2.2.2 b blk hle hs
    · exact Or.inr (hro.2.2 b blk (Nat.le_of_not_lt hm) hs)

theorem LocalFrameMem.freeStack_sub {m0 m : Mem} {drop keep : List BlockId}
    (hf : LocalFrameMem m0 m (drop ++ keep)) :
    LocalFrameMem m0 (m.freeStack drop) keep := by
  have hnodup := List.nodup_append.mp hf.2.2.1
  refine ⟨hf.1, ?_, hnodup.2.1, ?_, ?_⟩
  · intro b hb
    have hnot : b ∉ drop := fun hmem => by
      have hge := (hf.2.2.2.1 b (List.mem_append_left _ hmem)).1
      exact Nat.not_lt_of_le hge hb
    rw [freeStack_blocks_not_mem _ _ hnot, hf.2.1 b hb]
  · intro b hb
    have hnot : b ∉ drop := fun hd => hnodup.2.2 b hd b hb rfl
    obtain ⟨hge, blk, hblk, hk⟩ := hf.2.2.2.1 b (List.mem_append_right _ hb)
    exact ⟨hge, blk, by rw [freeStack_blocks_not_mem _ _ hnot]; exact hblk, hk⟩
  · intro b blk hle hs
    by_cases hd : b ∈ drop
    · obtain ⟨_, blk0, hb0, hk0⟩ := hf.2.2.2.1 b (List.mem_append_left _ hd)
      rw [freeStack_blocks_mem_stack m drop hd hb0 hk0] at hs
      cases hs
    · rw [freeStack_blocks_not_mem _ _ hd] at hs
      rcases hf.2.2.2.2 b blk hle hs with ⟨hk, hmem⟩ | hro
      · rcases List.mem_append.mp hmem with h1 | h2
        · exact False.elim (hd h1)
        · exact Or.inl ⟨hk, h2⟩
      · exact Or.inr hro

theorem LocalFrameMem.to_roExt {m0 m : Mem} (hf : LocalFrameMem m0 m []) : ROExt m0 m := by
  refine ⟨hf.1, hf.2.1, ?_⟩
  intro b blk hle hs
  rcases hf.2.2.2.2 b blk hle hs with ⟨_, hmem⟩ | hro
  · cases hmem
  · exact hro

end C99.Proof
