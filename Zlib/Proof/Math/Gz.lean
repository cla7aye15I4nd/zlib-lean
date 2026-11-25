/-!
# Pure Arithmetic, Mode-Parser, Decimal-Buffer, Counter & Window Math (`Zlib.Proof.Math.Gz`)

Heap-free mathematical library supporting safety and bounded-termination proofs for
`gzlib.c`, `gzread.c`, `gzwrite.c`, `gzclose.c`, `inflate.c`, and `infback.c`.

Covers:
- Constants (`GZBUFSIZE`, `GZ_OFF_MAX`, `GZ_FD_PATH_CAP`, `MAX_WBITS`, `MIN_WBITS`)
- `gz_open` signed-char mode-parser byte classification & accumulator bounds
- Decimal digit-count bounds, UTF-8 byte NUL-freedom, and `gzdopen` `<fd:%d>` buffer fit
- 32/64-bit counter accounting (`difference_cast`, `charge_rebase`), multiplication overflow
  detection (`gzfread`/`gzfwrite`), `gzbuffer` shift guard, `gzseek64` / `gz_room` /
  `gz_vacate` signed-offset bounds
- `inflate` / `infback` `windowBits` / `wrap` decoding bounds, window ring-buffer invariant
  (`WindowInv`, `updateWindowStep`), dictionary/match copy bounds, and `inflatePrime` bounds
-/

namespace Zlib.Proof.Math

/-! ## 1. Gzip & Inflate Constants -/

def GZBUFSIZE : Nat := 8192
def GZ_NONE : Int := 0
def GZ_READ : Int := 7247
def GZ_WRITE : Int := 31153
def GZ_APPEND : Int := 1
def GZ_LOOK : Int := 0
def GZ_COPY : Int := 1
def GZ_GZIP : Int := 2
def GZ_OFF_MAX : Int := 2 ^ 63 - 1
def GZ_FD_PATH_CAP : Nat := 7 + 3 * 4
def MIN_WBITS : Nat := 8
def MAX_WBITS : Nat := 15
def MAX_WINDOW_SIZE : Nat := 2 ^ MAX_WBITS

theorem gz_bufsize_eq : GZBUFSIZE = 8192 := rfl
theorem gz_off_max_eq : GZ_OFF_MAX = 2 ^ 63 - 1 := rfl
theorem gz_off_max_nonneg : 0 ≤ GZ_OFF_MAX := by decide
theorem gz_off_max_lt_pow63 : GZ_OFF_MAX < 2 ^ 63 := by decide
theorem gz_fd_path_cap_eq : GZ_FD_PATH_CAP = 19 := rfl
theorem max_window_size_eq : MAX_WINDOW_SIZE = 32768 := rfl

/-! ## 2. Gzip Mode Parser Byte Classification & Accumulator Bounds (`gz_open`) -/

inductive GzMode where
  | none
  | read
  | write
  | append
  deriving DecidableEq, Repr

def GzMode.toInt : GzMode → Int
  | .none => GZ_NONE
  | .read => GZ_READ
  | .write => GZ_WRITE
  | .append => GZ_APPEND

inductive ModeAction where
  | level (value : Int32)
  | mode (value : GzMode)
  | bad
  | binary
  | cloexec
  | exclusive
  | strategy (value : Nat)
  | gzipOnly
  | nonblock
  | transparent
  | ignore
  deriving DecidableEq

inductive SemanticAction where
  | level (value : Int)
  | mode (value : GzMode)
  | bad
  | strategy (value : Nat)
  | direct (value : Int)
  | ignore
  deriving DecidableEq

/-- Exact byte classification of `gz_open` in `Zlib/Gzlib.lean`, including LP64 signed `char`
to `int` conversion (`b.toInt8.toInt32`). -/
def sourceAction (b : UInt8) : ModeAction :=
  let c : Int32 := b.toInt8.toInt32
  if c ≥ 48 && c ≤ 57 then .level (c - 48)
  else if c == 114 then .mode .read
  else if c == 119 then .mode .write
  else if c == 97 then .mode .append
  else if c == 43 then .bad
  else if c == 98 then .binary
  else if c == 101 then .cloexec
  else if c == 120 then .exclusive
  else if c == 102 then .strategy 1
  else if c == 104 then .strategy 2
  else if c == 82 then .strategy 3
  else if c == 70 then .strategy 4
  else if c == 71 then .gzipOnly
  else if c == 78 then .nonblock
  else if c == 84 then .transparent
  else .ignore

def semanticAction : ModeAction → SemanticAction
  | .level v => .level v.toInt
  | .mode m => .mode m
  | .bad => .bad
  | .strategy s => .strategy s
  | .gzipOnly => .direct (-1)
  | .transparent => .direct 1
  | _ => .ignore

def charAction (c : Char) : SemanticAction :=
  if '0' ≤ c ∧ c ≤ '9' then .level (c.toNat - '0'.toNat : Nat)
  else if c = 'r' then .mode .read
  else if c = 'w' then .mode .write
  else if c = 'a' then .mode .append
  else if c = '+' then .bad
  else if c = 'f' then .strategy 1
  else if c = 'h' then .strategy 2
  else if c = 'R' then .strategy 3
  else if c = 'F' then .strategy 4
  else if c = 'G' then .direct (-1)
  else if c = 'T' then .direct 1
  else .ignore

/-- Exhaustive agreement between signed-`char` source dispatch and character dispatch over `UInt8`. -/
theorem sourceAction_semantic (b : UInt8) :
    semanticAction (sourceAction b) = charAction (Char.ofNat b.toNat) := by
  have complete : ∀ j : Fin 256,
      semanticAction (sourceAction (UInt8.ofNat j.val)) =
        charAction (Char.ofNat (UInt8.ofNat j.val).toNat) := by decide +kernel
  have h := complete ⟨b.toNat, b.toNat_lt⟩
  simpa using h

/-- `'+'` (byte `43`) is the unique byte selecting `.bad`. -/
theorem sourceAction_bad (b : UInt8) : sourceAction b = .bad ↔ b = 43 := by
  have complete : ∀ j : Fin 256,
      sourceAction (UInt8.ofNat j.val) = .bad ↔ UInt8.ofNat j.val = 43 := by
    decide +kernel
  simpa using complete ⟨b.toNat, b.toNat_lt⟩

/-- High-bit bytes (`≥ 128`) become negative `Int8` values and always classify as `.ignore`. -/
theorem sourceAction_highBit_ignore (b : UInt8) (hb : 128 ≤ b.toNat) :
    sourceAction b = .ignore := by
  have complete : ∀ j : Fin 256,
      128 ≤ j.val → sourceAction (UInt8.ofNat j.val) = .ignore := by decide +kernel
  simpa using complete ⟨b.toNat, b.toNat_lt⟩ hb

private def modeActionLevelStrategyOk (a : ModeAction) : Bool :=
  match a with
  | .level w => decide (0 ≤ w.toInt ∧ w.toInt ≤ 9)
  | .strategy s => decide (1 ≤ s ∧ s ≤ 4)
  | _ => true

private theorem sourceAction_action_ok (b : UInt8) :
    modeActionLevelStrategyOk (sourceAction b) = true := by
  have complete : ∀ j : Fin 256,
      modeActionLevelStrategyOk (sourceAction (UInt8.ofNat j.val)) = true := by decide +kernel
  simpa using complete ⟨b.toNat, b.toNat_lt⟩

/-- Any digit byte produces a compression level in `[0, 9]`. -/
theorem sourceAction_level_range (b : UInt8) (v : Int32) (h : sourceAction b = .level v) :
    0 ≤ v.toInt ∧ v.toInt ≤ 9 := by
  have ok := sourceAction_action_ok b
  rw [h] at ok
  simpa [modeActionLevelStrategyOk] using ok

/-- Any strategy byte produces a strategy code in `[1, 4]`. -/
theorem sourceAction_strategy_range (b : UInt8) (s : Nat) (h : sourceAction b = .strategy s) :
    1 ≤ s ∧ s ≤ 4 := by
  have ok := sourceAction_action_ok b
  rw [h] at ok
  simpa [modeActionLevelStrategyOk] using ok

/-- Accumulator fields updated by the `while (*mode)` loop in `gz_open`. -/
structure ModeAcc where
  mode : GzMode := .none
  level : Int := -1
  strategy : Nat := 0
  direct : Int := 0
  exclusive : Bool := false
  bad : Bool := false
  deriving DecidableEq, Repr

def ModeAcc.init : ModeAcc := {}

def ModeAcc.step (acc : ModeAcc) (b : UInt8) : ModeAcc :=
  match sourceAction b with
  | .level v => { acc with level := v.toInt }
  | .mode m => { acc with mode := m }
  | .bad => { acc with bad := true }
  | .strategy s => { acc with strategy := s }
  | .exclusive => { acc with exclusive := true }
  | .gzipOnly => { acc with direct := -1 }
  | .transparent => { acc with direct := 1 }
  | .binary | .cloexec | .nonblock | .ignore => acc

def ModeAcc.ValidBounds (acc : ModeAcc) : Prop :=
  (-1 ≤ acc.level ∧ acc.level ≤ 9) ∧
  (acc.strategy ≤ 4) ∧
  (-1 ≤ acc.direct ∧ acc.direct ≤ 1)

theorem modeAcc_init_valid : ModeAcc.ValidBounds ModeAcc.init := by
  simp [ModeAcc.ValidBounds, ModeAcc.init]

theorem modeAcc_step_valid (acc : ModeAcc) (b : UInt8) (hv : acc.ValidBounds) :
    (acc.step b).ValidBounds := by
  rcases hv with ⟨⟨hl1, hl2⟩, hs, ⟨hd1, hd2⟩⟩
  cases ha : sourceAction b with
  | level v =>
    have hr := sourceAction_level_range b v ha
    simp only [ModeAcc.step, ModeAcc.ValidBounds, ha]
    exact ⟨⟨by omega, hr.2⟩, hs, ⟨hd1, hd2⟩⟩
  | mode m => simpa [ModeAcc.step, ModeAcc.ValidBounds, ha] using And.intro (And.intro hl1 hl2) (And.intro hs (And.intro hd1 hd2))
  | bad => simpa [ModeAcc.step, ModeAcc.ValidBounds, ha] using And.intro (And.intro hl1 hl2) (And.intro hs (And.intro hd1 hd2))
  | strategy s =>
    have hr := sourceAction_strategy_range b s ha
    simpa [ModeAcc.step, ModeAcc.ValidBounds, ha] using And.intro (And.intro hl1 hl2) (And.intro hr.2 (And.intro hd1 hd2))
  | exclusive | binary | cloexec | nonblock | ignore =>
    simpa [ModeAcc.step, ModeAcc.ValidBounds, ha] using And.intro (And.intro hl1 hl2) (And.intro hs (And.intro hd1 hd2))
  | gzipOnly =>
    simp only [ModeAcc.step, ModeAcc.ValidBounds, ha]
    exact ⟨⟨hl1, hl2⟩, hs, by omega⟩
  | transparent =>
    simp only [ModeAcc.step, ModeAcc.ValidBounds, ha]
    exact ⟨⟨hl1, hl2⟩, hs, by omega⟩

theorem modeAcc_fold_valid (bs : List UInt8) (acc : ModeAcc) (hv : acc.ValidBounds) :
    (bs.foldl ModeAcc.step acc).ValidBounds := by
  induction bs generalizing acc with
  | nil => exact hv
  | cons b rest ih => exact ih (acc.step b) (modeAcc_step_valid acc b hv)

theorem modeAcc_step_bad (acc : ModeAcc) (b : UInt8) :
    (acc.step b).bad = (acc.bad || decide (b = 43)) := by
  unfold ModeAcc.step
  cases ha : sourceAction b with
  | bad =>
    have hb : b = 43 := (sourceAction_bad b).mp ha
    simp [hb]
  | level _ | mode _ | binary | cloexec | exclusive | strategy _
  | gzipOnly | nonblock | transparent | ignore =>
    have hne : b ≠ 43 := fun h => by
      have hb : sourceAction b = .bad := (sourceAction_bad b).mpr h
      rw [hb] at ha
      cases ha
    simp [hne]

theorem modeAcc_fold_bad (bs : List UInt8) (acc : ModeAcc) :
    (bs.foldl ModeAcc.step acc).bad = (acc.bad || decide ((43 : UInt8) ∈ bs)) := by
  induction bs generalizing acc with
  | nil => simp
  | cons b rest ih =>
    rw [List.foldl_cons, ih, modeAcc_step_bad]
    cases acc.bad <;> by_cases h43 : b = 43 <;> simp [h43, List.mem_cons, eq_comm]

/-! ## 3. Decimal Text, Digit-Length Bounds, & `gzdopen` Buffer Fit -/

private theorem byteArray_toList_loop (bytes : ByteArray) :
    ∀ k i acc, bytes.size - i = k →
      ByteArray.toList.loop bytes i acc = acc.reverse ++ bytes.data.toList.drop i := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro i acc hk
    rw [ByteArray.toList.loop]
    split
    · rename_i hi
      rw [ih (bytes.size - (i + 1)) (by omega) (i + 1) (bytes.get! i :: acc) rfl]
      have hli : i < bytes.data.toList.length := by simpa using hi
      rw [List.drop_eq_getElem_cons hli]
      have hget : bytes.get! i = bytes.data[i] := by
        simp [ByteArray.get!, getElem!_pos bytes.data i (by simpa using hi)]
      simp [List.reverse_cons, List.append_assoc, hget]
    · rename_i hi
      have hli : bytes.data.toList.length ≤ i := by simpa using Nat.le_of_not_lt hi
      simp [List.drop_eq_nil_of_le hli]

theorem byteArray_toList (bytes : ByteArray) : bytes.toList = bytes.data.toList := by
  simpa [ByteArray.toList] using byteArray_toList_loop bytes bytes.size 0 [] (by simp)

theorem byteArray_toList_append (a b : ByteArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  rw [byteArray_toList, ByteArray.toList_data_append, ← byteArray_toList, ← byteArray_toList]

theorem string_utf8_append (a b : String) :
    (a ++ b).toUTF8.toList = a.toUTF8.toList ++ b.toUTF8.toList := by
  simp only [String.toUTF8, String.toByteArray_append, byteArray_toList_append]

private theorem decimal_digit_nonzero (n : Nat) (hn : n < 10) :
    (0 : UInt8) ∉ ([Nat.digitChar n].utf8Encode).data.toList := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
      n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem decimal_digits_nonzero (fuel n : Nat) (ds : List Char)
    (nonzero : (0 : UInt8) ∉ ds.utf8Encode.data.toList) :
    (0 : UInt8) ∉ (Nat.toDigitsCore 10 fuel n ds).utf8Encode.data.toList := by
  induction fuel generalizing n ds with
  | zero => simpa [Nat.toDigitsCore] using nonzero
  | succ fuel ih =>
    have digit := decimal_digit_nonzero (n % 10) (Nat.mod_lt n (by decide))
    have hcons : (0 : UInt8) ∉ (Nat.digitChar (n % 10) :: ds).utf8Encode.data.toList := by
      rw [List.utf8Encode_cons, ByteArray.data_append, Array.toList_append]
      simpa only [List.mem_append, not_or] using And.intro digit nonzero
    rw [Nat.toDigitsCore]
    split
    · exact hcons
    · exact ih (n / 10) _ hcons

theorem integer_decimal_nonzero (z : Int) :
    (0 : UInt8) ∉ (toString z).toUTF8.data.toList := by
  change (0 : UInt8) ∉ (Int.repr z).toByteArray.data.toList
  cases z with
  | ofNat n =>
    simpa [Int.repr, Nat.repr, Nat.toDigits] using
      decimal_digits_nonzero (n + 1) n [] (by simp)
  | negSucc n =>
    have digits := decimal_digits_nonzero (n + 1 + 1) (n + 1) [] (by simp)
    simp only [Int.repr, Nat.repr, Nat.toDigits, String.toByteArray_append,
      ByteArray.data_append, Array.toList_append, String.toByteArray_ofList,
      List.mem_append, not_or]
    exact ⟨by decide, digits⟩

private theorem toDigitsCore_length (fuel n : Nat) (ds : List Char) (h : n < 10 ^ fuel)
    (hfuel : 1 ≤ fuel) :
    (Nat.toDigitsCore 10 fuel n ds).length ≤ ds.length + fuel := by
  induction fuel generalizing n ds with
  | zero => omega
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    split
    · simp
    · rename_i hge
      have hdiv : n / 10 < 10 ^ fuel := by
        rw [Nat.pow_succ] at h
        omega
      cases fuel with
      | zero =>
        simp at hdiv
        omega
      | succ f' =>
        have hrec := ih (n / 10) (Nat.digitChar (n % 10) :: ds) hdiv (by omega)
        simp only [List.length_cons] at hrec
        omega

private theorem toDigitsCore_eq_of_lt (n : Nat) :
    ∀ fuel1 fuel2 ds, n < 10 ^ fuel1 → n < 10 ^ fuel2 → 1 ≤ fuel1 → 1 ≤ fuel2 →
      Nat.toDigitsCore 10 fuel1 n ds = Nat.toDigitsCore 10 fuel2 n ds := by
  intro fuel1
  induction fuel1 generalizing n with
  | zero => intro fuel2 ds _ _ h1 _; omega
  | succ f1 ih =>
    intro fuel2 ds hlt1 hlt2 hf1 hf2
    cases fuel2 with
    | zero => omega
    | succ f2 =>
      rw [Nat.toDigitsCore, Nat.toDigitsCore]
      split
      · rfl
      · rename_i hge
        have hdiv1 : n / 10 < 10 ^ f1 := by rw [Nat.pow_succ] at hlt1; omega
        have hdiv2 : n / 10 < 10 ^ f2 := by rw [Nat.pow_succ] at hlt2; omega
        cases f1 with
        | zero => simp at hdiv1; omega
        | succ f1' =>
          cases f2 with
          | zero => simp at hdiv2; omega
          | succ f2' => exact ih (n / 10) (f2' + 1) _ hdiv1 hdiv2 (by omega) (by omega)

theorem nat_toDigits_length_le {n k : Nat} (hk : 1 ≤ k) (hn : n < 10 ^ k) :
    (Nat.toDigits 10 n).length ≤ k := by
  unfold Nat.toDigits
  have hpow : n < 10 ^ (n + 1) := by
    have hlt : n < 2 ^ n := Nat.lt_two_pow_self
    have hle1 : 2 ^ n ≤ 10 ^ n := Nat.pow_le_pow_left (by decide) n
    have hle2 : 10 ^ n ≤ 10 ^ (n + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [toDigitsCore_eq_of_lt n (n + 1) k [] hpow hn (by omega) hk]
  simpa using toDigitsCore_length k n [] hn hk

theorem int32_decimal_digits_length_le_10 {n : Nat} (hn : n < 2 ^ 31) :
    (Nat.toDigits 10 n).length ≤ 10 :=
  nat_toDigits_length_le (by decide) (Nat.lt_of_lt_of_le hn (by decide : 2 ^ 31 ≤ 10 ^ 10))

theorem digit_encode (c : Char) (hc : c.isDigit) :
    String.utf8EncodeChar c = [c.toNat.toUInt8] := by
  have hd := Char.isDigit_iff_toNat.mp hc
  have hs : c.utf8Size = 1 := by
    simp [Char.utf8Size, UInt32.le_iff_toNat_le]
    simp at hd
    omega
  exact String.utf8EncodeChar_eq_singleton hs

theorem digits_utf8 (cs : List Char) (hc : ∀ c, c ∈ cs → c.isDigit) :
    (String.ofList cs).toUTF8.toList = cs.map (fun c => c.toNat.toUInt8) := by
  simp only [String.toUTF8, String.toByteArray_ofList, List.utf8Encode, byteArray_toList,
    List.toList_data_toByteArray]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, digit_encode c (hc c (by simp)), List.cons_append,
      List.nil_append, List.map_cons]
    rw [ih (fun d hd => hc d (by simp [hd]))]

theorem nat_toString_utf8 (n : Nat) :
    (toString n).toUTF8.toList = (Nat.toDigits 10 n).map (fun c => c.toNat.toUInt8) := by
  rw [Nat.toString_eq_ofList_toDigits]
  exact digits_utf8 _ (fun _ hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)

theorem nat_toString_utf8ByteSize_le {n k : Nat} (hk : 1 ≤ k) (hn : n < 10 ^ k) :
    (toString n).utf8ByteSize ≤ k := by
  have hlen : (toString n).utf8ByteSize = (toString n).toUTF8.toList.length := by
    rw [byteArray_toList]
    change (toString n).toUTF8.data.size = (toString n).toUTF8.data.toList.length
    rw [Array.length_toList]
  rw [hlen, nat_toString_utf8, List.length_map]
  exact nat_toDigits_length_le hk hn

/-- `gzdopen`'s `7 + 3 * sizeof(int) = 19` byte allocation always fits `"<fd:%d>"` + NUL
for any `0 ≤ fd < 2^31`. -/
theorem gzdopen_fd_path_fits {fd : Nat} (hfd : fd < 2 ^ 31) :
    ("<fd:" ++ toString fd ++ ">").utf8ByteSize + 1 ≤ GZ_FD_PATH_CAP := by
  have hs1 : ("<fd:" ++ toString fd ++ ">").utf8ByteSize =
      "<fd:".utf8ByteSize + (toString fd).utf8ByteSize + ">".utf8ByteSize := by
    simp [String.utf8ByteSize_append, Nat.add_assoc]
  have hlen := nat_toString_utf8ByteSize_le (n := fd) (k := 10) (by decide)
    (Nat.lt_of_lt_of_le hfd (by decide))
  have h4 : "<fd:".utf8ByteSize = 4 := by decide
  have h1 : ">".utf8ByteSize = 1 := by decide
  rw [hs1, h4, h1, gz_fd_path_cap_eq]
  omega

/-! ## 4. Counter Accounting, Overflow Guards & Offset Bounds (`gz*`, `inflate`) -/

/-- A bounded 32-bit remaining count gives an exact 64-bit difference. -/
theorem difference_cast (base remaining : UInt32) (bound : remaining.toNat ≤ base.toNat) :
    (base - remaining).toUInt64 + remaining.toUInt64 = base.toUInt64 := by
  have numeric : (base - remaining).toNat + remaining.toNat = base.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr bound), Nat.sub_add_cancel bound]
  have words := congrArg UInt64.ofNat numeric
  simpa only [UInt64.ofNat_add, UInt64.ofNat_uInt32ToNat] using words

/-- Charging a produced prefix and rebasing to the remaining count conserves the total-plus-base
ledger, even when the 64-bit total wraps. -/
theorem charge_rebase (total : UInt64) (base remaining : UInt32)
    (bound : remaining.toNat ≤ base.toNat) :
    total + (base - remaining).toUInt64 + remaining.toUInt64 = total + base.toUInt64 := by
  rw [UInt64.add_assoc, difference_cast base remaining bound]

/-- `gzbuffer`'s `(size << 1) < size` check ensures `2 * size < 2^32`. -/
theorem gzbuffer_shift_guard (sz : UInt32) (h : ¬ (sz <<< 1 < sz)) :
    sz.toNat < 2 ^ 31 ∧ 2 * sz.toNat < 2 ^ 32 := by
  have hle : sz.toNat ≤ (sz <<< 1).toNat := by
    rcases Nat.lt_or_ge (sz <<< 1).toNat sz.toNat with hlt | hge
    · exact False.elim (h (UInt32.lt_iff_toNat_lt.mpr hlt))
    · exact hge
  have hsh : (sz <<< 1).toNat = (sz.toNat * 2) % 2 ^ 32 := by
    change ((sz.toBitVec <<< (1 % 32)).toNat) = (sz.toNat * 2) % 2 ^ 32
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [hsh] at hle
  have hlt32 : sz.toNat < 2 ^ 32 := sz.toBitVec.isLt
  have hlt31 : sz.toNat < 2 ^ 31 := by
    rcases Nat.lt_or_ge sz.toNat (2 ^ 31) with hlt | hge
    · exact hlt
    · have hmod : (sz.toNat * 2) % 2 ^ 32 = sz.toNat * 2 - 2 ^ 32 := by omega
      omega
  exact ⟨hlt31, by omega⟩

/-- `gzfread`/`gzfwrite`'s `size && len / size != nitems` guard detects 64-bit product overflow. -/
theorem gzfwrite_mul_overflow_guard (size nitems : UInt64) (hsz : size ≠ 0) :
    (nitems * size) / size = nitems ↔ nitems.toNat * size.toNat < 2 ^ 64 := by
  have hspos : 0 < size.toNat := by
    rcases Nat.eq_zero_or_pos size.toNat with h0 | hpos
    · exfalso
      apply hsz
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      exact h0
    · exact hpos
  constructor
  · intro hdiv
    have hnat : ((nitems * size) / size).toNat = nitems.toNat := congrArg UInt64.toNat hdiv
    rw [UInt64.toNat_div] at hnat
    have hmul_le : ((nitems * size).toNat / size.toNat) * size.toNat ≤ (nitems * size).toNat :=
      Nat.div_mul_le_self _ _
    rw [hnat] at hmul_le
    exact Nat.lt_of_le_of_lt hmul_le (nitems * size).toBitVec.isLt
  · intro hlt
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    change ((nitems * size) / size).toNat = nitems.toNat
    rw [UInt64.toNat_div, UInt64.toNat_mul, Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel _ hspos]

/-- `gzseek64`'s overflow guards ensure `0 ≤ pos + offset ≤ GZ_OFF_MAX`. -/
theorem gzseek_pos_add_bounds {pos offset : Int}
    (hpos0 : 0 ≤ pos) (hposMax : pos ≤ GZ_OFF_MAX)
    (hoffMax : offset ≤ GZ_OFF_MAX)
    (hguard1 : pos > 0 → offset ≤ GZ_OFF_MAX - pos)
    (hguard2 : -pos ≤ offset) :
    0 ≤ pos + offset ∧ pos + offset ≤ GZ_OFF_MAX := by
  by_cases hp : pos > 0
  · have := hguard1 hp
    omega
  · have : pos = 0 := by omega
    subst this
    omega

/-- `gzseek64`'s `state->x.pos < 0` guard prevents overflow in both `GZ_OFF_MAX + state->x.pos`
and `pos - state->x.pos`. -/
theorem gzseek_delta_bounds {pos xpos : Int}
    (hpos0 : 0 ≤ pos) (hposMax : pos ≤ GZ_OFF_MAX)
    (hxMin : -(2 ^ 63 : Int) ≤ xpos) (hxLe : xpos ≤ pos)
    (hguard : xpos < 0 → pos ≤ GZ_OFF_MAX + xpos) :
    (xpos < 0 → 0 ≤ GZ_OFF_MAX + xpos ∧ GZ_OFF_MAX + xpos < GZ_OFF_MAX) ∧
    (0 ≤ pos - xpos ∧ pos - xpos ≤ GZ_OFF_MAX) := by
  have hz := gz_off_max_eq
  constructor
  · intro hx; omega
  · by_cases hx : xpos < 0
    · have := hguard hx; omega
    · omega

/-- `gz_room` bounds: returning `n` guarantees `state->x.pos + n ≤ GZ_OFF_MAX` and `n < 2^32`. -/
theorem gz_room_bounds {xpos : Int} {max : Nat}
    (hx0 : 0 ≤ xpos) (hxMax : xpos ≤ GZ_OFF_MAX) (hmax : max < 2 ^ 32) :
    let n : Nat := if xpos > 0 ∧ GZ_OFF_MAX - xpos < (max : Int)
                   then (GZ_OFF_MAX - xpos).toNat else max
    n ≤ max ∧ n < 2 ^ 32 ∧ xpos + (n : Int) ≤ GZ_OFF_MAX := by
  dsimp only
  split
  · next h =>
    have hsub : 0 ≤ GZ_OFF_MAX - xpos := by omega
    have hlt : GZ_OFF_MAX - xpos < (max : Int) := h.2
    omega
  · next h =>
    have hge : xpos = 0 ∨ (max : Int) ≤ GZ_OFF_MAX - xpos := by
      by_cases hp : xpos > 0
      · right
        by_cases hle : (max : Int) ≤ GZ_OFF_MAX - xpos
        · exact hle
        · exact False.elim (h ⟨hp, by omega⟩)
      · left; omega
    rcases hge with rfl | hle
    · have hmax_le : (max : Int) ≤ GZ_OFF_MAX := by
        rw [gz_off_max_eq]
        have : (2 ^ 32 : Int) ≤ 2 ^ 63 - 1 := by decide
        omega
      omega
    · omega

/-- In `gzvprintf`, once vacated (`inOff + avail ≤ size`), `0 < len < size` keeps total
buffered input within `2 * size`. -/
theorem gz_vacate_vprintf_bounds {inOff avail len size : Nat}
    (hvac : inOff + avail ≤ size) (hlen : len < size) :
    inOff + avail + len < 2 * size := by
  omega

/-! ## 5. `inflate` / `infback` Window, `windowBits`, `wrap` & Bit-Buffer Bounds -/

def inflateWrapOf (wb : Int) : Int :=
  if wb < 0 then 0 else wb / 16 + 5

def inflateNormBits (wb : Int) : Int :=
  if wb < 0 then -wb else if wb < 48 then wb % 16 else wb

/-- `inflateReset2` bounds: when `windowBits` passes the `-15` and `8..15` guards,
`wrap` never overflows `Int32` and normalized `windowBits` is `0` or in `[8, 15]`. -/
theorem inflateReset2_bounds {wb : Int}
    (hmin : -(2 ^ 31 : Int) ≤ wb) (hmax : wb < 2 ^ 31)
    (_hneg : wb < 0 → -15 ≤ wb)
    (hchk : inflateNormBits wb = 0 ∨ (8 ≤ inflateNormBits wb ∧ inflateNormBits wb ≤ 15)) :
    0 ≤ inflateWrapOf wb ∧ inflateWrapOf wb < 2 ^ 31 ∧
    (inflateNormBits wb = 0 ∨ (8 ≤ inflateNormBits wb ∧ inflateNormBits wb ≤ 15)) := by
  refine ⟨?_, ?_, hchk⟩
  · unfold inflateWrapOf
    split <;> omega
  · unfold inflateWrapOf
    split
    · decide
    · omega

theorem inflate_wsize_bounds {wbits : Nat} (hlo : 8 ≤ wbits) (hhi : wbits ≤ 15) :
    256 ≤ 2 ^ wbits ∧ 2 ^ wbits ≤ 32768 ∧ 2 ^ wbits < 2 ^ 32 := by
  have h1 : 2 ^ 8 ≤ 2 ^ wbits := Nat.pow_le_pow_right (by decide) hlo
  have h2 : 2 ^ wbits ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hhi
  have h8 : 2 ^ 8 = 256 := rfl
  have h15 : 2 ^ 15 = 32768 := rfl
  have h32 : 32768 < 2 ^ 32 := by decide
  omega

/-- Ring-buffer invariant for `inflate_state`: `0 < wsize`, `wnext < wsize`, `whave ≤ wsize`,
and `whave` equals `wnext` until the window wraps for the first time. -/
def WindowInv (wsize whave wnext : Nat) : Prop :=
  0 < wsize ∧ wnext < wsize ∧ whave ≤ wsize ∧ (whave < wsize → whave = wnext)

theorem windowInv_init {wsize : Nat} (hw : 0 < wsize) : WindowInv wsize 0 0 :=
  ⟨hw, hw, Nat.zero_le _, fun _ => rfl⟩

/-- Pure model of `(whave', wnext')` after `updatewindow` in `Zlib/Inflate.lean`. -/
def updateWindowStep (wsize whave wnext copy : Nat) : Nat × Nat :=
  if copy ≥ wsize then
    (wsize, 0)
  else
    let dist := min (wsize - wnext) copy
    let rem := copy - dist
    if rem > 0 then
      (wsize, rem)
    else
      let wnext' := if wnext + dist == wsize then 0 else wnext + dist
      let whave' := if whave < wsize then whave + dist else whave
      (whave', wnext')

/-- `updatewindow` preserves `WindowInv` and all intermediate slice bounds stay within `wsize`. -/
theorem updateWindowStep_spec {wsize whave wnext copy : Nat} (hinv : WindowInv wsize whave wnext) :
    let dist := min (wsize - wnext) copy
    let rem := copy - dist
    (copy < wsize → wnext + dist ≤ wsize ∧ rem < wsize) ∧
    WindowInv wsize (updateWindowStep wsize whave wnext copy).1
                    (updateWindowStep wsize whave wnext copy).2 := by
  rcases hinv with ⟨hw, hwn, hwh, hprefix⟩
  constructor
  · intro hcopy
    have hd1 : min (wsize - wnext) copy ≤ wsize - wnext := Nat.min_le_left _ _
    have hrem : copy - min (wsize - wnext) copy < wsize := by omega
    exact ⟨by omega, hrem⟩
  · unfold updateWindowStep
    split
    · exact ⟨hw, hw, Nat.le_refl _, fun hlt => False.elim (Nat.lt_irrefl _ hlt)⟩
    · next hcopy =>
      dsimp only
      have hcopy' : copy < wsize := Nat.lt_of_not_le hcopy
      have hd1 : min (wsize - wnext) copy ≤ wsize - wnext := Nat.min_le_left _ _
      have hd2 : min (wsize - wnext) copy ≤ copy := Nat.min_le_right _ _
      split
      · next hrem =>
        have hrem_lt : copy - min (wsize - wnext) copy < wsize := by omega
        exact ⟨hw, hrem_lt, Nat.le_refl _, fun hlt => False.elim (Nat.lt_irrefl _ hlt)⟩
      · next hrem =>
        have hrem0 : copy - min (wsize - wnext) copy = 0 := by omega
        have hle_w : wnext + min (wsize - wnext) copy ≤ wsize := by omega
        by_cases hwrap : wnext + min (wsize - wnext) copy = wsize
        · have hbeq : (wnext + min (wsize - wnext) copy == wsize) = true := beq_iff_eq.mpr hwrap
          simp only [hbeq, ↓reduceIte]
          by_cases hlt : whave < wsize
          · have heq := hprefix hlt
            have hsum : whave + min (wsize - wnext) copy = wsize := by omega
            rw [ite_eq_left hlt, hsum]
            exact ⟨hw, hw, Nat.le_refl _, fun h => False.elim (Nat.lt_irrefl _ h)⟩
          · have hweq : whave = wsize := by omega
            rw [ite_eq_right hlt, hweq]
            exact ⟨hw, hw, Nat.le_refl _, fun h => False.elim (Nat.lt_irrefl _ h)⟩
        · have hbeq : (wnext + min (wsize - wnext) copy == wsize) = false := beq_false_of_ne hwrap
          have hlt_w : wnext + min (wsize - wnext) copy < wsize := by omega
          simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
          by_cases hlt : whave < wsize
          · have heq := hprefix hlt
            have hsum : whave + min (wsize - wnext) copy < wsize := by omega
            rw [ite_eq_left hlt]
            exact ⟨hw, hlt_w, by omega, fun _ => by omega⟩
          · have hweq : whave = wsize := by omega
            rw [ite_eq_right hlt, hweq]
            exact ⟨hw, hlt_w, Nat.le_refl _, fun h => False.elim (Nat.lt_irrefl _ h)⟩

/-- `inflateGetDictionary` bounds: `wnext ≤ whave` and both copy ranges fit within `wsize`. -/
theorem windowInv_getDict_bounds {wsize whave wnext : Nat} (hinv : WindowInv wsize whave wnext) :
    wnext ≤ whave ∧ wnext + (whave - wnext) = whave ∧ whave ≤ wsize := by
  rcases hinv with ⟨_, hwn, hwh, hprefix⟩
  by_cases hlt : whave < wsize
  · have := hprefix hlt
    omega
  · omega

/-- Match-copy window slice bounds in `inflate`: copying `copy ≤ whave` bytes stays inside
`[0, wsize]`. -/
theorem windowInv_copy_bounds {wsize whave wnext copy : Nat}
    (hinv : WindowInv wsize whave wnext) (hcopy : copy ≤ whave) :
    (wnext < copy → whave = wsize ∧ copy - wnext ≤ wsize - wnext ∧
      (wsize - (copy - wnext)) + (copy - wnext) = wsize) ∧
    (copy ≤ wnext → (wnext - copy) + copy = wnext ∧ wnext ≤ wsize) := by
  rcases hinv with ⟨_, hwn, hwh, hprefix⟩
  constructor
  · intro hgt
    have hfull : whave = wsize := by
      rcases Nat.lt_or_eq_of_le hwh with hlt | hfull
      · have := hprefix hlt
        omega
      · exact hfull
    omega
  · intro hle
    omega

/-- `inflatePrime` bit-count and mask bounds: `0 < bits ≤ 16`, `stateBits + bits ≤ 32`. -/
theorem inflatePrime_bounds {bits stateBits : Int}
    (hlo : 0 < bits) (hhi : bits ≤ 16) (_hs0 : 0 ≤ stateBits) (hsum : stateBits + bits ≤ 32) :
    bits.toNat ≤ 16 ∧ 1 ≤ 2 ^ bits.toNat ∧ 2 ^ bits.toNat - 1 < 2 ^ 31 ∧
    stateBits.toNat < 32 ∧ stateBits.toNat + bits.toNat ≤ 32 := by
  have hb : bits.toNat ≤ 16 := by omega
  have hpow1 : 1 ≤ 2 ^ bits.toNat := Nat.one_le_two_pow
  have hpow16 : 2 ^ bits.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hb
  have h16_31 : 2 ^ 16 < 2 ^ 31 := by decide
  exact ⟨hb, hpow1, by omega, by omega, by omega⟩

end Zlib.Proof.Math
