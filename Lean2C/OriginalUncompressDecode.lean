import Lean2C.OriginalUncompressTable
import ZlibF.Proof.«inflate.c.register-frame»
import ZlibF.Proof.«inflate.c.header-default»

/-! Streaming inflate modes when the output supplied by uncompress2_z is full. -/
namespace Lean2C.OriginalUncompress.Refill
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs
set_option autoImplicit false

def NoRoom (l : IL) : Prop := l.left = 0 ∧ l.out_ = 0

/-- Both executions agree from every zero-capacity checkpoint, and every
returning or leaving execution preserves that checkpoint's output counts. -/
structure AtZero {α : Type} (k : Nat) (p : BPtr) (x : X α) : Prop where
  same : ∀ l h, NoRoom l → runX x (registers p l) (heap k p h) =
    mapped (fun (v, l') => (v, registers p l')) (heap k p) (runX x l h)
  counts : RegisterFrame NoRoom x

private theorem ofIndependent {α : Type} {k : Nat} {p : BPtr} {x : X α}
    (eqv : Independent k p x) (counts : RegisterFrame NoRoom x) : AtZero k p x :=
  ⟨fun l h _ => eqv l h, counts⟩

private theorem value {α : Type} (k : Nat) (p : BPtr) (v : α) : AtZero k p (pure v) :=
  ⟨fun _ _ _ => rfl, registerFrame_pure _ _⟩

private theorem exit {α : Type} (k : Nat) (p : BPtr) (e : Ex) : AtZero k p (throw e : X α) :=
  ⟨fun _ _ _ => rfl, registerFrame_throw _ _⟩

private theorem seq {α β : Type} {k : Nat} {p : BPtr} {a : X α} {f : α → X β}
    (first : AtZero k p a) (next : ∀ v, AtZero k p (f v)) : AtZero k p (a >>= f) := by
  refine ⟨?_, registerFrame_bind first.counts (fun v => (next v).counts)⟩
  intro l h zero
  rw [runX_bind, runX_bind, first.same l h zero]
  rcases stage : runX a l h with err | ⟨⟨res, regs⟩, H⟩
  · rfl
  · cases res with
    | error e => rfl
    | ok v => exact (next v).same regs H (first.counts _ _ _ _ _ zero stage)

private theorem inspect {α : Type} {k : Nat} {p : BPtr} {f : IL → X α}
    (same : ∀ l, NoRoom l → f (registers p l) = f l)
    (rest : ∀ l, NoRoom l → AtZero k p (f l)) : AtZero k p ((get : X IL) >>= f) := by
  refine ⟨?_, registerFrame_get_bind (fun l zero => (rest l zero).counts)⟩
  intro l h zero
  simp only [runX_bind, runX_get, same l zero]
  exact (rest l zero).same l h zero

private theorem update {k : Nat} {p : BPtr} (f : IL → IL)
    (commute : ∀ l, f (registers p l) = registers p (f l))
    (counts : ∀ l, NoRoom l → NoRoom (f l)) : AtZero k p (modify f) := by
  refine ⟨?_, registerFrame_modify _ f counts⟩
  intro l h _
  rw [runX_modify, runX_modify, commute]; rfl

private theorem liftM {α : Type} {k : Nat} {p : BPtr} {m : M α}
    (commute : ∀ h, m (heap k p h) = mapped id (heap k p) (m h)) : AtZero k p (monadLift m) :=
  ofIndependent (lift_eq commute) (registerFrame_lift _ _)

private theorem readState (k : Nat) (p : BPtr) (st : InflateStatePtr) : AtZero k p (monadLift (ldInflateState st)) :=
  ofIndependent (decoder_state k p st) (registerFrame_lift _ _)

private theorem stateWrite (k : Nat) (p : BPtr) (st : InflateStatePtr) (f : InflateState → InflateState) (h : Heap) :
    wrS st f (heap k p h) = mapped id (heap k p) (wrS st f h) := by
  rcases st with _ | ⟨⟨i⟩⟩
  · rfl
  · simp only [wrI_eq, heap]
    cases h.istates i <;> rfl

private theorem writeState (k : Nat) (p : BPtr) (st : InflateStatePtr) (f : InflateState → InflateState) :
    AtZero k p (monadLift (wrS st f)) := liftM (stateWrite k p st f)

private theorem writeStreamPair {k : Nat} {p : BPtr} (f g : ZStream → ZStream)
    (commute : ∀ z, g {z with next_out := p} = {(f z) with next_out := p}) (h : Heap) :
    wrZ (some (.tab k)) g (heap k p h) = mapped id (heap k p) (wrZ (some (.tab k)) f h) := by
  simp only [wrZ_eq, ZStreamRef.get, ZStreamRef.put, heap, mapped]
  cases live : h.streams k <;> simp [Except.map, live, upd_upd, commute]

private theorem writeStream {k : Nat} {p : BPtr} (f : ZStream → ZStream)
    (commute : ∀ z, f {z with next_out := p} = {(f z) with next_out := p}) :
    ∀ h, wrZ (some (.tab k)) f (heap k p h) = mapped id (heap k p) (wrZ (some (.tab k)) f h) :=
  writeStreamPair (k := k) f f commute

private theorem errorMode {k : Nat} {p : BPtr} {c : Ctx} (stream : c.strm = some (.tab k)) (msg : String) :
    AtZero k p (monadLift (badMode c msg)) := by
  apply liftM
  unfold badMode
  apply memBind
  · rw [stream]
    change ∀ h, (Zlib.Zutil.strLit msg >>= fun q => wrZ (some (.tab k)) (fun z => {z with msg := q})) _ = _
    apply memBind
    · intro h
      unfold Zlib.Zutil.strLit strLitRef
      cases strIndex msg <;> rfl
    · exact fun _ => writeStream _ (by intro; rfl)
  · exact fun _ => stateWrite k p _ _

private theorem bits (k : Nat) (p : BPtr) (n : UInt32) : AtZero k p (BITS n) := by
  apply ofIndependent (extract_bits k p n)
  unfold BITS
  register_frame_source <;> assumption

private theorem drop (k : Nat) (p : BPtr) (n : UInt32) : AtZero k p (DROPBITS n) := by
  constructor
  · intro l h _
    by_cases small : n < 64 <;>
      simp [DROPBITS, runX_bind, runX_get, runX_lift, registers, shr64, small, runX_set, pure_app, mapped, Except.map, ub]
  · unfold DROPBITS
    register_frame_source <;> assumption

private theorem need (k : Nat) (p : BPtr) (n : UInt32) : AtZero k p (NEEDBITS n) := by
  apply ofIndependent (need_bits k p n)
  unfold NEEDBITS PULLBYTE absorbInputByte
  register_frame_source <;> assumption

private theorem root (k : Nat) (p : BPtr) (c : Ctx) (dist : Bool) : AtZero k p (lookup1 c dist) := by
  apply ofIndependent (lookup_root k p c dist)
  unfold lookup1 lookupRoot BITS PULLBYTE absorbInputByte
  register_frame_source <;> assumption

private theorem link (k : Nat) (p : BPtr) (c : Ctx) (dist : Bool) : AtZero k p (lookup2 c dist) := by
  apply ofIndependent (lookup_link k p c dist)
  unfold lookup2 lookupLink BITS PULLBYTE absorbInputByte
  register_frame_source <;> assumption

private theorem checked (k : Nat) (p : BPtr) (v : Int) : AtZero k p (monadLift (chkI32 v)) := by
  apply liftM
  intro h; unfold chkI32; split <;> rfl

private theorem mode (k : Nat) (p : BPtr) (st : InflateStatePtr) (m : UInt32) : AtZero k p (monadLift (setMode st m)) :=
  writeState k p _ _

private theorem initBits (k : Nat) (p : BPtr) : AtZero k p INITBITS :=
  update _ (fun _ => rfl) (fun _ z => z)

private theorem branch {α : Type} {k : Nat} {p : BPtr} {test : Prop} [Decidable test] {a b : X α}
    (left : AtZero k p a) (right : AtZero k p b) :
    AtZero k p (if test then a else b) := by
  split <;> assumption

-- Follow monadic source statements. Register reads are permitted only if
-- replacing the output address leaves their continuation unchanged.
local macro "zero_step" : tactic =>
  `(tactic| first
    | with_reducible assumption
    | with_reducible exact value _ _ _
    | with_reducible exact exit _ _ _
    | with_reducible exact mode _ _ _ _
    | with_reducible exact writeState _ _ _ _
    | with_reducible exact readState _ _ _
    | with_reducible exact checked _ _ _
    | with_reducible exact initBits _ _
    | with_reducible exact drop _ _ _
    | with_reducible exact need _ _ _
    | with_reducible exact bits _ _ _
    | with_reducible exact root _ _ _ _
    | with_reducible exact link _ _ _ _
    | with_reducible exact errorMode (by assumption) _
    | with_reducible refine inspect (fun _ _ => rfl) (fun _ _ => ?_)
    | with_reducible apply branch
    | with_reducible refine seq ?_ (fun _ => ?_)
    | exact update _ (fun _ => rfl) (fun _ z => z))

local macro "zero_steps" : tactic => `(tactic| repeat' zero_step)

private theorem extra (k : Nat) (p : BPtr) (st : InflateStatePtr) (dist : Bool) : AtZero k p (addExtra st dist) := by
  unfold addExtra
  zero_steps

private theorem width (k : Nat) (p : BPtr) (st : InflateStatePtr) (last : Bool) :
    AtZero k p (consumeCodeWidth st last) := by
  unfold consumeCodeWidth
  zero_steps

private theorem matchWait (k : Nat) (p : BPtr) (c : Ctx) : AtZero k p (inflate_MATCH c) := by
  unfold inflate_MATCH
  apply inspect (by intro; intro; rfl)
  intro l z
  simp only [z.1, beq_self_eq_true, ↓reduceIte]
  exact exit k p _

theorem distance_extra (k : Nat) (p : BPtr) (c : Ctx) : AtZero k p (inflate_DISTEXT c) := by
  unfold inflate_DISTEXT
  exact seq (extra k p _ _) (fun _ => seq (mode k p _ _) (fun _ => matchWait k p c))

theorem distance (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (inflate_DIST c) := by
  have tails := distance_extra k p c
  have w1 := width k p c.st true
  have w2 := width k p c.st false
  unfold inflate_DIST
  zero_steps

theorem length_extra (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (inflate_LENEXT c) := by
  have dst := distance k p c stream
  have ext := extra k p c.st false
  unfold inflate_LENEXT
  zero_steps

/-- No output space rules out the fast call. Every remaining Huffman branch,
including invalid code, match, literal and end of block, commutes with changing
the destination address. Table indices, input and bit counts may be arbitrary. -/
theorem length (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (inflate_LEN c) := by
  have ext := length_extra k p c stream
  have w1 := width k p c.st true
  have w2 := width k p c.st false
  unfold inflate_LEN
  apply inspect (by intro; intro; rfl)
  intro l z
  simp only [z.1, show decide ((0 : UInt32) ≥ 258) = false from rfl, Bool.and_false,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  zero_steps

theorem trailer_length (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (inflate_LENGTH c) := by
  have doneCase : AtZero k p (inflate_DONE c) := by unfold inflate_DONE; zero_steps
  unfold inflate_LENGTH
  zero_steps

private theorem account (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (accountCheckedOutput c.strm c.st) := by
  unfold accountCheckedOutput
  rw [stream]
  apply seq (update _ (by intro; rfl) (by rintro l ⟨a, b⟩; simp [NoRoom, a, b]))
  intro _
  apply inspect
  · intro l z
    simp only [registers, z.2, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  intro l z
  simp only [z.2, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  apply seq (liftM (writeStream _ (by intro; rfl)))
  intro _
  apply seq (writeState k p _ _)
  intro _
  apply seq (readState k p _)
  intro _
  exact update _ (fun _ => rfl) (fun _ zero => ⟨zero.1, zero.1⟩)

theorem check (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) : AtZero k p (inflate_CHECK c) := by
  have counted := account k p c stream
  have tail := trailer_length k p c stream
  unfold inflate_CHECK
  zero_steps

private theorem byteAlign (k : Nat) (p : BPtr) : AtZero k p BYTEBITS := by
  constructor
  · intro l h _
    by_cases small : (l.bits &&& 7) < 64 <;>
      simp [BYTEBITS, runX_bind, runX_get, runX_lift, registers, shr64, small, runX_set, pure_app, mapped, Except.map, ub]
  · unfold BYTEBITS
    register_frame_source <;> assumption

private theorem copyStall (k : Nat) (p : BPtr) (st : InflateStatePtr) : AtZero k p (copyStoredInput st) := by
  have run (l : IL) (h : Heap) (full : l.left = 0) :
      runX (copyStoredInput st) l h = .ok ((.error Ex.leave, {l with copy := 0}), h) := by
    unfold copyStoredInput
    rw [runX_bind, runX_get]
    simp only [full]
    split <;> rename_i cap
    all_goals split
    all_goals simp_all [runX_bind, runX_set, runX_throw]
  constructor
  · intro l h z
    rw [run l h z.1, run (registers p l) _ z.1]; rfl
  · intro l h res regs H z executed
    rw [run l h z.1] at executed; cases executed; exact z

theorem stored (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) : AtZero k p (inflate_STORED c) := by
  have align := byteAlign k p
  have stall := copyStall k p c.st
  unfold inflate_STORED inflate_COPY_ inflate_COPY
  zero_steps

private theorem fixedTables (k : Nat) (p : BPtr) (st : InflateStatePtr) :
    AtZero k p (monadLift (Zlib.Inftrees.inflate_fixed st)) := by
  apply liftM
  intro h
  rcases st with _ | ⟨⟨i⟩⟩
  · rfl
  · cases live : h.istates i with
    | none => simp [Zlib.Inftrees.inflate_fixed, bind_app, ldI_eq, heap, live, mapped, Except.map]
    | some s =>
      have base := Zlib.Inftrees.Proofs.inflate_fixed_ok live
      have changed := Zlib.Inftrees.Proofs.inflate_fixed_ok (h := heap k p h) (show (heap k p h).istates i = some s from live)
      change Zlib.Inftrees.inflate_fixed _ _ = _ at base changed
      rw [base, changed]; rfl

theorem block_type (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) : AtZero k p (inflate_TYPEDO c) := by
  have align := byteAlign k p
  have fixed := fixedTables k p c.st
  unfold inflate_TYPEDO
  zero_steps
  all_goals split <;> zero_steps

theorem type (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) : AtZero k p (inflate_TYPE c) := by
  have tail := block_type k p c stream
  unfold inflate_TYPE
  zero_steps

private theorem readField {α : Type} (k : Nat) (p : BPtr) (st : InflateStatePtr) (f : InflateState → α) :
    AtZero k p (monadLift (rdS st f)) := by
  apply liftM
  intro h
  rcases st with _ | ⟨⟨i⟩⟩
  · rfl
  · simp only [rdI_eq, heap]
    cases h.istates i <;> rfl

private theorem checksum {k : Nat} {p : BPtr} (st : InflateStatePtr) (v : UInt64) (h : Heap) :
    storeChecksum (some (.tab k)) st v (heap k p h) = mapped id (heap k p) (storeChecksum (some (.tab k)) st v h) := by
  unfold storeChecksum
  exact memBind (stateWrite k p st _) (fun _ => writeStream _ (fun _ => rfl)) h

private theorem startAdler (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (monadLift (startDataCheck c.strm c.st false)) := by
  apply liftM
  unfold startDataCheck
  simp only [Bool.false_eq_true, ↓reduceIte, stream, Zlib.Adler32.Proofs.adler32_null_init]
  exact memBind (fun _ => rfl) (fun _ => checksum _ _)

private theorem restore (k : Nat) (p : BPtr) (st : InflateStatePtr) :
    AtZero k p (RESTORE (some (.tab k)) st) := by
  constructor
  · intro l h _
    let put (l : IL) (z : ZStream) := {z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_}
    let save (s : InflateState) := {s with hold := l.hold, bits := l.bits}
    have first := writeStreamPair (k := k) (p := p) (put l) (put (registers p l)) (fun _ => rfl) h
    simp only [RESTORE, runX_bind, runX_get, runX_lift]
    rw [first]
    rcases wrZ (some (.tab k)) (put l) h with e | ⟨_, H⟩
    · rfl
    · simpa only [runX_lift, mapped, Except.map, id_eq, registers, save] using
        (lift_eq (stateWrite k p st save) l H)
  · unfold RESTORE
    register_frame_source

private theorem dictMode (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (inflate_DICT c) := by
  have restored : AtZero k p (RESTORE c.strm c.st) := stream ▸ restore k p c.st
  have count : AtZero k p (countDictionaryInput c.strm) := by
    unfold countDictionaryInput
    apply inspect (by intro; intro; rfl)
    intro l _
    rw [stream]
    exact liftM (writeStream _ (fun _ => rfl))
  have field := readField k p c.st (·.havedict)
  have start := startAdler k p c stream
  have tail := type k p c stream
  unfold inflate_DICT
  zero_steps

theorem dictionary (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (inflate_DICTID c) := by
  have dict := dictMode k p c stream
  have store : AtZero k p (storeDictId c.strm c.st) := by
    unfold storeDictId
    apply inspect (by intro; intro; rfl)
    intro l _
    rw [stream]
    exact liftM (checksum _ _)
  unfold inflate_DICTID
  zero_steps

private theorem headerChecks (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (headZlibChecks c) := by
  have start := startAdler k p c stream
  have limit (v : UInt32) : AtZero k p (monadLift (shl32 1 v)) := by
    apply liftM; intro h; unfold shl32; split <;> rfl
  unfold headZlibChecks invalidHeaderWord windowBitsFromHeader setWindowLimit
  zero_steps <;> exact limit _

private theorem headerCut {c : Ctx} {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} {l regs : IL} {v : Except Ex Unit} (E : Env c h r i z s)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (header : s.head = none)
    (read : runX (NEEDBITS 16) l h = .ok ((v, regs), h)) :
    runX (inflate_HEAD c) l h = runX (NEEDBITS 16 >>= fun _ => headZlibChecks c) l h := by
  have wrap0 : (s.wrap == 0) = false := by rcases wrap with w | w <;> rw [w] <;> rfl
  have gzip : ((s.wrap &&& 2) != 0) = false := by rcases wrap with w | w <;> rw [w] <;> rfl
  unfold inflate_HEAD
  rw [runX_bind, runX_rdS E]
  simp only [wrap0, Bool.false_eq_true, ↓reduceIte, runX_bind, read]
  cases v with
  | error e => rfl
  | ok u =>
    simp only [runX_ldS E, runX_get, gzip, Bool.false_and, Bool.false_eq_true, ↓reduceIte, updateHeader,
      header, bne_self_eq_false, runX_bind, runX_pure, headZlibChecks, invalidHeaderWord]

/-- All zlib header outcomes for the wrapper's real stream. This includes
short or malformed headers, preset dictionary selection and accepted headers. -/
theorem header {c : Ctx} {h : Heap} {k i : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {l : IL} (p : BPtr) (E : Env c h (.tab k) i z s) (input : BitInv h l bs)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (noHeader : s.head = none) (zero : NoRoom l) :
    runX (inflate_HEAD c) (registers p l) (heap k p h) =
      mapped (fun (v, regs) => (v, registers p regs)) (heap k p) (runX (inflate_HEAD c) l h) ∧
    ∀ v regs after, runX (inflate_HEAD c) l h = .ok ((v, regs), after) → NoRoom regs := by
  have stream : h.streams k = some z := E.hz
  have changed : Env c (heap k p h) (.tab k) i {z with next_out := p} s :=
    ⟨E.strm, E.st, by simp [heap, ZStreamRef.get, stream], E.hs⟩
  obtain ⟨v, regs, _, read, _⟩ := NEEDBITS_run input 16 (by decide)
  have alternate := need_bits k p 16 l h
  rw [read] at alternate
  have other : runX (NEEDBITS 16) (registers p l) (heap k p h) =
      .ok ((v, registers p regs), heap k p h) := alternate
  rw [headerCut E wrap noHeader read, headerCut changed wrap noHeader other]
  have body := seq (need k p 16) (fun _ => headerChecks k p c E.strm)
  exact ⟨body.same l h zero, fun _ _ _ run => body.counts _ _ _ _ _ zero run⟩

private theorem whileBreak {k : Nat} {p : BPtr} {test body : X Bool}
    (ct : AtZero k p test) (bt : AtZero k p body) : AtZero k p (xwhileBrk test body) :=
  ⟨xloop_on (fun l _ => NoRoom l) ct.same bt.same ct.counts bt.counts,
    registerFrame_xwhileBrk ct.counts bt.counts⟩

private theorem whileLoop {k : Nat} {p : BPtr} {test : X Bool} {body : X Unit}
    (ct : AtZero k p test) (bt : AtZero k p body) : AtZero k p (xwhile test body) :=
  whileBreak ct (seq bt (fun _ => value k p false))

private theorem append (k : Nat) (p : BPtr) (st : InflateStatePtr) (v : UInt16) :
    AtZero k p (appendLength st v) := by
  unfold appendLength
  apply seq (readField k p _ _)
  intro _
  apply seq (writeState k p _ _)
  intro _
  apply seq (liftM (Tables.word_add k p _ _))
  intro _
  exact liftM (Tables.word_store k p _ _)

private theorem repeatLength (k : Nat) (p : BPtr) (st : InflateStatePtr) : AtZero k p (repeatCodeLength st) := by
  unfold repeatCodeLength
  apply whileLoop
  · constructor
    · intro l h _; rfl
    · register_frame_source <;> assumption
  · apply inspect (by intro; intro; rfl)
    exact fun _ _ => append k p st _

private theorem ordered {k : Nat} {p : BPtr} (st : InflateStatePtr) {x : X UInt16} (value : AtZero k p x) :
    AtZero k p (storeOrderedLength st x) := by
  unfold storeOrderedLength withLengthOrder
  apply seq (readState k p _)
  intro s
  apply seq (writeState k p _ _)
  intro _
  have atIndex : AtZero k p (monadLift (orderAt s.have)) := by
    apply liftM; intro h; unfold orderAt; cases order[s.have.toNat]? <;> rfl
  apply seq atIndex
  intro _
  apply seq value
  intro _
  apply seq (liftM (Tables.word_add k p _ _))
  intro _
  exact liftM (Tables.word_store k p _ _)

private theorem startTable (k : Nat) (p : BPtr) (st : InflateStatePtr) :
    AtZero k p (monadLift (startLengthTable st)) := by
  apply liftM; unfold startLengthTable
  exact memBind (stateWrite k p _ _) (fun _ => memBind (stateWrite k p _ _) (fun _ => stateWrite k p _ _))

private theorem fromMemory {α : Type} {k : Nat} {p : BPtr} {m : M α}
    (eqv : Memory k p m) : AtZero k p (monadLift m) := liftM eqv

local macro "dynamic_steps" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact readField _ _ _ _
    | with_reducible exact startTable _ _ _
    | with_reducible exact repeatLength _ _ _
    | with_reducible exact append _ _ _ _
    | with_reducible exact fromMemory (Tables.word_add _ _ _ _)
    | with_reducible exact fromMemory (Tables.word_index _ _ _ _)
    | with_reducible exact fromMemory (Tables.build _ _ _ _ _ _ _ _)
    | with_reducible apply ordered
    | with_reducible apply whileLoop
    | with_reducible apply whileBreak
    | zero_step)

private theorem codeLengths (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (inflate_CODELENS c) := by
  have tail := length k p c stream
  have startLen : AtZero k p (inflate_LEN_ c) := by unfold inflate_LEN_; zero_steps
  have widths : AtZero k p (readCodeLengths c.st (lookup1 c false) NEEDBITS (badMode c "invalid bit length repeat")) := by
    unfold readCodeLengths appendCurrentCode setPreviousLength setRepeatCount
    dynamic_steps
  unfold inflate_CODELENS
  dynamic_steps

private theorem lengthWidths (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (inflate_LENLENS c) := by
  have codes := codeLengths k p c stream
  unfold inflate_LENLENS
  dynamic_steps

/-- All code lengths and repeat counts, the three Huffman table calls and
the subsequent slow length/distance path from a dynamic block header. -/
theorem dynamic (k : Nat) (p : BPtr) (c : Ctx) (stream : c.strm = some (.tab k)) :
    AtZero k p (inflate_TABLE c) := by
  have lengths := lengthWidths k p c stream
  unfold inflate_TABLE
  dynamic_steps

private theorem literalWait (k : Nat) (p : BPtr) (c : Ctx) : AtZero k p (inflate_LIT c) := by
  constructor
  · intro l h z
    rw [inflate_LIT_full c l h z.1, inflate_LIT_full c (registers p l) _ z.1]
    rfl
  · intro l h v regs after z run
    rw [inflate_LIT_full c l h z.1] at run
    cases run; exact z

private theorem onRuns {k : Nat} {p : BPtr} {x : X Unit} (proof : AtZero k p x) (l : IL) (h : Heap) (zero : NoRoom l) :
    runX x (registers p l) (heap k p h) = mapped (fun (v, regs) => (v, registers p regs)) (heap k p) (runX x l h) ∧
    ∀ v regs after, runX x l h = .ok ((v, regs), after) → NoRoom regs :=
  ⟨proof.same l h zero, fun _ _ _ run => proof.counts _ _ _ _ _ zero run⟩

/-- Once the decoder is at or past DICTID it has passed every gzip-only case
label. Compare the two executions of the actual switch on the live state. -/
theorem dispatch_after_header {c : Ctx} {h : Heap} {k i : Nat} {z : ZStream} {s : InflateState}
    (p : BPtr) (l : IL) (E : Env c h (.tab k) i z s) (passed : DICTID ≤ s.mode) (zero : NoRoom l) :
    runX (inflate_dispatch c) (registers p l) (heap k p h) =
      mapped (fun (v, regs) => (v, registers p regs)) (heap k p) (runX (inflate_dispatch c) l h) ∧
    ∀ v regs after, runX (inflate_dispatch c) l h = .ok ((v, regs), after) → NoRoom regs := by
  have live : h.streams k = some z := E.hz
  have changed : Env c (heap k p h) (.tab k) i {z with next_out := p} s :=
    ⟨E.strm, E.st, by simp [heap, ZStreamRef.get, live], E.hs⟩
  have past {m : UInt32} (earlier : m < DICTID) : (s.mode == m) = false :=
    beq_false_of_ne (fun e => by
      rw [← e] at earlier
      exact Nat.not_lt_of_ge (UInt32.le_iff_toNat_le.mp passed) (UInt32.lt_iff_toNat_lt.mp earlier))
  unfold inflate_dispatch
  simp only [runX_bind, runX_rdS E, runX_rdS changed, past (m := HEAD) (by decide),
    past (m := FLAGS) (by decide), past (m := TIME) (by decide), past (m := OS) (by decide),
    past (m := EXLEN) (by decide), past (m := EXTRA) (by decide), past (m := NAME) (by decide),
    past (m := COMMENT) (by decide), past (m := HCRC) (by decide), Bool.false_eq_true, ↓reduceIte]
  refine onRuns ?_ l h zero
  have stalled := copyStall k p c.st
  have copy : AtZero k p (inflate_COPY c) := by unfold inflate_COPY; zero_steps
  have copyStart : AtZero k p (inflate_COPY_ c) := by unfold inflate_COPY_; zero_steps
  have len := length k p c E.strm
  have lenStart : AtZero k p (inflate_LEN_ c) := by unfold inflate_LEN_; zero_steps
  have doneCase : AtZero k p (inflate_DONE c) := by unfold inflate_DONE; zero_steps
  repeat' first
    | with_reducible exact dictionary k p c E.strm
    | with_reducible exact dictMode k p c E.strm
    | with_reducible exact type k p c E.strm
    | with_reducible exact block_type k p c E.strm
    | with_reducible exact stored k p c E.strm
    | with_reducible exact dynamic k p c E.strm
    | with_reducible exact lengthWidths k p c E.strm
    | with_reducible exact codeLengths k p c E.strm
    | with_reducible exact length_extra k p c E.strm
    | with_reducible exact distance k p c E.strm
    | with_reducible exact distance_extra k p c
    | with_reducible exact literalWait k p c
    | with_reducible exact matchWait k p c
    | with_reducible exact check k p c E.strm
    | with_reducible exact trailer_length k p c E.strm
    | zero_step

#print axioms dispatch_after_header
#print axioms dynamic
#print axioms header
#print axioms dictionary
#print axioms stored
#print axioms block_type
#print axioms check
#print axioms length
#print axioms trailer_length
end Lean2C.OriginalUncompress.Refill
