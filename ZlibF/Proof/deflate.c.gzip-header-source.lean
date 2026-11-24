import ZlibF.Proof.«deflate.c.trailer-source»
import ZlibF.Proof.«deflate.c.base»
import ZlibF.Proof.«deflate.c.strategy-loop»

/-! The gzip header rereads its fields between successive byte writes. A write may
touch the pending buffer or the depth array inside a deflate record. Both preserve
the installed gzip header and the level and strategy used to compute XFL. -/

namespace Zlib.Deflate.HeaderSource
open C Zlib.Deflate Zlib.Deflate.Proofs Zlib.Deflate.Spec

private def keys (d : DeflateState) := (d.gzhead, d.level, d.strategy)
private def view (i : Nat) (h : Heap) := ((h.dstates i).map keys, h.gzheaders)
private abbrev Keeps (i : Nat) (op : M α) := Preserves (fun h h' => view i h' = view i h) op

private theorem bindKeeps {i : Nat} {op : M α} {next : α → M β}
    (first : Keeps i op) (rest : ∀ a, Keeps i (next a)) : Keeps i (op >>= next) :=
  Preserves.bind (R := fun h after => view i after = view i h) (fun x y => y.trans x) first rest

private theorem readKeeps (i : Nat) (p : DeflateStatePtr) : Keeps i (ldDeflateState p) := by
  intro h a after got
  unfold ldDeflateState at got
  repeat' first | split at got | contradiction | (cases got; rfl)

private theorem addKeeps (i : Nat) (p : BPtr) (n : Int) : Keeps i (p.add n) := by
  intro h a after got
  unfold Ptr.add at got
  repeat' first | split at got | contradiction | (cases got; rfl)

private theorem byteKeeps (i : Nat) (p : BPtr) (v : UInt8) : Keeps i (store8 p v) := by
  have frame (h : Heap) (b : BRef) (a : Array UInt8) (f : Array UInt8 → Array UInt8)
      (get : Space.get h b = some a) : view i (Space.modify h b f) = view i h := by
    rw [Space.modify_eq h b a f get]
    cases b with
    | dstate_depth j =>
      cases existsState : h.dstates j with
      | none => simp [Space.get, existsState] at get
      | some d =>
        rw [BRef.put_dstate_depth existsState]
        by_cases same : i = j
        · subst i; simp [view, keys, existsState]
        · simp [view, upd_ne _ _ _ _ same]
    | _ => rfl
  intro h a after got
  unfold store8 Ptr.store at got
  repeat' first | split at got | contradiction | (cases got; apply frame; assumption)

private theorem pendingKeeps (i : Nat) (s : DeflateStatePtr) :
    Keeps i (Zlib.Trees.md s (fun d => {d with pending := d.pending + 1})) := by
  intro h a after got
  cases s with
  | none => cases got
  | some ref =>
    obtain ⟨j⟩ := ref
    cases dj : h.dstates j with
    | none => simp [Zlib.Trees.md, ldD_eq, bind_app, dj] at got
    | some d =>
      simp only [Zlib.Trees.md, bind_app, ldDeflateState_tab dj, stD_eq, dj] at got
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj got)
      by_cases same : i = j
      · subst i; simp [view, setD, keys, dj]
      · simp [view, setD, upd_ne _ _ _ _ same]

private theorem byteFrame (i : Nat) (s : DeflateStatePtr) (v : UInt8) : Keeps i (put_byte s v) := by
  unfold put_byte Zlib.Trees.put_byte
  simp only [cdecl_eq, C.M_pure_bind]
  apply bindKeeps (readKeeps i s)
  intro d
  apply bindKeeps (addKeeps i _ _)
  intro p
  exact bindKeeps (pendingKeeps i s) fun _ => byteKeeps i p _

private theorem byteFields {i : Nat} {h after : Heap} {v : UInt8} {u : Unit} {d : DeflateState}
    (state : h.dstates i = some d) (wrote : put_byte (some (.tab i)) v h = .ok (u,after)) :
    ∃ d', after.dstates i = some d' ∧ d'.gzhead = d.gzhead ∧ d'.level = d.level ∧
      d'.strategy = d.strategy ∧ after.gzheaders = h.gzheaders := by
  have same := Prod.mk.inj (byteFrame i _ _ _ _ _ wrote)
  cases newState : after.dstates i with
  | none => simp [state, newState] at same
  | some new =>
    have data : keys new = keys d := by simpa [state, newState] using same.1
    exact ⟨new, rfl, (Prod.mk.inj data).1, (Prod.mk.inj (Prod.mk.inj data).2).1,
      (Prod.mk.inj (Prod.mk.inj data).2).2, same.2⟩

open Zlib.Crc32 (crc32_z)
def sourceGzip (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  let d ← ldDeflateState s
  -- the XFL byte: s->level == 9 ? 2 : (s->strategy >= Z_HUFFMAN_ONLY || s->level < 2 ? 4 : 0)
  if d.gzhead == none then
    put_byte s 0
    put_byte s 0
    put_byte s 0
    put_byte s 0
    put_byte s 0
    let d ← ldDeflateState s
    let xfl : UInt8 := if d.level == 9 then 2 else if d.strategy ≥ Z_HUFFMAN_ONLY || d.level < 2 then 4 else 0
    put_byte s xfl
    put_byte s OS_CODE.toUInt32.toUInt8
    wr s (fun d => { d with status := BUSY_STATE })
    -- Compression must start with an empty pending buffer
    flush_pending strm
    if (← rd s (·.pending)) != 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  else
    let gh ← ldGzHeader d.gzhead
    -- put_byte(s, (text ? 1 : 0) + (hcrc ? 2 : 0) + (extra == NULL ? 0 : 4) + (name == NULL ? 0 : 8) + (comment == NULL ? 0 : 16));
    -- (each term is a constant, so the sum is at most 31 and cannot overflow)
    put_byte s (((if gh.text != 0 then 1 else 0) + (if gh.hcrc != 0 then 2 else 0) +
      (if gh.extra == .null then 0 else 4) + (if gh.name == .null then 0 else 8) +
      (if gh.comment == .null then 0 else 16) : Nat).toUInt8)
    let gh ← ldGzHeader (← rd s (·.gzhead))
    put_byte s (gh.time &&& 0xff).toUInt8
    let gh ← ldGzHeader (← rd s (·.gzhead))
    put_byte s ((gh.time >>> 8) &&& 0xff).toUInt8
    let gh ← ldGzHeader (← rd s (·.gzhead))
    put_byte s ((gh.time >>> 16) &&& 0xff).toUInt8
    let gh ← ldGzHeader (← rd s (·.gzhead))
    put_byte s ((gh.time >>> 24) &&& 0xff).toUInt8
    let d ← ldDeflateState s
    let xfl : UInt8 := if d.level == 9 then 2 else if d.strategy ≥ Z_HUFFMAN_ONLY || d.level < 2 then 4 else 0
    put_byte s xfl
    let gh ← ldGzHeader (← rd s (·.gzhead))
    put_byte s (gh.os &&& 0xff).toUInt32.toUInt8
    let gh ← ldGzHeader (← rd s (·.gzhead))
    if gh.extra != .null then
      let gh ← ldGzHeader (← rd s (·.gzhead))
      put_byte s (gh.extra_len &&& 0xff).toUInt8
      let gh ← ldGzHeader (← rd s (·.gzhead))
      put_byte s ((gh.extra_len >>> 8) &&& 0xff).toUInt8
    let gh ← ldGzHeader (← rd s (·.gzhead))
    if gh.hcrc != 0 then
      -- strm->adler = crc32_z(strm->adler, s->pending_buf, s->pending);
      let d ← ldDeflateState s
      let a ← zrd strm (·.adler)
      let r ← crc32_z a d.pending_buf d.pending
      zwr strm (fun z => { z with adler := r })
    -- s->gzindex = 0; s->status = EXTRA_STATE;
    wr s (fun d => { d with gzindex := 0 })
    wr s (fun d => { d with status := EXTRA_STATE })
  k

def previousGzip (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  let d ← ldDeflateState s
  -- the XFL byte: s->level == 9 ? 2 : (s->strategy >= Z_HUFFMAN_ONLY || s->level < 2 ? 4 : 0)
  let xfl : UInt8 := if d.level == 9 then 2 else if d.strategy ≥ Z_HUFFMAN_ONLY || d.level < 2 then 4 else 0
  if d.gzhead == none then
    put_byte s 0
    put_byte s 0
    put_byte s 0
    put_byte s 0
    put_byte s 0
    put_byte s xfl
    put_byte s OS_CODE.toUInt32.toUInt8
    wr s (fun d => { d with status := BUSY_STATE })
    -- Compression must start with an empty pending buffer
    flush_pending strm
    if (← rd s (·.pending)) != 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  else
    let gh ← ldGzHeader d.gzhead
    -- put_byte(s, (text ? 1 : 0) + (hcrc ? 2 : 0) + (extra == NULL ? 0 : 4) + (name == NULL ? 0 : 8) + (comment == NULL ? 0 : 16));
    -- (each term is a constant, so the sum is at most 31 and cannot overflow)
    put_byte s (((if gh.text != 0 then 1 else 0) + (if gh.hcrc != 0 then 2 else 0) +
      (if gh.extra == .null then 0 else 4) + (if gh.name == .null then 0 else 8) +
      (if gh.comment == .null then 0 else 16) : Nat).toUInt8)
    put_byte s (gh.time &&& 0xff).toUInt8
    put_byte s ((gh.time >>> 8) &&& 0xff).toUInt8
    put_byte s ((gh.time >>> 16) &&& 0xff).toUInt8
    put_byte s ((gh.time >>> 24) &&& 0xff).toUInt8
    put_byte s xfl
    put_byte s (gh.os &&& 0xff).toUInt32.toUInt8
    if gh.extra != .null then
      put_byte s (gh.extra_len &&& 0xff).toUInt8
      put_byte s ((gh.extra_len >>> 8) &&& 0xff).toUInt8
    if gh.hcrc != 0 then
      -- strm->adler = crc32_z(strm->adler, s->pending_buf, s->pending);
      let d ← ldDeflateState s
      let a ← zrd strm (·.adler)
      let r ← crc32_z a d.pending_buf d.pending
      zwr strm (fun z => { z with adler := r })
    -- s->gzindex = 0; s->status = EXTRA_STATE;
    wr s (fun d => { d with gzindex := 0, status := EXTRA_STATE })
  k


private theorem index_status (st : DeflateStatePtr) (tail : M α) :
    (do wr st fun s => {s with gzindex := 0}
        wr st fun s => {s with status := EXTRA_STATE}
        tail) =
    (do wr st fun s => {s with gzindex := 0, status := EXTRA_STATE}
        tail) := by
  rw [← C.M_bind_assoc, StrategyLoop.wr_then_wr]

local macro "gzip_read" : tactic =>
  `(tactic| simp (config := {failIfUnchanged := false}) only
     [bind_app, ldD_eq, rdD_eq, ldGzHeader, GzHeaderRef.get,
      beq_iff_eq, Option.some.injEq, reduceCtorEq, ↓reduceIte, *])

local macro "gzip_write" : tactic =>
  `(tactic|
    (generalize hw : put_byte (some (.tab _)) _ _ = result
     cases result
     case error => rfl
     rename_i pair
     obtain ⟨u, after⟩ := pair
     obtain ⟨next, live, gz, level, strategy, headers⟩ :=
       byteFields (by assumption) hw
     gzip_read))

theorem gzip_eq (p : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) :
    sourceGzip p s k = previousGzip p s k := by
  funext h
  cases s with
  | none => rfl
  | some ref =>
    obtain ⟨i⟩ := ref
    cases live : h.dstates i with
    | none => simp only [sourceGzip, previousGzip, bind_app, ldD_eq, live]
    | some d =>
      simp only [sourceGzip, previousGzip, index_status, bind_app, ldDeflateState_tab live]
      cases installed : d.gzhead with
      | none =>
        gzip_read
        iterate 5 gzip_write
        all_goals rfl
      | some hdr =>
        obtain ⟨j⟩ := hdr
        gzip_read
        cases header : h.gzheaders j with
        | none => rfl
        | some g =>
          gzip_read
          iterate 7 gzip_write
          by_cases extra : (g.extra != .null) = true
          · gzip_read
            iterate 2 gzip_write
            all_goals rfl
          · gzip_read
end Zlib.Deflate.HeaderSource
