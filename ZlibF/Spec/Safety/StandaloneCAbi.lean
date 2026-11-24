import ZlibF.Spec.Common.Checksums
import ZlibF.Spec.Common.Inflate.InflateFast
import ZlibF.Spec.Safety.Inflate.Table
import ZlibF.Spec.Safety.GzCalls

/-!
# Standalone C-ABI companion safety goals

Safety contracts stated directly over the exact-shape `*_c` companion implementations whose C99
emission achieves byte-identical object compilation (`make binary` and `-arch x86_64`) without
modifying the existing verified Lean definitions.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs

/-- `uLong adler32_z(uLong adler, const Bytef *buf, z_size_t len)` (exact-shape C-ABI companion).
**Safety of `adler32_z_c`**: on a readable buffer of `len` bytes, or `NULL` with `len = 0`
(`AdlerBufferBytes`), the call returns and the heap is unchanged. -/
def Goal.adler32_z_c_safety : Prop :=
  ∀ (h : Heap) (seed : UInt64) (pointer : BPtr) (length : UInt64) (bytes : List UInt8),
    AdlerBufferBytes h pointer length.toNat bytes →
    ∃ value, C.run (Zlib.Adler32.adler32_z_c seed pointer length) h = .ok (value, h)

/-- `gzFile gzopen(const char *, const char *)` (exact-shape C-ABI companion).
**Safety of `gzopen_c`**: as `Goal.gzopen_safety` (`GzOpenSafe`). -/
def Goal.gzopen_c_safety : Prop :=
  GzOpenSafe Zlib.Gzlib.gzopen_c

/-- `z_off64_t gzseek64(gzFile, z_off64_t, int)` (exact-shape C-ABI companion).
**Safety of `gzseek64_c`**: a `NULL` handle is refused with nothing changed; on any reachable
handle in `GzHistory`, every failure is `.outOfFuel`, reachable calls succeed, and every success
satisfies `FdsKept` and `GzStepPost`. -/
def Goal.gzseek64_c_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) offset whence,
    Zlib.Gzlib.gzseek64_c none offset whence fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s offset whence,
    let call := Call.gzseek64 (some (.in_gzstate_x i)) offset whence
    GzHistory h fs i → h.gzstates i = some s → GzArguments h i s call →
    (∀ e, Zlib.Gzlib.gzseek64_c (some (.in_gzstate_x i)) offset whence fs h = .error e → e = .outOfFuel) ∧
    ((NeedsReadBound call → ReadsFinite fs s.fd) →
      ∃ value fs' after,
        Zlib.Gzlib.gzseek64_c (some (.in_gzstate_x i)) offset whence fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after,
      Zlib.Gzlib.gzseek64_c (some (.in_gzstate_x i)) offset whence fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s call fs' after))

end ZlibF.Spec.Public

namespace Zlib.Inffast.Spec
open C Zlib.Inffast

/-- Safety, termination, frame and exact register writeback of the exact-shape C-ABI fast
decoder companion `inflate_fast_c`. -/
def Goal.fast_c_safe : Prop :=
  ∀ e : Proofs.Env, ∃ after,
    C.run (inflate_fast_c e.strm e.start) e.h0 = .ok ((), after) ∧ FastPost e after

end Zlib.Inffast.Spec

namespace Zlib.Inftrees.Spec
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- Safety, termination, and table-decoder invariant for the exact-shape C-ABI builder
companion `inflate_table_c`. -/
def Goal.inflate_table_c_decoder_safe : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32) (rc : CodeRef) (oc : Nat) (bits : UInt32)
    (rw : WRef) (ow : Nat) (pre : CallPre h type rl ol codes rc oc bits rw ow),
    ∃ r after,
      C.run (inflate_table_c type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (r, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits r after ∧
      (r.1 = 0 → ∃ ca : Array Code, Space.get after rc = some ca ∧
        1 ≤ r.2.2.toNat ∧ r.2.2.toNat ≤ 15 ∧
        (type = CODES → CodeLengthTableSafe ca oc r.2.2.toNat) ∧
        (type = LENS → Zlib.Inffast.Spec.LenTableSafe ca oc r.2.2.toNat) ∧
        (type = DISTS → Zlib.Inffast.Spec.DistTableSafe ca oc r.2.2.toNat))

end Zlib.Inftrees.Spec
