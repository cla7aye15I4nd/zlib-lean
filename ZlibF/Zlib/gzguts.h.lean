import ZlibF.Runtime.Tables
import ZlibF.Runtime.CAbi
import ZlibF.Zlib.gzfs

/-!
# gzguts.h — the header content of the gz* files

Default x86_64 Linux build (`STDC`, `STDC99`, `HAVE_VSNPRINTF`, `_LARGEFILE64_SOURCE` defined; `NO_GZCOMPRESS`,
`WIDECHAR`, `UNDER_CE`, `NO_snprintf`, `NO_vsnprintf` undefined). The constants `GZBUFSIZE`, `GZ_NONE`, `GZ_READ`,
`GZ_WRITE`, `GZ_APPEND`, `LOOK`, `GZIP`, the struct `gz_state` and `gzFile_s` come from the generated schema.
`COPY` of `gzguts.h` is `GZ_COPY` in the runtime (the name `COPY` is the inflate enumerator).

Decisions (see `docs/en/design/external-io.md`):

* `gzFile` is `GzFilePtr` (`some (.in_gzstate_x id)`), `gz_statep` is `GzStatePtr` (`some (.tab id)`); the cast
  `(gz_statep)file` is `castState`, `(gzFile)state` is `castFile`.
* `&(state->strm)` is `strmOf state`, computed without a dereference.
* Locals whose address is taken (`unsigned char buf[1]`) are blocks made by `allocLocal` (no allocation oracle:
  automatic storage cannot fail) and freed before every return.
* A pointer to a scalar (`int *errnum`, `z_size_t *destLen`) is a pointer to a byte block holding the value in
  little-endian order (`load32`, `store32`, `load64`, `store64`), because the runtime has no pointer to a single cell.
* Signed arithmetic is checked (`i64add`, `i64sub`, `i64neg`: overflow is `Fault.ub`).
-/

namespace Zlib.Gzguts
open C Zlib.GzFs

/-- `(gz_statep)file` -/
def castState (f : GzFilePtr) : GzStatePtr :=
  f.map fun | .in_gzstate_x i => .tab i

/-- `(gzFile)state` -/
def castFile (s : GzStatePtr) : GzFilePtr :=
  s.map fun | .tab i => .in_gzstate_x i

/-- `&(state->strm)` -/
def strmOf (s : GzStatePtr) : ZStreamPtr :=
  s.map fun | .tab i => .in_gzstate_strm i

/-- `*state` -/
def ldS (s : GzStatePtr) : M GzState := ldGzState s

/-- `*state = f(*state)`: a field write. -/
def updS (s : GzStatePtr) (f : GzState → GzState) : M Unit := do
  stGzState s (f (← ldGzState s))

/-- A field write of `state->x`. -/
def updX (s : GzStatePtr) (f : GzFile → GzFile) : M Unit :=
  updS s fun st => { st with x := f st.x }

/-- `*strm` -/
def ldZ (z : ZStreamPtr) : M ZStream := ldZStream z

/-- A field write of `*strm`. -/
def updZ (z : ZStreamPtr) (f : ZStream → ZStream) : M Unit := do
  stZStream z (f (← ldZStream z))

/-- Checked `z_off64_t` arithmetic: signed overflow is undefined. -/
def i64chk (r : Int) : M Int64 :=
  if -9223372036854775808 ≤ r ∧ r < 9223372036854775808 then pure (Int64.ofInt r) else C.ub "signed overflow (long)"
def i64add (a b : Int64) : M Int64 := i64chk (a.toInt + b.toInt)
def i64sub (a b : Int64) : M Int64 := i64chk (a.toInt - b.toInt)
def i64neg (a : Int64) : M Int64 := i64chk (-a.toInt)

/-- `(z_off64_t)u` for an unsigned 32-bit value. -/
def u32ToI64 (u : UInt32) : Int64 := Int64.ofNat u.toNat

/-- `GZ_OFF_MAX`: `((((z_off64_t)1 << (sizeof(z_off64_t) * CHAR_BIT - 2)) - 1) * 2 + 1)` -/
def GZ_OFF_MAX : Int64 := Int64.ofInt 9223372036854775807

/-- A local array: a fresh writable block with arbitrary content, outside the allocation oracle (automatic storage
cannot fail). Made by the runtime allocator `allocBytes`. -/
def allocLocal (n : Nat) : M BPtr := fun h =>
  allocBytes (Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val)) h

/-- An 8-byte automatic scalar cell (`z_size_t got`, `uLong used`). -/
abbrev allocLocal64 : M C.StackScalar64 := allocLocal 8

-- `*(int *)p`, `*(uint64_t *)p`, and their stores live in `C` (`ZlibF.Runtime.CAbi`) and are re-exported here.
export C (load32 store32 load64 store64)

/-- `memchr(p, c, n)`: reads at most `n` bytes and stops at the first match; faults if a byte it reads is outside
the object. Returns NULL if there is no match. -/
def memchrB (p : BPtr) (c : UInt8) (n : Nat) : M BPtr := do
  for i in [0:n] do
    if (← index8 p i) == c then return (← p.add i)
  return .null

end Zlib.Gzguts
