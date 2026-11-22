import ZlibF.Spec.Safety.GzSafety

/-!
# gz file interface: one safety goal per function

Safety goals (`docs/en/design/safety-functional-split.md`, "Two goals per public function"). Each goal restricts a clause of
`Goal.gz_sequence_safety` to the calls of one function:
- a call on a handle (`GzCallSafety`): clause 2, one more call on a handle of any `GzHistory`;
- `gzgetc` also has clause 3, the `gzgetc()` macro of `zlib.h`; `gzerror` also has clause 4, the
  string it returns;
- a close (`GzCloseCallSafety`): clause 5;
- an open: `GzOpenSafe` or `GzDopenSafe`.
Each can fail: the call must return, keep the descriptors, keep `GzInv`, write only the handle's
blocks and the declared caller regions, and change the live blocks by the handle's ledger. The
histories are non-empty (`Goal.gz_sequence_nonvacuity`). Each goal of a call on a handle also has
the function's clause of `Goal.gz_refusal`: a `NULL` handle is refused at once with nothing changed.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
set_option autoImplicit false

/-- **Safety of one call on a handle**, for the calls that `selects` admits: clause 2 of
`Goal.gz_sequence_safety` restricted to them. The call is on handle `i` of a history
(`GzOperation`), with the caller's arguments of `zlib.h` (`GzArguments`). -/
def GzCallSafety (selects : Call → Prop) : Prop :=
  ∀ h fs i s call, GzHistory h fs i → h.gzstates i = some s → selects call → GzOperation i call →
    GzArguments h i s call →
    (∀ e, call.execute fs h = .error e → e = .outOfFuel) ∧
    ((NeedsReadBound call → ReadsFinite fs s.fd) →
      ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, call.execute fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s call fs' after)

/-- **Safety of a close** of handle `i`, for the close calls that `selects` admits: clause 5 of
`Goal.gz_sequence_safety` restricted to them. -/
def GzCloseCallSafety (selects : Call → Prop) : Prop :=
  ∀ h fs i s call, GzHistory h fs i → h.gzstates i = some s → selects call → GzCloseCall i call →
    ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after) ∧
      ((CloseRefuses s call ∧ after = h ∧ fs' = fs) ∨ (¬ CloseRefuses s call ∧ GzReleased h after fs fs' i s))

/-- `int gzbuffer(gzFile file, unsigned size)`.
**Safety of `gzbuffer`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzbuffer_safety : Prop :=
  (∀ (h : Heap) size, Zlib.Gzlib.gzbuffer none size h = .ok (-1, h)) ∧
  GzCallSafety (fun | .gzbuffer .. => True | _ => False)

/-- `void gzclearerr(gzFile file)`.
**Safety of `gzclearerr`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzclearerr_safety : Prop :=
  (∀ h : Heap, Zlib.Gzlib.gzclearerr none h = .ok ((), h)) ∧
  GzCallSafety (fun | .gzclearerr .. => True | _ => False)

/-- `int gzdirect(gzFile file)`.
**Safety of `gzdirect`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzdirect_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzdirect none fs h = .ok ((0, fs), h)) ∧
  GzCallSafety (fun | .gzdirect .. => True | _ => False)

/-- `int gzeof(gzFile file)`.
**Safety of `gzeof`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzeof_safety : Prop :=
  (∀ h : Heap, Zlib.Gzlib.gzeof none h = .ok (0, h)) ∧
  GzCallSafety (fun | .gzeof .. => True | _ => False)

/-- `int gzflush(gzFile file, int flush)`.
**Safety of `gzflush`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzflush_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) flush,
    Zlib.Gzwrite.gzflush none flush fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  GzCallSafety (fun | .gzflush .. => True | _ => False)

/-- `z_size_t gzfread(voidp buf, z_size_t size, z_size_t nitems, gzFile file)`.
**Safety of `gzfread`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzfread_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) buf size nitems,
    Zlib.Gzread.gzfread buf size nitems none fs h = .ok ((0, fs), h)) ∧
  GzCallSafety (fun | .gzfread .. => True | _ => False)

/-- `z_size_t gzfwrite(voidpc buf, z_size_t size, z_size_t nitems, gzFile file)`.
**Safety of `gzfwrite`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzfwrite_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) buf size nitems,
    Zlib.Gzwrite.gzfwrite buf size nitems none fs h = .ok ((0, fs), h)) ∧
  GzCallSafety (fun | .gzfwrite .. => True | _ => False)

/-- `int gzgetc_(gzFile file)`.
**Safety of `gzgetc_`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzgetc__safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzgetc_ none fs h = .ok ((-1, fs), h)) ∧
  GzCallSafety (fun | .gzgetc_ .. => True | _ => False)

/-- `char * gzgets(gzFile file, char *buf, int len)`.
**Safety of `gzgets`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzgets_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) buf len, Zlib.Gzread.gzgets none buf len fs h = .ok ((.null, fs), h)) ∧
  GzCallSafety (fun | .gzgets .. => True | _ => False)

/-- `z_off_t gzoffset(gzFile)`.
**Safety of `gzoffset`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzoffset_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzlib.gzoffset none fs h = .ok ((-1, fs), h)) ∧
  GzCallSafety (fun | .gzoffset .. => True | _ => False)

/-- `z_off64_t gzoffset64(gzFile)`.
**Safety of `gzoffset64`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzoffset64_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzlib.gzoffset64 none fs h = .ok ((-1, fs), h)) ∧
  GzCallSafety (fun | .gzoffset64 .. => True | _ => False)

/-- `int gzprintf(gzFile file, const char *format, ...)`.
**Safety of `gzprintf`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzprintf_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) format (va : List VaArg),
    Zlib.Gzwrite.gzprintf none format va fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  GzCallSafety (fun | .gzprintf .. => True | _ => False)

/-- `int gzvprintf(gzFile file, const char *format, va_list va)`.
**Safety of `gzvprintf`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). `zlib.h` lists it
among the undocumented functions; the gz sequence goals range over it, and its own goal is required. -/
def Goal.gzvprintf_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) format (va : List VaArg),
    Zlib.Gzwrite.gzvprintf none format va fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  GzCallSafety (fun | .gzvprintf .. => True | _ => False)

/-- `int gzputc(gzFile file, int c)`.
**Safety of `gzputc`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzputc_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) c, Zlib.Gzwrite.gzputc none c fs h = .ok ((-1, fs), h)) ∧
  GzCallSafety (fun | .gzputc .. => True | _ => False)

/-- `int gzputs(gzFile file, const char *s)`.
**Safety of `gzputs`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzputs_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) str, Zlib.Gzwrite.gzputs none str fs h = .ok ((-1, fs), h)) ∧
  GzCallSafety (fun | .gzputs .. => True | _ => False)

/-- `int gzread(gzFile file, voidp buf, unsigned len)`.
**Safety of `gzread`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzread_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) buf len, Zlib.Gzread.gzread none buf len fs h = .ok ((-1, fs), h)) ∧
  GzCallSafety (fun | .gzread .. => True | _ => False)

/-- `int gzrewind(gzFile file)`.
**Safety of `gzrewind`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzrewind_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzlib.gzrewind none fs h = .ok ((-1, fs), h)) ∧
  GzCallSafety (fun | .gzrewind .. => True | _ => False)

/-- `z_off_t gzseek(gzFile, z_off_t, int)`.
**Safety of `gzseek`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzseek_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) offset whence,
    Zlib.Gzlib.gzseek none offset whence fs h = .ok ((-1, fs), h)) ∧
  GzCallSafety (fun | .gzseek .. => True | _ => False)

/-- `z_off64_t gzseek64(gzFile, z_off64_t, int)`.
**Safety of `gzseek64`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzseek64_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) offset whence,
    Zlib.Gzlib.gzseek64 none offset whence fs h = .ok ((-1, fs), h)) ∧
  GzCallSafety (fun | .gzseek64 .. => True | _ => False)

/-- `int gzsetparams(gzFile file, int level, int strategy)`.
**Safety of `gzsetparams`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzsetparams_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) level strategy,
    Zlib.Gzwrite.gzsetparams none level strategy fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  GzCallSafety (fun | .gzsetparams .. => True | _ => False)

/-- `z_off_t gztell(gzFile)`.
**Safety of `gztell`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gztell_safety : Prop :=
  (∀ h : Heap, Zlib.Gzlib.gztell none h = .ok (-1, h)) ∧
  GzCallSafety (fun | .gztell .. => True | _ => False)

/-- `z_off64_t gztell64(gzFile)`.
**Safety of `gztell64`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gztell64_safety : Prop :=
  (∀ h : Heap, Zlib.Gzlib.gztell64 none h = .ok (-1, h)) ∧
  GzCallSafety (fun | .gztell64 .. => True | _ => False)

/-- `int gzungetc(int c, gzFile file)`.
**Safety of `gzungetc`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzungetc_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) c, Zlib.Gzread.gzungetc c none fs h = .ok ((-1, fs), h)) ∧
  GzCallSafety (fun | .gzungetc .. => True | _ => False)

/-- `int gzwrite(gzFile file, voidpc buf, unsigned len)`.
**Safety of `gzwrite`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`). -/
def Goal.gzwrite_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) buf len, Zlib.Gzwrite.gzwrite none buf len fs h = .ok ((0, fs), h)) ∧
  GzCallSafety (fun | .gzwrite .. => True | _ => False)

/-- `int gzgetc(gzFile file)`.
**Safety of `gzgetc`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and the function on a handle of any history (`GzCallSafety`), and the
`gzgetc()` macro of `zlib.h`, which reads buffered output inline and calls the function otherwise
(clause 3 of `Goal.gz_sequence_safety`). -/
def Goal.gzgetc_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzgetc none fs h = .ok ((-1, fs), h)) ∧
  GzCallSafety (fun | .gzgetc .. => True | _ => False) ∧
  (∀ h fs i s, GzHistory h fs i → h.gzstates i = some s →
    (∀ e, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .error e → e = .outOfFuel) ∧
    ((s.x.have = 0 → NeedsReadBound (.gzgetc (some (.in_gzstate_x i))) → ReadsFinite fs s.fd) →
      ∃ value fs' after, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s (.gzgetc (some (.in_gzstate_x i))) fs' after))

/-- `const char * gzerror(gzFile file, int *errnum)`.
**Safety of `gzerror`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and one call on a handle of any history (`GzCallSafety`), and the pointer it
returns is a readable NUL-terminated string in the heap after the call (clause 4 of
`Goal.gz_sequence_safety`). -/
def Goal.gzerror_safety : Prop :=
  (∀ (h : Heap) errnum, Zlib.Gzlib.gzerror none errnum h = .ok (.null, h)) ∧
  GzCallSafety (fun | .gzerror .. => True | _ => False) ∧
  (∀ h fs i s errnum, GzHistory h fs i → h.gzstates i = some s →
    GzArguments h i s (.gzerror (some (.in_gzstate_x i)) errnum) →
    ∀ (value : BPtr) fs' after,
      (Call.gzerror (some (.in_gzstate_x i)) errnum).execute fs h = .ok ((value, fs'), after) →
      ∃ t, CString after value t)

/-- `int gzclose(gzFile file)`.
**Safety of `gzclose`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and it returns on a handle of any history, and either refuses on the wrong mode
with nothing changed or frees every owned block and releases the descriptor (`GzCloseCallSafety`). -/
def Goal.gzclose_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzclose.gzclose none fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  GzCloseCallSafety (fun | .gzclose .. => True | _ => False)

/-- `int gzclose_r(gzFile file)`.
**Safety of `gzclose_r`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and it returns on a handle of any history, and either refuses on the wrong mode
with nothing changed or frees every owned block and releases the descriptor (`GzCloseCallSafety`). -/
def Goal.gzclose_r_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzclose_r none fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  GzCloseCallSafety (fun | .gzclose_r .. => True | _ => False)

/-- `int gzclose_w(gzFile file)`.
**Safety of `gzclose_w`**: a `NULL` handle is refused with nothing changed (its clause of
`Goal.gz_refusal`); and it returns on a handle of any history, and either refuses on the wrong mode
with nothing changed or frees every owned block and releases the descriptor (`GzCloseCallSafety`). -/
def Goal.gzclose_w_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzwrite.gzclose_w none fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  GzCloseCallSafety (fun | .gzclose_w .. => True | _ => False)

/-- `gzFile gzopen(const char *, const char *)`.
**Safety of `gzopen`** (`GzOpenSafe`): it returns and frames the heap; a failure leaves no block and
no open descriptor; a handle is in `GzInv`, owns exactly the new blocks, and its descriptor is the
only newly opened one. -/
def Goal.gzopen_safety : Prop :=
  GzOpenSafe Zlib.Gzlib.gzopen

/-- `gzFile gzopen64(const char *, const char *)`.
**Safety of `gzopen64`**: as `Goal.gzopen_safety` (`GzOpenSafe`). -/
def Goal.gzopen64_safety : Prop :=
  GzOpenSafe Zlib.Gzlib.gzopen64

/-- `gzFile gzdopen(int fd, const char *mode)`.
**Safety of `gzdopen`** (`GzDopenSafe`): as `GzOpenSafe`, but no descriptor is opened or closed. -/
def Goal.gzdopen_safety : Prop :=
  GzDopenSafe

end ZlibF.Spec.Public
