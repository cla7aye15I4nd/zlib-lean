# Safety Scope, Trusted Computing Base, and UB Exceptions

This document defines the safety-only specification in `zlib-lean`, the minimal Trusted Computing Base (TCB), and the two intentional C17 pointer-arithmetic exceptions.

## 1. Safety Scope and Specification Structure

`zlib-lean` targets the patched zlib revision (`1.4.0.1-motley` at `617e19a8` plus the 6 ordered patches in [pins.json](../pins.json)) compiled for the default x86-64 LP64 static library build.

- **Verus-style embedded API contracts (86 / 86 documented `zlib.h` APIs)**: Every documented function in `build/reference/zlib.h` carries `requires` / `modifies` / `ensures` clauses directly on its `c_fn` definition across `Zlib/*.lean`, sharing predicates from [`Zlib/Spec/Memory.lean`](../Zlib/Spec/Memory.lean) and collected into [`Zlib.allContracts`](../Zlib.lean#L46-L63). The 9 non-Windows undocumented exports (`deflateResetKeep`, `get_crc_table`, `gzvprintf`, `inflateCodesUsed`, `inflateResetKeep`, `inflateSyncPoint`, `inflateUndermine`, `inflateValidate`, `zError`) are also compiled and exported in `Zlib.allTUs` (95 POSIX exports total).
- **Top-level whole-library safety statement ([`Goal.libz_safety`](../Zlib/Spec/Safety.lean#L101-L111))**:
  - Establishes an inductive library invariant `Inv : ClientView → BlockSet → Mem → OSState → Prop` starting from `ClientView.empty` with zero library-owned heap blocks after `initLibz`.
  - Requires `Inv` to be stable under arbitrary valid caller mutations between calls (`ClientFrame`), allowing caller buffer updates, allocation/freeing of caller memory, arbitrary `readBudget` changes, and interleaved multi-stream / multi-`gzFile` calls while protecting library-owned heap blocks, `.ro .global` string literals, `errnoBlk`, `strerrorBlk`, and active stream internal pointers (`state`, `zalloc`, `zfree`, `opaque`).
  - Requires every contracted API call `c ∈ Zlib.allContracts` (`ContractSafe`) to satisfy:
    1. **UB freedom (`C99.Sem.Safe`)**: No reachable state steps to `RunState.ub` under `zlibPointerConfig`.
    2. **Bounded termination (`C99.Sem.TerminatesSafely`)**: Whenever `os.readBudget.isSome` (and user `inflateBack` callbacks satisfy `SafeUserCallbacks`), execution reaches `RunState.returned`. Unbounded `none` read budgets exclude `RunState.ub` without asserting loop termination over infinite reads.
    3. **Frame & leak freedom**: Every pre-existing block outside `owned ∪ owned' ∪ modSet ∪ userWrite ∪ {errnoBlk, strerrorBlk}` is unchanged (`FramePreserved`), every new heap block is tracked (`NoHeapLeak`), and closing all active handles in `ClientView` leaves zero owned heap blocks (`v'.isEmpty → ∀ b, ¬ owned' b`).
- **Safety-only runtime simplification**: Functional output correctness, mock POSIX filesystems, exact `strerror` tables, and `snprintf` text formatting are intentionally omitted from [`C99/Libc.lean`](../C99/Libc.lean) and [`Zlib/Spec/`](../Zlib/Spec/Safety.lean). Differential test drivers are replaced completely by byte-for-byte binary equality against patched zlib (`make binary-equal` / `make archive-equal`).
- **Scope restrictions**: Default internal allocator only (`zalloc == NULL`, `zfree == NULL` at stream initialization); single-threaded sequential call sequences (concurrent data races out of scope).
- **Proof status**: `Zlib.Spec.Goal.libz_safety` is currently stated as a clean, `sorry`-free `Prop` specification on branch `dev`; migrating and discharging the machine-checked safety proofs against `C99.Sem` (drawing from the legacy proof suite preserved on `origin/main`) is the next phase.

## 2. Trusted Computing Base (TCB)

Running `make check-tcb` and `make check-kernel` enforces:

1. **Zero `sorry` and zero custom `axiom`** across all Lean modules (`C99/`, `Zlib/`, `Zlib.lean`, `Main.lean`), verified by [`tools/check_tcb.py`](../tools/check_tcb.py) and replayed in a fresh Lean kernel via `lake env leanchecker --fresh Zlib.Spec.Safety`.
2. **Compact, zlib-agnostic Core C99 TCB (2,179 LOC, limit 2,300 LOC)**:
   - [`C99/AST.lean`](../C99/AST.lean) (406 LOC): C99 types, LP64 size/alignment/field-offset rules, expressions, statements, translation units.
   - [`C99/Mem.lean`](../C99/Mem.lean) (222 LOC): flat never-reused `BlockId` heap/stack/global memory, `ptrFrag`/`fnFrag` pointer bytes, `ptrDiffLimit = 2^63`.
   - [`C99/Libc.lean`](../C99/Libc.lean) (233 LOC): safety-only `ExtStep` relation for `malloc`/`calloc`/`free`/`memcpy`/`memmove`/`memset`/`memcmp`/`strlen`/`memchr` and POSIX `open`/`close`/`fcntl`/`lseek`/`lseek64`/`read`/`write`/`strerror`/`snprintf`/`vsnprintf` (including `%n` rejection).
   - [`C99/Semantics.lean`](../C99/Semantics.lean) (978 LOC): small-step operational semantics (`Step`, `Safe`, `TerminatesSafely`, `initProg`).
   - [`C99/EmitC.lean`](../C99/EmitC.lean) (335 LOC) and [`C99.lean`](../C99.lean) (5 LOC): pure 1-to-1 structural C99 printer.
3. **Verus Contract Wrapper & Safety Spec**: [`C99/DSL/Contract.lean`](../C99/DSL/Contract.lean) (22 LOC) and [`Zlib/Spec/`](../Zlib/Spec/Safety.lean) (316 LOC, limit 500 LOC), plus 86/86 `zlib.h` API & ABI signature matching in [`tools/check_public_api.py`](../tools/check_public_api.py).
4. **Outside-kernel compilation trust**: Faithfulness of the modeled x86-64 LP64 semantics to compiled C relies on Clang compilation and byte-for-byte identity checks (`make binary-equal` / `make archive-equal`), which verify `_Static_assert` sizes/offsets across 10 ABI structs (163 fields) and byte equality of all 15 `.o` object files and `libz.a` against configured reference zlib.

## 3. Manual Undefined-Behavior Exceptions

`zlibPointerConfig` in [`Zlib/Spec/Safety.lean`](../Zlib/Spec/Safety.lean#L14-L16) enables two permissive `PointerConfig` flags in [`C99/Semantics.lean`](../C99/Semantics.lean#L13-L16). Any safety theorem proven under `zlibPointerConfig` relies on Clang preserving these two runtime behaviors at the cited call sites:

| Flag / Rule | Runtime Semantics & Guard | Patched zlib & Lean Call Sites | Effect on Safety Claim |
| --- | --- | --- | --- |
| `allowAddZeroAny = true` | In [`evalPtrAdd`](../C99/Semantics.lean#L121-L131), when `idx == 0` and `p` is `.null` or any `.ptr b off`, pointer addition returns `some p` without checking block liveness (`m.blocks b`) or offset bounds (`0 ≤ off ≤ blk.size`). | `gzseek64` (`build/reference/gzlib.c:435`, [`Zlib/Gzlib.lean`](../Zlib/Gzlib.lean#L304)) and `gz_skip_have` (`build/reference/gzread.c:315`, [`Zlib/Gzread.lean`](../Zlib/Gzread.lean#L248)) execute `state->x.next += n;` when `n == 0` and `x.next` is `NULL`, uninitialized, or refers to a previously expired caller buffer. | Excludes `RunState.ub` on zero-offset pointer arithmetic in `gz*` read/seek paths; any compiler-introduced trap/poison on `NULL + 0` or dangling `p + 0` sits outside the Lean guarantee. |
| `allowNullDiffNull = true` | In [`evalPtrDiff`](../C99/Semantics.lean#L133-L145), `NULL - NULL` matches `.null, .null` and returns `some (.int .i64 0)` (matching C++, whereas C17/C23 leave `NULL - NULL` undefined); non-null distinct-block or out-of-bounds subtraction still steps to `ub`. | `compress2_z` (`build/reference/compress.c:63`, [`Zlib/Compress.lean`](../Zlib/Compress.lean#L60)) evaluates `stream.next_out - dest` at exit when caller passes `dest == NULL` and `*destLen == 0`. | Excludes `RunState.ub` for zero-capacity `compress*` calls with `dest == NULL`; assumes target compiler evaluates `NULL - NULL` to `0`. |

### Additional Source-Level Modeling Boundaries

- **Strict aliasing / word-braid checksums**: [`C99.Mem`](../C99/Mem.lean) models memory as untyped byte arrays without C effective-type tags. In [`crc32_z`](../Zlib/Crc32.lean#L190-L270), aligned word-sized pointer casts (`(z_word_t const *)buf`) assume target compliance under Clang's LP64 ABI / `-fno-strict-aliasing` or compiler code generation verified via `make binary-equal`.
- **Variadic arguments (`gzprintf`)**: [`Libc.ExtOk`](../C99/Libc.lean#L206-L226) requires a NUL-terminated format string without `%n` (`SafeFmtString`) for `snprintf`/`vsnprintf`, without type-checking C variadic argument conversions at runtime; callers of [`gzprintf`](../Zlib/Gzwrite.lean#L436-L441) must supply format-matching variadic arguments.
