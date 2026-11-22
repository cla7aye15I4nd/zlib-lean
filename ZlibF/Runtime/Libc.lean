import ZlibF.Runtime.LibcAllocation
import ZlibF.Runtime.LibcCString
import ZlibF.Runtime.LibcMemory
import ZlibF.Runtime.LibcTables

/-!
# Runtime: the C library

Trusted base of every translation; see `docs/en/trusted-base.md`. Everything here models a function of the C library
(or of the compiler's literal handling), not the C language: the language level (pointers, arithmetic, loops, the
heap tables) is in `Space.lean`, `Monad.lean` and `Ptr.lean`. Each function says how it differs from the real one.

| C library | Lean | Differs from the real function |
| --- | --- | --- |
| `memcpy`, `zmemcpy` | `Ptr.memcpy`, `memcpyB` (and `copyK` for a whole record, `LibcTables.lean`) | faults on NULL even for `n = 0`; on a read-only destination (for `n > 0`); on overlap; counts elements, not bytes |
| `memmove` | `Ptr.memmove`, `memmoveB` | the same without the overlap fault |
| `memset`, `zmemzero` | `Ptr.fill` (set `n` elements to a value), `Ptr.memset` (every byte of each element is `c`), `memsetB` | counts elements; `Ptr.fill` is `memset` only for bytes or the value 0 |
| `strlen` | `strlenB` | faults when no NUL lies inside the block (the C reads past the object) |
| `malloc` (through `ZALLOC`) | `allocB`, `allocW`, `allocK` per struct kind | the content is arbitrary integers and NULL pointers; a request above `PTRDIFF_MAX` bytes returns NULL (glibc); below that, success is decided by the oracle `Heap.allocOk`; each call consumes one oracle number; faults if the heap is not `Fresh`; the size is a count of elements |
| `free` | `freeB`, `freeW`, `freeK` | faults on a pointer that is not the start of a live block, on a freed block (double free), on a read-only block; NULL is a no-op |
| string literal | `strLitRef` (the table `strTable`) | a static read-only array, the same pointer every time; a text outside the sources is a fault |
| (test harness, not a C function) | `allocBytes`, `allocBytesRO` | put given bytes in a fresh block; take no allocation call |

Not modelled: `calloc` and `realloc` (no call site in the verified LP64 build: `zcalloc` takes its `malloc` branch),
`printf` and the `gz` file calls other than through `GzFs` (the file system model of
the translations, in `ZlibF/Zlib/gzfs.lean`), `errno`, `abs`, `strerror` (the translations write them themselves).
-/
