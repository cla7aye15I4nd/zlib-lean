import ZlibF.Runtime.Alloc

/-!
# gzfs: the external world of the gz* files (trusted base)

The runtime heap (`ZlibF/Runtime`) has no file system, no `errno` and no `printf`. The gz* functions call `open`,
`read`, `write`, `lseek`, `close`, `fcntl`, `strerror`, `snprintf`/`vsnprintf`. This file is the model of those
calls, written next to the translation; it is part of the trusted base (`docs/en/design/external-io.md`
lists every decision and narrowing).

The world is a record `Fs` that lives beside the heap: a gz computation is `G α = StateT Fs C.M α`, so a heap
computation (`C.M`) lifts into it and a fault is still `Fault.ub`.
-/

namespace Zlib.GzFs
open C

/-- An open file description (what a file descriptor refers to). -/
structure OFile where
  node : Nat
  pos : Nat
  rd : Bool
  wr : Bool
  append : Bool
  deriving Inhabited

/-- A file (its bytes) or a directory (no bytes; `open` for reading succeeds, `read` fails with `EISDIR`). -/
structure Node where
  data : Array UInt8
  isDir : Bool
  deriving Inhabited

/-- What call `n` of `read` does (the OS-call oracle, M1). `regular`: the regular-file read. `fail e`: `-1` with
errno `e` (`0` reads as `EINTR`). `bytes bs`: a read that delivers a prefix of `bs`, cut to the request and to the
descriptor's budget. -/
inductive ReadChoice where
  | regular
  | fail (e : Int32)
  | bytes (bs : Array UInt8)
  deriving Inhabited

/-- What call `n` of `write` does (M2). `regular`: the regular-file write. `fail e`: `-1` with errno `e`. `count k`:
`k` clamped to `[1, len]` for a nonempty buffer, `0` for an empty one. -/
inductive WriteChoice where
  | regular
  | fail (e : Int32)
  | count (k : Nat)
  deriving Inhabited

/-- What call `n` of `lseek` does (M3). `regular`: the regular-file `lseek`. `fail e`: `-1` with errno `e`.
`value v`: `v`, any 64-bit value, without moving the descriptor. A real `lseek` returns `-1` for a failure and
otherwise an `off_t`, which need not be a position of a regular file: on Linux a file with unsigned offsets
(`/proc/<pid>/mem`, `/dev/mem`) returns every 64-bit value except `-4095 .. -1` (which the C library reports as
failures), and POSIX allows negative offsets for some devices. The oracle admits every value. -/
inductive LseekChoice where
  | regular
  | fail (e : Int32)
  | value (v : Int64)
  deriving Inhabited

/-- The file system, the descriptor table, `errno` and the file size limit (`RLIMIT_FSIZE`). Paths are flat
byte strings (no directory structure). The world also carries two oracles: the `vsnprintf` oracle (`printfRet` ..
`nprintf`) and the OS-call oracle (`nos` .. `readBudget`), which choose each call's result within its contract
(`docs/en/trusted-base.md`). -/
structure Fs where
  names : Array (Array UInt8 × Nat) := #[]
  nodes : Array Node := #[]
  fds : Array (Option OFile) := #[]
  errno : Int32 := 0
  fsizeLimit : Nat := 2 ^ 62
  /-- The `vsnprintf` oracle: the value the caller-format call number `n` returns, any `int`: the length of its full
  output, or a negative value for a failure. The defaults of this and the next two fields serve the executable
  drivers only; every goal quantifies over all worlds. -/
  printfRet : Nat → Int32 := fun _ => 0
  /-- The bytes the caller-format call `n` writes into the buffer: the output on success (padded with zeros to the
  length the call writes), the buffer contents on a failure (cut to `size`). -/
  printfOut : Nat → Array UInt8 := fun _ => #[]
  /-- The `errno` a failed caller-format call `n` leaves (zero reads as `EOVERFLOW`: `errno` is nonzero after a
  failure). -/
  printfErrno : Nat → Int32 := fun _ => 75
  /-- The number of caller-format `vsnprintf` calls so far. -/
  nprintf : Nat := 0
  /-- The number of `read`, `write`, `lseek`, `close` and `open` calls so far: it numbers the entries of the OS-call
  oracle below. The defaults of the oracle fields reproduce the regular-file model and serve the executable
  drivers only; every goal quantifies over all worlds. The oracle is deliberately wider than any real system
  (`docs/en/trusted-base.md`): `bytes` and `count` succeed whatever the descriptor's state, a `count` write does not
  change the file, a `value` `lseek` does not move the descriptor. -/
  nos : Nat := 0
  /-- What read call `n` does (M1). -/
  readChoice : Nat → ReadChoice := fun _ => .regular
  /-- What write call `n` does (M2). -/
  writeChoice : Nat → WriteChoice := fun _ => .regular
  /-- What lseek call `n` does (M3). -/
  lseekChoice : Nat → LseekChoice := fun _ => .regular
  /-- Close call `n` reports `-1` with this errno; the descriptor is released anyway (M4). -/
  closeFail : Nat → Option Int32 := fun _ => none
  /-- Open call `n` fails with this errno, before anything is created (M5). -/
  openFail : Nat → Option Int32 := fun _ => none
  /-- Open call `n` returns this descriptor number instead, if it is not open and below `2^31` (M5). -/
  openFd : Nat → Option Nat := fun _ => none
  /-- A successful call `n` leaves this errno (libc may change errno on success). -/
  okErrno : Nat → Option Int32 := fun _ => none
  /-- M7: the bytes the non-negative descriptor number `fd` may still deliver (`none`: no bound); a negative
  descriptor is unbudgeted. Keyed by number: a number reused after `close` inherits the remaining budget, which is
  harmless because the premise that uses it asks only for finiteness. -/
  readBudget : Nat → Option Nat := fun _ => none
  deriving Inhabited

/-- A gz computation: the world in, the heap in, a value and both out, or a fault. -/
abbrev G (α : Type) : Type := StateT Fs M α

/-- Undefined behaviour inside `G`. -/
def gub {α : Type} (what : String) : G α := fun _ => C.ub what

/-- `ENOENT` etc. (Linux x86_64 values). -/
def ENOENT : Int32 := 2
def EBADF : Int32 := 9
def EEXIST : Int32 := 17
def EISDIR : Int32 := 21
def EINVAL : Int32 := 22
def EFBIG : Int32 := 27
def ENOSPC : Int32 := 28
def EOVERFLOW : Int32 := 75
def EAGAIN : Int32 := 11
def EINTR : Int32 := 4
def EIO : Int32 := 5
def EACCES : Int32 := 13
def ESPIPE : Int32 := 29
def EMFILE : Int32 := 24

/-- `errno` as read by the C. -/
def getErrno : G Int32 := do return (← get).errno
/-- `errno = e`. -/
def setErrno (e : Int32) : G Unit := modify fun w => { w with errno := e }

/-- `BLOCKED(e)`: `e == EAGAIN || e == EWOULDBLOCK` (both are 11). -/
def BLOCKED (e : Int32) : Bool := e == EAGAIN

/-- The same fixed-locale Linux error-text table as before, now shared with
borrowed static view lookup. This preserves every Int32 fallback value. -/
def strerrorText (e : Int32) : String := C.libcErrnoText e

/-- A string literal of the C sources: the static read-only array of the runtime (`strLitRef`, the same pointer
every time). -/
def strLit (s : String) : M BPtr := strLitRef s

/-- Borrow the current external errno text. It is not a source literal and
not a malloc object. The four C call sites synchronously copy it with gz_error;
no use of this borrowed pointer across another strerror call is justified here.
This helper now takes errno, not an arbitrary String. -/
def libcStr (e : Int32) : M BPtr := fun h =>
  let epoch := match h.libcErrorBorrow with | none => 1 | some (previous, _) => previous + 1
  .ok (.ref (.str (libcErrnoIndex epoch e)) 0, { h with libcErrorBorrow := some (epoch, e) })

/-- `strerror(errno)`: borrow the current text without allocating storage. -/
def zstrerror : G BPtr := do
  let e ← getErrno
  libcStr e

/-- The bytes of the NUL-terminated string at `p` (without the NUL). Faults if `p` is null or has no NUL. -/
def cstring (p : BPtr) : M (Array UInt8) := do
  let n ← strlenB p
  let mut out : Array UInt8 := #[]
  for i in [0:n.toNat] do
    out := out.push (← index8 p i)
  return out

/-- Store `bs` at `p`, `p + 1`, ... as one block copy (what `read` and `vsnprintf` do to their buffer): faults if the
range is not inside the object or the object is read-only. (One copy instead of a store per byte: every store makes the
heap function one level deeper, which costs memory in the interpreter, not in the model.) -/
def storeBytes (p : BPtr) (bs : Array UInt8) : M Unit := do
  if bs.isEmpty then return
  let t ← allocBytes bs
  memcpyB p t bs.size
  freeB t

/-- Load `n` bytes from `p`. -/
def loadBytes (p : BPtr) (n : Nat) : M (Array UInt8) := do
  let mut out : Array UInt8 := #[]
  for i in [0:n] do
    out := out.push (← index8 p i)
  return out

/-! ## System calls -/

def O_WRONLY : Int32 := 1
def O_CREAT : Int32 := 64
def O_EXCL : Int32 := 128
def O_TRUNC : Int32 := 512
def O_APPEND : Int32 := 1024
def O_NONBLOCK : Int32 := 2048
def O_CLOEXEC : Int32 := 524288
def O_LARGEFILE : Int32 := 0
def SEEK_SET : Int32 := 0
def SEEK_CUR : Int32 := 1
def SEEK_END : Int32 := 2

private def findName (w : Fs) (p : Array UInt8) : Option Nat :=
  (w.names.find? (fun e => e.1 == p)).map (·.2)

/-- The lowest descriptor number from 3 up that is not open in the model's table (`fds.size` or more when every slot
from 3 is taken). -/
def lowestFd (w : Fs) : Nat :=
  let rec go (i : Nat) : Nat → Nat
    | 0 => i
    | k + 1 => if i < w.fds.size then (if (w.fds[i]!).isNone then i else go (i + 1) k) else i
  go 3 (w.fds.size + 3)

/-- The regular-file `open(path, oflag, 0666)` for `path` given as its bytes. Returns the descriptor or -1 with `errno`. The
access mode is read-only or write-only; `O_CREAT`, `O_EXCL`, `O_TRUNC`, `O_APPEND` are honoured; `O_NONBLOCK`,
`O_CLOEXEC` and `O_LARGEFILE` do nothing (regular files only). Permissions are not modelled. A descriptor is a C
`int`: when no number below `2^31` is free, `open` fails with `EMFILE` before anything is created or truncated (Linux
allocates the descriptor after checking the flags and the path string, before the lookup). -/
def fsOpenReg (path : Array UInt8) (oflag : Int32) : G Int32 := fun w =>
  let acc := oflag &&& 3
  let has (f : Int32) := (oflag &&& f) != 0
  let fail (e : Int32) : M (Int32 × Fs) := pure (-1, { w with errno := e })
  let fd := lowestFd w
  let openNode (n : Nat) (w : Fs) : M (Int32 × Fs) :=
    let node := w.nodes[n]!
    let wr := acc == 1
    if wr && node.isDir then pure (-1, { w with errno := EISDIR })
    else
      let w := if wr && has O_TRUNC then { w with nodes := w.nodes.set! n { node with data := #[] } } else w
      let fds := if fd < w.fds.size then w.fds else w.fds ++ Array.replicate (fd + 1 - w.fds.size) none
      let of : OFile := { node := n, pos := 0, rd := acc == 0, wr, append := has O_APPEND }
      pure (Int32.ofNat fd, { w with fds := fds.set! fd (some of) })
  if acc ≥ 2 then fail EINVAL
  else if path.isEmpty then fail ENOENT
  else if fd ≥ 2 ^ 31 then fail EMFILE
  else match findName w path with
    | some n => if has O_CREAT && has O_EXCL then fail EEXIST else openNode n w
    | none =>
      if has O_CREAT then
        let n := w.nodes.size
        openNode n { w with names := w.names.push (path, n), nodes := w.nodes.push { data := #[], isDir := false } }
      else fail ENOENT

/-- The regular-file `read(fd, buf, n)` as a pair: the result and the bytes that were read. -/
def fsReadReg (fd : Int32) (n : UInt64) : G (Int64 × Array UInt8) := fun w =>
  let fail (e : Int32) : M ((Int64 × Array UInt8) × Fs) := pure ((-1, #[]), { w with errno := e })
  if fd < 0 || fd.toInt ≥ w.fds.size then fail EBADF
  else match w.fds[fd.toInt.toNat]! with
    | none => fail EBADF
    | some of =>
      if !of.rd then fail EBADF
      else
        let node := w.nodes[of.node]!
        if node.isDir then fail EISDIR
        else
          let k := min n.toNat (node.data.size - of.pos)
          let bs := node.data.extract of.pos (of.pos + k)
          pure ((Int64.ofNat k, bs),
            { w with fds := w.fds.set! fd.toInt.toNat (some { of with pos := of.pos + k }) })

/-- The regular-file `write(fd, buf, n)` for the bytes `bs` of the buffer. A write past the size limit is cut (a short write), and
a write with no room fails with `EFBIG`. -/
def fsWriteReg (fd : Int32) (bs : Array UInt8) : G Int64 := fun w =>
  let fail (e : Int32) : M (Int64 × Fs) := pure (-1, { w with errno := e })
  if fd < 0 || fd.toInt ≥ w.fds.size then fail EBADF
  else match w.fds[fd.toInt.toNat]! with
    | none => fail EBADF
    | some of =>
      if !of.wr then fail EBADF
      else if bs.isEmpty then pure (0, w)
      else
        let node := w.nodes[of.node]!
        let pos := if of.append then node.data.size else of.pos
        if pos ≥ w.fsizeLimit then fail EFBIG
        else
          let k := min bs.size (w.fsizeLimit - pos)
          let old := if pos > node.data.size then node.data ++ Array.replicate (pos - node.data.size) 0 else node.data
          let new := old.extract 0 pos ++ bs.extract 0 k ++ old.extract (pos + k) old.size
          pure (Int64.ofNat k,
            { w with nodes := w.nodes.set! of.node { node with data := new }
                     fds := w.fds.set! fd.toInt.toNat (some { of with pos := pos + k }) })

/-- The regular-file `lseek(fd, off, whence)`. -/
def fsLseekReg (fd : Int32) (off : Int64) (whence : Int32) : G Int64 := fun w =>
  let fail (e : Int32) : M (Int64 × Fs) := pure (-1, { w with errno := e })
  if fd < 0 || fd.toInt ≥ w.fds.size then fail EBADF
  else match w.fds[fd.toInt.toNat]! with
    | none => fail EBADF
    | some of =>
      let base : Option Int :=
        if whence == SEEK_SET then some 0
        else if whence == SEEK_CUR then some of.pos
        else if whence == SEEK_END then some (w.nodes[of.node]!.data.size) else none
      match base with
      | none => fail EINVAL
      | some b =>
        let np := b + off.toInt
        if np < 0 then fail EINVAL
        else if np > 9223372036854775807 then fail EOVERFLOW
        else pure (Int64.ofInt np,
          { w with fds := w.fds.set! fd.toInt.toNat (some { of with pos := np.toNat }) })

/-- The regular-file `close(fd)`. -/
def fsCloseReg (fd : Int32) : G Int32 := fun w =>
  if fd < 0 || fd.toInt ≥ w.fds.size then pure (-1, { w with errno := EBADF })
  else match w.fds[fd.toInt.toNat]! with
    | none => pure (-1, { w with errno := EBADF })
    | some _ => pure (0, { w with fds := w.fds.set! fd.toInt.toNat none })

/-! ## The OS-call oracle

Each of the five calls takes the next call number `c = nos`, then behaves as its regular-file version (the `Reg`
functions above) or as the oracle chooses. Every oracle value is mapped into the call's POSIX contract (cut or
clamp, never reject), so every world is legal. -/

/-- The world with the call counter advanced. -/
def tickW (w : Fs) : Fs := { w with nos := w.nos + 1 }

/-- errno after a successful call, as the oracle chose it (`okErrno c` of the world the call started in). -/
def okErrW (o : Option Int32) (w : Fs) : Fs :=
  match o with
  | some e => { w with errno := e }
  | none => w

/-- A nonzero errno for a failure. -/
def failErrno (e dflt : Int32) : Int32 := if e == 0 then dflt else e

/-- The bytes a read of `n` on `fd` may deliver: `n`, cut to the budget of a non-negative descriptor. -/
def readCap (fd : Int32) (n : UInt64) (w : Fs) : Nat :=
  if fd < 0 then n.toNat
  else match w.readBudget fd.toInt.toNat with
    | some b => min n.toNat b
    | none => n.toNat

/-- Debit `k` bytes from the budget of a non-negative descriptor `fd`. -/
def debitW (fd : Int32) (k : Nat) (w : Fs) : Fs :=
  if fd < 0 then w
  else { w with readBudget := fun j => if j = fd.toInt.toNat then (w.readBudget j).map (· - k) else w.readBudget j }

/-- `read(fd, buf, n)` as a pair: the result and the bytes that were read (to be stored at `buf` by the caller).
M1: `-1` with a nonzero errno, or `k ∈ [0, n]` bytes, within the budget (M7). -/
def fsRead (fd : Int32) (n : UInt64) : G (Int64 × Array UInt8) := fun w0 =>
  let c := w0.nos
  let w := tickW w0
  let cap := readCap fd n w0
  match w0.readChoice c with
  | .regular => do
    let ((r, bs), w') ← fsReadReg fd (UInt64.ofNat cap) w
    pure ((r, bs), if r = -1 then w' else okErrW (w0.okErrno c) (debitW fd bs.size w'))
  | .fail e => pure ((-1, #[]), { w with errno := failErrno e EINTR })
  | .bytes bs =>
    let out := bs.extract 0 cap
    pure ((Int64.ofNat out.size, out), okErrW (w0.okErrno c) (debitW fd out.size w))

/-- `write(fd, buf, n)` for the bytes `bs` of the buffer. M2: `-1` with a nonzero errno, or `k ∈ [1, n]` for a
nonempty buffer, `0` for an empty one. -/
def fsWrite (fd : Int32) (bs : Array UInt8) : G Int64 := fun w0 =>
  let c := w0.nos
  let w := tickW w0
  match w0.writeChoice c with
  | .regular => do
    let (r, w') ← fsWriteReg fd bs w
    pure (r, if r = -1 then w' else okErrW (w0.okErrno c) w')
  | .fail e => pure (-1, { w with errno := failErrno e EIO })
  | .count k => pure ((if bs.isEmpty then 0 else Int64.ofNat (max 1 (min k bs.size))), okErrW (w0.okErrno c) w)

/-- `lseek(fd, off, whence)`. M3: `-1` with a nonzero errno, or any 64-bit value, possibly unrelated to later
reads (`LseekChoice`). -/
def fsLseek (fd : Int32) (off : Int64) (whence : Int32) : G Int64 := fun w0 =>
  let c := w0.nos
  let w := tickW w0
  match w0.lseekChoice c with
  | .regular => do
    let (r, w') ← fsLseekReg fd off whence w
    pure (r, if r = -1 then w' else okErrW (w0.okErrno c) w')
  | .fail e => pure (-1, { w with errno := failErrno e ESPIPE })
  | .value v => pure (v, okErrW (w0.okErrno c) w)

/-- `close(fd)`. M4: `0`, or `-1` with a nonzero errno; the descriptor is released in both cases. -/
def fsClose (fd : Int32) : G Int32 := fun w0 =>
  let c := w0.nos
  let w := tickW w0
  do
    let (r, w') ← fsCloseReg fd w
    pure (match w0.closeFail c with
      | some e => (-1, { w' with errno := failErrno e EIO })
      | none => (r, if r = -1 then w' else okErrW (w0.okErrno c) w'))

/-- Move the open descriptor `r` to number `k` if `k` is not open and below `2^31`; the number actually used. -/
def relocateW (r : Int32) (k : Nat) (w : Fs) : Int32 × Fs :=
  let free : Bool := match w.fds[k]? with
    | some (some _) => false
    | _ => true
  if 0 ≤ r.toInt ∧ k < 2 ^ 31 ∧ free = true then
    let grown := if k < w.fds.size then w.fds else w.fds ++ Array.replicate (k + 1 - w.fds.size) none
    let entry := (w.fds[r.toInt.toNat]?).getD none
    (Int32.ofNat k, { w with fds := (grown.set! k entry).set! r.toInt.toNat none })
  else (r, w)

/-- `open(path, oflag, 0666)`. M5: `-1` with a nonzero errno (nothing created), or any descriptor number below
`2^31` that was not open (the regular-file open picks the lowest, and fails with `EMFILE` when none is free;
`openFd` may choose another). -/
def fsOpen (path : Array UInt8) (oflag : Int32) : G Int32 := fun w0 =>
  let c := w0.nos
  let w := tickW w0
  match w0.openFail c with
  | some e => pure (-1, { w with errno := failErrno e EACCES })
  | none => do
    let (r, w') ← fsOpenReg path oflag w
    pure (if r = -1 then (r, w')
      else match w0.openFd c with
        | some k => relocateW r k (okErrW (w0.okErrno c) w')
        | none => (r, okErrW (w0.okErrno c) w'))

/-- `fcntl(fd, F_SETFL / F_SETFD, ...)` as used by `gz_open`: the result is ignored by the C and regular files
do not change behaviour, so it does nothing. -/
def fsFcntl (_fd : Int32) : G Unit := pure ()

/-! ## Harness access to the world (not C operations) -/

/-- Create or replace the file `name`. -/
def Fs.put (w : Fs) (name : Array UInt8) (data : Array UInt8) : Fs :=
  match findName w name with
  | some n => { w with nodes := w.nodes.set! n { data, isDir := false } }
  | none => { w with names := w.names.push (name, w.nodes.size), nodes := w.nodes.push { data, isDir := false } }

/-- Create a directory entry `name`. -/
def Fs.mkdir (w : Fs) (name : Array UInt8) : Fs :=
  { w with names := w.names.push (name, w.nodes.size), nodes := w.nodes.push { data := #[], isDir := true } }

/-- The bytes of the file `name`, if any. -/
def Fs.get? (w : Fs) (name : Array UInt8) : Option (Array UInt8) :=
  (findName w name).map fun n => w.nodes[n]!.data

/-- The position of the descriptor, if open. -/
def Fs.posOf? (w : Fs) (fd : Nat) : Option Nat :=
  if h : fd < w.fds.size then (w.fds[fd]).map (·.pos) else none

/-! ## Loops in `G` -/

def gwhile {σ : Type} (cond : σ → G (Bool × σ)) (body : σ → G σ) (s : σ) : G σ :=
  go C.fuel s
where
  go : Nat → σ → G σ
    | 0, _ => fun _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      let (c, s) ← cond s
      if c then go n (← body s) else pure s

def gdoWhile {σ : Type} (body : σ → G σ) (cond : σ → G (Bool × σ)) (s : σ) : G σ :=
  go C.fuel s
where
  go : Nat → σ → G σ
    | 0, _ => fun _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      let s ← body s
      let (c, s) ← cond s
      if c then go n s else pure s

/-! ## printf -/

/-- One variadic argument. `int`/`uint` are 32-bit, `str` is a `char *`. `long`/`ulong` are 64-bit and stand for the
64-bit type the conversion expects: `long`, `long long`, `intmax_t`, `ptrdiff_t` or `size_t` (and their unsigned or
signed counterparts); on x86_64 all of them are 64-bit. -/
inductive VaArg where
  | int (v : Int32)
  | uint (v : UInt32)
  | long (v : Int64)
  | ulong (v : UInt64)
  | str (p : BPtr)

structure Spec where
  minus : Bool := false
  zero : Bool := false
  plus : Bool := false
  space : Bool := false
  alt : Bool := false
  width : Nat := 0
  prec : Option Nat := none
  /-- the length modifier: 0 none, 1 `l`, 2 `ll`, 3 `z`, 4 `j`, 5 `t` -/
  lmod : Nat := 0
  conv : UInt8 := 0
  deriving DecidableEq

/-- A length modifier is present. On x86_64 every one the model reads (`l`, `ll`, `z`, `j`, `t`) names a 64-bit
integer type, so `%ld` and `%lld` both take `VaArg.long`: `VaArg.long` stands for the 64-bit type the conversion
expects. -/
def Spec.long (sp : Spec) : Bool := sp.lmod != 0

/-- The conversion specification is defined in C17 7.21.6.1 for the conversions the model formats: `%%` is the whole
specification (p8); `c` and `s` take no length modifier (`l` is a wide conversion, not modelled; `ll`, `z`, `j`, `t`
are undefined, p7), no `0` flag and no `#` flag (p6); `c` takes no precision (p4); `d`, `i`, `u` take no `#` flag
(p6). Other conversions are checked where they are formatted. -/
def specDefined (sp : Spec) : Bool :=
  if sp.conv == 37 then sp == { conv := 37 }
  else if sp.conv == 99 then sp.lmod == 0 && !sp.zero && !sp.alt && sp.prec.isNone
  else if sp.conv == 115 then sp.lmod == 0 && !sp.zero && !sp.alt
  else if sp.conv == 100 || sp.conv == 105 || sp.conv == 117 then !sp.alt
  else true

def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

/-- The decimal number that starts at `j` (at most `fuel` digits) added to `v`: its value and the position after it. -/
def readNumGo (f : Array UInt8) : Nat → Nat → Nat → Nat × Nat
  | 0, j, v => (v, j)
  | k + 1, j, v =>
    if j < f.size && isDigit f[j]! then readNumGo f k (j + 1) (v * 10 + (f[j]!.toNat - 48)) else (v, j)

/-- The decimal number that starts at `i` and the position after it. -/
def readNum (f : Array UInt8) (i : Nat) : Nat × Nat := readNumGo f f.size i 0

/-- The flags `-0+ #` that start at `j` (at most `fuel` of them), set in `sp`, and the position after them. -/
def parseFlags (f : Array UInt8) : Nat → Nat → Spec → Spec × Nat
  | 0, j, sp => (sp, j)
  | k + 1, j, sp =>
    if j < f.size then
      if f[j]! == 45 then parseFlags f k (j + 1) { sp with minus := true }
      else if f[j]! == 48 then parseFlags f k (j + 1) { sp with zero := true }
      else if f[j]! == 43 then parseFlags f k (j + 1) { sp with plus := true }
      else if f[j]! == 32 then parseFlags f k (j + 1) { sp with space := true }
      else if f[j]! == 35 then parseFlags f k (j + 1) { sp with alt := true }
      else (sp, j)
    else (sp, j)

/-- The conversion specification that starts at `i` (after the `%`): flags, width, precision, length modifier and
conversion character, and the position after it; `none` if the format ends first. -/
def parseSpec (f : Array UInt8) (i : Nat) : Option (Spec × Nat) :=
  let (sp, j) := parseFlags f f.size i {}
  let (w, j) := readNum f j
  let sp := { sp with width := w }
  let (sp, j) :=
    if j < f.size && f[j]! == 46 then
      let (p, j3) := readNum f (j + 1)
      ({ sp with prec := some p }, j3)
    else (sp, j)
  let (sp, j) :=
    if j < f.size && f[j]! == 108 then
      if j + 1 < f.size && f[j + 1]! == 108 then ({ sp with lmod := 2 }, j + 2) else ({ sp with lmod := 1 }, j + 1)
    else if j < f.size && f[j]! == 122 then ({ sp with lmod := 3 }, j + 1)
    else if j < f.size && f[j]! == 106 then ({ sp with lmod := 4 }, j + 1)
    else if j < f.size && f[j]! == 116 then ({ sp with lmod := 5 }, j + 1)
    else (sp, j)
  if j < f.size then some ({ sp with conv := f[j]! }, j + 1) else none

def natDigits (v : Nat) (base : Nat) (upper : Bool) : Array UInt8 :=
  (Nat.toDigits base v).toArray.map fun c =>
    let b := c.toNat.toUInt8
    if upper && b ≥ 97 then b - 32 else b

def pad (sp : Spec) (body : Array UInt8) (zeroOk : Bool) : Array UInt8 :=
  if body.size ≥ sp.width then body
  else
    let n := sp.width - body.size
    if sp.minus then body ++ Array.replicate n 32
    else if sp.zero && zeroOk then
      -- zeros go after the sign / prefix: callers pass sign/prefix separately, see fmtInt
      Array.replicate n 48 ++ body
    else Array.replicate n 32 ++ body

def fmtInt (sp : Spec) (neg : Bool) (mag : Nat) (base : Nat) (upper : Bool) (signed : Bool) :
    Array UInt8 :=
  let ds0 := natDigits mag base upper
  let ds1 := match sp.prec with
    | some 0 => if mag == 0 then #[] else ds0
    | some p => if ds0.size < p then Array.replicate (p - ds0.size) 48 ++ ds0 else ds0
    | none => ds0
  let prefixB : Array UInt8 :=
    if signed then (if neg then #[45] else if sp.plus then #[43] else if sp.space then #[32] else #[])
    else if sp.alt && mag != 0 && base == 16 then (if upper then #[48, 88] else #[48, 120])
    else #[]
  let ds1 := if sp.alt && base == 8 && (ds1.isEmpty || ds1[0]! != 48) then #[48] ++ ds1 else ds1
  let total := prefixB.size + ds1.size
  if total ≥ sp.width then prefixB ++ ds1
  else
    let n := sp.width - total
    if sp.minus then prefixB ++ ds1 ++ Array.replicate n 32
    else if sp.zero && sp.prec.isNone then prefixB ++ Array.replicate n 48 ++ ds1
    else Array.replicate n 32 ++ prefixB ++ ds1

/-- The text of a `%s` argument: what the heap resolver `res` gives; none for a null pointer (C17 7.21.6.1p8: the
argument is a pointer to an array; glibc's `(null)` is not C). -/
def argStr (res : BPtr → Option (Array UInt8)) (p : BPtr) : Option (Array UInt8) :=
  if p == .null then none else res p

/-- The output of `printf(f, args)` from position `i` on, as bytes, appended to `out`; `res p` is the string at `p` in
the heap (`none` if there is none). `fuel` is the number of steps left (`f.size + 1` suffices: each step consumes a
character). Supports `%%`, `%c`, `%s`, `%d`, `%i`, `%u`, `%x`, `%X`, `%o` with the flags `-0+ #`, a width, a
precision and the length modifiers `l`, `ll`, `z`, `j`, `t` on the integer conversions, where C17 7.21.6.1 defines
them (`specDefined`). Anything else, an argument of the wrong kind, a negative signed argument for an unsigned
conversion (p9), or too few arguments is an error: undefined in C, or not modelled (`%lc`, `%ls`, `h`, `hh`, `L`,
`*`, `%n`, `%p`, floating point, positional arguments). -/
def formatGo (f : Array UInt8) (res : BPtr → Option (Array UInt8)) :
    Nat → Nat → List VaArg → Array UInt8 → Except String (Array UInt8)
  | 0, _, _, out => .ok out
  | fuel + 1, i, args, out =>
    if i < f.size then
      if f[i]! != 37 then formatGo f res fuel (i + 1) args (out.push f[i]!)
      else
        match parseSpec f (i + 1) with
        | none => .error "printf: incomplete conversion"
        | some (sp, j) =>
          let cv := sp.conv
          if !specDefined sp then .error "printf: conversion specification undefined in C or not modelled"
          else if cv == 37 then formatGo f res fuel j args (out.push 37)
          else if cv == 99 then
            match args with
            | .int v :: r => formatGo f res fuel j r (out ++ pad sp #[v.toUInt32.toUInt8] false)
            | _ => .error "printf: %c needs an int"
          else if cv == 115 then
            match args with
            | .str p :: r =>
              match argStr res p with
              | some s =>
                let s := match sp.prec with | some k => s.extract 0 k | none => s
                formatGo f res fuel j r (out ++ pad sp s false)
              | none => .error "printf: %s argument is NULL or not a NUL-terminated string"
            | _ => .error "printf: %s needs a pointer"
          else if cv == 100 || cv == 105 then
            match sp.long, args with
            | false, .int v :: r =>
              formatGo f res fuel j r (out ++ fmtInt sp (v.toInt < 0) v.toInt.natAbs 10 false true)
            | true, .long v :: r =>
              formatGo f res fuel j r (out ++ fmtInt sp (v.toInt < 0) v.toInt.natAbs 10 false true)
            | _, _ => .error "printf: %d argument of the wrong kind"
          else if cv == 117 || cv == 120 || cv == 88 || cv == 111 then
            let base := if cv == 117 then 10 else if cv == 111 then 8 else 16
            match sp.long, args with
            | false, .uint v :: r => formatGo f res fuel j r (out ++ fmtInt sp false v.toNat base (cv == 88) false)
            | false, .int v :: r =>
              if v < 0 then .error "printf: negative int for an unsigned conversion"
              else formatGo f res fuel j r (out ++ fmtInt sp false v.toUInt32.toNat base (cv == 88) false)
            | true, .ulong v :: r => formatGo f res fuel j r (out ++ fmtInt sp false v.toNat base (cv == 88) false)
            | true, .long v :: r =>
              if v < 0 then .error "printf: negative long for an unsigned conversion"
              else formatGo f res fuel j r (out ++ fmtInt sp false v.toUInt64.toNat base (cv == 88) false)
            | _, _ => .error "printf: unsigned conversion argument of the wrong kind"
          else .error "printf: conversion not modelled"
    else .ok out

/-- The string at `p` in the heap `h` (the bytes before the first NUL), if there is one. -/
def heapStr (h : Heap) (p : BPtr) : Option (Array UInt8) :=
  match cstring p h with | .ok (s, _) => some s | .error _ => none

/-- The full output of `printf(fmt, args)` as bytes (`formatGo`); the heap is read, not changed. -/
def formatBytes (f : Array UInt8) (args : List VaArg) : M (Array UInt8) := fun h =>
  match formatGo f (heapStr h) (f.size + 1) 0 args #[] with
  | .ok out => .ok (out, h)
  | .error m => .error (.ub m)

/-- `snprintf(dst, size, fmt, ...)` for the fixed formats of gzlib.c (`"%s%s%s"`, `"%s"`, `"<fd:%d>"`): writes at
most `size - 1` characters of the full output and a NUL (nothing if `size` is 0), and returns the full length, or −1
when it exceeds `INT_MAX`. For `%s` with a `char *` and `%d` that is glibc's only failure (`EOVERFLOW`); `errno` is
not modelled here, and no caller reads it before a system call sets it again (docs/en/trusted-base.md). -/
def snprintf (dst : BPtr) (size : UInt64) (fmt : BPtr) (args : List VaArg) : M Int32 := do
  let f ← cstring fmt
  let out ← formatBytes f args
  if size != 0 then
    let k := min out.size (size.toNat - 1)
    storeBytes dst (out.extract 0 k)
    let q ← dst.add k
    store8 q 0
  return if out.size > 2147483647 then -1 else Int32.ofNat out.size

/-- A pointer argument whose block was freed: its value is indeterminate (C17 6.2.4p2), and passing it is undefined. -/
def argDangling (h : Heap) : VaArg → Bool
  | .str (.ref (.blk b) _) => (h.bytes b).isNone
  | _ => false

/-- The arguments of a caller-format call: none points into a freed block. -/
def argsLive (args : List VaArg) : M Unit := fun h =>
  if args.any (argDangling h) then .error (.ub "vsnprintf: a pointer argument into a freed block")
  else .ok ((), h)

/-- `vsnprintf(dst, size, fmt, va)` with a caller's format (`gzvprintf`): an external call, modelled by its C contract
(C17 7.21.6.12), not by formatting. The caller guarantees that the call is defined for its format and arguments
(`docs/en/trusted-base.md`). The model reads the format as a string and faults on a pointer argument into a freed
block; it does not read the format's conversions. The world oracle chooses the result `r = printfRet n`, any `int`.
If `r ≥ 0` (success, `r` the length of the full output, possibly `size` or more): the first `min(r, size - 1)` bytes
of `printfOut n` (padded with zeros) and a NUL after them, nothing if `size` is 0. If `r < 0` (failure): `errno` is
set nonzero (`printfErrno n`, zero reads as `EOVERFLOW`), and the buffer gets arbitrary bytes, the first `size` bytes
of `printfOut n` at most, with no NUL promised. Nothing outside `[dst, dst + size)` is written. -/
def vsnprintf (dst : BPtr) (size : UInt64) (fmt : BPtr) (args : List VaArg) : G Int32 := do
  let w ← get
  set { w with nprintf := w.nprintf + 1 }
  let _ ← cstring fmt
  argsLive args
  let r := w.printfRet w.nprintf
  if 0 ≤ r then
    if size != 0 then
      let k := min r.toInt.toNat (size.toNat - 1)
      storeBytes dst ((w.printfOut w.nprintf ++ Array.replicate k 0).extract 0 k)
      let q ← dst.add k
      store8 q 0
    return r
  else
    let e := w.printfErrno w.nprintf
    setErrno (if e == 0 then EOVERFLOW else e)
    storeBytes dst ((w.printfOut w.nprintf).extract 0 size.toNat)
    return r

end Zlib.GzFs
