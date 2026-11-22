import ZlibF.Spec.Common.Copy
import ZlibF.Spec.Common.HeapUniq

namespace ZlibF.Spec.Public
open C Zlib.GzFs ZlibF.Spec

def FileSystem (fs : Fs) : Prop :=
  fs.fsizeLimit ≤ 2 ^ 63 - 1 ∧
  (∀ path node, (path, node) ∈ fs.names.toList → node < fs.nodes.size) ∧
  (∀ (i : Nat) (file : OFile), fs.fds[i]? = some (some file) → file.node < fs.nodes.size ∧
    file.pos ≤ 2 ^ 63 - 1 ∧ (∀ node : Node, fs.nodes[file.node]? = some node → node.isDir = true → file.wr = false)) ∧
  (∀ (i : Nat) (node : Node), fs.nodes[i]? = some node → node.data.size ≤ 2 ^ 63 - 1)

def GzOwned (h : Heap) (i : Nat) (s : GzState) (b : Nat) : Prop :=
  b = i ∨ s.path = .ref (.blk b) 0 ∨ s.msg = .ref (.blk b) 0 ∨
  (s.size ≠ 0 ∧ (s.in = .ref (.blk b) 0 ∨
    ((s.mode = GZ_READ ∨ s.direct = 0) ∧
      (s.out = .ref (.blk b) 0 ∨ StreamOwned h (.in_gzstate_strm i) b))))

def MallocBuffer (h : Heap) (p : BPtr) (n : Nat) : Prop :=
  ∃ b a, p = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false ∧ n ≤ a.size

def GzRange (h : Heap) (i : Nat) (s : GzState) (p : BPtr) (n : Nat) (write : Bool) : Prop :=
  n = 0 ∨ ((∃ xs, Bytes h p n xs) ∧ (write = true → Writable h p n) ∧
    ∀ b, ByteRoot p b → ¬ GzOwned h i s b)

def Formatted (h : Heap) (format : BPtr) (args : List VaArg) (xs : List UInt8) : Prop :=
  ∃ fmt, CString h format fmt ∧
    Zlib.GzFs.formatGo fmt.toArray (Zlib.GzFs.heapStr h) (fmt.length + 1) 0 args #[] = .ok xs.toArray

def GzOperation (i : Nat) : Call → Prop
  | .gzbuffer p _ | .gzclearerr p | .gzdirect p | .gzeof p | .gzerror p _
  | .gzflush p _ | .gzgetc p | .gzgetc_ p | .gzgets p _ _ | .gzoffset p | .gzoffset64 p
  | .gzprintf p _ _ | .gzputc p _ | .gzputs p _ | .gzread p _ _ | .gzrewind p
  | .gzseek p _ _ | .gzseek64 p _ _ | .gzsetparams p _ _ | .gztell p | .gztell64 p
  | .gzvprintf p _ _ | .gzwrite p _ _ | .gzungetc _ p | .gzfread _ _ _ p | .gzfwrite _ _ _ p =>
      p = some (.in_gzstate_x i)
  | _ => False

def GzArguments (h : Heap) (i : Nat) (s : GzState) : Call → Prop
  | .gzread _ p n =>
      if n.toNat ≥ 2 ^ 31 then True else GzRange h i s p n.toNat true
  | .gzwrite _ p n =>
      if n.toNat ≥ 2 ^ 31 then True else GzRange h i s p n.toNat false
  | .gzfread p size n _ =>
      if size.toNat * n.toNat ≥ 2 ^ 64 then True else GzRange h i s p (size.toNat * n.toNat) true
  | .gzfwrite p size n _ =>
      if size.toNat * n.toNat ≥ 2 ^ 64 then True else GzRange h i s p (size.toNat * n.toNat) false
  | .gzgets _ p n => if n.toInt < 1 ∨ p = .null then True else GzRange h i s p n.toInt.toNat true
  | .gzputs _ p => ∃ xs, CString h p xs ∧ GzRange h i s p (xs.length + 1) false
  | .gzprintf _ p args | .gzvprintf _ p args =>
      -- past gzvprintf's mode test, vsnprintf reads the format and is passed the pointer arguments; that the call
      -- is defined in C for this format and these arguments is the caller's (docs/en/trusted-base.md, vsnprintf)
      ((s.mode = GZ_WRITE ∧ (s.err = Z_OK ∨ s.again ≠ 0)) →
        (∃ fmt, CString h p fmt) ∧ ∀ q, VaArg.str q ∈ args → ∀ b o, q = .ref (.blk b) o → ∃ a, h.bytes b = some a) ∧
      (∀ b, ByteRoot p b → ¬ GzOwned h i s b) ∧
      ∀ q, VaArg.str q ∈ args → ∀ b, ByteRoot q b → ¬ GzOwned h i s b
  | .gzerror _ p => p = .null ∨ GzRange h i s p 4 true
  | _ => True

def GzCallerFrame (h after : Heap) (i : Nat) (s : GzState) : Prop :=
  Fresh after ∧ Zlib.Gzlib.Spec.Uniq after ∧ LibraryGlobals after ∧
  Frame h after (fun b => ¬ GzOwned h i s b)

def NoAllocationFailure (h : Heap) : Prop := ∀ n, h.allocOk n = true

def putGz (h : Heap) (i : Nat) (s : GzState) : Heap :=
  { h with gzstates := upd h.gzstates i (some s) }

end ZlibF.Spec.Public
