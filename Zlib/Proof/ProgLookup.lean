import Zlib.Spec.Safety
import C99.Proof.Mem
import Lean

/-!
# Program Lookup & `initLibz` Inversion Lemmas (`Zlib.Proof.ProgLookup`)

Structural lookup lemmas for `progOfTUs Zlib.allFiles` and `initLibz` without
reducing large static data tables (`crc_table`, `crc_braid5_table`, `inffixed`, `trees`).
-/

namespace Zlib.Proof

open C99 C99.Sem C99.Proof Zlib Zlib.Spec

/-! ## 1. List, Lookup, and TU Extraction Helpers -/

theorem lookup_append_some {α β : Type} [BEq α] {l1 l2 : List (α × β)} {k : α} {v : β}
    (h : l1.lookup k = some v) : (l1 ++ l2).lookup k = some v := by
  induction l1 with
  | nil => simp at h
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [List.cons_append, List.lookup] at h ⊢
    cases hbeq : k == k'
    · simp only [hbeq] at h ⊢; exact ih h
    · simp only [hbeq] at h ⊢; exact h

theorem lookup_append_none {α β : Type} [BEq α] {l1 l2 : List (α × β)} {k : α}
    (h : l1.lookup k = none) : (l1 ++ l2).lookup k = l2.lookup k := by
  induction l1 with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [List.cons_append, List.lookup] at h ⊢
    cases hbeq : k == k'
    · simp only [hbeq] at h ⊢; exact ih h
    · simp only [hbeq] at h; cases h

theorem lookup_cons_eq {α β : Type} [BEq α] [LawfulBEq α] {k : α} {v : β}
    (l : List (α × β)) : ((k, v) :: l).lookup k = some v := by
  simp [List.lookup]

theorem lookup_cons_ne {α β : Type} [BEq α] [LawfulBEq α] {k k' : α} {v : β}
    (l : List (α × β)) (hne : k ≠ k') : ((k', v) :: l).lookup k = l.lookup k := by
  simp [List.lookup, beq_false_of_ne hne]

theorem env_lookup_none_of_not_mem {env : Env} {x : String}
    (h : x ∉ env.map (·.1)) : env.lookup x = none := by
  induction env with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup, beq_false_of_ne h.1]
    exact ih h.2

def tuFnEntries (tu : TU) : List (String × FnDef) :=
  tu.items.filterMap fun | .fnDef f => some (f.name, f) | _ => none

def tuProtoEntries (tu : TU) : List (String × FnSig) :=
  tu.items.filterMap fun
    | .fnDef f => some (f.name, (f.retTy, f.params.map (·.ty), f.variadic))
    | .fnProto _ r n ps v => some (n, (r, ps.map (·.ty), v))
    | _ => none

def tuGlobals (tu : TU) : List (Linkage × VarDecl) :=
  tu.items.filterMap fun | .globalDecl l d => if l == .extern_ then none else some (l, d) | _ => none

def tuFnNames (tu : TU) : List String :=
  tu.items.filterMap fun | .fnDef f => some f.name | _ => none

def tuProtoNames (tu : TU) : List String :=
  tu.items.filterMap fun
    | .fnDef f => some f.name
    | .fnProto _ _ n _ _ => some n
    | _ => none

def fnDefSig (f : FnDef) : FnSig :=
  (f.retTy, f.params.map (·.ty), f.variadic)

theorem collectTagEnv_append (xs ys : List TopItem) :
    collectTagEnv (xs ++ ys) = collectTagEnv xs ++ collectTagEnv ys := by
  simp [collectTagEnv, List.filterMap_append]

theorem progOfTUs_tags (tus : List TU) :
    (progOfTUs tus).tags = collectTagEnv (tus.flatMap (·.items)) := rfl

theorem filterMap_flatMap {α β γ : Type} (f : α → List β) (g : β → Option γ) (xs : List α) :
    (xs.flatMap f).filterMap g = xs.flatMap fun a => (f a).filterMap g := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.flatMap_cons, List.filterMap_append, ih]

theorem progOfTUs_globals (tus : List TU) :
    (progOfTUs tus).globals = tus.flatMap tuGlobals := by
  unfold progOfTUs tuGlobals
  exact filterMap_flatMap _ _ tus

theorem progOfTUs_fns (tus : List TU) (sym : String) :
    (progOfTUs tus).fns sym = (tus.flatMap tuFnEntries).lookup sym := by
  unfold progOfTUs tuFnEntries
  dsimp only
  rw [filterMap_flatMap]
  rfl

theorem progOfTUs_fnProtos (tus : List TU) (sym : String) :
    (progOfTUs tus).fnProtos sym = ((tus.flatMap tuProtoEntries) ++ stdLibcProtos).lookup sym := by
  unfold progOfTUs tuProtoEntries
  dsimp only
  rw [filterMap_flatMap]
  rfl

/-! ## 2. Type Layout Lemmas (`sizeofTy`, `alignofTy`, `fieldLayout?`) -/

@[simp] theorem alignofAux_void (tags : TypeEnv) (f : Nat) : alignofAux tags f .void = 1 := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_int (tags : TypeEnv) (f : Nat) (k : IntKind) :
    alignofAux tags f (.int k) = k.align := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_const (tags : TypeEnv) (f : Nat) (t : CTy) :
    alignofAux tags f (.const_ t) = alignofAux tags f t := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_ptr (tags : TypeEnv) (f : Nat) (t : CTy) :
    alignofAux tags f (.ptr t) = 8 := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_array (tags : TypeEnv) (f : Nat) (el : CTy) (n? : Option Nat) :
    alignofAux tags f (.array el n?) = alignofAux tags f el := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_enumTy (tags : TypeEnv) (f : Nat) (tag : String) (isU : Bool) :
    alignofAux tags f (.enumTy tag isU) = 4 := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_fnPtr (tags : TypeEnv) (f : Nat) (r : CTy) (ps : List CTy) (v : Bool) :
    alignofAux tags f (.fnPtr r ps v) = 8 := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_vaList (tags : TypeEnv) (f : Nat) :
    alignofAux tags f .vaList = 8 := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_typedef (tags : TypeEnv) (f : Nat) (n : String) (t : CTy) :
    alignofAux tags f (.typedef n t) = alignofAux tags f t := by
  cases f <;> simp [alignofAux]

@[simp] theorem sizeofAux_void (tags : TypeEnv) (f : Nat) : sizeofAux tags f .void = 0 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_int (tags : TypeEnv) (f : Nat) (k : IntKind) :
    sizeofAux tags f (.int k) = k.bytes := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_const (tags : TypeEnv) (f : Nat) (t : CTy) :
    sizeofAux tags f (.const_ t) = sizeofAux tags f t := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_ptr (tags : TypeEnv) (f : Nat) (t : CTy) :
    sizeofAux tags f (.ptr t) = 8 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_array_some (tags : TypeEnv) (f : Nat) (el : CTy) (n : Nat) :
    sizeofAux tags f (.array el (some n)) = n * sizeofAux tags f el := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_array_none (tags : TypeEnv) (f : Nat) (el : CTy) :
    sizeofAux tags f (.array el none) = 0 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_enumTy (tags : TypeEnv) (f : Nat) (tag : String) (isU : Bool) :
    sizeofAux tags f (.enumTy tag isU) = 4 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_fnPtr (tags : TypeEnv) (f : Nat) (r : CTy) (ps : List CTy) (v : Bool) :
    sizeofAux tags f (.fnPtr r ps v) = 8 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_vaList (tags : TypeEnv) (f : Nat) :
    sizeofAux tags f .vaList = 24 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_typedef (tags : TypeEnv) (f : Nat) (n : String) (t : CTy) :
    sizeofAux tags f (.typedef n t) = sizeofAux tags f t := by
  cases f <;> simp [sizeofAux]

@[simp] theorem alignofTy_void (tags : TypeEnv) : alignofTy tags .void = 1 :=
  alignofAux_void tags _
@[simp] theorem alignofTy_int (tags : TypeEnv) (k : IntKind) : alignofTy tags (.int k) = k.align :=
  alignofAux_int tags _ k
@[simp] theorem alignofTy_const (tags : TypeEnv) (t : CTy) :
    alignofTy tags (.const_ t) = alignofTy tags t :=
  alignofAux_const tags _ t
@[simp] theorem alignofTy_ptr (tags : TypeEnv) (t : CTy) : alignofTy tags (.ptr t) = 8 :=
  alignofAux_ptr tags _ t
@[simp] theorem alignofTy_array (tags : TypeEnv) (el : CTy) (n? : Option Nat) :
    alignofTy tags (.array el n?) = alignofTy tags el :=
  alignofAux_array tags _ el n?
@[simp] theorem alignofTy_enumTy (tags : TypeEnv) (tag : String) (isU : Bool) :
    alignofTy tags (.enumTy tag isU) = 4 :=
  alignofAux_enumTy tags _ tag isU
@[simp] theorem alignofTy_fnPtr (tags : TypeEnv) (r : CTy) (ps : List CTy) (v : Bool) :
    alignofTy tags (.fnPtr r ps v) = 8 :=
  alignofAux_fnPtr tags _ r ps v
@[simp] theorem alignofTy_vaList (tags : TypeEnv) : alignofTy tags .vaList = 8 :=
  alignofAux_vaList tags _
@[simp] theorem alignofTy_typedef (tags : TypeEnv) (n : String) (t : CTy) :
    alignofTy tags (.typedef n t) = alignofTy tags t :=
  alignofAux_typedef tags _ n t

@[simp] theorem sizeofTy_void (tags : TypeEnv) : sizeofTy tags .void = 0 :=
  sizeofAux_void tags _
@[simp] theorem sizeofTy_int (tags : TypeEnv) (k : IntKind) : sizeofTy tags (.int k) = k.bytes :=
  sizeofAux_int tags _ k
@[simp] theorem sizeofTy_const (tags : TypeEnv) (t : CTy) :
    sizeofTy tags (.const_ t) = sizeofTy tags t :=
  sizeofAux_const tags _ t
@[simp] theorem sizeofTy_ptr (tags : TypeEnv) (t : CTy) : sizeofTy tags (.ptr t) = 8 :=
  sizeofAux_ptr tags _ t
@[simp] theorem sizeofTy_array_some (tags : TypeEnv) (el : CTy) (n : Nat) :
    sizeofTy tags (.array el (some n)) = n * sizeofTy tags el :=
  sizeofAux_array_some tags _ el n
@[simp] theorem sizeofTy_array_none (tags : TypeEnv) (el : CTy) :
    sizeofTy tags (.array el none) = 0 :=
  sizeofAux_array_none tags _ el
@[simp] theorem sizeofTy_enumTy (tags : TypeEnv) (tag : String) (isU : Bool) :
    sizeofTy tags (.enumTy tag isU) = 4 :=
  sizeofAux_enumTy tags _ tag isU
@[simp] theorem sizeofTy_fnPtr (tags : TypeEnv) (r : CTy) (ps : List CTy) (v : Bool) :
    sizeofTy tags (.fnPtr r ps v) = 8 :=
  sizeofAux_fnPtr tags _ r ps v
@[simp] theorem sizeofTy_vaList (tags : TypeEnv) : sizeofTy tags .vaList = 24 :=
  sizeofAux_vaList tags _
@[simp] theorem sizeofTy_typedef (tags : TypeEnv) (n : String) (t : CTy) :
    sizeofTy tags (.typedef n t) = sizeofTy tags t :=
  sizeofAux_typedef tags _ n t

def headerTagEnv : TypeEnv :=
  collectTagEnv (Zlib.allHeaders.flatMap (·.items))

private theorem headerTagEnv_len : headerTagEnv.length = 12 := rfl

theorem prog_tags_eq_append :
    (progOfTUs Zlib.allFiles).tags =
      headerTagEnv ++ collectTagEnv (Zlib.allTUs.flatMap (·.items)) := by
  rw [progOfTUs_tags, Zlib.allFiles, List.flatMap_append, collectTagEnv_append]
  rfl

private theorem prog_tags_len_ge : 12 ≤ (progOfTUs Zlib.allFiles).tags.length := by
  rw [prog_tags_eq_append, List.length_append, headerTagEnv_len]
  exact Nat.le_add_right _ _

theorem prog_tags_lookup_header {tag : String} {defn : TagDef}
    (h : headerTagEnv.lookup tag = some defn) :
    (progOfTUs Zlib.allFiles).tags.lookup tag = some defn := by
  rw [prog_tags_eq_append]
  exact lookup_append_some h

private def zStreamFields : List (String × CTy) := [
  ("next_in", .ptr (.const_ (.typedef "Bytef" (.typedef "Byte" (.int .u8))))),
  ("avail_in", .typedef "uInt" (.int .u32)),
  ("total_in", .typedef "uLong" (.int .u64)),
  ("next_out", .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))),
  ("avail_out", .typedef "uInt" (.int .u32)),
  ("total_out", .typedef "uLong" (.int .u64)),
  ("msg", .ptr (.const_ (.int .i8))),
  ("state", .ptr (.structTy "internal_state")),
  ("zalloc", .typedef "alloc_func" (.fnPtr (.typedef "voidpf" (.ptr .void))
    [.typedef "voidpf" (.ptr .void), .typedef "uInt" (.int .u32), .typedef "uInt" (.int .u32)] false)),
  ("zfree", .typedef "free_func" (.fnPtr .void
    [.typedef "voidpf" (.ptr .void), .typedef "voidpf" (.ptr .void)] false)),
  ("opaque", .typedef "voidpf" (.ptr .void)),
  ("data_type", .int .i32),
  ("adler", .typedef "uLong" (.int .u64)),
  ("reserved", .typedef "uLong" (.int .u64))
]

private theorem headerTagEnv_lookup_z_stream_s :
    headerTagEnv.lookup "z_stream_s" = some (.structDef zStreamFields) := rfl

private theorem headerTagEnv_lookup_gz_header_s :
    headerTagEnv.lookup "gz_header_s" = some (.structDef [
      ("text", .int .i32),
      ("time", .typedef "uLong" (.int .u64)),
      ("xflags", .int .i32),
      ("os", .int .i32),
      ("extra", .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))),
      ("extra_len", .typedef "uInt" (.int .u32)),
      ("extra_max", .typedef "uInt" (.int .u32)),
      ("name", .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))),
      ("name_max", .typedef "uInt" (.int .u32)),
      ("comment", .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))),
      ("comm_max", .typedef "uInt" (.int .u32)),
      ("hcrc", .int .i32),
      ("done", .int .i32)
    ]) := rfl

private theorem alignofFields_cons (tags : TypeEnv) (fuel : Nat) (nm : String) (fty : CTy)
    (rest : List (String × CTy)) (acc : Nat) :
    alignofFields tags fuel ((nm, fty) :: rest) acc =
      alignofFields tags fuel rest (max acc (alignofAux tags fuel fty)) := by
  cases fuel <;> simp [alignofFields]

private theorem alignofFields_nil (tags : TypeEnv) (fuel : Nat) (acc : Nat) :
    alignofFields tags fuel [] acc = acc := by
  cases fuel <;> simp [alignofFields]

private theorem sizeofStructFields_cons (tags : TypeEnv) (fuel sz al : Nat) (nm : String)
    (fty : CTy) (rest : List (String × CTy)) :
    sizeofStructFields tags fuel sz al ((nm, fty) :: rest) =
      let fa := max 1 (alignofAux tags fuel fty)
      let off := alignUp sz fa
      sizeofStructFields tags fuel (off + sizeofAux tags fuel fty) (max al fa) rest := by
  cases fuel <;> simp [sizeofStructFields]

private theorem sizeofStructFields_nil (tags : TypeEnv) (fuel sz al : Nat) :
    sizeofStructFields tags fuel sz al [] = alignUp sz al := by
  cases fuel <;> simp [sizeofStructFields]

private theorem alignofAux_ge_one_z_stream_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "z_stream_s" = some (.structDef zStreamFields)) :
    alignofAux tags (n + 1) (.structTy "z_stream_s") = 8 := by
  rw [alignofAux, hlook]
  simp only [zStreamFields, alignofFields_cons, alignofFields_nil,
    alignofAux_ptr, alignofAux_typedef, alignofAux_int, alignofAux_fnPtr, IntKind.align]
  rfl

private theorem sizeofAux_ge_one_z_stream_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "z_stream_s" = some (.structDef zStreamFields)) :
    sizeofAux tags (n + 1) (.structTy "z_stream_s") = 112 := by
  rw [sizeofAux, hlook]
  simp only [zStreamFields, sizeofStructFields_cons, sizeofStructFields_nil,
    alignofAux_ptr, alignofAux_typedef, alignofAux_int, alignofAux_fnPtr,
    sizeofAux_ptr, sizeofAux_typedef, sizeofAux_int, sizeofAux_fnPtr,
    IntKind.align, IntKind.bytes, alignUp]
  rfl

private theorem alignofAux_ge_one_gz_header_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "gz_header_s" = headerTagEnv.lookup "gz_header_s") :
    alignofAux tags (n + 1) (.structTy "gz_header_s") = 8 := by
  rw [alignofAux, hlook, headerTagEnv_lookup_gz_header_s]
  simp only [alignofFields_cons, alignofFields_nil,
    alignofAux_int, alignofAux_typedef, alignofAux_ptr, IntKind.align]
  rfl

private theorem sizeofAux_ge_one_gz_header_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "gz_header_s" = headerTagEnv.lookup "gz_header_s") :
    sizeofAux tags (n + 1) (.structTy "gz_header_s") = 80 := by
  rw [sizeofAux, hlook, headerTagEnv_lookup_gz_header_s]
  simp only [sizeofStructFields_cons, sizeofStructFields_nil,
    alignofAux_int, alignofAux_typedef, alignofAux_ptr,
    sizeofAux_int, sizeofAux_typedef, sizeofAux_ptr,
    IntKind.align, IntKind.bytes, alignUp]
  rfl

theorem alignofTy_z_stream_s :
    alignofTy (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") = 8 := by
  unfold alignofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge
  rw [hk]
  exact alignofAux_ge_one_z_stream_s _ _ (prog_tags_lookup_header headerTagEnv_lookup_z_stream_s)

theorem sizeofTy_z_stream_s :
    sizeofTy (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") = 112 := by
  unfold sizeofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge
  rw [hk]
  exact sizeofAux_ge_one_z_stream_s _ _ (prog_tags_lookup_header headerTagEnv_lookup_z_stream_s)

theorem alignofTy_gz_header_s :
    alignofTy (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") = 8 := by
  unfold alignofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge
  rw [hk]
  exact alignofAux_ge_one_gz_header_s _ _ (by
    rw [prog_tags_eq_append]
    exact lookup_append_some headerTagEnv_lookup_gz_header_s |>.trans headerTagEnv_lookup_gz_header_s.symm)

theorem sizeofTy_gz_header_s :
    sizeofTy (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") = 80 := by
  unfold sizeofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge
  rw [hk]
  exact sizeofAux_ge_one_gz_header_s _ _ (by
    rw [prog_tags_eq_append]
    exact lookup_append_some headerTagEnv_lookup_gz_header_s |>.trans headerTagEnv_lookup_gz_header_s.symm)

theorem prog_tags_lookup_z_stream_s :
    (progOfTUs Zlib.allFiles).tags.lookup "z_stream_s" = some (.structDef zStreamFields) :=
  prog_tags_lookup_header headerTagEnv_lookup_z_stream_s

section PrivateUnfoldHelper

open Lean Meta Elab Tactic in
local elab "unfold_lhs" h:ident : tactic => withMainContext do
  let decl ← getLocalDeclFromUserName h.getId
  let some (_, lhs, rhs) := decl.type.eq? | throwError "expected equality at {h}"
  let some lhs' ← unfoldDefinition? lhs | throwError "cannot unfold head of {lhs}"
  let newType ← mkEq lhs' rhs
  let goal ← getMainGoal
  let prf := mkFVar decl.fvarId
  let newGoal ← goal.assert decl.userName newType prf
  let (_, newGoal) ← newGoal.intro1P
  let newGoal ← newGoal.tryClear decl.fvarId
  replaceMainGoal [newGoal]

open Lean Meta Elab Tactic in
local elab "unfold_head_lhs" : tactic => withMainContext do
  let tgt ← getMainTarget
  let some (_, lhs, rhs) := tgt.eq? | throwError "expected eq"
  let some lhs' ← unfoldDefinition? lhs | throwError "cannot unfold head of {lhs}"
  replaceMainGoal [← (← getMainGoal).change (← mkEq lhs' rhs)]

private theorem fieldLayout_z_stream_s_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") fld =
      (if fld = "next_in" then some (0, .ptr (.const_ (.typedef "Bytef" (.typedef "Byte" (.int .u8)))))
       else if fld = "avail_in" then some (8, .typedef "uInt" (.int .u32))
       else if fld = "total_in" then some (16, .typedef "uLong" (.int .u64))
       else if fld = "next_out" then some (24, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8))))
       else if fld = "avail_out" then some (32, .typedef "uInt" (.int .u32))
       else if fld = "total_out" then some (40, .typedef "uLong" (.int .u64))
       else if fld = "msg" then some (48, .ptr (.const_ (.int .i8)))
       else if fld = "state" then some (56, .ptr (.structTy "internal_state"))
       else if fld = "zalloc" then some (64, .typedef "alloc_func" (.fnPtr (.typedef "voidpf" (.ptr .void))
           [.typedef "voidpf" (.ptr .void), .typedef "uInt" (.int .u32), .typedef "uInt" (.int .u32)] false))
       else if fld = "zfree" then some (72, .typedef "free_func" (.fnPtr .void
           [.typedef "voidpf" (.ptr .void), .typedef "voidpf" (.ptr .void)] false))
       else if fld = "opaque" then some (80, .typedef "voidpf" (.ptr .void))
       else if fld = "data_type" then some (88, .int .i32)
       else if fld = "adler" then some (96, .typedef "uLong" (.int .u64))
       else if fld = "reserved" then some (104, .typedef "uLong" (.int .u64))
       else none) := by
  unfold fieldLayout?
  simp only [CTy.unqual, prog_tags_lookup_z_stream_s]
  unfold zStreamFields
  unfold_head_lhs
  by_cases h1 : fld = "next_in"
  · subst h1
    rw [show ("next_in" == "next_in") = true from rfl, ite_eq_left rfl, ite_eq_left rfl, alignofTy_ptr]
    rfl
  · rw [show ("next_in" == fld) = false from beq_false_of_ne (Ne.symm h1),
      ite_eq_right Bool.false_ne_true, ite_eq_right h1, alignofTy_ptr, sizeofTy_ptr]
    rw [show alignUp 0 (max 1 8) + 8 = 8 from rfl]
    unfold_head_lhs
    by_cases h2 : fld = "avail_in"
    · subst h2
      rw [show ("avail_in" == "avail_in") = true from rfl, ite_eq_left rfl, ite_eq_left rfl,
        alignofTy_typedef, alignofTy_int]
      rfl
    · rw [show ("avail_in" == fld) = false from beq_false_of_ne (Ne.symm h2),
        ite_eq_right Bool.false_ne_true, ite_eq_right h2, alignofTy_typedef, alignofTy_int, sizeofTy_typedef, sizeofTy_int]
      rw [show alignUp 8 (max 1 IntKind.u32.align) + IntKind.u32.bytes = 12 from rfl]
      unfold_head_lhs
      by_cases h3 : fld = "total_in"
      · subst h3
        rw [show ("total_in" == "total_in") = true from rfl, ite_eq_left rfl, ite_eq_left rfl,
          alignofTy_typedef, alignofTy_int]
        rfl
      · rw [show ("total_in" == fld) = false from beq_false_of_ne (Ne.symm h3),
          ite_eq_right Bool.false_ne_true, ite_eq_right h3, alignofTy_typedef, alignofTy_int, sizeofTy_typedef, sizeofTy_int]
        rw [show alignUp 12 (max 1 IntKind.u64.align) + IntKind.u64.bytes = 24 from rfl]
        unfold_head_lhs
        by_cases h4 : fld = "next_out"
        · subst h4
          rw [show ("next_out" == "next_out") = true from rfl, ite_eq_left rfl, ite_eq_left rfl, alignofTy_ptr]
          rfl
        · rw [show ("next_out" == fld) = false from beq_false_of_ne (Ne.symm h4),
            ite_eq_right Bool.false_ne_true, ite_eq_right h4, alignofTy_ptr, sizeofTy_ptr]
          rw [show alignUp 24 (max 1 8) + 8 = 32 from rfl]
          unfold_head_lhs
          by_cases h5 : fld = "avail_out"
          · subst h5
            rw [show ("avail_out" == "avail_out") = true from rfl, ite_eq_left rfl, ite_eq_left rfl,
              alignofTy_typedef, alignofTy_int]
            rfl
          · rw [show ("avail_out" == fld) = false from beq_false_of_ne (Ne.symm h5),
              ite_eq_right Bool.false_ne_true, ite_eq_right h5, alignofTy_typedef, alignofTy_int, sizeofTy_typedef, sizeofTy_int]
            rw [show alignUp 32 (max 1 IntKind.u32.align) + IntKind.u32.bytes = 36 from rfl]
            unfold_head_lhs
            by_cases h6 : fld = "total_out"
            · subst h6
              rw [show ("total_out" == "total_out") = true from rfl, ite_eq_left rfl, ite_eq_left rfl,
                alignofTy_typedef, alignofTy_int]
              rfl
            · rw [show ("total_out" == fld) = false from beq_false_of_ne (Ne.symm h6),
                ite_eq_right Bool.false_ne_true, ite_eq_right h6, alignofTy_typedef, alignofTy_int, sizeofTy_typedef, sizeofTy_int]
              rw [show alignUp 36 (max 1 IntKind.u64.align) + IntKind.u64.bytes = 48 from rfl]
              unfold_head_lhs
              by_cases h7 : fld = "msg"
              · subst h7
                rw [show ("msg" == "msg") = true from rfl, ite_eq_left rfl, ite_eq_left rfl, alignofTy_ptr]
                rfl
              · rw [show ("msg" == fld) = false from beq_false_of_ne (Ne.symm h7),
                  ite_eq_right Bool.false_ne_true, ite_eq_right h7, alignofTy_ptr, sizeofTy_ptr]
                rw [show alignUp 48 (max 1 8) + 8 = 56 from rfl]
                unfold_head_lhs
                by_cases h8 : fld = "state"
                · subst h8
                  rw [show ("state" == "state") = true from rfl, ite_eq_left rfl, ite_eq_left rfl, alignofTy_ptr]
                  rfl
                · rw [show ("state" == fld) = false from beq_false_of_ne (Ne.symm h8),
                    ite_eq_right Bool.false_ne_true, ite_eq_right h8, alignofTy_ptr, sizeofTy_ptr]
                  rw [show alignUp 56 (max 1 8) + 8 = 64 from rfl]
                  unfold_head_lhs
                  by_cases h9 : fld = "zalloc"
                  · subst h9
                    rw [show ("zalloc" == "zalloc") = true from rfl, ite_eq_left rfl, ite_eq_left rfl,
                      alignofTy_typedef, alignofTy_fnPtr]
                    rfl
                  · rw [show ("zalloc" == fld) = false from beq_false_of_ne (Ne.symm h9),
                      ite_eq_right Bool.false_ne_true, ite_eq_right h9, alignofTy_typedef, alignofTy_fnPtr, sizeofTy_typedef, sizeofTy_fnPtr]
                    rw [show alignUp 64 (max 1 8) + 8 = 72 from rfl]
                    unfold_head_lhs
                    by_cases h10 : fld = "zfree"
                    · subst h10
                      rw [show ("zfree" == "zfree") = true from rfl, ite_eq_left rfl, ite_eq_left rfl,
                        alignofTy_typedef, alignofTy_fnPtr]
                      rfl
                    · rw [show ("zfree" == fld) = false from beq_false_of_ne (Ne.symm h10),
                        ite_eq_right Bool.false_ne_true, ite_eq_right h10, alignofTy_typedef, alignofTy_fnPtr, sizeofTy_typedef, sizeofTy_fnPtr]
                      rw [show alignUp 72 (max 1 8) + 8 = 80 from rfl]
                      unfold_head_lhs
                      by_cases h11 : fld = "opaque"
                      · subst h11
                        rw [show ("opaque" == "opaque") = true from rfl, ite_eq_left rfl, ite_eq_left rfl,
                          alignofTy_typedef, alignofTy_ptr]
                        rfl
                      · rw [show ("opaque" == fld) = false from beq_false_of_ne (Ne.symm h11),
                          ite_eq_right Bool.false_ne_true, ite_eq_right h11, alignofTy_typedef, alignofTy_ptr, sizeofTy_typedef, sizeofTy_ptr]
                        rw [show alignUp 80 (max 1 8) + 8 = 88 from rfl]
                        unfold_head_lhs
                        by_cases h12 : fld = "data_type"
                        · subst h12
                          rw [show ("data_type" == "data_type") = true from rfl, ite_eq_left rfl, ite_eq_left rfl, alignofTy_int]
                          rfl
                        · rw [show ("data_type" == fld) = false from beq_false_of_ne (Ne.symm h12),
                            ite_eq_right Bool.false_ne_true, ite_eq_right h12, alignofTy_int, sizeofTy_int]
                          rw [show alignUp 88 (max 1 IntKind.i32.align) + IntKind.i32.bytes = 92 from rfl]
                          unfold_head_lhs
                          by_cases h13 : fld = "adler"
                          · subst h13
                            rw [show ("adler" == "adler") = true from rfl, ite_eq_left rfl, ite_eq_left rfl,
                              alignofTy_typedef, alignofTy_int]
                            rfl
                          · rw [show ("adler" == fld) = false from beq_false_of_ne (Ne.symm h13),
                              ite_eq_right Bool.false_ne_true, ite_eq_right h13, alignofTy_typedef, alignofTy_int, sizeofTy_typedef, sizeofTy_int]
                            rw [show alignUp 92 (max 1 IntKind.u64.align) + IntKind.u64.bytes = 104 from rfl]
                            unfold_head_lhs
                            by_cases h14 : fld = "reserved"
                            · subst h14
                              rw [show ("reserved" == "reserved") = true from rfl, ite_eq_left rfl, ite_eq_left rfl,
                                alignofTy_typedef, alignofTy_int]
                              rfl
                            · rw [show ("reserved" == fld) = false from beq_false_of_ne (Ne.symm h14),
                                ite_eq_right Bool.false_ne_true, ite_eq_right h14, alignofTy_typedef, alignofTy_int, sizeofTy_typedef, sizeofTy_int]
                              unfold_head_lhs
                              rfl

theorem fieldLayout_z_stream_s_next_in :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "next_in" =
      some (0, .ptr (.const_ (.typedef "Bytef" (.typedef "Byte" (.int .u8))))) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_avail_in :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "avail_in" =
      some (8, .typedef "uInt" (.int .u32)) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_total_in :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "total_in" =
      some (16, .typedef "uLong" (.int .u64)) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_next_out :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "next_out" =
      some (24, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_avail_out :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "avail_out" =
      some (32, .typedef "uInt" (.int .u32)) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_total_out :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "total_out" =
      some (40, .typedef "uLong" (.int .u64)) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_msg :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "msg" =
      some (48, .ptr (.const_ (.int .i8))) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_state :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "state" =
      some (56, .ptr (.structTy "internal_state")) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_zalloc :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "zalloc" =
      some (64, .typedef "alloc_func" (.fnPtr (.typedef "voidpf" (.ptr .void))
        [.typedef "voidpf" (.ptr .void), .typedef "uInt" (.int .u32), .typedef "uInt" (.int .u32)] false)) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_zfree :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "zfree" =
      some (72, .typedef "free_func" (.fnPtr .void
        [.typedef "voidpf" (.ptr .void), .typedef "voidpf" (.ptr .void)] false)) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_opaque :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "opaque" =
      some (80, .typedef "voidpf" (.ptr .void)) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_data_type :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "data_type" =
      some (88, .int .i32) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_adler :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "adler" =
      some (96, .typedef "uLong" (.int .u64)) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

theorem fieldLayout_z_stream_s_reserved :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "z_stream_s") "reserved" =
      some (104, .typedef "uLong" (.int .u64)) := by
  rw [fieldLayout_z_stream_s_eq]; rfl

/-! ## 3. Program Function & Prototype Lookup Lemmas -/

def crc32_zProtoSig : FnSig :=
  (.typedef "uLong" (.int .u64),
    [.typedef "uLong" (.int .u64),
     .ptr (.const_ (.typedef "Bytef" (.typedef "Byte" (.int .u8)))),
     .typedef "z_size_t" (.int .u64)],
    false)

def crc32ProtoSig : FnSig :=
  (.typedef "uLong" (.int .u64),
    [.typedef "uLong" (.int .u64),
     .ptr (.const_ (.typedef "Bytef" (.typedef "Byte" (.int .u8)))),
     .typedef "uInt" (.int .u32)],
    false)

def targetFnNames : List String := [
  "zlibVersion", "zlibCompileFlags", "zError", "zcalloc", "zcfree",
  "compress2_z", "compress2", "compress_z", "compress", "compressBound_z", "compressBound",
  "adler32_z", "adler32", "adler32_combine_", "adler32_combine", "adler32_combine64",
  "byte_swap", "multmodp", "x2nmodp", "get_crc_table", "crc_word", "crc_word_big",
  "crc32_braid", "crc32_z", "crc32", "crc32_combine_gen64", "crc32_combine_gen",
  "crc32_combine_op", "crc32_combine64", "crc32_combine"
]

private theorem allHeaders_fnEntries_eq :
    Zlib.allHeaders.flatMap tuFnEntries = [] := rfl

private theorem gzcloseTU_fnEntries :
    tuFnEntries Zlib.Gzclose.gzcloseTU =
      [("gzclose", Zlib.Gzclose.gzcloseTU_fn_gzclose)] := rfl

private theorem zutilTU_fnEntries :
    tuFnEntries Zlib.Zutil.zutilTU = [
      ("zlibVersion", Zlib.Zutil.zutilTU_fn_zlibVersion),
      ("zlibCompileFlags", Zlib.Zutil.zutilTU_fn_zlibCompileFlags),
      ("zError", Zlib.Zutil.zutilTU_fn_zError),
      ("zcalloc", Zlib.Zutil.zutilTU_fn_zcalloc),
      ("zcfree", Zlib.Zutil.zutilTU_fn_zcfree)
    ] := rfl

private theorem adler32TU_fnEntries :
    tuFnEntries Zlib.Adler32.adler32TU = [
      ("adler32_z", Zlib.Adler32.adler32TU_fn_adler32_z),
      ("adler32", Zlib.Adler32.adler32TU_fn_adler32),
      ("adler32_combine_", Zlib.Adler32.adler32TU_fn_adler32_combine_),
      ("adler32_combine", Zlib.Adler32.adler32TU_fn_adler32_combine),
      ("adler32_combine64", Zlib.Adler32.adler32TU_fn_adler32_combine64)
    ] := rfl

private theorem compressTU_fnEntries :
    tuFnEntries Zlib.Compress.compressTU = [
      ("compress2_z", Zlib.Compress.compressTU_fn_compress2_z),
      ("compress2", Zlib.Compress.compressTU_fn_compress2),
      ("compress_z", Zlib.Compress.compressTU_fn_compress_z),
      ("compress", Zlib.Compress.compressTU_fn_compress),
      ("compressBound_z", Zlib.Compress.compressTU_fn_compressBound_z),
      ("compressBound", Zlib.Compress.compressTU_fn_compressBound)
    ] := rfl

private theorem uncomprTU_fnEntries :
    tuFnEntries Zlib.Uncompr.uncomprTU = [
      ("uncompress2_z", Zlib.Uncompr.uncomprTU_fn_uncompress2_z),
      ("uncompress2", Zlib.Uncompr.uncomprTU_fn_uncompress2),
      ("uncompress_z", Zlib.Uncompr.uncomprTU_fn_uncompress_z),
      ("uncompress", Zlib.Uncompr.uncomprTU_fn_uncompress)
    ] := rfl

private theorem inftreesTU_fnEntries :
    tuFnEntries Zlib.Inftrees.inftreesTU = [
      ("inflate_table", Zlib.Inftrees.inftreesTU_fn_inflate_table),
      ("inflate_fixed", Zlib.Inftrees.inftreesTU_fn_inflate_fixed)
    ] := rfl

private theorem inffastTU_fnEntries :
    tuFnEntries Zlib.Inffast.inffastTU = [
      ("load64", Zlib.Inffast.inffastTU_fn_load64),
      ("copy_back", Zlib.Inffast.inffastTU_fn_copy_back),
      ("inflate_fast", Zlib.Inffast.inffastTU_fn_inflate_fast)
    ] := rfl

private theorem crc32TU_fnEntries :
    tuFnEntries Zlib.Crc32.crc32TU = [
      ("byte_swap", Zlib.Crc32.crc32TU_fn_byte_swap),
      ("multmodp", Zlib.Crc32.crc32TU_fn_multmodp),
      ("x2nmodp", Zlib.Crc32.crc32TU_fn_x2nmodp),
      ("get_crc_table", Zlib.Crc32.crc32TU_fn_get_crc_table),
      ("crc_word", Zlib.Crc32.crc32TU_fn_crc_word),
      ("crc_word_big", Zlib.Crc32.crc32TU_fn_crc_word_big),
      ("crc32_braid", Zlib.Crc32.crc32TU_fn_crc32_braid),
      ("crc32_z", Zlib.Crc32.crc32TU_fn_crc32_z),
      ("crc32", Zlib.Crc32.crc32TU_fn_crc32),
      ("crc32_combine_gen64", Zlib.Crc32.crc32TU_fn_crc32_combine_gen64),
      ("crc32_combine_gen", Zlib.Crc32.crc32TU_fn_crc32_combine_gen),
      ("crc32_combine_op", Zlib.Crc32.crc32TU_fn_crc32_combine_op),
      ("crc32_combine64", Zlib.Crc32.crc32TU_fn_crc32_combine64),
      ("crc32_combine", Zlib.Crc32.crc32TU_fn_crc32_combine)
    ] := rfl

private def prefixTUs : List TU := [
  Zlib.Gzclose.gzcloseTU,
  Zlib.Zutil.zutilTU,
  Zlib.Adler32.adler32TU,
  Zlib.Compress.compressTU,
  Zlib.Uncompr.uncomprTU,
  Zlib.Inftrees.inftreesTU,
  Zlib.Inffast.inffastTU,
  Zlib.Crc32.crc32TU
]

private def suffixTUs : List TU := [
  Zlib.Trees.treesTU,
  Zlib.Infback.infbackTU,
  Zlib.Inflate.inflateTU,
  Zlib.Deflate.deflateTU,
  Zlib.Gzlib.gzlibTU,
  Zlib.Gzread.gzreadTU,
  Zlib.Gzwrite.gzwriteTU
]

private theorem allTUs_eq_append :
    Zlib.allTUs = prefixTUs ++ suffixTUs := rfl

private theorem prefixTUs_fnEntries_eq :
    prefixTUs.flatMap tuFnEntries =
      tuFnEntries Zlib.Gzclose.gzcloseTU ++
      tuFnEntries Zlib.Zutil.zutilTU ++
      tuFnEntries Zlib.Adler32.adler32TU ++
      tuFnEntries Zlib.Compress.compressTU ++
      tuFnEntries Zlib.Uncompr.uncomprTU ++
      tuFnEntries Zlib.Inftrees.inftreesTU ++
      tuFnEntries Zlib.Inffast.inffastTU ++
      tuFnEntries Zlib.Crc32.crc32TU := by
  simp [prefixTUs, List.flatMap_cons, List.append_assoc]

private theorem prefixTUs_fnEntries_concrete :
    prefixTUs.flatMap tuFnEntries = [
      ("gzclose", Zlib.Gzclose.gzcloseTU_fn_gzclose),
      ("zlibVersion", Zlib.Zutil.zutilTU_fn_zlibVersion),
      ("zlibCompileFlags", Zlib.Zutil.zutilTU_fn_zlibCompileFlags),
      ("zError", Zlib.Zutil.zutilTU_fn_zError),
      ("zcalloc", Zlib.Zutil.zutilTU_fn_zcalloc),
      ("zcfree", Zlib.Zutil.zutilTU_fn_zcfree),
      ("adler32_z", Zlib.Adler32.adler32TU_fn_adler32_z),
      ("adler32", Zlib.Adler32.adler32TU_fn_adler32),
      ("adler32_combine_", Zlib.Adler32.adler32TU_fn_adler32_combine_),
      ("adler32_combine", Zlib.Adler32.adler32TU_fn_adler32_combine),
      ("adler32_combine64", Zlib.Adler32.adler32TU_fn_adler32_combine64),
      ("compress2_z", Zlib.Compress.compressTU_fn_compress2_z),
      ("compress2", Zlib.Compress.compressTU_fn_compress2),
      ("compress_z", Zlib.Compress.compressTU_fn_compress_z),
      ("compress", Zlib.Compress.compressTU_fn_compress),
      ("compressBound_z", Zlib.Compress.compressTU_fn_compressBound_z),
      ("compressBound", Zlib.Compress.compressTU_fn_compressBound),
      ("uncompress2_z", Zlib.Uncompr.uncomprTU_fn_uncompress2_z),
      ("uncompress2", Zlib.Uncompr.uncomprTU_fn_uncompress2),
      ("uncompress_z", Zlib.Uncompr.uncomprTU_fn_uncompress_z),
      ("uncompress", Zlib.Uncompr.uncomprTU_fn_uncompress),
      ("inflate_table", Zlib.Inftrees.inftreesTU_fn_inflate_table),
      ("inflate_fixed", Zlib.Inftrees.inftreesTU_fn_inflate_fixed),
      ("load64", Zlib.Inffast.inffastTU_fn_load64),
      ("copy_back", Zlib.Inffast.inffastTU_fn_copy_back),
      ("inflate_fast", Zlib.Inffast.inffastTU_fn_inflate_fast),
      ("byte_swap", Zlib.Crc32.crc32TU_fn_byte_swap),
      ("multmodp", Zlib.Crc32.crc32TU_fn_multmodp),
      ("x2nmodp", Zlib.Crc32.crc32TU_fn_x2nmodp),
      ("get_crc_table", Zlib.Crc32.crc32TU_fn_get_crc_table),
      ("crc_word", Zlib.Crc32.crc32TU_fn_crc_word),
      ("crc_word_big", Zlib.Crc32.crc32TU_fn_crc_word_big),
      ("crc32_braid", Zlib.Crc32.crc32TU_fn_crc32_braid),
      ("crc32_z", Zlib.Crc32.crc32TU_fn_crc32_z),
      ("crc32", Zlib.Crc32.crc32TU_fn_crc32),
      ("crc32_combine_gen64", Zlib.Crc32.crc32TU_fn_crc32_combine_gen64),
      ("crc32_combine_gen", Zlib.Crc32.crc32TU_fn_crc32_combine_gen),
      ("crc32_combine_op", Zlib.Crc32.crc32TU_fn_crc32_combine_op),
      ("crc32_combine64", Zlib.Crc32.crc32TU_fn_crc32_combine64),
      ("crc32_combine", Zlib.Crc32.crc32TU_fn_crc32_combine)
    ] := by
  rw [prefixTUs_fnEntries_eq, gzcloseTU_fnEntries, zutilTU_fnEntries, adler32TU_fnEntries,
    compressTU_fnEntries, uncomprTU_fnEntries, inftreesTU_fnEntries, inffastTU_fnEntries,
    crc32TU_fnEntries]
  rfl

private theorem progOfTUs_allFiles_fns_of_prefix {sym : String} {fn : FnDef}
    (h : (prefixTUs.flatMap tuFnEntries).lookup sym = some fn) :
    (progOfTUs Zlib.allFiles).fns sym = some fn := by
  rw [progOfTUs_fns, Zlib.allFiles, List.flatMap_append, allHeaders_fnEntries_eq, List.nil_append,
    allTUs_eq_append, List.flatMap_append]
  exact lookup_append_some h

private theorem tuProtoEntries_eq_map_fnDefSig (tu : TU)
    (h : tuProtoEntries tu = (tuFnEntries tu).map fun (n, f) => (n, fnDefSig f)) :
    tuProtoEntries tu = (tuFnEntries tu).map fun (n, f) => (n, fnDefSig f) := h

private theorem prefixTUs_protoEntries_eq :
    prefixTUs.flatMap tuProtoEntries =
      (prefixTUs.flatMap tuFnEntries).map (fun (n, f) => (n, fnDefSig f)) := by
  have h1 : tuProtoEntries Zlib.Gzclose.gzcloseTU = (tuFnEntries Zlib.Gzclose.gzcloseTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
  have h2 : tuProtoEntries Zlib.Zutil.zutilTU = (tuFnEntries Zlib.Zutil.zutilTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
  have h3 : tuProtoEntries Zlib.Adler32.adler32TU = (tuFnEntries Zlib.Adler32.adler32TU).map (fun (n, f) => (n, fnDefSig f)) := rfl
  have h4 : tuProtoEntries Zlib.Compress.compressTU = (tuFnEntries Zlib.Compress.compressTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
  have h5 : tuProtoEntries Zlib.Uncompr.uncomprTU = (tuFnEntries Zlib.Uncompr.uncomprTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
  have h6 : tuProtoEntries Zlib.Inftrees.inftreesTU = (tuFnEntries Zlib.Inftrees.inftreesTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
  have h7 : tuProtoEntries Zlib.Inffast.inffastTU = (tuFnEntries Zlib.Inffast.inffastTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
  have h8 : tuProtoEntries Zlib.Crc32.crc32TU = (tuFnEntries Zlib.Crc32.crc32TU).map (fun (n, f) => (n, fnDefSig f)) := rfl
  simp only [prefixTUs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

private theorem progOfTUs_allFiles_fnProtos_of_header {sym : String} {sig : FnSig}
    (h : (Zlib.allHeaders.flatMap tuProtoEntries).lookup sym = some sig) :
    (progOfTUs Zlib.allFiles).fnProtos sym = some sig := by
  rw [progOfTUs_fnProtos, Zlib.allFiles, List.flatMap_append, List.append_assoc]
  exact lookup_append_some h

private theorem progOfTUs_allFiles_fnProtos_of_prefix {sym : String} {sig : FnSig}
    (hhdr : (Zlib.allHeaders.flatMap tuProtoEntries).lookup sym = none)
    (hpre : (prefixTUs.flatMap tuProtoEntries).lookup sym = some sig) :
    (progOfTUs Zlib.allFiles).fnProtos sym = some sig := by
  rw [progOfTUs_fnProtos, Zlib.allFiles, List.flatMap_append, List.append_assoc]
  rw [lookup_append_none hhdr, allTUs_eq_append, List.flatMap_append, List.append_assoc]
  exact lookup_append_some hpre

/-! ### Exact `prog0.fns` Theorems -/

theorem prog0_fns_zlibVersion : (progOfTUs Zlib.allFiles).fns "zlibVersion" = some Zlib.Zutil.zutilTU_fn_zlibVersion :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_zlibCompileFlags : (progOfTUs Zlib.allFiles).fns "zlibCompileFlags" = some Zlib.Zutil.zutilTU_fn_zlibCompileFlags :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_zError : (progOfTUs Zlib.allFiles).fns "zError" = some Zlib.Zutil.zutilTU_fn_zError :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_zcalloc : (progOfTUs Zlib.allFiles).fns "zcalloc" = some Zlib.Zutil.zutilTU_fn_zcalloc :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_zcfree : (progOfTUs Zlib.allFiles).fns "zcfree" = some Zlib.Zutil.zutilTU_fn_zcfree :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)

theorem prog0_fns_compress2_z : (progOfTUs Zlib.allFiles).fns "compress2_z" = some Zlib.Compress.compressTU_fn_compress2_z :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_compress2 : (progOfTUs Zlib.allFiles).fns "compress2" = some Zlib.Compress.compressTU_fn_compress2 :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_compress_z : (progOfTUs Zlib.allFiles).fns "compress_z" = some Zlib.Compress.compressTU_fn_compress_z :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_compress : (progOfTUs Zlib.allFiles).fns "compress" = some Zlib.Compress.compressTU_fn_compress :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_compressBound_z : (progOfTUs Zlib.allFiles).fns "compressBound_z" = some Zlib.Compress.compressTU_fn_compressBound_z :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_compressBound : (progOfTUs Zlib.allFiles).fns "compressBound" = some Zlib.Compress.compressTU_fn_compressBound :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)

theorem prog0_fns_adler32_z : (progOfTUs Zlib.allFiles).fns "adler32_z" = some Zlib.Adler32.adler32TU_fn_adler32_z :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_adler32 : (progOfTUs Zlib.allFiles).fns "adler32" = some Zlib.Adler32.adler32TU_fn_adler32 :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_adler32_combine_ : (progOfTUs Zlib.allFiles).fns "adler32_combine_" = some Zlib.Adler32.adler32TU_fn_adler32_combine_ :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_adler32_combine : (progOfTUs Zlib.allFiles).fns "adler32_combine" = some Zlib.Adler32.adler32TU_fn_adler32_combine :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_adler32_combine64 : (progOfTUs Zlib.allFiles).fns "adler32_combine64" = some Zlib.Adler32.adler32TU_fn_adler32_combine64 :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)

theorem prog0_fns_byte_swap : (progOfTUs Zlib.allFiles).fns "byte_swap" = some Zlib.Crc32.crc32TU_fn_byte_swap :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_multmodp : (progOfTUs Zlib.allFiles).fns "multmodp" = some Zlib.Crc32.crc32TU_fn_multmodp :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_x2nmodp : (progOfTUs Zlib.allFiles).fns "x2nmodp" = some Zlib.Crc32.crc32TU_fn_x2nmodp :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_get_crc_table : (progOfTUs Zlib.allFiles).fns "get_crc_table" = some Zlib.Crc32.crc32TU_fn_get_crc_table :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_crc_word : (progOfTUs Zlib.allFiles).fns "crc_word" = some Zlib.Crc32.crc32TU_fn_crc_word :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_crc_word_big : (progOfTUs Zlib.allFiles).fns "crc_word_big" = some Zlib.Crc32.crc32TU_fn_crc_word_big :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_crc32_braid : (progOfTUs Zlib.allFiles).fns "crc32_braid" = some Zlib.Crc32.crc32TU_fn_crc32_braid :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_crc32_z : (progOfTUs Zlib.allFiles).fns "crc32_z" = some Zlib.Crc32.crc32TU_fn_crc32_z :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_crc32 : (progOfTUs Zlib.allFiles).fns "crc32" = some Zlib.Crc32.crc32TU_fn_crc32 :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_crc32_combine_gen64 : (progOfTUs Zlib.allFiles).fns "crc32_combine_gen64" = some Zlib.Crc32.crc32TU_fn_crc32_combine_gen64 :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_crc32_combine_gen : (progOfTUs Zlib.allFiles).fns "crc32_combine_gen" = some Zlib.Crc32.crc32TU_fn_crc32_combine_gen :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_crc32_combine_op : (progOfTUs Zlib.allFiles).fns "crc32_combine_op" = some Zlib.Crc32.crc32TU_fn_crc32_combine_op :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_crc32_combine64 : (progOfTUs Zlib.allFiles).fns "crc32_combine64" = some Zlib.Crc32.crc32TU_fn_crc32_combine64 :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fns_crc32_combine : (progOfTUs Zlib.allFiles).fns "crc32_combine" = some Zlib.Crc32.crc32TU_fn_crc32_combine :=
  progOfTUs_allFiles_fns_of_prefix (by rw [prefixTUs_fnEntries_concrete]; rfl)

/-! ### Exact `prog0.fnProtos` Theorems -/

theorem prog0_fnProtos_zlibVersion : (progOfTUs Zlib.allFiles).fnProtos "zlibVersion" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zlibVersion) :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)
theorem prog0_fnProtos_zlibCompileFlags : (progOfTUs Zlib.allFiles).fnProtos "zlibCompileFlags" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zlibCompileFlags) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_zError : (progOfTUs Zlib.allFiles).fnProtos "zError" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zError) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_zcalloc : (progOfTUs Zlib.allFiles).fnProtos "zcalloc" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zcalloc) :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)
theorem prog0_fnProtos_zcfree : (progOfTUs Zlib.allFiles).fnProtos "zcfree" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zcfree) :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)

theorem prog0_fnProtos_compress2_z : (progOfTUs Zlib.allFiles).fnProtos "compress2_z" = some (fnDefSig Zlib.Compress.compressTU_fn_compress2_z) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_compress2 : (progOfTUs Zlib.allFiles).fnProtos "compress2" = some (fnDefSig Zlib.Compress.compressTU_fn_compress2) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_compress_z : (progOfTUs Zlib.allFiles).fnProtos "compress_z" = some (fnDefSig Zlib.Compress.compressTU_fn_compress_z) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_compress : (progOfTUs Zlib.allFiles).fnProtos "compress" = some (fnDefSig Zlib.Compress.compressTU_fn_compress) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_compressBound_z : (progOfTUs Zlib.allFiles).fnProtos "compressBound_z" = some (fnDefSig Zlib.Compress.compressTU_fn_compressBound_z) :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)
theorem prog0_fnProtos_compressBound : (progOfTUs Zlib.allFiles).fnProtos "compressBound" = some (fnDefSig Zlib.Compress.compressTU_fn_compressBound) :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)

theorem prog0_fnProtos_adler32_z : (progOfTUs Zlib.allFiles).fnProtos "adler32_z" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_z) :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)
theorem prog0_fnProtos_adler32 : (progOfTUs Zlib.allFiles).fnProtos "adler32" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32) :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)
theorem prog0_fnProtos_adler32_combine_ : (progOfTUs Zlib.allFiles).fnProtos "adler32_combine_" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_combine_) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_adler32_combine : (progOfTUs Zlib.allFiles).fnProtos "adler32_combine" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_combine) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_adler32_combine64 : (progOfTUs Zlib.allFiles).fnProtos "adler32_combine64" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_combine64) :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)

theorem prog0_fnProtos_byte_swap : (progOfTUs Zlib.allFiles).fnProtos "byte_swap" = some (fnDefSig Zlib.Crc32.crc32TU_fn_byte_swap) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_multmodp : (progOfTUs Zlib.allFiles).fnProtos "multmodp" = some (fnDefSig Zlib.Crc32.crc32TU_fn_multmodp) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_x2nmodp : (progOfTUs Zlib.allFiles).fnProtos "x2nmodp" = some (fnDefSig Zlib.Crc32.crc32TU_fn_x2nmodp) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_get_crc_table : (progOfTUs Zlib.allFiles).fnProtos "get_crc_table" = some (fnDefSig Zlib.Crc32.crc32TU_fn_get_crc_table) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_crc_word : (progOfTUs Zlib.allFiles).fnProtos "crc_word" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc_word) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_crc_word_big : (progOfTUs Zlib.allFiles).fnProtos "crc_word_big" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc_word_big) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_crc32_braid : (progOfTUs Zlib.allFiles).fnProtos "crc32_braid" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_braid) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_crc32_z : (progOfTUs Zlib.allFiles).fnProtos "crc32_z" = some crc32_zProtoSig :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)
theorem prog0_fnProtos_crc32 : (progOfTUs Zlib.allFiles).fnProtos "crc32" = some crc32ProtoSig :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)
theorem prog0_fnProtos_crc32_combine_gen64 : (progOfTUs Zlib.allFiles).fnProtos "crc32_combine_gen64" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine_gen64) :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)
theorem prog0_fnProtos_crc32_combine_gen : (progOfTUs Zlib.allFiles).fnProtos "crc32_combine_gen" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine_gen) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)
theorem prog0_fnProtos_crc32_combine_op : (progOfTUs Zlib.allFiles).fnProtos "crc32_combine_op" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine_op) :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)
theorem prog0_fnProtos_crc32_combine64 : (progOfTUs Zlib.allFiles).fnProtos "crc32_combine64" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine64) :=
  progOfTUs_allFiles_fnProtos_of_header (by rfl)
theorem prog0_fnProtos_crc32_combine : (progOfTUs Zlib.allFiles).fnProtos "crc32_combine" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine) :=
  progOfTUs_allFiles_fnProtos_of_prefix (by rfl) (by rw [prefixTUs_protoEntries_eq, prefixTUs_fnEntries_concrete]; rfl)

private theorem fnEntries_lookup_none_of_not_mem {tu : TU} {sym : String}
    (h : sym ∉ tuFnNames tu) : (tuFnEntries tu).lookup sym = none := by
  rcases tu with ⟨_, items⟩
  unfold tuFnEntries tuFnNames at *
  dsimp only at *
  induction items with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | fnDef f =>
      simp only [List.filterMap_cons, List.mem_cons, not_or] at h
      simp only [List.filterMap_cons, List.lookup, beq_false_of_ne h.1]
      exact ih h.2
    | _ => exact ih h

private theorem protoEntries_lookup_none_of_not_mem {tu : TU} {sym : String}
    (h : sym ∉ tuProtoNames tu) : (tuProtoEntries tu).lookup sym = none := by
  rcases tu with ⟨_, items⟩
  unfold tuProtoEntries tuProtoNames at *
  dsimp only at *
  induction items with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | fnDef f =>
      simp only [List.filterMap_cons, List.mem_cons, not_or] at h
      simp only [List.filterMap_cons, List.lookup, beq_false_of_ne h.1]
      exact ih h.2
    | fnProto _ _ n _ _ =>
      simp only [List.filterMap_cons, List.mem_cons, not_or] at h
      simp only [List.filterMap_cons, List.lookup, beq_false_of_ne h.1]
      exact ih h.2
    | _ => exact ih h

private theorem flatMap_fnEntries_lookup_none {tus : List TU} {sym : String}
    (h : sym ∉ tus.flatMap tuFnNames) : (tus.flatMap tuFnEntries).lookup sym = none := by
  induction tus with
  | nil => rfl
  | cons tu tl ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at h
    simp only [List.flatMap_cons]
    exact lookup_append_none (fnEntries_lookup_none_of_not_mem h.1) |>.trans (ih h.2)

private theorem flatMap_protoEntries_lookup_none {tus : List TU} {sym : String}
    (h : sym ∉ tus.flatMap tuProtoNames) : (tus.flatMap tuProtoEntries).lookup sym = none := by
  induction tus with
  | nil => rfl
  | cons tu tl ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at h
    simp only [List.flatMap_cons]
    exact lookup_append_none (protoEntries_lookup_none_of_not_mem h.1) |>.trans (ih h.2)

theorem prog0_fns_none_of_not_mem {sym : String}
    (h : sym ∉ Zlib.allFiles.flatMap tuFnNames) :
    (progOfTUs Zlib.allFiles).fns sym = none := by
  rw [progOfTUs_fns]
  exact flatMap_fnEntries_lookup_none h

theorem prog0_fnProtos_stdLibc {sym : String}
    (h : sym ∉ Zlib.allFiles.flatMap tuProtoNames)
    {sig : FnSig} (hstd : stdLibcProtos.lookup sym = some sig) :
    (progOfTUs Zlib.allFiles).fnProtos sym = some sig := by
  rw [progOfTUs_fnProtos, lookup_append_none (flatMap_protoEntries_lookup_none h)]
  exact hstd

/-! ## 4. Memory & Global Initialization Inversion Helpers -/

def MemPreservedBelow (lim : BlockId) (m m' : Mem) : Prop :=
  m.nextBlock ≤ m'.nextBlock ∧ ∀ x, x < lim → m'.blocks x = m.blocks x

theorem MemPreservedBelow.refl (lim : BlockId) (m : Mem) : MemPreservedBelow lim m m :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem MemPreservedBelow.trans {lim : BlockId} {m1 m2 m3 : Mem}
    (h12 : MemPreservedBelow lim m1 m2) (h23 : MemPreservedBelow lim m2 m3) :
    MemPreservedBelow lim m1 m3 :=
  ⟨Nat.le_trans h12.1 h23.1, fun x hx => by rw [h23.2 x hx, h12.2 x hx]⟩

theorem MemPreservedBelow.mono {lim lim' : BlockId} {m m' : Mem}
    (hle : lim' ≤ lim) (h : MemPreservedBelow lim m m') : MemPreservedBelow lim' m m' :=
  ⟨h.1, fun x hx => h.2 x (Nat.lt_of_lt_of_le hx hle)⟩

theorem MemPreservedBelow.strlenAt {lim b : BlockId} {off : Int64} {m m' : Mem}
    (hb : b < lim) (hp : MemPreservedBelow lim m m') :
    m'.strlenAt b off = m.strlenAt b off := by
  unfold Mem.strlenAt
  rw [hp.2 b hb]

theorem MemPreservedBelow.readVal {lim b : BlockId} {off : Int64} {ty : CTy}
    {tags : TypeEnv} {m m' : Mem} (hb : b < lim) (hp : MemPreservedBelow lim m m') :
    Sem.readVal tags m' b off ty = Sem.readVal tags m b off ty := by
  unfold Sem.readVal Mem.readBytes
  rw [hp.2 b hb]

private theorem writeBytes_preservedBelow {lim b : BlockId} {off : Int64} {bs : List MemByte}
    {m m' : Mem} (hb : lim ≤ b) (h : m.writeBytes b off bs = some m') :
    MemPreservedBelow lim m m' := by
  refine ⟨by rw [writeBytes_nextBlock h]; exact Nat.le_refl _, fun x hx => ?_⟩
  exact writeBytes_blocks_ne h (Nat.ne_of_lt (Nat.lt_of_lt_of_le hx hb))

theorem mem_encodeInt_isByte {k : IntKind} {bv : BitVec k.bits} {x : MemByte}
    (hx : x ∈ Mem.encodeInt k bv) : ∃ u : UInt8, x = .byte u := by
  unfold Mem.encodeInt at hx
  rw [List.mem_map] at hx
  rcases hx with ⟨_, _, rfl⟩
  exact ⟨_, rfl⟩

theorem mem_flatMap_encodeInt_isByte {k : IntKind} {vals : List Int} {x : MemByte}
    (hx : x ∈ vals.flatMap fun v => Mem.encodeInt k (BitVec.ofInt k.bits v)) :
    ∃ u : UInt8, x = .byte u := by
  rw [List.mem_flatMap] at hx
  rcases hx with ⟨v, _, hxv⟩
  exact mem_encodeInt_isByte hxv

theorem flatMap_encodeInt_length (k : IntKind) (xs : List Int) :
    (xs.flatMap fun v => Mem.encodeInt k (BitVec.ofInt k.bits v)).length = xs.length * k.bytes := by
  induction xs with
  | nil => simp
  | cons _ tl ih =>
    simp only [List.flatMap_cons, List.length_append, encodeInt_length, ih, List.length_cons,
      Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem flatMap_encodeInt_getElem? (k : IntKind) (xs : List Int) (i j : Nat)
    (hi : i < xs.length) (hj : j < k.bytes) :
    (xs.flatMap fun v => Mem.encodeInt k (BitVec.ofInt k.bits v))[k.bytes * i + j]? =
      (Mem.encodeInt k (BitVec.ofInt k.bits xs[i]))[j]? := by
  induction xs generalizing i with
  | nil => cases hi
  | cons hd tl ih =>
    simp only [List.flatMap_cons]
    have hlen : (Mem.encodeInt k (BitVec.ofInt k.bits hd)).length = k.bytes := encodeInt_length _ _
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      exact List.getElem?_append_left (by omega)
    | succ i' =>
      have hmul : k.bytes * (i' + 1) = k.bytes * i' + k.bytes := by rw [Nat.mul_add, Nat.mul_one]
      have hge : (Mem.encodeInt k (BitVec.ofInt k.bits hd)).length ≤ k.bytes * (i' + 1) + j := by
        rw [hlen, hmul]; omega
      rw [List.getElem?_append_right hge, hlen]
      have hsub : k.bytes * (i' + 1) + j - k.bytes = k.bytes * i' + j := by rw [hmul]; omega
      rw [hsub]
      exact ih i' (Nat.lt_of_succ_lt_succ hi)

private theorem writeBytes_allBytes {m m' : Mem} {b : BlockId} {off : Int64} {bs : List MemByte}
    {blk : Block} (hb : m.blocks b = some blk) (hwb : m.writeBytes b off bs = some m')
    (hconcr : ∀ i < blk.size, ∃ u : UInt8, blk.bytes i = .byte u)
    (hbs : ∀ x ∈ bs, ∃ u : UInt8, x = .byte u) :
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.perm = blk.perm ∧
      blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr ∧
      (∀ i < blk'.size, ∃ u : UInt8, blk'.bytes i = .byte u) := by
  refine ⟨_, writeBytes_blocks_eq hb hwb, rfl, rfl, rfl, rfl, rfl, fun i hi => ?_⟩
  by_cases hrange : off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + bs.length
  · have hj : i - off.toInt.toNat < bs.length := by omega
    simp only [hrange, List.getElem?_eq_getElem hj, Option.getD_some]
    exact hbs _ (List.getElem_mem hj)
  · simp only [hrange, ↓reduceIte]
    exact hconcr i hi

private theorem writeBytes_allBytes_total {m m' : Mem} {b : BlockId} {off : Int64} {bs : List MemByte}
    {blk : Block} (hb : m.blocks b = some blk) (hwb : m.writeBytes b off bs = some m')
    (hconcr : ∀ i, ∃ u : UInt8, blk.bytes i = .byte u)
    (hbs : ∀ x ∈ bs, ∃ u : UInt8, x = .byte u) :
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.perm = blk.perm ∧
      blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr ∧
      (∀ i, ∃ u : UInt8, blk'.bytes i = .byte u) := by
  refine ⟨_, writeBytes_blocks_eq hb hwb, rfl, rfl, rfl, rfl, rfl, fun i => ?_⟩
  by_cases hrange : off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + bs.length
  · have hj : i - off.toInt.toNat < bs.length := by omega
    simp only [hrange, List.getElem?_eq_getElem hj, Option.getD_some]
    exact hbs _ (List.getElem_mem hj)
  · simp only [hrange, ↓reduceIte]
    exact hconcr i

theorem readVal_writeBytes_intArray (tags : TypeEnv) {m m' : Mem} {b : BlockId} {blk : Block}
    {k : IntKind} {vals : Array Int}
    (hb : m.blocks b = some blk)
    (hdvd : k.align ∣ blk.align)
    (hwb : m.writeBytes b 0 (vals.toList.flatMap fun v => Mem.encodeInt k (BitVec.ofInt k.bits v)) = some m')
    {i : Nat} (hi : i < vals.size) :
    Sem.readVal tags m' b (Int64.ofNat (k.bytes * i)) (.int k) =
      some (.int k (BitVec.ofInt k.bits vals[i])) := by
  let bs := vals.toList.flatMap fun v => Mem.encodeInt k (BitVec.ofInt k.bits v)
  have hinbs : Mem.inBounds blk 0 bs.length = true := by
    have hwb1 := hwb
    unfold Mem.writeBytes at hwb1
    split at hwb1
    · cases hwb1
    · rename_i blk' hblk_eq
      rw [hb, Option.some.injEq] at hblk_eq
      subst hblk_eq
      dsimp only at hwb1
      cases hc : (blk.perm == .rw && Mem.inBounds blk 0 bs.length)
      · rw [hc] at hwb1; cases hwb1
      · exact (Bool.and_eq_true _ _).mp hc |>.2
  have hlen_le : bs.length ≤ blk.size := by
    have := (inBounds_iff.mp hinbs).2
    simpa [Int64.toInt] using this
  have hbslen : bs.length = vals.size * k.bytes := by
    simpa [bs, Array.length_toList] using flatMap_encodeInt_length k vals.toList
  have hlt_blk : k.bytes * i + k.bytes ≤ blk.size := by
    have hmul : k.bytes * i + k.bytes = k.bytes * (i + 1) := (Nat.mul_succ k.bytes i).symm
    have hle : k.bytes * (i + 1) ≤ vals.size * k.bytes := by
      rw [Nat.mul_comm vals.size k.bytes]
      exact Nat.mul_le_mul_left _ hi
    omega
  have hlt_63 : k.bytes * i < 2 ^ 63 := by
    have := blk.sizeLt
    rw [ptrDiffLimit_val] at this
    have hkpos : 0 < k.bytes := by cases k <;> decide
    omega
  have hoff_eq : (Int64.ofNat (k.bytes * i)).toInt = (k.bytes * i : Int) := by
    change (Int64.ofInt (k.bytes * i : Nat)).toInt = (k.bytes * i : Int)
    exact int64_ofInt_toInt (by omega) (by omega)
  have hoff_nat : (Int64.ofNat (k.bytes * i)).toInt.toNat = k.bytes * i := by
    rw [hoff_eq]; omega
  have hblk' := writeBytes_blocks_eq hb hwb
  let newBytes : Nat → MemByte := fun x =>
    if (0 : Int64).toInt.toNat ≤ x ∧ x < (0 : Int64).toInt.toNat + bs.length then
      bs[x - (0 : Int64).toInt.toNat]?.getD .undef
    else blk.bytes x
  have hin : Mem.inBounds { blk with bytes := newBytes } (Int64.ofNat (k.bytes * i)) k.bytes = true := by
    rw [inBounds_iff, hoff_eq]
    have htoNat : (↑k.bytes * ↑i : Int).toNat = k.bytes * i := by omega
    rw [htoNat]
    exact ⟨by omega, hlt_blk⟩
  have hkbytes_align : k.align = k.bytes := by cases k <;> rfl
  have hal : Mem.isAligned { blk with bytes := newBytes } (Int64.ofNat (k.bytes * i)) k.align = true := by
    rw [isAligned_iff, hoff_eq]
    have htoNat : (↑k.bytes * ↑i : Int).toNat = k.bytes * i := by omega
    rw [htoNat]
    refine ⟨by omega, by cases k <;> decide, ?_⟩
    have hd1 : k.align ∣ blk.baseAddr.toNat := Nat.dvd_trans hdvd (Nat.dvd_of_mod_eq_zero blk.baseAligned)
    have hd2 : k.align ∣ k.bytes * i := by rw [hkbytes_align]; exact Nat.dvd_mul_right _ _
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add hd1 hd2)
  have hbytes_eq : ((List.range k.bytes).map fun j =>
      newBytes ((Int64.ofNat (k.bytes * i)).toInt.toNat + j)) =
      Mem.encodeInt k (BitVec.ofInt k.bits vals[i]) := by
    apply List.ext_getElem
    · simp [encodeInt_length]
    · intro j hj1 hj2
      have hj : j < k.bytes := by simpa using hj1
      have h0 : (0 : Int64).toInt.toNat = 0 := rfl
      have hrange : 0 ≤ k.bytes * i + j ∧ k.bytes * i + j < bs.length := by
        rw [hbslen]
        have h1 : k.bytes * i + j < k.bytes * (i + 1) := by rw [Nat.mul_succ]; omega
        have h2 : k.bytes * (i + 1) ≤ vals.size * k.bytes := by
          rw [Nat.mul_comm vals.size k.bytes]; exact Nat.mul_le_mul_left _ hi
        omega
      dsimp only [newBytes]
      rw [List.getElem_map, List.getElem_range, hoff_nat, h0, Nat.sub_zero, Nat.zero_add, ite_eq_left hrange]
      have hget := flatMap_encodeInt_getElem? k vals.toList i j (by simpa using hi) hj
      change (bs[k.bytes * i + j]?).getD .undef = (Mem.encodeInt k (BitVec.ofInt k.bits vals[i]))[j]
      rw [hget]
      have hlen_e : j < (Mem.encodeInt k (BitVec.ofInt k.bits vals[i])).length := by
        rw [encodeInt_length]; exact hj
      have hval_eq : vals.toList[i] = vals[i] := rfl
      rw [hval_eq, List.getElem?_eq_getElem hlen_e, Option.getD_some]
  dsimp only [newBytes] at hin hal hbytes_eq
  have hrd := readBytes_of_bounds hblk' hin
  unfold Sem.readVal
  simp only [CTy.unqual, CTy.intKind?, hblk', bind, Option.bind]
  dsimp only [guard]
  rw [ite_eq_left hal, hrd]
  dsimp only [pure, Pure.pure]
  have hbytes_eq' : ((List.range k.bytes).map fun j =>
      if (Int64.toInt 0).toNat ≤ (Int64.ofNat (k.bytes * i)).toInt.toNat + j ∧
        (Int64.ofNat (k.bytes * i)).toInt.toNat + j < (Int64.toInt 0).toNat + bs.length then
      bs[(Int64.ofNat (k.bytes * i)).toInt.toNat + j - (Int64.toInt 0).toNat]?.getD .undef
      else blk.bytes ((Int64.ofNat (k.bytes * i)).toInt.toNat + j)) =
      Mem.encodeInt k (BitVec.ofInt k.bits vals[i]) := hbytes_eq
  rw [hbytes_eq', decodeInt_encodeInt]

/-! ### Preservation of `MemPreservedBelow` across `evalConstExpr`, `writeInitVal`, `allocVarInit` -/

theorem evalConstExpr_preserves {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    (e : CExpr) {m m' : Mem} {ns ns' : Nat} {v : Val} {ty : CTy}
    (h : evalConstExpr prog env m strBase ns e = some (v, ty, m', ns')) :
    MemPreservedBelow m.nextBlock m m' := by
  cases e with
  | paren e0 => exact evalConstExpr_preserves e0 h
  | lit _ _ _ _ _ =>
    simp only [evalConstExpr, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h
    exact MemPreservedBelow.refl _ _
  | strLit s =>
    simp only [evalConstExpr, bind, Option.bind, pure, Pure.pure] at h
    split at h
    · cases h
    · next p heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl, _⟩ := h
      unfold_lhs heq
      split at heq
      · split at heq
        · split at heq
          · cases heq
            exact ⟨Nat.le_succ _, fun x hx => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hx)⟩
          · cases heq
        · cases heq
      · cases heq
  | var x =>
    simp only [evalConstExpr] at h
    split at h
    · cases h; exact MemPreservedBelow.refl _ _
    · split at h
      · cases h; exact MemPreservedBelow.refl _ _
      · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        rcases h with ⟨_, _, _, _, rfl, _⟩
        exact MemPreservedBelow.refl _ _
  | addrOf a =>
    cases a with
    | var name =>
      simp only [evalConstExpr] at h
      cases hlu : env.lookup name <;> simp only [hlu, Option.map_none, Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at h
      · cases h
      · obtain ⟨_, _, rfl, _⟩ := h
        exact MemPreservedBelow.refl _ _
    | _ => simp [evalConstExpr] at h
  | sizeOfTy _ =>
    simp only [evalConstExpr, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h
    exact MemPreservedBelow.refl _ _
  | cast _ e0 =>
    simp only [evalConstExpr, bind, Option.bind] at h
    cases heq : evalConstExpr prog env m strBase ns e0 with
    | none => simp [heq] at h
    | some p =>
      rcases p with ⟨v0, t0, m1, ns1⟩
      simp only [heq] at h
      split at h
      · cases h
      · simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, _⟩ := h
        exact evalConstExpr_preserves e0 heq
  | unary _ e0 =>
    simp only [evalConstExpr, bind, Option.bind] at h
    cases heq : evalConstExpr prog env m strBase ns e0 with
    | none => simp [heq] at h
    | some p =>
      rcases p with ⟨v0, t0, m1, ns1⟩
      simp only [heq] at h
      split at h
      · cases h
      · simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, _⟩ := h
        exact evalConstExpr_preserves e0 heq
  | binary _ l r =>
    simp only [evalConstExpr, bind, Option.bind] at h
    cases h1 : evalConstExpr prog env m strBase ns l with
    | none => simp [h1] at h
    | some p1 =>
      rcases p1 with ⟨v1, t1, m1, ns1⟩
      simp only [h1] at h
      cases h2 : evalConstExpr prog env m1 strBase ns1 r with
      | none => simp [h2] at h
      | some p2 =>
        rcases p2 with ⟨v2, t2, m2, ns2⟩
        simp only [h2] at h
        split at h
        · cases h
        · simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, _, rfl, _⟩ := h
          have hp1 := evalConstExpr_preserves l h1
          have hp2 := (evalConstExpr_preserves r h2).mono hp1.1
          exact hp1.trans hp2
  | sizeOfExpr _ | logAnd _ _ | logOr _ _ | cond _ _ _ | comma _ _ | deref _
  | index _ _ | member _ _ | arrow _ _ | assign _ _ _ | incDec _ _ | call _ _
  | vaStart _ _ | vaEnd _ => simp [evalConstExpr] at h
termination_by sizeOf e

private theorem writeVal_preservedBelow {lim b : BlockId} {off : Int64} {ty : CTy} {v : Val}
    {m m' : Mem} (hb : lim ≤ b) (h : writeVal m b off ty v = some m') :
    MemPreservedBelow lim m m' := by
  unfold writeVal at h
  simp only [bind, Option.bind, guard, Pure.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · dsimp only at h
      cases hty : ty.unqual <;> rw [hty] at h <;> dsimp only at h
      all_goals try cases h
      · -- int
        split at h
        · cases h
        · dsimp only at h
          split at h
          · cases h
          · cases hvi : valAsInt? v with
            | none => rw [hvi] at h; cases h
            | some p =>
              rw [hvi] at h
              exact writeBytes_preservedBelow hb h
      · -- ptr
        split at h
        · cases h
        · dsimp only at h
          cases hv : v <;> rw [hv] at h <;> dsimp only at h
          all_goals try cases h
          · rename_i k bv
            cases hzero : (bv.toNat == 0)
            · simp [hzero] at h
            · simp only [hzero, ↓reduceIte] at h
              exact writeBytes_preservedBelow hb h
          · exact writeBytes_preservedBelow hb h
          · exact writeBytes_preservedBelow hb h
      · -- enumTy
        split at h
        · cases h
        · dsimp only at h
          split at h
          · cases h
          · cases hvi : valAsInt? v with
            | none => rw [hvi] at h; cases h
            | some p =>
              rw [hvi] at h
              exact writeBytes_preservedBelow hb h
      · -- fnPtr
        split at h
        · cases h
        · dsimp only at h
          cases hv : v <;> rw [hv] at h <;> dsimp only at h
          all_goals try cases h
          · rename_i k bv
            cases hzero : (bv.toNat == 0)
            · simp [hzero] at h
            · simp only [hzero, ↓reduceIte] at h
              exact writeBytes_preservedBelow hb h
          · exact writeBytes_preservedBelow hb h
          · exact writeBytes_preservedBelow hb h
      · -- vaList
        cases hv : v <;> rw [hv] at h
        all_goals try cases h
        rename_i bval
        cases bval
        · cases h
        · exact writeBytes_preservedBelow hb h

mutual
theorem writeInitList_preserves {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {b : BlockId} {off : Int64} {elem : CTy} {idx : Nat} {xs : List InitVal}
    {m m' : Mem} {ns ns' : Nat} {lim : BlockId}
    (hb : lim ≤ b) (hm : lim ≤ m.nextBlock)
    (h : writeInitList prog env m strBase b off elem idx xs ns = some (m', ns')) :
    MemPreservedBelow lim m m' := by
  cases xs with
  | nil =>
    simp only [writeInitList, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact MemPreservedBelow.refl _ _
  | cons iv rest =>
    unfold writeInitList at h
    dsimp only [bind, Option.bind] at h
    split at h
    · cases h
    · next a h1 =>
      rcases a with ⟨m1, ns1⟩
      dsimp only at h
      have hp1 := writeInitVal_preserves hb hm h1
      have hp2 := writeInitList_preserves hb (Nat.le_trans hm hp1.1) h
      exact hp1.trans hp2
termination_by sizeOf xs

theorem writeInitFields_preserves {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {b : BlockId} {baseOff offAcc : Nat} {flds : List (String × CTy)} {xs : List InitVal}
    {m m' : Mem} {ns ns' : Nat} {lim : BlockId}
    (hb : lim ≤ b) (hm : lim ≤ m.nextBlock)
    (h : writeInitFields prog env m strBase b baseOff offAcc flds xs ns = some (m', ns')) :
    MemPreservedBelow lim m m' := by
  cases flds with
  | nil =>
    simp only [writeInitFields, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact MemPreservedBelow.refl _ _
  | cons f frest =>
    cases xs with
    | nil =>
      simp only [writeInitFields, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact MemPreservedBelow.refl _ _
    | cons iv irest =>
      unfold writeInitFields at h
      dsimp only [bind, Option.bind] at h
      split at h
      · cases h
      · next a h1 =>
        rcases a with ⟨m1, ns1⟩
        dsimp only at h
        have hp1 := writeInitVal_preserves hb hm h1
        have hp2 := writeInitFields_preserves hb (Nat.le_trans hm hp1.1) h
        exact hp1.trans hp2
termination_by sizeOf xs

theorem writeInitVal_preserves {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {b : BlockId} {off : Int64} {ty : CTy} {iv : InitVal}
    {m m' : Mem} {ns ns' : Nat} {lim : BlockId}
    (hb : lim ≤ b) (hm : lim ≤ m.nextBlock)
    (h : writeInitVal prog env m strBase b off ty iv ns = some (m', ns')) :
    MemPreservedBelow lim m m' := by
  cases iv with
  | expr e =>
    cases e with
    | strLit s =>
      unfold writeInitVal at h
      cases hty : ty.unqual <;> rw [hty] at h <;> dsimp only [bind, Option.bind] at h
      all_goals try (
        cases hev : evalConstExpr prog env m strBase ns (.strLit s) with
        | none => rw [hev] at h; cases h
        | some p =>
          rcases p with ⟨v, t, m1, ns1⟩
          rw [hev] at h
          dsimp only at h
          cases hwr : writeVal m1 b off ty.stripConst v with
          | none => rw [hwr] at h; cases h
          | some m2 =>
            rw [hwr] at h
            cases h
            exact ((evalConstExpr_preserves (.strLit s) hev).mono hm).trans (writeVal_preservedBelow hb hwr))
      cases hwb : m.writeBytes b off
          ((List.range s.utf8ByteSize).map (fun i => MemByte.byte ((s.toUTF8[i]?).getD 0)) ++ [.byte 0]) with
      | none => rw [hwb] at h; cases h
      | some m1 =>
        rw [hwb] at h
        cases h
        exact writeBytes_preservedBelow hb hwb
    | _ =>
      unfold writeInitVal at h
      dsimp only [bind, Option.bind] at h
      split at h
      · cases h
      · next p hev =>
        rcases p with ⟨v, t, m1, ns1⟩
        dsimp only at h
        cases hwr : writeVal m1 b off ty.stripConst v with
        | none => simp [hwr] at h
        | some m2 =>
          simp only [hwr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          exact ((evalConstExpr_preserves _ hev).mono hm).trans (writeVal_preservedBelow hb hwr)
  | list xs =>
    unfold writeInitVal at h
    cases hty : ty.unqual <;> rw [hty] at h <;> dsimp only at h
    · cases h
    · cases h
    · cases h
    · cases h
    · exact writeInitList_preserves hb hm h
    · rename_i tag
      cases hlu : prog.tags.lookup tag with
      | none => simp [hlu] at h
      | some defn =>
        cases defn with
        | structDef flds =>
          simp [hlu] at h
          exact writeInitFields_preserves hb hm h
        | unionDef _ | enumDef _ _ => simp [hlu] at h
    · rename_i tag
      cases xs with
      | nil =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact MemPreservedBelow.refl _ _
      | cons x _ =>
        cases hlu : prog.tags.lookup tag with
        | none => simp [hlu] at h
        | some defn =>
          cases defn with
          | unionDef flds =>
            cases flds with
            | nil => simp [hlu] at h
            | cons f _ =>
              simp only [hlu] at h
              exact writeInitVal_preserves hb hm h
          | structDef _ | enumDef _ _ => simp [hlu] at h
    · exact writeInitFields_preserves hb hm h
    · rename_i flds
      cases xs with
      | nil =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact MemPreservedBelow.refl _ _
      | cons x _ =>
        cases flds with
        | nil => cases h
        | cons f _ => exact writeInitVal_preserves hb hm h
    · cases h
    · cases h
    · cases h
    · cases h
  | intSeq rad vals =>
    unfold writeInitVal at h
    cases hty : ty.unqual <;> rw [hty] at h <;> dsimp only at h
    all_goals try cases h
    cases hk : ty.arrayLeafIntKind? with
    | none => simp [hk] at h
    | some k =>
      simp only [hk, Option.map_eq_some_iff, Prod.mk.injEq] at h
      rcases h with ⟨m1, hwb, rfl, _⟩
      exact writeBytes_preservedBelow hb hwb
termination_by sizeOf iv
end

private theorem memPreservedBelow_roIf {lim : BlockId} {m m2 : Mem} (c : Bool)
    (hp : MemPreservedBelow lim m m2) :
    MemPreservedBelow lim m (if c then
      { m2 with
        blocks := fun x => if x == lim then (m2.blocks lim).map ({ · with perm := .ro }) else m2.blocks x
        fresh := fun x hx => by
          by_cases hxb : x == lim
          · have heq : x = lim := beq_iff_eq.mp hxb; subst heq; simp [m2.fresh x hx]
          · simp [hxb, m2.fresh x hx] }
      else m2) := by
  cases c
  · exact hp
  · refine ⟨hp.1, fun x hx => ?_⟩
    simp only [beq_false_of_ne (Nat.ne_of_lt hx), ↓reduceIte]
    exact hp.2 x hx

theorem allocVarInit_preserves {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {bid : BlockId} {ty : CTy}
    (h : allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns')) :
    bid = m.nextBlock ∧ MemPreservedBelow m.nextBlock m m' := by
  unfold allocVarInit at h
  simp only [bind, Option.bind, pure, Pure.pure] at h
  split at h
  · cases h
  · next a halloc =>
    rcases a with ⟨bid0, m1⟩
    dsimp only at h
    unfold_lhs halloc
    have hbid0 : bid0 = m.nextBlock ∧ MemPreservedBelow m.nextBlock m m1 ∧ m1.nextBlock = m.nextBlock + 1 := by
      split at halloc
      · split at halloc
        · split at halloc
          · cases halloc
            exact ⟨rfl, ⟨Nat.le_succ _, fun x hx => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hx)⟩, rfl⟩
          · cases halloc
        · cases halloc
      · cases halloc
    rcases hbid0 with ⟨rfl, hp1, hm1next⟩
    cases hinit : d.init? with
    | none =>
      rw [hinit] at h
      dsimp only at h
      cases h
      exact ⟨rfl, memPreservedBelow_roIf _ hp1⟩
    | some iv =>
      rw [hinit] at h
      dsimp only at h
      cases hwr : writeInitVal prog env m1 strBase m.nextBlock 0 (resolveDeclTy d.ty (some iv)) iv ns with
      | none => rw [hwr] at h; cases h
      | some p =>
        rcases p with ⟨m2, ns2⟩
        rw [hwr] at h
        dsimp only at h
        cases h
        have hp2 := writeInitVal_preserves (lim := m.nextBlock) (Nat.le_refl _) (by rw [hm1next]; exact Nat.le_succ _) hwr
        exact ⟨rfl, memPreservedBelow_roIf _ (hp1.trans hp2)⟩

theorem allocVarInit_intSeq_inv {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {el : CTy} {len? : Option Nat} {k : IntKind} {rad : LitRadix} {vals : Array Int}
    (hty : (resolveDeclTy d.ty d.init?).unqual = .array el len?)
    (hk : (resolveDeclTy d.ty d.init?).arrayLeafIntKind? = some k)
    (hinit : d.init? = some (.intSeq rad vals))
    {bid : BlockId} {ty : CTy}
    (h : allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns')) :
    bid = m.nextBlock ∧ ty = resolveDeclTy d.ty d.init? ∧ ns' = ns ∧
    m'.nextBlock = m.nextBlock + 1 ∧
    (∀ x < m.nextBlock, m'.blocks x = m.blocks x) ∧
    ∃ blk, m'.blocks bid = some blk ∧
      blk.size = max 1 (sizeofTy prog.tags ty) ∧
      blk.align = max 1 (alignofTy prog.tags ty) ∧
      blk.kind = .global ∧
      blk.perm = (if ty.isReadOnly then .ro else .rw) ∧
      (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
      (k.align ∣ blk.align → ∀ i (hi : i < vals.size),
        Sem.readVal prog.tags m' bid (Int64.ofNat (k.bytes * i)) (.int k) =
          some (.int k (BitVec.ofInt k.bits vals[i]))) := by
  unfold allocVarInit at h
  simp only [bind, Option.bind, pure, Pure.pure] at h
  split at h
  · cases h
  · next a halloc =>
    rcases a with ⟨bid0, m1⟩
    dsimp only at h
    unfold_lhs halloc
    have ha : bid0 = m.nextBlock ∧ m1.nextBlock = m.nextBlock + 1 ∧
        (∀ x < m.nextBlock, m1.blocks x = m.blocks x) ∧
        ∃ blk1, m1.blocks bid0 = some blk1 ∧
          blk1.size = max 1 (sizeofTy prog.tags (resolveDeclTy d.ty d.init?)) ∧
          blk1.align = max 1 (alignofTy prog.tags (resolveDeclTy d.ty d.init?)) ∧
          blk1.perm = .rw ∧ blk1.kind = .global ∧ (∀ i, blk1.bytes i = .byte 0) := by
      split at halloc
      · split at halloc
        · split at halloc
          · cases halloc
            refine ⟨rfl, rfl, fun x hx => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hx),
              _, alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, rfl, rfl, rfl, rfl, fun _ => rfl⟩
          · cases halloc
        · cases halloc
      · cases halloc
    rcases ha with ⟨rfl, hm1next, hm1lt, blk1, hblk1, hsz1, hal1, hperm1, hk1, hbytes1⟩
    rw [hinit] at h
    dsimp only at h
    split at h
    · cases h
    · next m2 ns2 hwr =>
      dsimp only at h
      have hwr1 := hwr
      unfold writeInitVal at hwr
      have hty' := hty
      have hk' := hk
      rw [hinit] at hty' hk'
      rw [hty', hk'] at hwr
      dsimp at hwr
      cases hwb : m1.writeBytes m.nextBlock 0
          (vals.toList.flatMap fun v => Mem.encodeInt k (BitVec.ofInt k.bits v)) with
      | none => simp [hwb] at hwr
      | some m2' =>
        simp [hwb] at hwr
        obtain ⟨rfl, rfl⟩ := hwr
        obtain ⟨blk2, hblk2, hsz2, hal2, hperm2, hk2, hba2, hconcr2⟩ :=
          writeBytes_allBytes_total hblk1 hwb (fun i => ⟨0, hbytes1 i⟩)
            (fun _ hx => mem_flatMap_encodeInt_isByte hx)
        have hread : k.align ∣ blk2.align → ∀ i (hi : i < vals.size),
            Sem.readVal prog.tags m2' m.nextBlock (Int64.ofNat (k.bytes * i)) (.int k) =
              some (.int k (BitVec.ofInt k.bits vals[i])) := by
          intro hdvd i hi
          have hd1 : k.align ∣ blk1.align := by rw [← hal2]; exact hdvd
          exact readVal_writeBytes_intArray prog.tags hblk1 hd1 hwb hi
        split at h <;> rename_i hro <;> cases h
        · refine ⟨rfl, by rw [hinit], rfl, ?_, fun x hx => ?_, ?_⟩
          · simp [writeBytes_nextBlock hwb, hm1next]
          · simp only [beq_false_of_ne (Nat.ne_of_lt hx), Bool.false_eq_true, ↓reduceIte]
            rw [writeBytes_blocks_ne hwb (Nat.ne_of_lt hx), hm1lt x hx]
          · refine ⟨{ blk2 with perm := .ro }, by simp [hblk2], by rw [hsz2, hsz1, hinit],
              by rw [hal2, hal1, hinit], by rw [hk2, hk1], ?_, hconcr2, ?_⟩
            · rw [ite_eq_left hro]
            · intro hdvd i hi
              have hr := hread hdvd i hi
              unfold Sem.readVal Mem.readBytes at hr ⊢
              rw [hblk2] at hr
              simp only [beq_self_eq_true, ↓reduceIte, hblk2, Option.map_some]
              exact hr
        · refine ⟨rfl, by rw [hinit], rfl, ?_, fun x hx => ?_, ?_⟩
          · rw [writeBytes_nextBlock hwb, hm1next]
          · rw [writeBytes_blocks_ne hwb (Nat.ne_of_lt hx), hm1lt x hx]
          · refine ⟨blk2, hblk2, by rw [hsz2, hsz1, hinit], by rw [hal2, hal1, hinit], by rw [hk2, hk1], ?_, hconcr2, hread⟩
            rw [ite_eq_right hro, hperm2, hperm1]

/-! ### String Pointer List Initialization (for `z_errmsg`) -/

def CStringLitOk (s : String) : Bool :=
  (List.range s.utf8ByteSize).all (fun i => (s.toUTF8[i]?).getD 0 != 0) &&
  ((s.toUTF8[s.utf8ByteSize]?).getD 0 == 0)

private theorem cstringLitOk_props {s : String} (h : CStringLitOk s = true) :
    (∀ i < s.utf8ByteSize, (s.toUTF8[i]?).getD 0 ≠ 0) ∧
    (s.toUTF8[s.utf8ByteSize]?).getD 0 = 0 := by
  unfold CStringLitOk at h
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  refine ⟨fun i hi => ?_, beq_iff_eq.mp h2⟩
  have hm := List.all_eq_true.mp h1 i (List.mem_range.mpr hi)
  exact bne_iff_ne.mp hm

private theorem writeBytes_blocks_preserve_lt {m m' : Mem} {b : BlockId} {blk blk' : Block}
    {off : Nat} {bs : List MemByte}
    (hb : m.blocks b = some blk) (hwb : m.writeBytes b (Int64.ofNat off) bs = some m')
    (hb' : m'.blocks b = some blk')
    (hoff_lt : off < ptrDiffLimit) :
    blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.perm = blk.perm ∧
    blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr ∧
    (∀ j < off, blk'.bytes j = blk.bytes j) := by
  have heq := writeBytes_blocks_eq hb hwb
  rw [hb', Option.some.injEq] at heq
  subst heq
  have hoff_eq : (Int64.ofNat off).toInt = (off : Int) := by
    change (Int64.ofInt (off : Nat)).toInt = (off : Int)
    rw [ptrDiffLimit_val] at hoff_lt
    exact int64_ofInt_toInt (by omega) (by omega)
  have hoff_nat : (Int64.ofNat off).toInt.toNat = off := by rw [hoff_eq]; omega
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun j hj => ?_⟩
  have hnot : ¬ (off ≤ j ∧ j < off + bs.length) := by omega
  dsimp only
  rw [hoff_nat]
  simp only [hnot, ↓reduceIte]

private theorem readVal_ptr_eq_of_bytes {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId}
    {blk1 blk2 : Block} {off : Nat} {ty : CTy}
    (hb1 : m1.blocks b = some blk1) (hb2 : m2.blocks b = some blk2)
    (hsz : blk2.size = blk1.size) (_hal : blk2.align = blk1.align) (hba : blk2.baseAddr = blk1.baseAddr)
    (hoff : off < ptrDiffLimit)
    (hbytes : ∀ j, off ≤ j → j < off + 8 → blk2.bytes j = blk1.bytes j)
    (htu : ty.unqual = .ptr (.const_ (.int .i8))) :
    Sem.readVal tags m2 b (Int64.ofNat off) ty = Sem.readVal tags m1 b (Int64.ofNat off) ty := by
  unfold Sem.readVal Mem.readBytes
  simp only [htu, hb1, hb2, bind, Option.bind]
  have h1 : Mem.isAligned blk2 (Int64.ofNat off) 8 = Mem.isAligned blk1 (Int64.ofNat off) 8 := by
    simp [Mem.isAligned, hba]
  have h2 : Mem.inBounds blk2 (Int64.ofNat off) 8 = Mem.inBounds blk1 (Int64.ofNat off) 8 := by
    simp [Mem.inBounds, hsz]
  rw [h1, h2]
  cases ha : Mem.isAligned blk1 (Int64.ofNat off) 8
  · rfl
  · cases hin : Mem.inBounds blk1 (Int64.ofNat off) 8
    · rfl
    · have hoff_eq : (Int64.ofNat off).toInt = (off : Int) := by
        change (Int64.ofInt (off : Nat)).toInt = (off : Int)
        rw [ptrDiffLimit_val] at hoff
        exact int64_ofInt_toInt (by omega) (by omega)
      have hoff_nat : (Int64.ofNat off).toInt.toNat = off := by rw [hoff_eq]; omega
      have hmap : ((List.range 8).map fun i => blk2.bytes (off + i)) =
          ((List.range 8).map fun i => blk1.bytes (off + i)) := by
        apply List.map_congr_left
        intro i hi
        have hi8 : i < 8 := List.mem_range.mp hi
        exact hbytes (off + i) (by omega) (by omega)
      simp only [guard, ↓reduceIte, hoff_nat, pure, Pure.pure]
      rw [hmap]

def zErrmsgElemTy : CTy := .const_ (.ptr (.const_ (.int .i8)))

private theorem writeInitList_strPtr_inv {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {b : BlockId} {idx : Nat} {strs : List String}
    {m m' : Mem} {ns ns' : Nat} {blk : Block}
    (hb : m.blocks b = some blk)
    (hblt : b < m.nextBlock)
    (hperm : blk.perm = .rw)
    (hal : 8 ∣ blk.align)
    (hsz : 8 * (idx + strs.length) ≤ blk.size)
    (hok : ∀ s ∈ strs, CStringLitOk s = true)
    (hwr : writeInitList prog env m strBase b 0 zErrmsgElemTy idx
      (strs.map fun s => .expr (.cast (.ptr (.const_ (.int .i8))) (.strLit s))) ns = some (m', ns')) :
    m.nextBlock ≤ m'.nextBlock ∧
    (∀ x < m.nextBlock, x ≠ b → m'.blocks x = m.blocks x) ∧
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.perm = blk.perm ∧
      blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr ∧
      (∀ j < 8 * idx, blk'.bytes j = blk.bytes j) ∧
      (∀ i < strs.length, ∃ sb len,
        Sem.readVal prog.tags m' b (Int64.ofNat (8 * (idx + i))) (.ptr (.const_ (.int .i8))) = some (.ptr sb 0) ∧
        m'.strlenAt sb 0 = some len ∧ b < sb ∧ sb < m'.nextBlock) := by
  induction strs generalizing idx m ns blk with
  | nil =>
    simp only [List.map_nil, writeInitList, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨rfl, _⟩ := hwr
    refine ⟨Nat.le_refl _, fun _ _ _ => rfl, blk, hb, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
      fun i hi => by cases hi⟩
  | cons s rest ih =>
    simp only [List.map_cons, writeInitList, zErrmsgElemTy, sizeofTy_const, sizeofTy_ptr, bind, Option.bind] at hwr
    split at hwr
    · cases hwr
    · next p hstep =>
      rcases p with ⟨m2, ns2⟩
      have hidx_lt : 8 * idx < ptrDiffLimit := by
        have := blk.sizeLt
        simp only [List.length_cons] at hsz
        omega
      have hoff_eq : (Int64.ofInt ((0 : Int64).toInt + (idx : Int) * 8)).toInt = (8 * idx : Int) := by
        have : (0 : Int64).toInt = 0 := rfl
        rw [this, Int.zero_add, Int.mul_comm]
        rw [ptrDiffLimit_val] at hidx_lt
        exact int64_ofInt_toInt (by omega) (by omega)
      have hcast_off : Int64.ofInt ((0 : Int64).toInt + (idx : Int) * 8) = Int64.ofNat (8 * idx) := by
        apply Int64.toInt_inj.mp
        rw [hoff_eq]
        change (8 * idx : Int) = (Int64.ofInt (8 * idx : Nat)).toInt
        rw [ptrDiffLimit_val] at hidx_lt
        exact (int64_ofInt_toInt (by omega) (by omega)).symm
      -- Unpack `writeInitVal` for `.expr (.cast _ (.strLit s))`
      have hstrstep : ∃ m1, m1.nextBlock = m.nextBlock + 1 ∧
          (∀ x < m.nextBlock, m1.blocks x = m.blocks x) ∧
          m1.strlenAt m.nextBlock 0 = some s.utf8ByteSize ∧
          writeVal m1 b (Int64.ofNat (8 * idx)) (CTy.int IntKind.i8).const_.ptr
            (.ptr m.nextBlock 0) = some m2 := by
        unfold writeInitVal at hstep
        simp only [CTy.stripConst, bind, Option.bind] at hstep
        cases hev0 : evalConstExpr prog env m strBase ns (.strLit s) with
        | none =>
          unfold evalConstExpr at hstep
          rw [hev0] at hstep
          cases hstep
        | some p0 =>
          rcases p0 with ⟨v0, t0, m1', ns1'⟩
          have halloc := hev0
          unfold evalConstExpr at halloc
          simp only [bind, Option.bind, pure, Pure.pure] at halloc
          split at halloc
          · cases halloc
          · next a hchk =>
            rcases a with ⟨sb0, m1⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at halloc
            obtain ⟨rfl, rfl, rfl, rfl⟩ := halloc
            unfold_lhs hchk
            have hs0 : sb0 = m.nextBlock ∧ m1.nextBlock = m.nextBlock + 1 ∧
                (∀ x < m.nextBlock, m1.blocks x = m.blocks x) ∧
                m1.strlenAt sb0 0 = some s.utf8ByteSize := by
              split at hchk
              · split at hchk
                · split at hchk
                  · cases hchk
                    have hlit := cstringLitOk_props (hok s (.head _))
                    refine ⟨rfl, rfl, fun x hx => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hx), ?_⟩
                    exact strlenAt_alloc_strLit _ rfl hlit.1 hlit.2
                  · cases hchk
                · cases hchk
              · cases hchk
            rcases hs0 with ⟨rfl, hm1next, hm1lt, hstrlen0⟩
            unfold evalConstExpr at hstep
            rw [hev0] at hstep
            dsimp only [bind, Option.bind] at hstep
            rw [castVal_ptr_ptr] at hstep
            dsimp only [pure, Pure.pure] at hstep
            have hoff_rw : Int64.ofInt ((0 : Int64).toInt + (idx : Int) * ((8 : Nat) : Int)) =
                Int64.ofNat (8 * idx) := hcast_off
            rw [hoff_rw] at hstep
            cases hwrval : writeVal m1 b (Int64.ofNat (8 * idx))
                (CTy.int IntKind.i8).const_.ptr (.ptr m.nextBlock 0) with
            | none => rw [hwrval] at hstep; cases hstep
            | some m2' =>
              rw [hwrval] at hstep
              cases hstep
              exact ⟨m1, hm1next, hm1lt, hstrlen0, hwrval⟩
      obtain ⟨m1, hm1next, hm1lt, hstrlen0, hwrval⟩ := hstrstep
      have hb1 : m1.blocks b = some blk := by rw [hm1lt b hblt, hb]
      -- Extract `m1.writeBytes` from `writeVal`
      unfold writeVal at hwrval
      dsimp only [bind, Option.bind, guard, pure, Pure.pure] at hwrval
      rw [ite_eq_left (by decide)] at hwrval
      dsimp only at hwrval
      rw [hb1] at hwrval
      dsimp only [CTy.unqual] at hwrval
      cases hal8 : Mem.isAligned blk (Int64.ofNat (8 * idx)) 8
      · rw [hal8] at hwrval
        rw [ite_eq_right Bool.false_ne_true] at hwrval
        cases hwrval
      · rw [hal8] at hwrval
        rw [ite_eq_left rfl] at hwrval
        dsimp only at hwrval
        have hm2next : m2.nextBlock = m.nextBlock + 1 := by
          rw [writeBytes_nextBlock hwrval, hm1next]
        have hm2lt : ∀ x < m.nextBlock, x ≠ b → m2.blocks x = m.blocks x := by
          intro x hx hne
          rw [writeBytes_blocks_ne hwrval hne, hm1lt x hx]
        have hm2sb : m2.blocks m.nextBlock = m1.blocks m.nextBlock :=
          writeBytes_blocks_ne hwrval (Nat.ne_of_gt hblt)
        have hstr2 : m2.strlenAt m.nextBlock 0 = some s.utf8ByteSize := by
          unfold Mem.strlenAt; rw [hm2sb]; exact hstrlen0
        have hrd2 : Sem.readVal prog.tags m2 b (Int64.ofNat (8 * idx)) (.ptr (.const_ (.int .i8))) =
            some (.ptr m.nextBlock 0) := by
          have hrb := readBytes_writeBytes_same hb1 hwrval
          have hblk2 := writeBytes_blocks_eq hb1 hwrval
          let ptrBytes : Nat → MemByte := fun i =>
            if (Int64.ofNat (8 * idx)).toInt.toNat ≤ i ∧
               i < (Int64.ofNat (8 * idx)).toInt.toNat + (Mem.encodePtr m.nextBlock 0).length then
              (Mem.encodePtr m.nextBlock 0)[i - (Int64.ofNat (8 * idx)).toInt.toNat]?.getD .undef
            else blk.bytes i
          have hal8' : Mem.isAligned { blk with bytes := ptrBytes } (Int64.ofNat (8 * idx)) 8 = true := by
            simpa [Mem.isAligned] using hal8
          have hlen8 : (Mem.encodePtr m.nextBlock 0).length = 8 := encodePtr_length m.nextBlock 0
          rw [hlen8] at hrb
          dsimp only [ptrBytes] at hal8'
          unfold Sem.readVal
          dsimp only [CTy.unqual, bind, Option.bind, guard, pure, Pure.pure]
          rw [hblk2]
          dsimp only
          rw [ite_eq_left hal8']
          dsimp only
          rw [hrb]
          dsimp only
          rw [decodePtr_encodePtr]
        obtain ⟨blk2, hb2⟩ : ∃ blk2, m2.blocks b = some blk2 := ⟨_, writeBytes_blocks_eq hb1 hwrval⟩
        obtain ⟨hsz2, hal2, hperm2, hk2, hba2, hbytes2⟩ :=
          writeBytes_blocks_preserve_lt (off := 8 * idx) hb1 hwrval hb2 hidx_lt
        have hsz_rest : 8 * ((idx + 1) + rest.length) ≤ blk2.size := by
          rw [hsz2]; simp only [List.length_cons] at hsz
          have : idx + 1 + rest.length = idx + (rest.length + 1) := by omega
          rw [this]; exact hsz
        obtain ⟨hnext_r, hlt_r, blk', hb', hsz', hal', hperm', hk', hba', hbytes', hrest⟩ :=
          ih (idx := idx + 1) (m := m2) (ns := ns2) (blk := blk2) hb2
            (by rw [hm2next]; exact Nat.lt_succ_of_lt hblt) (by rw [hperm2, hperm])
            (by rw [hal2]; exact hal) hsz_rest (fun x hx => hok x (.tail _ hx)) (by dsimp only at hwr; exact hwr)
        refine ⟨Nat.le_trans (by rw [hm2next]; exact Nat.le_succ _) hnext_r,
          fun x hx hne => ?_, blk', hb', by rw [hsz', hsz2], by rw [hal', hal2],
          by rw [hperm', hperm2], by rw [hk', hk2], by rw [hba', hba2], fun j hj => ?_, ?_⟩
        · rw [hlt_r x (by rw [hm2next]; exact Nat.lt_succ_of_lt hx) hne, hm2lt x hx hne]
        · rw [hbytes' j (by omega), hbytes2 j hj]
        · intro i hi
          cases i with
          | zero =>
            refine ⟨m.nextBlock, s.utf8ByteSize, ?_, ?_, hblt,
              Nat.lt_of_lt_of_le (by rw [hm2next]; exact Nat.lt_succ_self _) hnext_r⟩
            · rw [Nat.add_zero]
              rw [readVal_ptr_eq_of_bytes (off := 8 * idx) hb2 hb' hsz' hal' hba' hidx_lt
                (fun j hj1 hj2 => hbytes' j (by omega)) rfl]
              exact hrd2
            · unfold Mem.strlenAt
              rw [hlt_r m.nextBlock (by rw [hm2next]; exact Nat.lt_succ_self _) (Nat.ne_of_gt hblt)]
              exact hstr2
          | succ i' =>
            simp only [List.length_cons] at hi
            have hi' : i' < rest.length := Nat.lt_of_succ_lt_succ hi
            have hidx_eq : idx + (i' + 1) = (idx + 1) + i' := by omega
            rw [hidx_eq]
            exact hrest i' hi'

theorem allocVarInit_zErrmsg_inv {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {strs : List String}
    (hty : d.ty = .array zErrmsgElemTy (some strs.length))
    (hinit : d.init? = some (.list (strs.map fun s => .expr (.cast (.ptr (.const_ (.int .i8))) (.strLit s)))))
    (hok : ∀ s ∈ strs, CStringLitOk s = true)
    {bid : BlockId} {ty : CTy}
    (h : allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns')) :
    bid = m.nextBlock ∧ ty = .array zErrmsgElemTy (some strs.length) ∧
    MemPreservedBelow m.nextBlock m m' ∧
    ∃ blk, m'.blocks bid = some blk ∧
      blk.size = max 1 (8 * strs.length) ∧ blk.align = 8 ∧
      blk.kind = .global ∧ blk.perm = .ro ∧
      (∀ i < strs.length, ∃ sb len,
        Sem.readVal prog.tags m' bid (Int64.ofNat (8 * i)) (.ptr (.const_ (.int .i8))) = some (.ptr sb 0) ∧
        m'.strlenAt sb 0 = some len ∧ sb < m'.nextBlock) := by
  have hres : resolveDeclTy d.ty d.init? = .array zErrmsgElemTy (some strs.length) := by
    rw [hty]; rfl
  have hsz_eq : max 1 (sizeofTy prog.tags (resolveDeclTy d.ty d.init?)) = max 1 (8 * strs.length) := by
    rw [hres, zErrmsgElemTy, sizeofTy_array_some, sizeofTy_const, sizeofTy_ptr, Nat.mul_comm]
  have hal_eq : max 1 (alignofTy prog.tags (resolveDeclTy d.ty d.init?)) = 8 := by
    rw [hres, zErrmsgElemTy, alignofTy_array, alignofTy_const, alignofTy_ptr]; rfl
  unfold allocVarInit at h
  simp only [bind, Option.bind, pure, Pure.pure] at h
  split at h
  · cases h
  · next a halloc =>
    rcases a with ⟨bid0, m1⟩
    dsimp only at h
    unfold_lhs halloc
    have ha : bid0 = m.nextBlock ∧ m1.nextBlock = m.nextBlock + 1 ∧
        (∀ x < m.nextBlock, m1.blocks x = m.blocks x) ∧
        ∃ blk1, m1.blocks bid0 = some blk1 ∧
          blk1.size = max 1 (8 * strs.length) ∧ blk1.align = 8 ∧
          blk1.perm = .rw ∧ blk1.kind = .global := by
      split at halloc
      · split at halloc
        · split at halloc
          · cases halloc
            refine ⟨rfl, rfl, fun x hx => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hx),
              _, alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, hsz_eq, hal_eq, rfl, rfl⟩
          · cases halloc
        · cases halloc
      · cases halloc
    rcases ha with ⟨rfl, hm1next, hm1lt, blk1, hblk1, hsz1, hal1, hperm1, hk1⟩
    rw [hinit] at h
    dsimp only at h
    split at h
    · cases h
    · next p hwr =>
      rcases p with ⟨m2, ns2⟩
      dsimp only at h
      unfold writeInitVal at hwr
      have hres' := hres
      rw [hinit] at hres'
      rw [hres'] at hwr
      simp only [CTy.unqual] at hwr
      have h0len : 8 * (0 + strs.length) ≤ blk1.size := by
        rw [hsz1, Nat.zero_add]; exact Nat.le_max_right _ _
      obtain ⟨hm2next, hm2lt, blk2, hblk2, hsz2, hal2, hperm2, hk2, hba2, _, hptrs⟩ :=
        writeInitList_strPtr_inv hblk1 (by rw [hm1next]; exact Nat.lt_succ_self _) hperm1
          (by rw [hal1]; exact Nat.dvd_refl 8) h0len hok hwr
      rw [hres'] at h
      simp only [zErrmsgElemTy, CTy.isReadOnly, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, _⟩ := h
      refine ⟨rfl, rfl, ⟨Nat.le_trans (by rw [hm1next]; exact Nat.le_succ _) hm2next, fun x hx => ?_⟩, ?_⟩
      · have hne : x ≠ m.nextBlock := Nat.ne_of_lt hx
        simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
        rw [hm2lt x (by rw [hm1next]; exact Nat.lt_succ_of_lt hx) hne, hm1lt x hx]
      · refine ⟨{ blk2 with perm := .ro }, by simp [hblk2], by rw [hsz2, hsz1], by rw [hal2, hal1],
          by rw [hk2, hk1], rfl, fun i hi => ?_⟩
        obtain ⟨sb, len, hrv, hstr, hsb_gt, hsb_lt⟩ := hptrs i hi
        refine ⟨sb, len, ?_, ?_, hsb_lt⟩
        · unfold Sem.readVal Mem.readBytes at hrv ⊢
          rw [Nat.zero_add, hblk2] at hrv
          simp only [CTy.unqual] at hrv ⊢
          simp only [beq_self_eq_true, ↓reduceIte, hblk2, Option.map_some]
          exact hrv
        · have hne : sb ≠ m.nextBlock := Nat.ne_of_gt hsb_gt
          unfold Mem.strlenAt
          simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
          exact hstr

/-! ### `initGlobs` & `initStatics` Preservation & Lookup Lemmas -/

theorem initGlobs_preserves {globBase strBase : Nat → UInt64} {prog0 : Prog}
    {idx ns ns' : Nat} {env env' : Env} {m m' : Mem}
    {globs : List (Linkage × VarDecl)}
    (h : initProg.initGlobs globBase strBase prog0 idx ns env m globs = some (env', m', ns')) :
    MemPreservedBelow m.nextBlock m m' ∧
    (∀ x v, env.lookup x = some v → env'.lookup x = some v) := by
  induction globs generalizing idx ns env m with
  | nil =>
    simp only [initProg.initGlobs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨MemPreservedBelow.refl _ _, fun _ _ hx => hx⟩
  | cons hd rest ih =>
    rcases hd with ⟨_, d⟩
    unfold initProg.initGlobs at h
    split at h
    · exact ih h
    · next hnot =>
      simp only [bind, Option.bind] at h
      split at h
      · cases h
      · next a hal =>
        rcases a with ⟨bid, ty, m1, ns1⟩
        dsimp only at h
        obtain ⟨rfl, hp1⟩ := allocVarInit_preserves hal
        obtain ⟨hp2, henv2⟩ := ih h
        refine ⟨hp1.trans (hp2.mono hp1.1), fun x v hx => ?_⟩
        apply henv2
        have hnone : env.lookup d.name = none := by
          cases hlu : env.lookup d.name <;> simp_all
        have hne : x ≠ d.name := fun heq => by subst heq; rw [hnone] at hx; cases hx
        rw [lookup_cons_ne env hne]
        exact hx

theorem initGlobs_preserves_none {globBase strBase : Nat → UInt64} {prog0 : Prog}
    {idx ns ns' : Nat} {env env' : Env} {m m' : Mem}
    {globs : List (Linkage × VarDecl)}
    (h : initProg.initGlobs globBase strBase prog0 idx ns env m globs = some (env', m', ns'))
    {x : String} (henv : env.lookup x = none)
    (hglobs : ∀ g ∈ globs, g.2.name ≠ x) :
    env'.lookup x = none := by
  induction globs generalizing idx ns env m with
  | nil =>
    simp only [initProg.initGlobs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact henv
  | cons hd rest ih =>
    rcases hd with ⟨_, d⟩
    unfold initProg.initGlobs at h
    split at h
    · exact ih h henv (fun g hg => hglobs g (List.mem_cons_of_mem _ hg))
    · next hnot =>
      simp only [bind, Option.bind] at h
      split at h
      · cases h
      · next a hal =>
        rcases a with ⟨bid, ty, m1, ns1⟩
        dsimp only at h
        apply ih h
        · have hne : x ≠ d.name := Ne.symm (hglobs _ (List.mem_cons_self))
          rw [lookup_cons_ne env hne]
          exact henv
        · exact fun g hg => hglobs g (List.mem_cons_of_mem _ hg)

theorem initGlobs_step_fresh {globBase strBase : Nat → UInt64} {prog0 : Prog}
    {idx ns ns' : Nat} {env env' : Env} {m m' : Mem}
    {l : Linkage} {d : VarDecl} {rest : List (Linkage × VarDecl)}
    (hnone : env.lookup d.name = none)
    (h : initProg.initGlobs globBase strBase prog0 idx ns env m ((l, d) :: rest) = some (env', m', ns')) :
    ∃ bid ty m1 ns1,
      allocVarInit prog0 env m globBase strBase idx ns d = some (bid, ty, m1, ns1) ∧
      initProg.initGlobs globBase strBase prog0 (idx + 1) ns1 ((d.name, bid, ty) :: env) m1 rest =
        some (env', m', ns') := by
  unfold initProg.initGlobs at h
  simp only [hnone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, bind, Option.bind] at h
  split at h
  · cases h
  · next a hal =>
    rcases a with ⟨bid, ty, m1, ns1⟩
    exact ⟨bid, ty, m1, ns1, hal, h⟩

theorem initStatics_preserves {staticBase strBase : Nat → UInt64} {prog0 : Prog} {gEnv : Env}
    {idx ns : Nat} {m m' : Mem} {fnAcc fnList : List (String × Env)}
    {fns : List FnDef}
    (h : initProg.initStatics staticBase strBase prog0 gEnv idx ns m fnAcc fns = some (fnList, m')) :
    MemPreservedBelow m.nextBlock m m' := by
  induction fns generalizing idx ns m fnAcc with
  | nil =>
    simp only [initProg.initStatics, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact MemPreservedBelow.refl _ _
  | cons f frest ih =>
    unfold initProg.initStatics at h
    simp only [bind, Option.bind] at h
    split at h
    · cases h
    · next a hfold =>
      rcases a with ⟨sEnv, m1, idx1, ns1⟩
      dsimp only at h
      have hfold_pres : ∀ (ds : List VarDecl) (sE : Env) (mA : Mem) (iA nA : Nat)
          (sE' : Env) (mA' : Mem) (iA' nA' : Nat),
          ds.foldlM (fun (sE, mA, iA, nA) d => do
            let (bid, ty, mB, nB) ← allocVarInit prog0 gEnv mA staticBase strBase iA nA d
            return ((d.name, bid, ty) :: sE, mB, iA + 1, nB)) (sE, mA, iA, nA) =
            some (sE', mA', iA', nA') →
          MemPreservedBelow mA.nextBlock mA mA' := by
        intro ds
        induction ds with
        | nil =>
          intro sE mA iA nA sE' mA' iA' nA' hf
          simp only [List.foldlM_nil, pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨_, rfl, _, _⟩ := hf
          exact MemPreservedBelow.refl _ _
        | cons d drest ihd =>
          intro sE mA iA nA sE' mA' iA' nA' hf
          simp only [List.foldlM_cons, bind, Option.bind, pure, Pure.pure] at hf
          cases hal1 : allocVarInit prog0 gEnv mA staticBase strBase iA nA d with
          | none => rw [hal1] at hf; cases hf
          | some b =>
            rcases b with ⟨bid, ty, mB, nB⟩
            rw [hal1] at hf
            dsimp only at hf
            obtain ⟨_, hp1⟩ := allocVarInit_preserves hal1
            have hp2 := ihd _ _ _ _ _ _ _ _ hf
            exact hp1.trans (hp2.mono hp1.1)
      have hp1 := hfold_pres (collectFnStatics f.body) [] m idx ns sEnv m1 idx1 ns1 hfold
      have hp2 := ih h
      exact hp1.trans (hp2.mono hp1.1)

theorem initStatics_fnStatics_empty {staticBase strBase : Nat → UInt64} {prog0 : Prog} {gEnv : Env}
    {idx ns : Nat} {m m' : Mem} {fnAcc fnList : List (String × Env)}
    {fns : List FnDef} {sym : String}
    (hinit : initProg.initStatics staticBase strBase prog0 gEnv idx ns m fnAcc fns = some (fnList, m'))
    (hacc : (fnAcc.lookup sym).getD [] = [])
    (hrest : ∀ f ∈ fns, f.name = sym → collectFnStatics f.body = []) :
    (fnList.lookup sym).getD [] = [] := by
  induction fns generalizing idx ns m fnAcc with
  | nil =>
    simp only [initProg.initStatics, Option.some.injEq, Prod.mk.injEq] at hinit
    obtain ⟨rfl, _⟩ := hinit
    exact hacc
  | cons f frest ih =>
    unfold initProg.initStatics at hinit
    simp only [bind, Option.bind] at hinit
    split at hinit
    · cases hinit
    · next a hfold =>
      rcases a with ⟨sEnv, m1, idx1, ns1⟩
      dsimp only at hinit
      apply ih hinit _ (fun g hg => hrest g (.tail _ hg))
      by_cases hnm : sym = f.name
      · have hds : collectFnStatics f.body = [] := hrest f (.head _) hnm.symm
        rw [hds] at hfold
        simp only [List.foldlM_nil, pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at hfold
        obtain ⟨rfl, _, _, _⟩ := hfold
        rw [← hnm, lookup_cons_eq]
        rfl
      · rw [lookup_cons_ne _ hnm]
        exact hacc

/-! ## 5. `InitLibzProps` and `initLibz_props` -/

def crcConstTy : CTy := .const_ (.typedef "z_crc_t" (.typedef "Z_U4" (.int .u32)))

theorem crcTableVals_size : Zlib.Tables.crc32H_vals_crc_table.size = 256 := by decide +kernel
theorem crcBraid2Vals_size : Zlib.Tables.crc32H_vals_crc_braid2_table.size = 1024 := by decide +kernel
theorem crcBraid5Vals_size : Zlib.Tables.crc32H_vals_crc_braid5_table.size = 1024 := by decide +kernel
theorem x2nTableVals_size : Zlib.Tables.crc32H_vals_x2n_table.size = 32 := rfl

theorem x2nTableVals_pos :
    (List.range 32).all (fun i =>
      decide (0 < Zlib.Tables.crc32H_vals_x2n_table[i]! ∧ Zlib.Tables.crc32H_vals_x2n_table[i]! < 2 ^ 32)) = true := by
  decide

private theorem x2nTableVals_bounds {i : Nat} (hi : i < 32) :
    0 < Zlib.Tables.crc32H_vals_x2n_table[i]! ∧ Zlib.Tables.crc32H_vals_x2n_table[i]! < 2 ^ 32 := by
  have hm := List.all_eq_true.mp x2nTableVals_pos i (List.mem_range.mpr hi)
  exact of_decide_eq_true hm

def zErrmsgStrs : List String := [
  "need dictionary",
  "stream end",
  "",
  "file error",
  "stream error",
  "data error",
  "insufficient memory",
  "buffer error",
  "incompatible version",
  ""
]

private theorem zErrmsgStrs_ok : ∀ s ∈ zErrmsgStrs, CStringLitOk s = true := by
  decide

private theorem allHeaders_globals_nil : Zlib.allHeaders.flatMap tuGlobals = [] := rfl
private theorem gzclose_globals_nil : tuGlobals Zlib.Gzclose.gzcloseTU = [] := rfl
private theorem adler32_globals_nil : tuGlobals Zlib.Adler32.adler32TU = [] := rfl
private theorem compress_globals_nil : tuGlobals Zlib.Compress.compressTU = [] := rfl
private theorem uncompr_globals_nil : tuGlobals Zlib.Uncompr.uncomprTU = [] := rfl
private theorem inffast_globals_nil : tuGlobals Zlib.Inffast.inffastTU = [] := rfl

private theorem zutil_globals_eq :
    tuGlobals Zlib.Zutil.zutilTU = [
      (.export_, Zlib.Zutil.zutilTU_global_z_errmsg)
    ] := rfl

private theorem zErrmsg_global_ty :
    Zlib.Zutil.zutilTU_global_z_errmsg.ty = .array zErrmsgElemTy (some zErrmsgStrs.length) := rfl

private theorem zErrmsg_global_init :
    Zlib.Zutil.zutilTU_global_z_errmsg.init? =
      some (.list (zErrmsgStrs.map fun s => .expr (.cast (.ptr (.const_ (.int .i8))) (.strLit s)))) := rfl

private theorem inftrees_globals_eq :
    tuGlobals Zlib.Inftrees.inftreesTU = [
      (.export_, Zlib.Inftrees.inftreesTU_global_inflate_copyright),
      (.static_, Zlib.Tables.inffixedH_global_lenfix),
      (.static_, Zlib.Tables.inffixedH_global_distfix)
    ] := rfl

private theorem crc32_globals_eq :
    tuGlobals Zlib.Crc32.crc32TU = [
      (.static_, Zlib.Tables.crc32H_global_crc_table),
      (.static_, Zlib.Tables.crc32H_global_crc_big_table),
      (.static_, Zlib.Tables.crc32H_global_crc_braid2_table),
      (.static_, Zlib.Tables.crc32H_global_crc_braid2_big_table),
      (.static_, Zlib.Tables.crc32H_global_crc_braid5_table),
      (.static_, Zlib.Tables.crc32H_global_crc_braid5_big_table),
      (.static_, Zlib.Tables.crc32H_global_x2n_table)
    ] := rfl

private theorem prefix_globals_eq :
    (progOfTUs Zlib.allFiles).globals =
      tuGlobals Zlib.Zutil.zutilTU ++
      tuGlobals Zlib.Inftrees.inftreesTU ++
      tuGlobals Zlib.Crc32.crc32TU ++
      suffixTUs.flatMap tuGlobals := by
  rw [progOfTUs_globals, Zlib.allFiles, List.flatMap_append, allHeaders_globals_nil, List.nil_append,
    allTUs_eq_append, List.flatMap_append]
  simp only [prefixTUs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    gzclose_globals_nil, adler32_globals_nil, compress_globals_nil, uncompr_globals_nil,
    inffast_globals_nil, List.nil_append, List.append_nil, List.append_assoc]

mutual
private def noStaticsStmt : CStmt → Bool
  | .decl d => !d.isStatic
  | .decls ds => ds.all (!·.isStatic)
  | .block ss => noStaticsList ss
  | .ifStmt _ t f? => noStaticsStmt t && match f? with | some f => noStaticsStmt f | none => true
  | .whileStmt _ b | .doWhileStmt b _ | .forStmt _ _ _ b | .switchStmt _ b
  | .caseStmt _ b | .defaultStmt b | .labelStmt _ b => noStaticsStmt b
  | _ => true

private def noStaticsList : List CStmt → Bool
  | [] => true
  | s :: ss => noStaticsStmt s && noStaticsList ss
end

mutual
private theorem collectFnStatics_eq_nil_of_noStatics (s : CStmt) (h : noStaticsStmt s = true) :
    collectFnStatics s = [] := by
  cases s with
  | decl d => unfold noStaticsStmt at h; unfold collectFnStatics; simp_all
  | decls ds =>
    unfold noStaticsStmt at h; unfold collectFnStatics
    simp only [List.filter_eq_nil_iff]; intro d hd
    simpa using List.all_eq_true.mp h d hd
  | block ss =>
    unfold noStaticsStmt at h; unfold collectFnStatics
    exact collectFnStatics_list_eq_nil ss h
  | ifStmt _ t f? =>
    unfold noStaticsStmt at h; unfold collectFnStatics
    obtain ⟨ht, hf⟩ := (Bool.and_eq_true _ _).mp h
    rw [collectFnStatics_eq_nil_of_noStatics t ht]
    cases f? with | none => rfl | some f => simp [collectFnStatics_eq_nil_of_noStatics f hf]
  | whileStmt _ b | doWhileStmt b _ | forStmt _ _ _ b | switchStmt _ b
  | caseStmt _ b | defaultStmt b | labelStmt _ b =>
    unfold noStaticsStmt at h; unfold collectFnStatics
    exact collectFnStatics_eq_nil_of_noStatics b h
  | nop | expr _ | returnStmt _ | breakStmt | continueStmt | gotoStmt _ =>
    simp [collectFnStatics]

private theorem collectFnStatics_list_eq_nil (ss : List CStmt) (h : noStaticsList ss = true) :
    ss.flatMap collectFnStatics = [] := by
  cases ss with
  | nil => rfl
  | cons s rest =>
    unfold noStaticsList at h
    obtain ⟨hs, hr⟩ := (Bool.and_eq_true _ _).mp h
    simp only [List.flatMap_cons, collectFnStatics_eq_nil_of_noStatics s hs,
      collectFnStatics_list_eq_nil rest hr, List.nil_append]
end

private def targetFnStaticsEmpty (tu : TU) : Bool :=
  (tuFnEntries tu).all fun (n, f) => !targetFnNames.contains n || noStaticsStmt f.body

private theorem targetFnNames_not_in_otherTUs :
    ([Zlib.Gzclose.gzcloseTU, Zlib.Uncompr.uncomprTU, Zlib.Inftrees.inftreesTU,
      Zlib.Inffast.inffastTU] ++ suffixTUs).all
      (fun tu => targetFnNames.all (fun s => !(tuFnNames tu).contains s)) = true := by
  decide

private theorem zutil_statics_empty : targetFnStaticsEmpty Zlib.Zutil.zutilTU = true := by decide
private theorem adler32_statics_empty : targetFnStaticsEmpty Zlib.Adler32.adler32TU = true := by decide
private theorem compress_statics_empty : targetFnStaticsEmpty Zlib.Compress.compressTU = true := by decide
private theorem crc32_statics_empty : targetFnStaticsEmpty Zlib.Crc32.crc32TU = true := by decide

private theorem collectFnStatics_empty_of_target {sym : String} (hsym : sym ∈ targetFnNames) :
    ∀ f ∈ ((Zlib.allFiles.flatMap (·.items)).filterMap fun | .fnDef f => some f | _ => none),
      f.name = sym → collectFnStatics f.body = [] := by
  have hall : ∀ tu ∈ Zlib.allFiles, ∀ f ∈ tu.items.filterMap (fun | .fnDef f => some f | _ => none),
      f.name = sym → collectFnStatics f.body = [] := by
    intro tu htu f hf hfn
    have hmem : f ∈ (tuFnEntries tu).map (·.2) := by
      unfold tuFnEntries
      simp only [List.mem_map, List.mem_filterMap] at hf ⊢
      rcases hf with ⟨it, hit, hfit⟩
      cases it with
      | fnDef g =>
        simp only [Option.some.injEq] at hfit
        subst hfit
        exact ⟨(g.name, g), ⟨.fnDef g, hit, rfl⟩, rfl⟩
      | _ => cases hfit
    have hnot_other : ∀ tu' ∈ ([Zlib.Gzclose.gzcloseTU, Zlib.Uncompr.uncomprTU,
        Zlib.Inftrees.inftreesTU, Zlib.Inffast.inffastTU] ++ suffixTUs),
        sym ∉ tuFnNames tu' := by
      intro tu' htu' hcontr
      have h1 := List.all_eq_true.mp targetFnNames_not_in_otherTUs tu' htu'
      have h2 := List.all_eq_true.mp h1 sym hsym
      simp [hcontr] at h2
    have hok_tu : ∀ {tu' : TU}, targetFnStaticsEmpty tu' = true → f ∈ (tuFnEntries tu').map (·.2) →
        f.name = sym → collectFnStatics f.body = [] := by
      intro tu' hst hf' hfn'
      simp only [List.mem_map] at hf'
      rcases hf' with ⟨⟨nm, g⟩, hmem', rfl⟩
      have hnm : nm = sym := by
        have hpair : ∀ (a : String) (b : FnDef), (a, b) ∈ tuFnEntries tu' → a = b.name := by
          intro a b hp; unfold tuFnEntries at hp; rw [List.mem_filterMap] at hp
          rcases hp with ⟨it, _, hit⟩; cases it with | fnDef _ => cases hit; rfl | _ => cases hit
        rw [hpair nm g hmem', hfn']
      have hall_st := List.all_eq_true.mp hst (nm, g) hmem'
      rw [hnm] at hall_st
      have hcon : targetFnNames.contains sym = true := List.elem_eq_true_of_mem hsym
      simp only [hcon, Bool.not_true, Bool.false_or] at hall_st
      exact collectFnStatics_eq_nil_of_noStatics g.body hall_st
    have hhdr : ∀ tu' ∈ Zlib.allHeaders, tuFnEntries tu' = [] := by
      intro tu' htu'
      unfold Zlib.allHeaders Zlib.Headers.allABIHeaders at htu'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at htu'
      rcases htu' with rfl | rfl | rfl | rfl <;> rfl
    rcases List.mem_append.mp htu with hh | ht
    · rw [hhdr tu hh] at hmem; cases hmem
    · rw [allTUs_eq_append, List.mem_append] at ht
      rcases ht with hp | hs
      · simp only [prefixTUs, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exfalso; apply hnot_other Zlib.Gzclose.gzcloseTU (by simp)
          rw [← hfn]
          unfold tuFnNames tuFnEntries at *
          simp only [List.mem_map, List.mem_filterMap] at hmem ⊢
          rcases hmem with ⟨⟨_, g⟩, ⟨it, hit, rfl?⟩, rfl⟩
          cases it with | fnDef _ => cases rfl?; exact ⟨_, hit, rfl⟩ | _ => cases rfl?
        · exact hok_tu zutil_statics_empty hmem hfn
        · exact hok_tu adler32_statics_empty hmem hfn
        · exact hok_tu compress_statics_empty hmem hfn
        · exfalso; apply hnot_other Zlib.Uncompr.uncomprTU (by simp)
          rw [← hfn]
          unfold tuFnNames tuFnEntries at *
          simp only [List.mem_map, List.mem_filterMap] at hmem ⊢
          rcases hmem with ⟨⟨_, g⟩, ⟨it, hit, rfl?⟩, rfl⟩
          cases it with | fnDef _ => cases rfl?; exact ⟨_, hit, rfl⟩ | _ => cases rfl?
        · exfalso; apply hnot_other Zlib.Inftrees.inftreesTU (by simp)
          rw [← hfn]
          unfold tuFnNames tuFnEntries at *
          simp only [List.mem_map, List.mem_filterMap] at hmem ⊢
          rcases hmem with ⟨⟨_, g⟩, ⟨it, hit, rfl?⟩, rfl⟩
          cases it with | fnDef _ => cases rfl?; exact ⟨_, hit, rfl⟩ | _ => cases rfl?
        · exfalso; apply hnot_other Zlib.Inffast.inffastTU (by simp)
          rw [← hfn]
          unfold tuFnNames tuFnEntries at *
          simp only [List.mem_map, List.mem_filterMap] at hmem ⊢
          rcases hmem with ⟨⟨_, g⟩, ⟨it, hit, rfl?⟩, rfl⟩
          cases it with | fnDef _ => cases rfl?; exact ⟨_, hit, rfl⟩ | _ => cases rfl?
        · exact hok_tu crc32_statics_empty hmem hfn
      · exfalso; apply hnot_other _ (List.mem_append_right _ hs)
        rw [← hfn]
        unfold tuFnNames tuFnEntries at *
        simp only [List.mem_map, List.mem_filterMap] at hmem ⊢
        rcases hmem with ⟨⟨_, g⟩, ⟨it, hit, rfl?⟩, rfl⟩
        cases it with | fnDef _ => cases rfl?; exact ⟨_, hit, rfl⟩ | _ => cases rfl?
  intro f hf hfn
  simp only [List.mem_filterMap, List.mem_flatMap] at hf
  rcases hf with ⟨it, ⟨tu, htu, hit⟩, hfit⟩
  exact hall tu htu f (List.mem_filterMap.mpr ⟨it, hit, hfit⟩) hfn

def allGlobalVarNames : List String :=
  [ "errno", "z_errmsg"
  , "inflate_copyright", "lenfix", "distfix"
  , "crc_table", "crc_big_table", "crc_braid2_table", "crc_braid2_big_table"
  , "crc_braid5_table", "crc_braid5_big_table", "x2n_table"
  , "extra_lbits", "extra_dbits", "extra_blbits", "bl_order"
  , "static_ltree", "static_dtree", "_dist_code", "_length_code"
  , "base_length", "base_dist", "static_l_desc", "static_d_desc", "static_bl_desc"
  , "deflate_copyright", "configuration_table" ]

private theorem allFiles_globNames_mem :
    Zlib.allFiles.all (fun tu =>
      (tuGlobals tu).all (fun (_, d) => allGlobalVarNames.contains d.name)) = true := by
  decide

structure InitLibzProps (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState) : Prop where
  globalEnv_eq : prog.globalEnv = gEnv
  prog_tags_eq : prog.tags = (progOfTUs Zlib.allFiles).tags
  prog_fns_eq : prog.fns = (progOfTUs Zlib.allFiles).fns
  prog_fnProtos_eq : prog.fnProtos = fun sym =>
    if sym == "LSEEK" then (progOfTUs Zlib.allFiles).fnProtos "lseek64"
    else (progOfTUs Zlib.allFiles).fnProtos sym
  prog_fnStatics_empty : ∀ sym ∈ targetFnNames, prog.fnStatics sym = []
  errno_lt : os0.errnoBlk < m0.nextBlock
  strerror_none : os0.strerrorBlk = none
  errno_blk : ∃ blk, m0.blocks os0.errnoBlk = some blk ∧
    blk.size = 4 ∧ blk.align = 4 ∧ blk.perm = .rw ∧ blk.kind = .global ∧
    (∀ i, blk.bytes i = .byte 0)
  errno_env : gEnv.lookup "errno" = some (os0.errnoBlk, .int .i32)
  z_errmsg_prop : ∃ b blk,
    gEnv.lookup "z_errmsg" = some (b, .array zErrmsgElemTy (some 10)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 80 ∧ blk.align = 8 ∧
    (∀ i < 10, ∃ sb len,
      Sem.readVal prog.tags m0 b (Int64.ofNat (8 * i)) (.ptr (.const_ (.int .i8))) = some (.ptr sb 0) ∧
      m0.strlenAt sb 0 = some len)
  crc_table_prop : ∃ b blk,
    gEnv.lookup "crc_table" = some (b, .array crcConstTy (some 256)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 1024 ∧ blk.align = 4 ∧
    (∀ i, ∃ u : UInt8, blk.bytes i = .byte u)
  crc_braid2_table_prop : ∃ b blk,
    gEnv.lookup "crc_braid2_table" = some (b, .array (.array crcConstTy (some 256)) (some 4)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 4096 ∧ blk.align = 4 ∧
    (∀ i, ∃ u : UInt8, blk.bytes i = .byte u)
  crc_braid5_table_prop : ∃ b blk,
    gEnv.lookup "crc_braid5_table" = some (b, .array (.array crcConstTy (some 256)) (some 4)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 4096 ∧ blk.align = 4 ∧
    (∀ i, ∃ u : UInt8, blk.bytes i = .byte u)
  x2n_table_prop : ∃ b blk,
    gEnv.lookup "x2n_table" = some (b, .array crcConstTy (some 32)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 128 ∧ blk.align = 4 ∧
    (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    (∀ i < 32, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i)) (.int .u32) = some (.int .u32 bv) ∧
      bv = BitVec.ofInt 32 Zlib.Tables.crc32H_vals_x2n_table[i]! ∧
      bv.toNat ≠ 0)
  gEnv_lookup_none : ∀ sym, sym ∉ allGlobalVarNames → gEnv.lookup sym = none

theorem initLibz_props {globBase staticBase strBase : Nat → UInt64} {errnoBase : UInt64}
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (h : initLibz globBase staticBase strBase errnoBase = some (prog, gEnv, m0, os0)) :
    InitLibzProps prog gEnv m0 os0 := by
  unfold initLibz at h
  simp only [bind, Option.bind, pure, Pure.pure] at h
  split at h
  · cases h
  · next a hinit =>
    rcases a with ⟨p, gEnv', mFinal, os'⟩
    cases h
    unfold initProg at hinit
    simp only [bind, Option.bind, pure, Pure.pure] at hinit
    split at hinit
    · cases hinit
    · next ePair hallocE =>
      rcases ePair with ⟨eBid, mStart⟩
      dsimp only at hinit
      unfold_lhs hallocE
      have he0 : eBid = 0 ∧ mStart.nextBlock = 1 ∧
          ∃ eblk, mStart.blocks 0 = some eblk ∧
            eblk.size = 4 ∧ eblk.align = 4 ∧ eblk.perm = .rw ∧ eblk.kind = .global ∧
            (∀ i, eblk.bytes i = .byte 0) := by
        split at hallocE
        · split at hallocE
          · split at hallocE
            · cases hallocE
              exact ⟨rfl, rfl, _, alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, rfl, rfl, rfl, rfl, fun _ => rfl⟩
            · cases hallocE
          · cases hallocE
        · cases hallocE
      rcases he0 with ⟨rfl, hmStartNext, eblk, heblk, hesz, heal, heperm, hekind, hebytes⟩
      split at hinit
      · cases hinit
      · next gPair hglobs =>
        rcases gPair with ⟨gEnv1, m1, ns1⟩
        dsimp only at hinit
        split at hinit
        · cases hinit
        · next sPair hstatics =>
          rcases sPair with ⟨fnStaticList, m2⟩
          cases hinit
          have hp_stat := initStatics_preserves hstatics
          have hg_none : ∀ sym, sym ∉ allGlobalVarNames → gEnv'.lookup sym = none := by
            intro sym hnot
            apply initGlobs_preserves_none hglobs
            · have hne : sym ≠ "errno" := fun h => hnot (h ▸ by decide)
              exact lookup_cons_ne [] hne
            · intro g hg heq
              rw [progOfTUs_globals] at hg
              simp only [List.mem_flatMap] at hg
              rcases hg with ⟨tu, htu, hgtu⟩
              have h1 := List.all_eq_true.mp allFiles_globNames_mem tu htu
              have h2 := List.all_eq_true.mp h1 g hgtu
              have hmem : g.2.name ∈ allGlobalVarNames := by simpa using h2
              exact hnot (heq ▸ hmem)
          -- Rewrite `prog0.globals` into explicit 11-item prefix ++ suffix
          rw [prefix_globals_eq, zutil_globals_eq, inftrees_globals_eq, crc32_globals_eq] at hglobs
          simp only [List.cons_append, List.nil_append] at hglobs
          -- Step 1: z_errmsg
          obtain ⟨bid_err, ty_err, m_err, ns_err, hal_err, hglobs⟩ :=
            initGlobs_step_fresh (by rfl) hglobs
          obtain ⟨hbid_err, hty_err, hp_err, blk_err, hblk_err, hsz_err, hal_err', hk_err, hperm_err, hptrs_err⟩ :=
            allocVarInit_zErrmsg_inv zErrmsg_global_ty zErrmsg_global_init zErrmsgStrs_ok hal_err
          -- Step 2: inflate_copyright
          obtain ⟨bid_ic, ty_ic, m_ic, ns_ic, hal_ic, hglobs⟩ :=
            initGlobs_step_fresh (by rfl) hglobs
          obtain ⟨hbid_ic, hp_ic⟩ := allocVarInit_preserves hal_ic
          -- Step 3: lenfix
          obtain ⟨bid_lf, ty_lf, m_lf, ns_lf, hal_lf, hglobs⟩ :=
            initGlobs_step_fresh (by rfl) hglobs
          obtain ⟨hbid_lf, hp_lf⟩ := allocVarInit_preserves hal_lf
          -- Step 4: distfix
          obtain ⟨bid_df, ty_df, m_df, ns_df, hal_df, hglobs⟩ :=
            initGlobs_step_fresh (by rfl) hglobs
          obtain ⟨hbid_df, hp_df⟩ := allocVarInit_preserves hal_df
          -- Step 5: crc_table
          obtain ⟨bid_ct, ty_ct, m_ct, ns_ct, hal_ct, hglobs⟩ :=
            initGlobs_step_fresh (by rfl) hglobs
          obtain ⟨hbid_ct, hty_ct, _, hm_ct_next, hm_ct_lt, blk_ct, hblk_ct, hsz_ct, hal_ct', hk_ct,
              hperm_ct, hconcr_ct, _⟩ :=
            allocVarInit_intSeq_inv (el := crcConstTy) (len? := some 256) (k := .u32) rfl rfl rfl hal_ct
          have hp_ct : MemPreservedBelow m_df.nextBlock m_df m_ct :=
            ⟨by rw [hm_ct_next]; exact Nat.le_succ _, hm_ct_lt⟩
          -- Step 6: crc_big_table
          obtain ⟨bid_cbt, ty_cbt, m_cbt, ns_cbt, hal_cbt, hglobs⟩ :=
            initGlobs_step_fresh (by rfl) hglobs
          obtain ⟨hbid_cbt, hp_cbt⟩ := allocVarInit_preserves hal_cbt
          -- Step 7: crc_braid2_table
          obtain ⟨bid_b2, ty_b2, m_b2, ns_b2, hal_b2, hglobs⟩ :=
            initGlobs_step_fresh (by rfl) hglobs
          obtain ⟨hbid_b2, hty_b2, _, hm_b2_next, hm_b2_lt, blk_b2, hblk_b2, hsz_b2, hal_b2', hk_b2,
              hperm_b2, hconcr_b2, _⟩ :=
            allocVarInit_intSeq_inv (el := .array crcConstTy (some 256)) (len? := some 4) (k := .u32)
              rfl rfl rfl hal_b2
          have hp_b2 : MemPreservedBelow m_cbt.nextBlock m_cbt m_b2 :=
            ⟨by rw [hm_b2_next]; exact Nat.le_succ _, hm_b2_lt⟩
          -- Step 8: crc_braid2_big_table
          obtain ⟨bid_b2b, ty_b2b, m_b2b, ns_b2b, hal_b2b, hglobs⟩ :=
            initGlobs_step_fresh (by rfl) hglobs
          obtain ⟨hbid_b2b, hp_b2b⟩ := allocVarInit_preserves hal_b2b
          -- Step 9: crc_braid5_table
          obtain ⟨bid_b5, ty_b5, m_b5, ns_b5, hal_b5, hglobs⟩ :=
            initGlobs_step_fresh (by rfl) hglobs
          obtain ⟨hbid_b5, hty_b5, _, hm_b5_next, hm_b5_lt, blk_b5, hblk_b5, hsz_b5, hal_b5', hk_b5,
              hperm_b5, hconcr_b5, _⟩ :=
            allocVarInit_intSeq_inv (el := .array crcConstTy (some 256)) (len? := some 4) (k := .u32)
              rfl rfl rfl hal_b5
          have hp_b5 : MemPreservedBelow m_b2b.nextBlock m_b2b m_b5 :=
            ⟨by rw [hm_b5_next]; exact Nat.le_succ _, hm_b5_lt⟩
          -- Step 10: crc_braid5_big_table
          obtain ⟨bid_b5b, ty_b5b, m_b5b, ns_b5b, hal_b5b, hglobs⟩ :=
            initGlobs_step_fresh (by rfl) hglobs
          obtain ⟨hbid_b5b, hp_b5b⟩ := allocVarInit_preserves hal_b5b
          -- Step 11: x2n_table
          obtain ⟨bid_x2n, ty_x2n, m_x2n, ns_x2n, hal_x2n, hglobs⟩ :=
            initGlobs_step_fresh (by rfl) hglobs
          obtain ⟨hbid_x2n, hty_x2n, _, hm_x2n_next, hm_x2n_lt, blk_x2n, hblk_x2n, hsz_x2n, hal_x2n',
              hk_x2n, hperm_x2n, hconcr_x2n, hread_x2n⟩ :=
            allocVarInit_intSeq_inv (el := crcConstTy) (len? := some 32) (k := .u32)
              rfl rfl rfl hal_x2n
          have hp_x2n : MemPreservedBelow m_b5b.nextBlock m_b5b m_x2n :=
            ⟨by rw [hm_x2n_next]; exact Nat.le_succ _, hm_x2n_lt⟩
          -- Step 12: suffix globals
          obtain ⟨hp_suf, henv_suf⟩ := initGlobs_preserves hglobs
          -- Combine `MemPreservedBelow` chains to `m2`
          have hp_from_x2n : MemPreservedBelow m_x2n.nextBlock m_x2n m2 :=
            hp_suf.trans (hp_stat.mono hp_suf.1)
          have hp_from_b5b : MemPreservedBelow m_b5b.nextBlock m_b5b m2 :=
            hp_x2n.trans (hp_from_x2n.mono hp_x2n.1)
          have hp_from_b5 : MemPreservedBelow m_b5.nextBlock m_b5 m2 :=
            hp_b5b.trans (hp_from_b5b.mono hp_b5b.1)
          have hp_from_b2b : MemPreservedBelow m_b2b.nextBlock m_b2b m2 :=
            hp_b5.trans (hp_from_b5.mono hp_b5.1)
          have hp_from_b2 : MemPreservedBelow m_b2.nextBlock m_b2 m2 :=
            hp_b2b.trans (hp_from_b2b.mono hp_b2b.1)
          have hp_from_cbt : MemPreservedBelow m_cbt.nextBlock m_cbt m2 :=
            hp_b2.trans (hp_from_b2.mono hp_b2.1)
          have hp_from_ct : MemPreservedBelow m_ct.nextBlock m_ct m2 :=
            hp_cbt.trans (hp_from_cbt.mono hp_cbt.1)
          have hp_from_df : MemPreservedBelow m_df.nextBlock m_df m2 :=
            hp_ct.trans (hp_from_ct.mono hp_ct.1)
          have hp_from_lf : MemPreservedBelow m_lf.nextBlock m_lf m2 :=
            hp_df.trans (hp_from_df.mono hp_df.1)
          have hp_from_ic : MemPreservedBelow m_ic.nextBlock m_ic m2 :=
            hp_lf.trans (hp_from_lf.mono hp_lf.1)
          have hp_from_err : MemPreservedBelow m_err.nextBlock m_err m2 :=
            hp_ic.trans (hp_from_ic.mono hp_ic.1)
          have hp_from_start : MemPreservedBelow mStart.nextBlock mStart m2 :=
            hp_err.trans (hp_from_err.mono hp_err.1)
          refine ⟨rfl, rfl, rfl, (by dsimp only), ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hg_none⟩
          · -- prog_fnStatics_empty
            intro sym hsym
            exact initStatics_fnStatics_empty hstatics (by rfl)
              (collectFnStatics_empty_of_target hsym)
          · -- errno_lt
            have hlt : mStart.nextBlock ≤ m2.nextBlock := hp_from_start.1
            rw [hmStartNext] at hlt
            exact hlt
          · -- errno_blk
            refine ⟨eblk, ?_, hesz, heal, heperm, hekind, hebytes⟩
            rw [hp_from_start.2 0 (by rw [hmStartNext]; exact Nat.zero_lt_one), heblk]
          · -- errno_env
            apply henv_suf
            simp only [List.lookup,
              show Zlib.Tables.crc32H_global_x2n_table.name = "x2n_table" from rfl,
              show Zlib.Tables.crc32H_global_crc_braid5_big_table.name = "crc_braid5_big_table" from rfl,
              show Zlib.Tables.crc32H_global_crc_braid5_table.name = "crc_braid5_table" from rfl,
              show Zlib.Tables.crc32H_global_crc_braid2_big_table.name = "crc_braid2_big_table" from rfl,
              show Zlib.Tables.crc32H_global_crc_braid2_table.name = "crc_braid2_table" from rfl,
              show Zlib.Tables.crc32H_global_crc_big_table.name = "crc_big_table" from rfl,
              show Zlib.Tables.crc32H_global_crc_table.name = "crc_table" from rfl,
              show Zlib.Tables.inffixedH_global_distfix.name = "distfix" from rfl,
              show Zlib.Tables.inffixedH_global_lenfix.name = "lenfix" from rfl,
              show Zlib.Inftrees.inftreesTU_global_inflate_copyright.name = "inflate_copyright" from rfl,
              show Zlib.Zutil.zutilTU_global_z_errmsg.name = "z_errmsg" from rfl,
              show ("errno" == "x2n_table") = false from rfl,
              show ("errno" == "crc_braid5_big_table") = false from rfl,
              show ("errno" == "crc_braid5_table") = false from rfl,
              show ("errno" == "crc_braid2_big_table") = false from rfl,
              show ("errno" == "crc_braid2_table") = false from rfl,
              show ("errno" == "crc_big_table") = false from rfl,
              show ("errno" == "crc_table") = false from rfl,
              show ("errno" == "distfix") = false from rfl,
              show ("errno" == "lenfix") = false from rfl,
              show ("errno" == "inflate_copyright") = false from rfl,
              show ("errno" == "z_errmsg") = false from rfl,
              beq_self_eq_true]
          · -- z_errmsg_prop
            have hlu_err : gEnv'.lookup "z_errmsg" = some (bid_err, .array zErrmsgElemTy (some 10)) := by
              have hty_err' : ty_err = .array zErrmsgElemTy (some 10) := hty_err
              rw [← hty_err']
              apply henv_suf
              simp only [List.lookup,
                show Zlib.Tables.crc32H_global_x2n_table.name = "x2n_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid5_big_table.name = "crc_braid5_big_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid5_table.name = "crc_braid5_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid2_big_table.name = "crc_braid2_big_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid2_table.name = "crc_braid2_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_big_table.name = "crc_big_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_table.name = "crc_table" from rfl,
                show Zlib.Tables.inffixedH_global_distfix.name = "distfix" from rfl,
                show Zlib.Tables.inffixedH_global_lenfix.name = "lenfix" from rfl,
                show Zlib.Inftrees.inftreesTU_global_inflate_copyright.name = "inflate_copyright" from rfl,
                show Zlib.Zutil.zutilTU_global_z_errmsg.name = "z_errmsg" from rfl,
                show ("z_errmsg" == "x2n_table") = false from rfl,
                show ("z_errmsg" == "crc_braid5_big_table") = false from rfl,
                show ("z_errmsg" == "crc_braid5_table") = false from rfl,
                show ("z_errmsg" == "crc_braid2_big_table") = false from rfl,
                show ("z_errmsg" == "crc_braid2_table") = false from rfl,
                show ("z_errmsg" == "crc_big_table") = false from rfl,
                show ("z_errmsg" == "crc_table") = false from rfl,
                show ("z_errmsg" == "distfix") = false from rfl,
                show ("z_errmsg" == "lenfix") = false from rfl,
                show ("z_errmsg" == "inflate_copyright") = false from rfl,
                beq_self_eq_true]
            have hbid_err_lt : bid_err < m_err.nextBlock := by
              have := lt_nextBlock_of_some hblk_err; exact this
            refine ⟨bid_err, blk_err, hlu_err, ?_, hperm_err, hk_err, ?_, hal_err', fun i hi => ?_⟩
            · rw [hp_from_err.2 bid_err hbid_err_lt, hblk_err]
            · rw [hsz_err]; rfl
            · obtain ⟨sb, len, hrv, hstr, hsb_lt⟩ := hptrs_err i hi
              refine ⟨sb, len, ?_, ?_⟩
              · rw [hp_from_err.readVal hbid_err_lt]; exact hrv
              · rw [hp_from_err.strlenAt hsb_lt]; exact hstr
          · -- crc_table_prop
            have hty_ct' : ty_ct = .array crcConstTy (some 256) := hty_ct
            have hlu_ct : gEnv'.lookup "crc_table" = some (bid_ct, .array crcConstTy (some 256)) := by
              rw [← hty_ct']
              apply henv_suf
              simp only [List.lookup,
                show Zlib.Tables.crc32H_global_x2n_table.name = "x2n_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid5_big_table.name = "crc_braid5_big_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid5_table.name = "crc_braid5_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid2_big_table.name = "crc_braid2_big_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid2_table.name = "crc_braid2_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_big_table.name = "crc_big_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_table.name = "crc_table" from rfl,
                show ("crc_table" == "x2n_table") = false from rfl,
                show ("crc_table" == "crc_braid5_big_table") = false from rfl,
                show ("crc_table" == "crc_braid5_table") = false from rfl,
                show ("crc_table" == "crc_braid2_big_table") = false from rfl,
                show ("crc_table" == "crc_braid2_table") = false from rfl,
                show ("crc_table" == "crc_big_table") = false from rfl,
                beq_self_eq_true]
            have hperm_ct' : blk_ct.perm = .ro := by
              rw [hperm_ct, hty_ct']; rfl
            have hsz_ct' : blk_ct.size = 1024 := by
              rw [hsz_ct, hty_ct']; simp [crcConstTy]; rfl
            have hal_ct'' : blk_ct.align = 4 := by
              rw [hal_ct', hty_ct']; simp [crcConstTy]; rfl
            refine ⟨bid_ct, blk_ct, hlu_ct, ?_, hperm_ct', hk_ct, hsz_ct', hal_ct'', hconcr_ct⟩
            rw [hp_from_ct.2 bid_ct (by rw [hbid_ct, hm_ct_next]; exact Nat.lt_succ_self _), hblk_ct]
          · -- crc_braid2_table_prop
            have hty_b2' : ty_b2 = .array (.array crcConstTy (some 256)) (some 4) := hty_b2
            have hlu_b2 : gEnv'.lookup "crc_braid2_table" =
                some (bid_b2, .array (.array crcConstTy (some 256)) (some 4)) := by
              rw [← hty_b2']
              apply henv_suf
              simp only [List.lookup,
                show Zlib.Tables.crc32H_global_x2n_table.name = "x2n_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid5_big_table.name = "crc_braid5_big_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid5_table.name = "crc_braid5_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid2_big_table.name = "crc_braid2_big_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid2_table.name = "crc_braid2_table" from rfl,
                show ("crc_braid2_table" == "x2n_table") = false from rfl,
                show ("crc_braid2_table" == "crc_braid5_big_table") = false from rfl,
                show ("crc_braid2_table" == "crc_braid5_table") = false from rfl,
                show ("crc_braid2_table" == "crc_braid2_big_table") = false from rfl,
                beq_self_eq_true]
            have hperm_b2' : blk_b2.perm = .ro := by
              rw [hperm_b2, hty_b2']; rfl
            have hsz_b2' : blk_b2.size = 4096 := by
              rw [hsz_b2, hty_b2']; simp [crcConstTy]; rfl
            have hal_b2'' : blk_b2.align = 4 := by
              rw [hal_b2', hty_b2']; simp [crcConstTy]; rfl
            refine ⟨bid_b2, blk_b2, hlu_b2, ?_, hperm_b2', hk_b2, hsz_b2', hal_b2'', hconcr_b2⟩
            rw [hp_from_b2.2 bid_b2 (by rw [hbid_b2, hm_b2_next]; exact Nat.lt_succ_self _), hblk_b2]
          · -- crc_braid5_table_prop
            have hty_b5' : ty_b5 = .array (.array crcConstTy (some 256)) (some 4) := hty_b5
            have hlu_b5 : gEnv'.lookup "crc_braid5_table" =
                some (bid_b5, .array (.array crcConstTy (some 256)) (some 4)) := by
              rw [← hty_b5']
              apply henv_suf
              simp only [List.lookup,
                show Zlib.Tables.crc32H_global_x2n_table.name = "x2n_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid5_big_table.name = "crc_braid5_big_table" from rfl,
                show Zlib.Tables.crc32H_global_crc_braid5_table.name = "crc_braid5_table" from rfl,
                show ("crc_braid5_table" == "x2n_table") = false from rfl,
                show ("crc_braid5_table" == "crc_braid5_big_table") = false from rfl,
                beq_self_eq_true]
            have hperm_b5' : blk_b5.perm = .ro := by
              rw [hperm_b5, hty_b5']; rfl
            have hsz_b5' : blk_b5.size = 4096 := by
              rw [hsz_b5, hty_b5']; simp [crcConstTy]; rfl
            have hal_b5'' : blk_b5.align = 4 := by
              rw [hal_b5', hty_b5']; simp [crcConstTy]; rfl
            refine ⟨bid_b5, blk_b5, hlu_b5, ?_, hperm_b5', hk_b5, hsz_b5', hal_b5'', hconcr_b5⟩
            rw [hp_from_b5.2 bid_b5 (by rw [hbid_b5, hm_b5_next]; exact Nat.lt_succ_self _), hblk_b5]
          · -- x2n_table_prop
            have hty_x2n' : ty_x2n = .array crcConstTy (some 32) := hty_x2n
            have hlu_x2n : gEnv'.lookup "x2n_table" = some (bid_x2n, .array crcConstTy (some 32)) := by
              rw [← hty_x2n']
              apply henv_suf
              simp only [List.lookup,
                show Zlib.Tables.crc32H_global_x2n_table.name = "x2n_table" from rfl,
                beq_self_eq_true]
            have hperm_x2n' : blk_x2n.perm = .ro := by
              rw [hperm_x2n, hty_x2n']; rfl
            have hsz_x2n' : blk_x2n.size = 128 := by
              rw [hsz_x2n, hty_x2n']; simp [crcConstTy]; rfl
            have hal_x2n'' : blk_x2n.align = 4 := by
              rw [hal_x2n', hty_x2n']; simp [crcConstTy]; rfl
            refine ⟨bid_x2n, blk_x2n, hlu_x2n, ?_, hperm_x2n', hk_x2n, hsz_x2n', hal_x2n'',
              hconcr_x2n, fun i hi => ?_⟩
            · rw [hp_from_x2n.2 bid_x2n (by rw [hbid_x2n, hm_x2n_next]; exact Nat.lt_succ_self _), hblk_x2n]
            · have hi' : i < Zlib.Tables.crc32H_vals_x2n_table.size := by rw [x2nTableVals_size]; exact hi
              have hr := hread_x2n (by rw [hal_x2n'']; exact Nat.dvd_refl 4) i hi'
              refine ⟨BitVec.ofInt 32 Zlib.Tables.crc32H_vals_x2n_table[i]!, ?_, rfl, ?_⟩
              · have hget : Zlib.Tables.crc32H_vals_x2n_table[i] = Zlib.Tables.crc32H_vals_x2n_table[i]! := by
                  simp [getElem!_pos Zlib.Tables.crc32H_vals_x2n_table i hi']
                rw [← hget, hp_from_x2n.readVal (by rw [hbid_x2n, hm_x2n_next]; exact Nat.lt_succ_self _)]
                exact hr
              · have hbounds := x2nTableVals_bounds hi
                rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
                omega

end PrivateUnfoldHelper

/-! ## 6. Convenience `InitLibzProps` Lookup Accessors -/

section Accessors
variable {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState} (h : InitLibzProps prog gEnv m0 os0)
include h

theorem prog_fns_zlibVersion : prog.fns "zlibVersion" = some Zlib.Zutil.zutilTU_fn_zlibVersion :=
  h.prog_fns_eq ▸ prog0_fns_zlibVersion
theorem prog_fns_zlibCompileFlags : prog.fns "zlibCompileFlags" = some Zlib.Zutil.zutilTU_fn_zlibCompileFlags :=
  h.prog_fns_eq ▸ prog0_fns_zlibCompileFlags
theorem prog_fns_zError : prog.fns "zError" = some Zlib.Zutil.zutilTU_fn_zError :=
  h.prog_fns_eq ▸ prog0_fns_zError
theorem prog_fns_zcalloc : prog.fns "zcalloc" = some Zlib.Zutil.zutilTU_fn_zcalloc :=
  h.prog_fns_eq ▸ prog0_fns_zcalloc
theorem prog_fns_zcfree : prog.fns "zcfree" = some Zlib.Zutil.zutilTU_fn_zcfree :=
  h.prog_fns_eq ▸ prog0_fns_zcfree

theorem prog_fns_compress2_z : prog.fns "compress2_z" = some Zlib.Compress.compressTU_fn_compress2_z :=
  h.prog_fns_eq ▸ prog0_fns_compress2_z
theorem prog_fns_compress2 : prog.fns "compress2" = some Zlib.Compress.compressTU_fn_compress2 :=
  h.prog_fns_eq ▸ prog0_fns_compress2
theorem prog_fns_compress_z : prog.fns "compress_z" = some Zlib.Compress.compressTU_fn_compress_z :=
  h.prog_fns_eq ▸ prog0_fns_compress_z
theorem prog_fns_compress : prog.fns "compress" = some Zlib.Compress.compressTU_fn_compress :=
  h.prog_fns_eq ▸ prog0_fns_compress
theorem prog_fns_compressBound_z : prog.fns "compressBound_z" = some Zlib.Compress.compressTU_fn_compressBound_z :=
  h.prog_fns_eq ▸ prog0_fns_compressBound_z
theorem prog_fns_compressBound : prog.fns "compressBound" = some Zlib.Compress.compressTU_fn_compressBound :=
  h.prog_fns_eq ▸ prog0_fns_compressBound

theorem prog_fns_adler32_z : prog.fns "adler32_z" = some Zlib.Adler32.adler32TU_fn_adler32_z :=
  h.prog_fns_eq ▸ prog0_fns_adler32_z
theorem prog_fns_adler32 : prog.fns "adler32" = some Zlib.Adler32.adler32TU_fn_adler32 :=
  h.prog_fns_eq ▸ prog0_fns_adler32
theorem prog_fns_adler32_combine_ : prog.fns "adler32_combine_" = some Zlib.Adler32.adler32TU_fn_adler32_combine_ :=
  h.prog_fns_eq ▸ prog0_fns_adler32_combine_
theorem prog_fns_adler32_combine : prog.fns "adler32_combine" = some Zlib.Adler32.adler32TU_fn_adler32_combine :=
  h.prog_fns_eq ▸ prog0_fns_adler32_combine
theorem prog_fns_adler32_combine64 : prog.fns "adler32_combine64" = some Zlib.Adler32.adler32TU_fn_adler32_combine64 :=
  h.prog_fns_eq ▸ prog0_fns_adler32_combine64

theorem prog_fns_byte_swap : prog.fns "byte_swap" = some Zlib.Crc32.crc32TU_fn_byte_swap :=
  h.prog_fns_eq ▸ prog0_fns_byte_swap
theorem prog_fns_multmodp : prog.fns "multmodp" = some Zlib.Crc32.crc32TU_fn_multmodp :=
  h.prog_fns_eq ▸ prog0_fns_multmodp
theorem prog_fns_x2nmodp : prog.fns "x2nmodp" = some Zlib.Crc32.crc32TU_fn_x2nmodp :=
  h.prog_fns_eq ▸ prog0_fns_x2nmodp
theorem prog_fns_get_crc_table : prog.fns "get_crc_table" = some Zlib.Crc32.crc32TU_fn_get_crc_table :=
  h.prog_fns_eq ▸ prog0_fns_get_crc_table
theorem prog_fns_crc_word : prog.fns "crc_word" = some Zlib.Crc32.crc32TU_fn_crc_word :=
  h.prog_fns_eq ▸ prog0_fns_crc_word
theorem prog_fns_crc_word_big : prog.fns "crc_word_big" = some Zlib.Crc32.crc32TU_fn_crc_word_big :=
  h.prog_fns_eq ▸ prog0_fns_crc_word_big
theorem prog_fns_crc32_braid : prog.fns "crc32_braid" = some Zlib.Crc32.crc32TU_fn_crc32_braid :=
  h.prog_fns_eq ▸ prog0_fns_crc32_braid
theorem prog_fns_crc32_z : prog.fns "crc32_z" = some Zlib.Crc32.crc32TU_fn_crc32_z :=
  h.prog_fns_eq ▸ prog0_fns_crc32_z
theorem prog_fns_crc32 : prog.fns "crc32" = some Zlib.Crc32.crc32TU_fn_crc32 :=
  h.prog_fns_eq ▸ prog0_fns_crc32
theorem prog_fns_crc32_combine_gen64 : prog.fns "crc32_combine_gen64" = some Zlib.Crc32.crc32TU_fn_crc32_combine_gen64 :=
  h.prog_fns_eq ▸ prog0_fns_crc32_combine_gen64
theorem prog_fns_crc32_combine_gen : prog.fns "crc32_combine_gen" = some Zlib.Crc32.crc32TU_fn_crc32_combine_gen :=
  h.prog_fns_eq ▸ prog0_fns_crc32_combine_gen
theorem prog_fns_crc32_combine_op : prog.fns "crc32_combine_op" = some Zlib.Crc32.crc32TU_fn_crc32_combine_op :=
  h.prog_fns_eq ▸ prog0_fns_crc32_combine_op
theorem prog_fns_crc32_combine64 : prog.fns "crc32_combine64" = some Zlib.Crc32.crc32TU_fn_crc32_combine64 :=
  h.prog_fns_eq ▸ prog0_fns_crc32_combine64
theorem prog_fns_crc32_combine : prog.fns "crc32_combine" = some Zlib.Crc32.crc32TU_fn_crc32_combine :=
  h.prog_fns_eq ▸ prog0_fns_crc32_combine

theorem prog_fnProtos_zlibVersion : prog.fnProtos "zlibVersion" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zlibVersion) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_zlibVersion
theorem prog_fnProtos_zlibCompileFlags : prog.fnProtos "zlibCompileFlags" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zlibCompileFlags) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_zlibCompileFlags
theorem prog_fnProtos_zError : prog.fnProtos "zError" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zError) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_zError
theorem prog_fnProtos_zcalloc : prog.fnProtos "zcalloc" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zcalloc) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_zcalloc
theorem prog_fnProtos_zcfree : prog.fnProtos "zcfree" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zcfree) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_zcfree

theorem prog_fnProtos_compress2_z : prog.fnProtos "compress2_z" = some (fnDefSig Zlib.Compress.compressTU_fn_compress2_z) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_compress2_z
theorem prog_fnProtos_compress2 : prog.fnProtos "compress2" = some (fnDefSig Zlib.Compress.compressTU_fn_compress2) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_compress2
theorem prog_fnProtos_compress_z : prog.fnProtos "compress_z" = some (fnDefSig Zlib.Compress.compressTU_fn_compress_z) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_compress_z
theorem prog_fnProtos_compress : prog.fnProtos "compress" = some (fnDefSig Zlib.Compress.compressTU_fn_compress) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_compress
theorem prog_fnProtos_compressBound_z : prog.fnProtos "compressBound_z" = some (fnDefSig Zlib.Compress.compressTU_fn_compressBound_z) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_compressBound_z
theorem prog_fnProtos_compressBound : prog.fnProtos "compressBound" = some (fnDefSig Zlib.Compress.compressTU_fn_compressBound) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_compressBound

theorem prog_fnProtos_adler32_z : prog.fnProtos "adler32_z" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_z) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_adler32_z
theorem prog_fnProtos_adler32 : prog.fnProtos "adler32" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_adler32
theorem prog_fnProtos_adler32_combine_ : prog.fnProtos "adler32_combine_" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_combine_) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_adler32_combine_
theorem prog_fnProtos_adler32_combine : prog.fnProtos "adler32_combine" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_combine) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_adler32_combine
theorem prog_fnProtos_adler32_combine64 : prog.fnProtos "adler32_combine64" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_combine64) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_adler32_combine64

theorem prog_fnProtos_byte_swap : prog.fnProtos "byte_swap" = some (fnDefSig Zlib.Crc32.crc32TU_fn_byte_swap) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_byte_swap
theorem prog_fnProtos_multmodp : prog.fnProtos "multmodp" = some (fnDefSig Zlib.Crc32.crc32TU_fn_multmodp) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_multmodp
theorem prog_fnProtos_x2nmodp : prog.fnProtos "x2nmodp" = some (fnDefSig Zlib.Crc32.crc32TU_fn_x2nmodp) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_x2nmodp
theorem prog_fnProtos_get_crc_table : prog.fnProtos "get_crc_table" = some (fnDefSig Zlib.Crc32.crc32TU_fn_get_crc_table) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_get_crc_table
theorem prog_fnProtos_crc_word : prog.fnProtos "crc_word" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc_word) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_crc_word
theorem prog_fnProtos_crc_word_big : prog.fnProtos "crc_word_big" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc_word_big) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_crc_word_big
theorem prog_fnProtos_crc32_braid : prog.fnProtos "crc32_braid" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_braid) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_crc32_braid
theorem prog_fnProtos_crc32_z : prog.fnProtos "crc32_z" = some crc32_zProtoSig := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_crc32_z
theorem prog_fnProtos_crc32 : prog.fnProtos "crc32" = some crc32ProtoSig := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_crc32
theorem prog_fnProtos_crc32_combine_gen64 : prog.fnProtos "crc32_combine_gen64" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine_gen64) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_crc32_combine_gen64
theorem prog_fnProtos_crc32_combine_gen : prog.fnProtos "crc32_combine_gen" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine_gen) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_crc32_combine_gen
theorem prog_fnProtos_crc32_combine_op : prog.fnProtos "crc32_combine_op" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine_op) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_crc32_combine_op
theorem prog_fnProtos_crc32_combine64 : prog.fnProtos "crc32_combine64" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine64) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_crc32_combine64
theorem prog_fnProtos_crc32_combine : prog.fnProtos "crc32_combine" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_crc32_combine

theorem prog_fnStatics_eq_nil {sym : String} (hsym : sym ∈ targetFnNames) :
    prog.fnStatics sym = [] :=
  h.prog_fnStatics_empty sym hsym

theorem prog_fnStatics_zlibVersion : prog.fnStatics "zlibVersion" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_zlibCompileFlags : prog.fnStatics "zlibCompileFlags" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_zError : prog.fnStatics "zError" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_zcalloc : prog.fnStatics "zcalloc" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_zcfree : prog.fnStatics "zcfree" = [] := h.prog_fnStatics_empty _ (by decide)

theorem prog_fnStatics_compress2_z : prog.fnStatics "compress2_z" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_compress2 : prog.fnStatics "compress2" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_compress_z : prog.fnStatics "compress_z" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_compress : prog.fnStatics "compress" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_compressBound_z : prog.fnStatics "compressBound_z" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_compressBound : prog.fnStatics "compressBound" = [] := h.prog_fnStatics_empty _ (by decide)

theorem prog_fnStatics_adler32_z : prog.fnStatics "adler32_z" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_adler32 : prog.fnStatics "adler32" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_adler32_combine_ : prog.fnStatics "adler32_combine_" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_adler32_combine : prog.fnStatics "adler32_combine" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_adler32_combine64 : prog.fnStatics "adler32_combine64" = [] := h.prog_fnStatics_empty _ (by decide)

theorem prog_fnStatics_byte_swap : prog.fnStatics "byte_swap" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_multmodp : prog.fnStatics "multmodp" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_x2nmodp : prog.fnStatics "x2nmodp" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_get_crc_table : prog.fnStatics "get_crc_table" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_crc_word : prog.fnStatics "crc_word" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_crc_word_big : prog.fnStatics "crc_word_big" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_crc32_braid : prog.fnStatics "crc32_braid" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_crc32_z : prog.fnStatics "crc32_z" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_crc32 : prog.fnStatics "crc32" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_crc32_combine_gen64 : prog.fnStatics "crc32_combine_gen64" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_crc32_combine_gen : prog.fnStatics "crc32_combine_gen" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_crc32_combine_op : prog.fnStatics "crc32_combine_op" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_crc32_combine64 : prog.fnStatics "crc32_combine64" = [] := h.prog_fnStatics_empty _ (by decide)
theorem prog_fnStatics_crc32_combine : prog.fnStatics "crc32_combine" = [] := h.prog_fnStatics_empty _ (by decide)

theorem prog_fns_malloc : prog.fns "malloc" = none :=
  h.prog_fns_eq ▸ prog0_fns_none_of_not_mem (by decide)
theorem prog_fns_calloc : prog.fns "calloc" = none :=
  h.prog_fns_eq ▸ prog0_fns_none_of_not_mem (by decide)
theorem prog_fns_free : prog.fns "free" = none :=
  h.prog_fns_eq ▸ prog0_fns_none_of_not_mem (by decide)

theorem prog_fnProtos_malloc : prog.fnProtos "malloc" = some (.ptr .void, [.int .u64], false) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_stdLibc (by decide) (by rfl)
theorem prog_fnProtos_calloc : prog.fnProtos "calloc" = some (.ptr .void, [.int .u64, .int .u64], false) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_stdLibc (by decide) (by rfl)
theorem prog_fnProtos_free : prog.fnProtos "free" = some (.void, [.ptr .void], false) := by
  rw [h.prog_fnProtos_eq]; exact prog0_fnProtos_stdLibc (by decide) (by rfl)

end Accessors

end Zlib.Proof

