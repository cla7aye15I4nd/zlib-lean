import Zlib.Proof.ProgLookup
import Zlib.Tables.InffixedH
import Zlib.Tables.TreesH

/-!
# Complete Program Lookup & `initLibz` Inversion Lemmas (`Zlib.Proof.ProgLookupAll`)

Extends `Zlib.Proof.ProgLookup` to cover ALL 15 translation units and `stdLibc`:
1. Struct layouts (`alignofTy`, `sizeofTy`, `fieldLayout?`) and enum constants under `prog.tags`.
2. `prog.fns` and `prog.fnProtos` lookups for all remaining 134 functions and all remaining `stdLibc` symbols.
3. `prog.fnStatics` emptiness for all 130 non-static functions and exact static block inversions
   for `inflate_table`, `inflate`, `inflateBack`, and `deflateInit2_`.
4. `InitLibzAllProps` and `initLibz_allProps` covering all global tables, `z_errmsg` string literal
   blocks, and local static tables without unfolding `Zlib.allFiles` via `rfl`.
-/

namespace Zlib.Proof

open C99 C99.Sem C99.Proof Zlib Zlib.Spec

/-! ## 1. Complete Tag Lookups, Enum Constants, and ABI Struct Layouts -/

section TagAndLayoutHelpers

private theorem collectTagEnv_flatMap (f : TU → List TopItem) (tus : List TU) :
    collectTagEnv (tus.flatMap f) = tus.flatMap (fun tu => collectTagEnv (f tu)) := by
  unfold collectTagEnv
  exact filterMap_flatMap _ _ tus

private theorem tags_gzclose : collectTagEnv Zlib.Gzclose.gzcloseTU.items = [] := rfl
private theorem tags_zutil : collectTagEnv Zlib.Zutil.zutilTU.items = [] := rfl
private theorem tags_adler32 : collectTagEnv Zlib.Adler32.adler32TU.items = [] := rfl
private theorem tags_compress : collectTagEnv Zlib.Compress.compressTU.items = [] := rfl
private theorem tags_uncompr : collectTagEnv Zlib.Uncompr.uncomprTU.items = [] := rfl
private theorem tags_inftrees : collectTagEnv Zlib.Inftrees.inftreesTU.items = [] := rfl
private theorem tags_inffast : collectTagEnv Zlib.Inffast.inffastTU.items = [] := rfl
private theorem tags_crc32 : collectTagEnv Zlib.Crc32.crc32TU.items = [] := rfl
private theorem tags_trees : collectTagEnv Zlib.Trees.treesTU.items = [] := rfl
private theorem tags_infback : collectTagEnv Zlib.Infback.infbackTU.items = [] := rfl
private theorem tags_inflate : collectTagEnv Zlib.Inflate.inflateTU.items = [] := rfl
private theorem tags_gzlib : collectTagEnv Zlib.Gzlib.gzlibTU.items = [] := rfl
private theorem tags_gzread : collectTagEnv Zlib.Gzread.gzreadTU.items = [] := rfl
private theorem tags_gzwrite : collectTagEnv Zlib.Gzwrite.gzwriteTU.items = [] := rfl

private def configFields : List (String × CTy) := [
  ("good_length", .typedef "ush" (.int .u16)),
  ("max_lazy", .typedef "ush" (.int .u16)),
  ("nice_length", .typedef "ush" (.int .u16)),
  ("max_chain", .typedef "ush" (.int .u16)),
  ("func", .typedef "compress_func" (.fnPtr (.typedef "block_state" (.int .u32))
    [.ptr (.typedef "deflate_state" (.structTy "internal_state")), .int .i32] false))
]

private def deflateTagEnv : TypeEnv := [
  ("block_state", .enumDef [("need_more", none), ("block_done", none),
    ("finish_started", none), ("finish_done", none)] true),
  ("config_s", .structDef configFields)
]

private theorem tags_deflate :
    collectTagEnv Zlib.Deflate.deflateTU.items = deflateTagEnv := rfl

private theorem allTUs_tags_eq :
    collectTagEnv (Zlib.allTUs.flatMap (·.items)) = deflateTagEnv := by
  rw [collectTagEnv_flatMap]
  simp only [Zlib.allTUs, List.flatMap_cons, List.flatMap_nil,
    tags_gzclose, tags_zutil, tags_adler32, tags_compress, tags_uncompr, tags_inftrees,
    tags_inffast, tags_crc32, tags_trees, tags_infback, tags_inflate, tags_deflate,
    tags_gzlib, tags_gzread, tags_gzwrite, List.nil_append, List.append_nil]

theorem prog0_tags_eq :
    (progOfTUs Zlib.allFiles).tags = headerTagEnv ++ deflateTagEnv := by
  rw [prog_tags_eq_append, allTUs_tags_eq]

private theorem headerTagEnv_len : headerTagEnv.length = 12 := rfl
private theorem deflateTagEnv_len : deflateTagEnv.length = 2 := rfl

theorem prog_tags_len : (progOfTUs Zlib.allFiles).tags.length = 14 := by
  rw [prog0_tags_eq, List.length_append, headerTagEnv_len, deflateTagEnv_len]

private theorem prog_tags_len_ge_14 : 14 ≤ (progOfTUs Zlib.allFiles).tags.length := by
  rw [prog_tags_len]; exact Nat.le_refl _

/-! ### Tag Field Definitions and `tags.lookup` Lemmas -/

def codeFields : List (String × CTy) := [
  ("op", .int .u8),
  ("bits", .int .u8),
  ("val", .int .u16)
]

def codeCTy : CTy := .typedef "code" (.anonStruct codeFields)
def codeConstTy : CTy := .const_ codeCTy

def ctDataFcUnionTy : CTy := .anonUnion [
  ("freq", .typedef "ush" (.int .u16)),
  ("code", .typedef "ush" (.int .u16))
]

def ctDataDlUnionTy : CTy := .anonUnion [
  ("dad", .typedef "ush" (.int .u16)),
  ("len", .typedef "ush" (.int .u16))
]

def ctDataFields : List (String × CTy) := [
  ("fc", ctDataFcUnionTy),
  ("dl", ctDataDlUnionTy)
]

def ctDataCTy : CTy := .typedef "ct_data" (.structTy "ct_data_s")
def ctDataConstTy : CTy := .const_ ctDataCTy

def staticTreeDescFields : List (String × CTy) := [
  ("static_tree", .ptr ctDataConstTy),
  ("extra_bits", .ptr (.const_ (.typedef "intf" (.int .i32)))),
  ("extra_base", .int .i32),
  ("elems", .int .i32),
  ("max_length", .int .i32)
]

def treeDescFields : List (String × CTy) := [
  ("dyn_tree", .ptr ctDataCTy),
  ("max_code", .int .i32),
  ("stat_desc", .ptr (.const_ (.typedef "static_tree_desc" (.structTy "static_tree_desc_s"))))
]

def gzHeaderFields : List (String × CTy) := [
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
]

def inflateStateFields : List (String × CTy) := [
  ("strm", .typedef "z_streamp" (.ptr (.typedef "z_stream" (.structTy "z_stream_s")))),
  ("mode", .typedef "inflate_mode" (.int .u32)),
  ("last", .int .i32),
  ("wrap", .int .i32),
  ("reqwrap", .int .i32),
  ("havedict", .int .i32),
  ("flags", .int .i32),
  ("dmax", .int .u32),
  ("check", .int .u64),
  ("total", .int .u64),
  ("head", .typedef "gz_headerp" (.ptr (.typedef "gz_header" (.structTy "gz_header_s")))),
  ("reqbits", .int .u32),
  ("wbits", .int .u32),
  ("wsize", .int .u32),
  ("whave", .int .u32),
  ("wnext", .int .u32),
  ("window", .ptr (.int .u8)),
  ("hold", .int .u64),
  ("bits", .int .u32),
  ("length", .int .u32),
  ("offset", .int .u32),
  ("extra", .int .u32),
  ("lencode", .ptr codeConstTy),
  ("distcode", .ptr codeConstTy),
  ("lenbits", .int .u32),
  ("distbits", .int .u32),
  ("ncode", .int .u32),
  ("nlen", .int .u32),
  ("ndist", .int .u32),
  ("have", .int .u32),
  ("next", .ptr codeCTy),
  ("lens", .array (.int .u16) (some 320)),
  ("work", .array (.int .u16) (some 288)),
  ("codes", .array codeCTy (some 1732)),
  ("sane", .int .i32),
  ("back", .int .i32),
  ("was", .int .u32)
]

def internalStateFields : List (String × CTy) := [
  ("strm", .typedef "z_streamp" (.ptr (.typedef "z_stream" (.structTy "z_stream_s")))),
  ("status", .int .i32),
  ("pending_buf", .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))),
  ("pending_buf_size", .typedef "ulg" (.int .u64)),
  ("pending_out", .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))),
  ("pending", .typedef "ulg" (.int .u64)),
  ("wrap", .int .i32),
  ("gzhead", .typedef "gz_headerp" (.ptr (.typedef "gz_header" (.structTy "gz_header_s")))),
  ("gzindex", .typedef "ulg" (.int .u64)),
  ("method", .typedef "Byte" (.int .u8)),
  ("last_flush", .int .i32),
  ("w_size", .typedef "uInt" (.int .u32)),
  ("w_bits", .typedef "uInt" (.int .u32)),
  ("w_mask", .typedef "uInt" (.int .u32)),
  ("window", .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))),
  ("window_size", .typedef "ulg" (.int .u64)),
  ("prev", .ptr (.typedef "Posf" (.typedef "Pos" (.typedef "ush" (.int .u16))))),
  ("head", .ptr (.typedef "Posf" (.typedef "Pos" (.typedef "ush" (.int .u16))))),
  ("ins_h", .typedef "uInt" (.int .u32)),
  ("hash_size", .typedef "uInt" (.int .u32)),
  ("hash_bits", .typedef "uInt" (.int .u32)),
  ("hash_mask", .typedef "uInt" (.int .u32)),
  ("hash_shift", .typedef "uInt" (.int .u32)),
  ("block_start", .int .i64),
  ("match_length", .typedef "uInt" (.int .u32)),
  ("prev_match", .typedef "IPos" (.int .u32)),
  ("match_available", .int .i32),
  ("strstart", .typedef "uInt" (.int .u32)),
  ("match_start", .typedef "uInt" (.int .u32)),
  ("lookahead", .typedef "uInt" (.int .u32)),
  ("prev_length", .typedef "uInt" (.int .u32)),
  ("max_chain_length", .typedef "uInt" (.int .u32)),
  ("max_lazy_match", .typedef "uInt" (.int .u32)),
  ("level", .int .i32),
  ("strategy", .int .i32),
  ("good_match", .typedef "uInt" (.int .u32)),
  ("nice_match", .int .i32),
  ("dyn_ltree", .array (.structTy "ct_data_s") (some 573)),
  ("dyn_dtree", .array (.structTy "ct_data_s") (some 61)),
  ("bl_tree", .array (.structTy "ct_data_s") (some 39)),
  ("l_desc", .structTy "tree_desc_s"),
  ("d_desc", .structTy "tree_desc_s"),
  ("bl_desc", .structTy "tree_desc_s"),
  ("bl_count", .array (.typedef "ush" (.int .u16)) (some 16)),
  ("heap", .array (.int .i32) (some 573)),
  ("heap_len", .int .i32),
  ("heap_max", .int .i32),
  ("depth", .array (.typedef "uch" (.int .u8)) (some 573)),
  ("sym_buf", .ptr (.typedef "uchf" (.typedef "uch" (.int .u8)))),
  ("lit_bufsize", .typedef "uInt" (.int .u32)),
  ("sym_next", .typedef "uInt" (.int .u32)),
  ("sym_end", .typedef "uInt" (.int .u32)),
  ("opt_len", .typedef "ulg" (.int .u64)),
  ("static_len", .typedef "ulg" (.int .u64)),
  ("matches", .typedef "uInt" (.int .u32)),
  ("insert", .typedef "uInt" (.int .u32)),
  ("bi_buf", .typedef "ush" (.int .u16)),
  ("bi_valid", .int .i32),
  ("bi_used", .int .i32),
  ("high_water", .typedef "ulg" (.int .u64)),
  ("slid", .int .i32)
]

def gzFileFields : List (String × CTy) := [
  ("have", .int .u32),
  ("next", .ptr (.int .u8)),
  ("pos", .typedef "z_off64_t" (.int .i64))
]

def gzStateFields : List (String × CTy) := [
  ("x", .structTy "gzFile_s"),
  ("mode", .int .i32),
  ("fd", .int .i32),
  ("path", .ptr (.int .i8)),
  ("size", .int .u32),
  ("want", .int .u32),
  ("in", .ptr (.int .u8)),
  ("out", .ptr (.int .u8)),
  ("direct", .int .i32),
  ("junk", .int .i32),
  ("how", .int .i32),
  ("again", .int .i32),
  ("start", .typedef "z_off64_t" (.int .i64)),
  ("eof", .int .i32),
  ("past", .int .i32),
  ("level", .int .i32),
  ("strategy", .int .i32),
  ("reset", .int .i32),
  ("skip", .typedef "z_off64_t" (.int .i64)),
  ("err", .int .i32),
  ("msg", .ptr (.int .i8)),
  ("strm", .typedef "z_stream" (.structTy "z_stream_s"))
]

private theorem hdr_lookup_gz_header_s : headerTagEnv.lookup "gz_header_s" = some (.structDef gzHeaderFields) := rfl
private theorem hdr_lookup_ct_data_s : headerTagEnv.lookup "ct_data_s" = some (.structDef ctDataFields) := rfl
private theorem hdr_lookup_static_tree_desc_s : headerTagEnv.lookup "static_tree_desc_s" = some (.structDef staticTreeDescFields) := rfl
private theorem hdr_lookup_tree_desc_s : headerTagEnv.lookup "tree_desc_s" = some (.structDef treeDescFields) := rfl
private theorem hdr_lookup_internal_state : headerTagEnv.lookup "internal_state" = some (.structDef internalStateFields) := rfl
private theorem hdr_lookup_code : headerTagEnv.lookup "code" = some (.structDef codeFields) := rfl
private theorem hdr_lookup_inflate_state : headerTagEnv.lookup "inflate_state" = some (.structDef inflateStateFields) := rfl
private theorem hdr_lookup_gzFile_s : headerTagEnv.lookup "gzFile_s" = some (.structDef gzFileFields) := rfl
private theorem hdr_lookup_gz_state : headerTagEnv.lookup "gz_state" = some (.structDef gzStateFields) := rfl

theorem prog_tags_lookup_gz_header_s :
    (progOfTUs Zlib.allFiles).tags.lookup "gz_header_s" = some (.structDef gzHeaderFields) :=
  prog_tags_lookup_header hdr_lookup_gz_header_s
theorem prog_tags_lookup_ct_data_s :
    (progOfTUs Zlib.allFiles).tags.lookup "ct_data_s" = some (.structDef ctDataFields) :=
  prog_tags_lookup_header hdr_lookup_ct_data_s
theorem prog_tags_lookup_static_tree_desc_s :
    (progOfTUs Zlib.allFiles).tags.lookup "static_tree_desc_s" = some (.structDef staticTreeDescFields) :=
  prog_tags_lookup_header hdr_lookup_static_tree_desc_s
theorem prog_tags_lookup_tree_desc_s :
    (progOfTUs Zlib.allFiles).tags.lookup "tree_desc_s" = some (.structDef treeDescFields) :=
  prog_tags_lookup_header hdr_lookup_tree_desc_s
theorem prog_tags_lookup_internal_state :
    (progOfTUs Zlib.allFiles).tags.lookup "internal_state" = some (.structDef internalStateFields) :=
  prog_tags_lookup_header hdr_lookup_internal_state
theorem prog_tags_lookup_code :
    (progOfTUs Zlib.allFiles).tags.lookup "code" = some (.structDef codeFields) :=
  prog_tags_lookup_header hdr_lookup_code
theorem prog_tags_lookup_codetype :
    (progOfTUs Zlib.allFiles).tags.lookup "codetype" =
      some (.enumDef [("CODES", none), ("LENS", none), ("DISTS", none)] true) :=
  prog_tags_lookup_header (by rfl)
theorem prog_tags_lookup_inflate_mode :
    (progOfTUs Zlib.allFiles).tags.lookup "inflate_mode" = headerTagEnv.lookup "inflate_mode" :=
  prog_tags_lookup_header (by rfl)
theorem prog_tags_lookup_inflate_state :
    (progOfTUs Zlib.allFiles).tags.lookup "inflate_state" = some (.structDef inflateStateFields) :=
  prog_tags_lookup_header hdr_lookup_inflate_state
theorem prog_tags_lookup_gzFile_s :
    (progOfTUs Zlib.allFiles).tags.lookup "gzFile_s" = some (.structDef gzFileFields) :=
  prog_tags_lookup_header hdr_lookup_gzFile_s
theorem prog_tags_lookup_gz_state :
    (progOfTUs Zlib.allFiles).tags.lookup "gz_state" = some (.structDef gzStateFields) :=
  prog_tags_lookup_header hdr_lookup_gz_state
theorem prog_tags_lookup_block_state :
    (progOfTUs Zlib.allFiles).tags.lookup "block_state" =
      some (.enumDef [("need_more", none), ("block_done", none),
        ("finish_started", none), ("finish_done", none)] true) := by
  rw [prog0_tags_eq, lookup_append_none (by rfl)]; rfl
theorem prog_tags_lookup_config_s :
    (progOfTUs Zlib.allFiles).tags.lookup "config_s" = some (.structDef configFields) := by
  rw [prog0_tags_eq, lookup_append_none (by rfl)]; rfl

/-! ### Enum Constant Evaluation (`enumConst?`) -/

private def scanEnumFast (nextVal : Int) (name : String) : List (String × Option Int) → Option Int
  | [] => none
  | (k, v?) :: tl =>
    let v := v?.getD nextVal
    if k == name then some v else scanEnumFast (v + 1) name tl

private def enumConstFast (tags : TypeEnv) (name : String) : Option Int :=
  match tags with
  | [] => none
  | (_, .enumDef items _) :: rest =>
    match scanEnumFast 0 name items with
    | some v => some v
    | none => enumConstFast rest name
  | _ :: rest => enumConstFast rest name

theorem enumConst_eq_fast (tags : TypeEnv) (name : String) :
    enumConst? tags name = enumConstFast tags name := by
  induction tags with
  | nil => unfold enumConst? enumConstFast; rfl
  | cons hd tl ih =>
    rcases hd with ⟨_, defn⟩
    cases defn with
    | structDef _ => unfold enumConst? enumConstFast; exact ih
    | unionDef _ => unfold enumConst? enumConstFast; exact ih
    | enumDef items _ =>
      unfold enumConst? enumConstFast
      have hscan : ∀ (nv : Int) (xs : List (String × Option Int)),
          enumConst?.scan tl name nv xs =
            match scanEnumFast nv name xs with
            | some v => some v
            | none => enumConst? tl name := by
        intro nv xs
        induction xs generalizing nv with
        | nil => unfold enumConst?.scan scanEnumFast; rfl
        | cons it rest ihs =>
          rcases it with ⟨k, v?⟩
          unfold enumConst?.scan scanEnumFast
          dsimp only
          split
          · rfl
          · exact ihs _
      rw [hscan, ih]

def allEnumConstNames : List String := [
  "CODES", "LENS", "DISTS",
  "HEAD", "FLAGS", "TIME", "OS", "EXLEN", "EXTRA", "NAME", "COMMENT", "HCRC",
  "DICTID", "DICT", "TYPE", "TYPEDO", "STORED", "COPY_", "COPY", "TABLE",
  "LENLENS", "CODELENS", "LEN_", "LEN", "LENEXT", "DIST", "DISTEXT", "MATCH",
  "LIT", "CHECK", "LENGTH", "DONE", "BAD", "MEM", "SYNC",
  "need_more", "block_done", "finish_started", "finish_done"
]

private def collectEnumItemNames : TypeEnv → List String
  | [] => []
  | (_, .enumDef items _) :: rest => items.map (·.1) ++ collectEnumItemNames rest
  | _ :: rest => collectEnumItemNames rest

private theorem scanEnumFast_none_of_not_mem (nv : Int) (name : String)
    (items : List (String × Option Int)) (h : name ∉ items.map (·.1)) :
    scanEnumFast nv name items = none := by
  induction items generalizing nv with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v?⟩
    simp only [List.map_cons, List.mem_cons, not_or] at h
    unfold scanEnumFast
    rw [show (k == name) = false from beq_false_of_ne (Ne.symm h.1)]
    exact ih _ h.2

private theorem enumConstFast_none_of_not_mem (tags : TypeEnv) (name : String)
    (h : name ∉ collectEnumItemNames tags) :
    enumConstFast tags name = none := by
  induction tags with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨_, defn⟩
    cases defn with
    | structDef _ => exact ih h
    | unionDef _ => exact ih h
    | enumDef items _ =>
      simp only [collectEnumItemNames, List.mem_append, not_or] at h
      unfold enumConstFast
      rw [scanEnumFast_none_of_not_mem 0 name items h.1]
      exact ih h.2

private theorem prog0_enumItemNames_eq :
    collectEnumItemNames (headerTagEnv ++ deflateTagEnv) = allEnumConstNames := rfl

theorem enumConst_none_of_not_mem {name : String} (h : name ∉ allEnumConstNames) :
    enumConst? (progOfTUs Zlib.allFiles).tags name = none := by
  rw [prog0_tags_eq, enumConst_eq_fast]
  apply enumConstFast_none_of_not_mem
  rw [prog0_enumItemNames_eq]
  exact h

private theorem prog0_enumConst_rw {name : String} {v : Int}
    (h : enumConstFast (headerTagEnv ++ deflateTagEnv) name = some v) :
    enumConst? (progOfTUs Zlib.allFiles).tags name = some v := by
  rw [prog0_tags_eq, enumConst_eq_fast]; exact h

theorem enumConst_CODES : enumConst? (progOfTUs Zlib.allFiles).tags "CODES" = some 0 := prog0_enumConst_rw rfl
theorem enumConst_LENS : enumConst? (progOfTUs Zlib.allFiles).tags "LENS" = some 1 := prog0_enumConst_rw rfl
theorem enumConst_DISTS : enumConst? (progOfTUs Zlib.allFiles).tags "DISTS" = some 2 := prog0_enumConst_rw rfl

theorem enumConst_HEAD : enumConst? (progOfTUs Zlib.allFiles).tags "HEAD" = some 16180 := prog0_enumConst_rw rfl
theorem enumConst_FLAGS : enumConst? (progOfTUs Zlib.allFiles).tags "FLAGS" = some 16181 := prog0_enumConst_rw rfl
theorem enumConst_TIME : enumConst? (progOfTUs Zlib.allFiles).tags "TIME" = some 16182 := prog0_enumConst_rw rfl
theorem enumConst_OS : enumConst? (progOfTUs Zlib.allFiles).tags "OS" = some 16183 := prog0_enumConst_rw rfl
theorem enumConst_EXLEN : enumConst? (progOfTUs Zlib.allFiles).tags "EXLEN" = some 16184 := prog0_enumConst_rw rfl
theorem enumConst_EXTRA : enumConst? (progOfTUs Zlib.allFiles).tags "EXTRA" = some 16185 := prog0_enumConst_rw rfl
theorem enumConst_NAME : enumConst? (progOfTUs Zlib.allFiles).tags "NAME" = some 16186 := prog0_enumConst_rw rfl
theorem enumConst_COMMENT : enumConst? (progOfTUs Zlib.allFiles).tags "COMMENT" = some 16187 := prog0_enumConst_rw rfl
theorem enumConst_HCRC : enumConst? (progOfTUs Zlib.allFiles).tags "HCRC" = some 16188 := prog0_enumConst_rw rfl
theorem enumConst_DICTID : enumConst? (progOfTUs Zlib.allFiles).tags "DICTID" = some 16189 := prog0_enumConst_rw rfl
theorem enumConst_DICT : enumConst? (progOfTUs Zlib.allFiles).tags "DICT" = some 16190 := prog0_enumConst_rw rfl
theorem enumConst_TYPE : enumConst? (progOfTUs Zlib.allFiles).tags "TYPE" = some 16191 := prog0_enumConst_rw rfl
theorem enumConst_TYPEDO : enumConst? (progOfTUs Zlib.allFiles).tags "TYPEDO" = some 16192 := prog0_enumConst_rw rfl
theorem enumConst_STORED : enumConst? (progOfTUs Zlib.allFiles).tags "STORED" = some 16193 := prog0_enumConst_rw rfl
theorem enumConst_COPY_ : enumConst? (progOfTUs Zlib.allFiles).tags "COPY_" = some 16194 := prog0_enumConst_rw rfl
theorem enumConst_COPY : enumConst? (progOfTUs Zlib.allFiles).tags "COPY" = some 16195 := prog0_enumConst_rw rfl
theorem enumConst_TABLE : enumConst? (progOfTUs Zlib.allFiles).tags "TABLE" = some 16196 := prog0_enumConst_rw rfl
theorem enumConst_LENLENS : enumConst? (progOfTUs Zlib.allFiles).tags "LENLENS" = some 16197 := prog0_enumConst_rw rfl
theorem enumConst_CODELENS : enumConst? (progOfTUs Zlib.allFiles).tags "CODELENS" = some 16198 := prog0_enumConst_rw rfl
theorem enumConst_LEN_ : enumConst? (progOfTUs Zlib.allFiles).tags "LEN_" = some 16199 := prog0_enumConst_rw rfl
theorem enumConst_LEN : enumConst? (progOfTUs Zlib.allFiles).tags "LEN" = some 16200 := prog0_enumConst_rw rfl
theorem enumConst_LENEXT : enumConst? (progOfTUs Zlib.allFiles).tags "LENEXT" = some 16201 := prog0_enumConst_rw rfl
theorem enumConst_DIST : enumConst? (progOfTUs Zlib.allFiles).tags "DIST" = some 16202 := prog0_enumConst_rw rfl
theorem enumConst_DISTEXT : enumConst? (progOfTUs Zlib.allFiles).tags "DISTEXT" = some 16203 := prog0_enumConst_rw rfl
theorem enumConst_MATCH : enumConst? (progOfTUs Zlib.allFiles).tags "MATCH" = some 16204 := prog0_enumConst_rw rfl
theorem enumConst_LIT : enumConst? (progOfTUs Zlib.allFiles).tags "LIT" = some 16205 := prog0_enumConst_rw rfl
theorem enumConst_CHECK : enumConst? (progOfTUs Zlib.allFiles).tags "CHECK" = some 16206 := prog0_enumConst_rw rfl
theorem enumConst_LENGTH : enumConst? (progOfTUs Zlib.allFiles).tags "LENGTH" = some 16207 := prog0_enumConst_rw rfl
theorem enumConst_DONE : enumConst? (progOfTUs Zlib.allFiles).tags "DONE" = some 16208 := prog0_enumConst_rw rfl
theorem enumConst_BAD : enumConst? (progOfTUs Zlib.allFiles).tags "BAD" = some 16209 := prog0_enumConst_rw rfl
theorem enumConst_MEM : enumConst? (progOfTUs Zlib.allFiles).tags "MEM" = some 16210 := prog0_enumConst_rw rfl
theorem enumConst_SYNC : enumConst? (progOfTUs Zlib.allFiles).tags "SYNC" = some 16211 := prog0_enumConst_rw rfl

theorem enumConst_need_more : enumConst? (progOfTUs Zlib.allFiles).tags "need_more" = some 0 := prog0_enumConst_rw rfl
theorem enumConst_block_done : enumConst? (progOfTUs Zlib.allFiles).tags "block_done" = some 1 := prog0_enumConst_rw rfl
theorem enumConst_finish_started : enumConst? (progOfTUs Zlib.allFiles).tags "finish_started" = some 2 := prog0_enumConst_rw rfl
theorem enumConst_finish_done : enumConst? (progOfTUs Zlib.allFiles).tags "finish_done" = some 3 := prog0_enumConst_rw rfl

/-! ### Struct & Anonymous Union `alignofTy` and `sizeofTy` Lemmas -/

private theorem alignofFields_cons (tags : TypeEnv) (fuel : Nat) (nm : String) (fty : CTy)
    (rest : List (String × CTy)) (acc : Nat) :
    alignofFields tags fuel ((nm, fty) :: rest) acc =
      alignofFields tags fuel rest (max acc (alignofAux tags fuel fty)) := by
  cases fuel <;> simp [alignofFields]

private theorem alignofFields_nil (tags : TypeEnv) (fuel : Nat) (acc : Nat) :
    alignofFields tags fuel [] acc = acc := by
  cases fuel <;> simp [alignofFields]

private theorem alignofAux_anonStruct (tags : TypeEnv) (fuel : Nat) (flds : List (String × CTy)) :
    alignofAux tags fuel (.anonStruct flds) = alignofFields tags fuel flds 1 := by
  cases fuel <;> simp [alignofAux]

private theorem alignofAux_anonUnion (tags : TypeEnv) (fuel : Nat) (flds : List (String × CTy)) :
    alignofAux tags fuel (.anonUnion flds) = alignofFields tags fuel flds 1 := by
  cases fuel <;> simp [alignofAux]

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

private theorem sizeofUnionFields_cons (tags : TypeEnv) (fuel sz al : Nat) (nm : String)
    (fty : CTy) (rest : List (String × CTy)) :
    sizeofUnionFields tags fuel sz al ((nm, fty) :: rest) =
      sizeofUnionFields tags fuel (max sz (sizeofAux tags fuel fty))
        (max al (alignofAux tags fuel fty)) rest := by
  cases fuel <;> simp [sizeofUnionFields]

private theorem sizeofUnionFields_nil (tags : TypeEnv) (fuel sz al : Nat) :
    sizeofUnionFields tags fuel sz al [] = alignUp sz al := by
  cases fuel <;> simp [sizeofUnionFields]

private theorem sizeofAux_anonStruct (tags : TypeEnv) (fuel : Nat) (flds : List (String × CTy)) :
    sizeofAux tags fuel (.anonStruct flds) = sizeofStructFields tags fuel 0 1 flds := by
  cases fuel <;> simp [sizeofAux]

private theorem sizeofAux_anonUnion (tags : TypeEnv) (fuel : Nat) (flds : List (String × CTy)) :
    sizeofAux tags fuel (.anonUnion flds) = sizeofUnionFields tags fuel 0 1 flds := by
  cases fuel <;> simp [sizeofAux]

@[simp] theorem alignofTy_codeCTy (tags : TypeEnv) : alignofTy tags codeCTy = 2 := by
  unfold alignofTy
  simp only [codeCTy, alignofAux_typedef, alignofAux_anonStruct, codeFields,
    alignofFields_cons, alignofFields_nil, alignofAux_int, IntKind.align]
  rfl

@[simp] theorem sizeofTy_codeCTy (tags : TypeEnv) : sizeofTy tags codeCTy = 4 := by
  unfold sizeofTy
  simp only [codeCTy, sizeofAux_typedef, sizeofAux_anonStruct, codeFields,
    sizeofStructFields_cons, sizeofStructFields_nil, alignofAux_int, sizeofAux_int,
    IntKind.align, IntKind.bytes, alignUp]
  rfl

@[simp] theorem alignofTy_codeAnon (tags : TypeEnv) :
    alignofTy tags (.anonStruct codeFields) = 2 := by
  simpa [codeCTy] using alignofTy_codeCTy tags

@[simp] theorem sizeofTy_codeAnon (tags : TypeEnv) :
    sizeofTy tags (.anonStruct codeFields) = 4 := by
  simpa [codeCTy] using sizeofTy_codeCTy tags

@[simp] theorem alignofTy_ctDataFcUnion (tags : TypeEnv) :
    alignofTy tags ctDataFcUnionTy = 2 := by
  unfold alignofTy
  simp only [ctDataFcUnionTy, alignofAux_anonUnion, alignofFields_cons, alignofFields_nil,
    alignofAux_typedef, alignofAux_int, IntKind.align]
  rfl

@[simp] theorem sizeofTy_ctDataFcUnion (tags : TypeEnv) :
    sizeofTy tags ctDataFcUnionTy = 2 := by
  unfold sizeofTy
  simp only [ctDataFcUnionTy, sizeofAux_anonUnion, sizeofUnionFields_cons, sizeofUnionFields_nil,
    alignofAux_typedef, alignofAux_int, sizeofAux_typedef, sizeofAux_int,
    IntKind.align, IntKind.bytes, alignUp]
  rfl

@[simp] theorem alignofTy_ctDataDlUnion (tags : TypeEnv) :
    alignofTy tags ctDataDlUnionTy = 2 := by
  unfold alignofTy
  simp only [ctDataDlUnionTy, alignofAux_anonUnion, alignofFields_cons, alignofFields_nil,
    alignofAux_typedef, alignofAux_int, IntKind.align]
  rfl

@[simp] theorem sizeofTy_ctDataDlUnion (tags : TypeEnv) :
    sizeofTy tags ctDataDlUnionTy = 2 := by
  unfold sizeofTy
  simp only [ctDataDlUnionTy, sizeofAux_anonUnion, sizeofUnionFields_cons, sizeofUnionFields_nil,
    alignofAux_typedef, alignofAux_int, sizeofAux_typedef, sizeofAux_int,
    IntKind.align, IntKind.bytes, alignUp]
  rfl

private theorem alignofAux_ge_one_code (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "code" = some (.structDef codeFields)) :
    alignofAux tags (n + 1) (.structTy "code") = 2 := by
  rw [alignofAux, hlook]
  simp only [codeFields, alignofFields_cons, alignofFields_nil, alignofAux_int, IntKind.align]
  rfl

private theorem sizeofAux_ge_one_code (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "code" = some (.structDef codeFields)) :
    sizeofAux tags (n + 1) (.structTy "code") = 4 := by
  rw [sizeofAux, hlook]
  simp only [codeFields, sizeofStructFields_cons, sizeofStructFields_nil,
    alignofAux_int, sizeofAux_int, IntKind.align, IntKind.bytes, alignUp]
  rfl

theorem alignofTy_code :
    alignofTy (progOfTUs Zlib.allFiles).tags (.structTy "code") = 2 := by
  unfold alignofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact alignofAux_ge_one_code _ _ prog_tags_lookup_code

theorem sizeofTy_code :
    sizeofTy (progOfTUs Zlib.allFiles).tags (.structTy "code") = 4 := by
  unfold sizeofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact sizeofAux_ge_one_code _ _ prog_tags_lookup_code

private theorem alignofAux_ge_one_ct_data_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "ct_data_s" = some (.structDef ctDataFields)) :
    alignofAux tags (n + 1) (.structTy "ct_data_s") = 2 := by
  rw [alignofAux, hlook]
  simp only [ctDataFields, ctDataFcUnionTy, ctDataDlUnionTy, alignofFields_cons, alignofFields_nil,
    alignofAux_anonUnion, alignofAux_typedef, alignofAux_int, IntKind.align]
  rfl

private theorem sizeofAux_ge_one_ct_data_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "ct_data_s" = some (.structDef ctDataFields)) :
    sizeofAux tags (n + 1) (.structTy "ct_data_s") = 4 := by
  rw [sizeofAux, hlook]
  simp only [ctDataFields, ctDataFcUnionTy, ctDataDlUnionTy,
    sizeofStructFields_cons, sizeofStructFields_nil, sizeofAux_anonUnion, alignofAux_anonUnion,
    sizeofUnionFields_cons, sizeofUnionFields_nil, alignofFields_cons, alignofFields_nil,
    alignofAux_typedef, alignofAux_int, sizeofAux_typedef, sizeofAux_int,
    IntKind.align, IntKind.bytes, alignUp]
  rfl

theorem alignofTy_ct_data_s :
    alignofTy (progOfTUs Zlib.allFiles).tags (.structTy "ct_data_s") = 2 := by
  unfold alignofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact alignofAux_ge_one_ct_data_s _ _ prog_tags_lookup_ct_data_s

theorem sizeofTy_ct_data_s :
    sizeofTy (progOfTUs Zlib.allFiles).tags (.structTy "ct_data_s") = 4 := by
  unfold sizeofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact sizeofAux_ge_one_ct_data_s _ _ prog_tags_lookup_ct_data_s

private theorem alignofAux_ge_one_static_tree_desc_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "static_tree_desc_s" = some (.structDef staticTreeDescFields)) :
    alignofAux tags (n + 1) (.structTy "static_tree_desc_s") = 8 := by
  rw [alignofAux, hlook]
  simp only [staticTreeDescFields, alignofFields_cons, alignofFields_nil,
    alignofAux_ptr, alignofAux_int, IntKind.align]
  rfl

private theorem sizeofAux_ge_one_static_tree_desc_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "static_tree_desc_s" = some (.structDef staticTreeDescFields)) :
    sizeofAux tags (n + 1) (.structTy "static_tree_desc_s") = 32 := by
  rw [sizeofAux, hlook]
  simp only [staticTreeDescFields, sizeofStructFields_cons, sizeofStructFields_nil,
    alignofAux_ptr, alignofAux_int, sizeofAux_ptr, sizeofAux_int,
    IntKind.align, IntKind.bytes, alignUp]
  rfl

theorem alignofTy_static_tree_desc_s :
    alignofTy (progOfTUs Zlib.allFiles).tags (.structTy "static_tree_desc_s") = 8 := by
  unfold alignofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact alignofAux_ge_one_static_tree_desc_s _ _ prog_tags_lookup_static_tree_desc_s

theorem sizeofTy_static_tree_desc_s :
    sizeofTy (progOfTUs Zlib.allFiles).tags (.structTy "static_tree_desc_s") = 32 := by
  unfold sizeofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact sizeofAux_ge_one_static_tree_desc_s _ _ prog_tags_lookup_static_tree_desc_s

private theorem alignofAux_ge_one_tree_desc_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "tree_desc_s" = some (.structDef treeDescFields)) :
    alignofAux tags (n + 1) (.structTy "tree_desc_s") = 8 := by
  rw [alignofAux, hlook]
  simp only [treeDescFields, alignofFields_cons, alignofFields_nil,
    alignofAux_ptr, alignofAux_int, IntKind.align]
  rfl

private theorem sizeofAux_ge_one_tree_desc_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "tree_desc_s" = some (.structDef treeDescFields)) :
    sizeofAux tags (n + 1) (.structTy "tree_desc_s") = 24 := by
  rw [sizeofAux, hlook]
  simp only [treeDescFields, sizeofStructFields_cons, sizeofStructFields_nil,
    alignofAux_ptr, alignofAux_int, sizeofAux_ptr, sizeofAux_int,
    IntKind.align, IntKind.bytes, alignUp]
  rfl

theorem alignofTy_tree_desc_s :
    alignofTy (progOfTUs Zlib.allFiles).tags (.structTy "tree_desc_s") = 8 := by
  unfold alignofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact alignofAux_ge_one_tree_desc_s _ _ prog_tags_lookup_tree_desc_s

theorem sizeofTy_tree_desc_s :
    sizeofTy (progOfTUs Zlib.allFiles).tags (.structTy "tree_desc_s") = 24 := by
  unfold sizeofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact sizeofAux_ge_one_tree_desc_s _ _ prog_tags_lookup_tree_desc_s

private theorem alignofAux_ge_one_config_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "config_s" = some (.structDef configFields)) :
    alignofAux tags (n + 1) (.structTy "config_s") = 8 := by
  rw [alignofAux, hlook]
  simp only [configFields, alignofFields_cons, alignofFields_nil,
    alignofAux_typedef, alignofAux_int, alignofAux_fnPtr, IntKind.align]
  rfl

private theorem sizeofAux_ge_one_config_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "config_s" = some (.structDef configFields)) :
    sizeofAux tags (n + 1) (.structTy "config_s") = 16 := by
  rw [sizeofAux, hlook]
  simp only [configFields, sizeofStructFields_cons, sizeofStructFields_nil,
    alignofAux_typedef, alignofAux_int, alignofAux_fnPtr,
    sizeofAux_typedef, sizeofAux_int, sizeofAux_fnPtr,
    IntKind.align, IntKind.bytes, alignUp]
  rfl

theorem alignofTy_config_s :
    alignofTy (progOfTUs Zlib.allFiles).tags (.structTy "config_s") = 8 := by
  unfold alignofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact alignofAux_ge_one_config_s _ _ prog_tags_lookup_config_s

theorem sizeofTy_config_s :
    sizeofTy (progOfTUs Zlib.allFiles).tags (.structTy "config_s") = 16 := by
  unfold sizeofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact sizeofAux_ge_one_config_s _ _ prog_tags_lookup_config_s

private theorem alignofAux_ge_one_gzFile_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "gzFile_s" = some (.structDef gzFileFields)) :
    alignofAux tags (n + 1) (.structTy "gzFile_s") = 8 := by
  rw [alignofAux, hlook]
  simp only [gzFileFields, alignofFields_cons, alignofFields_nil,
    alignofAux_int, alignofAux_ptr, alignofAux_typedef, IntKind.align]
  rfl

private theorem sizeofAux_ge_one_gzFile_s (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "gzFile_s" = some (.structDef gzFileFields)) :
    sizeofAux tags (n + 1) (.structTy "gzFile_s") = 24 := by
  rw [sizeofAux, hlook]
  simp only [gzFileFields, sizeofStructFields_cons, sizeofStructFields_nil,
    alignofAux_int, alignofAux_ptr, alignofAux_typedef,
    sizeofAux_int, sizeofAux_ptr, sizeofAux_typedef,
    IntKind.align, IntKind.bytes, alignUp]
  rfl

theorem alignofTy_gzFile_s :
    alignofTy (progOfTUs Zlib.allFiles).tags (.structTy "gzFile_s") = 8 := by
  unfold alignofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact alignofAux_ge_one_gzFile_s _ _ prog_tags_lookup_gzFile_s

theorem sizeofTy_gzFile_s :
    sizeofTy (progOfTUs Zlib.allFiles).tags (.structTy "gzFile_s") = 24 := by
  unfold sizeofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact sizeofAux_ge_one_gzFile_s _ _ prog_tags_lookup_gzFile_s

private theorem alignofAux_ge_one_inflate_state (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "inflate_state" = some (.structDef inflateStateFields)) :
    alignofAux tags (n + 1) (.structTy "inflate_state") = 8 := by
  rw [alignofAux, hlook]
  simp only [inflateStateFields, codeCTy, codeFields,
    alignofFields_cons, alignofFields_nil,
    alignofAux_typedef, alignofAux_ptr, alignofAux_int, alignofAux_array, alignofAux_anonStruct,
    IntKind.align]
  rfl

section SizeofHelper

private theorem alignofAux_codeAnon (tags : TypeEnv) (fuel : Nat) :
    alignofAux tags fuel (.anonStruct codeFields) = 2 := by
  cases fuel <;>
    simp [alignofAux, codeFields, alignofFields_cons, alignofFields_nil,
      alignofAux_int, IntKind.align] <;> rfl

private theorem sizeofAux_codeAnon (tags : TypeEnv) (fuel : Nat) :
    sizeofAux tags fuel (.anonStruct codeFields) = 4 := by
  cases fuel <;>
    simp [sizeofAux, codeFields, sizeofStructFields_cons, sizeofStructFields_nil,
      alignofAux_int, sizeofAux_int, IntKind.align, IntKind.bytes, alignUp] <;> rfl

open Lean Meta Elab Tactic in
local elab "norm_sizeof_args" : tactic => withMainContext do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | throwError "expected eq"
  let args := lhs.getAppArgs
  if args.size < 4 then throwError "expected >=4 args"
  for idx in [2, 3] do
    let e := args[idx]!
    let v ← withTransparency .all (whnf e)
    let nLit ← match v.rawNatLit?.orElse (fun _ => v.nat?) with
      | some n => pure (mkNatLit n)
      | none => throwError "arg {idx} did not reduce to nat in whnf: {v}"
    let hEq ← mkEq e nLit
    let rflPrf ← mkEqRefl nLit
    let goal ← getMainGoal
    let g1 ← goal.assert `h_sz hEq rflPrf
    let (_, g2) ← g1.intro1P
    replaceMainGoal [g2]
    evalTactic (← `(tactic| rw [$(mkIdent `h_sz):ident]; clear $(mkIdent `h_sz):ident))

open Lean Meta Elab Tactic in
local elab "solve_sizeof_fields" extras:ident* : tactic => do
  let rec loop : Nat → TacticM Unit
    | 0 => throwError "solve_sizeof_fields fuel exhausted"
    | fuel + 1 => withMainContext do
      let tgt := (← getMainTarget).consumeMData
      let some (_, lhs, _) := tgt.eq? | throwError "expected eq in solve_sizeof_fields: {tgt}"
      let args := lhs.getAppArgs
      if args.size < 5 then throwError "unexpected args: {args.size}"
      let listExpr ← whnf args[4]!
      if listExpr.isAppOfArity ``List.nil 1 then
        evalTactic (← `(tactic| rw [sizeofStructFields_nil]; rfl))
      else
        evalTactic (← `(tactic| rw [sizeofStructFields_cons]))
        for ex in extras do
          evalTactic (← `(tactic| try rw [$ex:ident]))
        evalTactic (← `(tactic|
          try simp only [alignofAux_typedef, alignofAux_ptr, alignofAux_int, alignofAux_array,
            alignofAux_codeAnon, alignofAux_fnPtr,
            sizeofAux_typedef, sizeofAux_ptr, sizeofAux_int, sizeofAux_array_some,
            sizeofAux_codeAnon, sizeofAux_fnPtr,
            IntKind.align, IntKind.bytes, alignUp]))
        for ex in extras do
          evalTactic (← `(tactic| try rw [$ex:ident]))
        evalTactic (← `(tactic| try simp only [IntKind.align, IntKind.bytes, alignUp]))
        evalTactic (← `(tactic| try norm_sizeof_args))
        loop fuel
  loop 100

private theorem sizeofAux_ge_one_inflate_state (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "inflate_state" = some (.structDef inflateStateFields)) :
    sizeofAux tags (n + 1) (.structTy "inflate_state") = 8328 := by
  rw [sizeofAux, hlook]
  dsimp only [inflateStateFields, codeCTy]
  solve_sizeof_fields

theorem alignofTy_inflate_state :
    alignofTy (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") = 8 := by
  unfold alignofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact alignofAux_ge_one_inflate_state _ _ prog_tags_lookup_inflate_state

theorem sizeofTy_inflate_state :
    sizeofTy (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") = 8328 := by
  unfold sizeofTy
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' prog_tags_len_ge_14
  rw [hk]; exact sizeofAux_ge_one_inflate_state _ _ prog_tags_lookup_inflate_state

private theorem alignofAux_ge_one_internal_state (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "internal_state" = some (.structDef internalStateFields))
    (hct : tags.lookup "ct_data_s" = some (.structDef ctDataFields))
    (htd : tags.lookup "tree_desc_s" = some (.structDef treeDescFields)) :
    alignofAux tags (n + 2) (.structTy "internal_state") = 8 := by
  rw [alignofAux, hlook]
  have hct_a : alignofAux tags (n + 1) (.structTy "ct_data_s") = 2 :=
    alignofAux_ge_one_ct_data_s tags n hct
  have htd_a : alignofAux tags (n + 1) (.structTy "tree_desc_s") = 8 :=
    alignofAux_ge_one_tree_desc_s tags n htd
  simp only [internalStateFields, alignofFields_cons, alignofFields_nil,
    alignofAux_typedef, alignofAux_ptr, alignofAux_int, alignofAux_array,
    hct_a, htd_a, IntKind.align]
  rfl

private theorem sizeofAux_ge_one_internal_state (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "internal_state" = some (.structDef internalStateFields))
    (hct : tags.lookup "ct_data_s" = some (.structDef ctDataFields))
    (htd : tags.lookup "tree_desc_s" = some (.structDef treeDescFields)) :
    sizeofAux tags (n + 2) (.structTy "internal_state") = 5968 := by
  rw [sizeofAux, hlook]
  have hct_a : alignofAux tags (n + 1) (.structTy "ct_data_s") = 2 :=
    alignofAux_ge_one_ct_data_s tags n hct
  have hct_s : sizeofAux tags (n + 1) (.structTy "ct_data_s") = 4 :=
    sizeofAux_ge_one_ct_data_s tags n hct
  have htd_a : alignofAux tags (n + 1) (.structTy "tree_desc_s") = 8 :=
    alignofAux_ge_one_tree_desc_s tags n htd
  have htd_s : sizeofAux tags (n + 1) (.structTy "tree_desc_s") = 24 :=
    sizeofAux_ge_one_tree_desc_s tags n htd
  dsimp only [internalStateFields]
  solve_sizeof_fields hct_a hct_s htd_a htd_s

end SizeofHelper

theorem alignofTy_internal_state :
    alignofTy (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") = 8 := by
  unfold alignofTy
  have hge : 2 ≤ (progOfTUs Zlib.allFiles).tags.length + 1 := by
    rw [prog_tags_len]; decide
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hge
  rw [hk]
  exact alignofAux_ge_one_internal_state _ _ prog_tags_lookup_internal_state
    prog_tags_lookup_ct_data_s prog_tags_lookup_tree_desc_s

theorem sizeofTy_internal_state :
    sizeofTy (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") = 5968 := by
  unfold sizeofTy
  have hge : 2 ≤ (progOfTUs Zlib.allFiles).tags.length + 1 := by
    rw [prog_tags_len]; decide
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hge
  rw [hk]
  exact sizeofAux_ge_one_internal_state _ _ prog_tags_lookup_internal_state
    prog_tags_lookup_ct_data_s prog_tags_lookup_tree_desc_s

private theorem alignofAux_ge_one_gz_state (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "gz_state" = some (.structDef gzStateFields))
    (hgzf : tags.lookup "gzFile_s" = some (.structDef gzFileFields))
    (hzs : tags.lookup "z_stream_s" = headerTagEnv.lookup "z_stream_s") :
    alignofAux tags (n + 2) (.structTy "gz_state") = 8 := by
  rw [alignofAux, hlook]
  have hgzf_a : alignofAux tags (n + 1) (.structTy "gzFile_s") = 8 :=
    alignofAux_ge_one_gzFile_s tags n hgzf
  have hzs_a : alignofAux tags (n + 1) (.structTy "z_stream_s") = 8 := by
    rw [alignofAux, hzs]
    have hdef : headerTagEnv.lookup "z_stream_s" = some (.structDef [
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
      ]) := rfl
    rw [hdef]
    simp only [alignofFields_cons, alignofFields_nil, alignofAux_ptr, alignofAux_typedef,
      alignofAux_int, alignofAux_fnPtr, IntKind.align]
    rfl
  simp only [gzStateFields, alignofFields_cons, alignofFields_nil,
    alignofAux_int, alignofAux_ptr, alignofAux_typedef, hgzf_a, hzs_a, IntKind.align]
  rfl

private theorem sizeofAux_ge_one_gz_state (tags : TypeEnv) (n : Nat)
    (hlook : tags.lookup "gz_state" = some (.structDef gzStateFields))
    (hgzf : tags.lookup "gzFile_s" = some (.structDef gzFileFields))
    (hzs : tags.lookup "z_stream_s" = headerTagEnv.lookup "z_stream_s") :
    sizeofAux tags (n + 2) (.structTy "gz_state") = 248 := by
  rw [sizeofAux, hlook]
  have hgzf_a : alignofAux tags (n + 1) (.structTy "gzFile_s") = 8 :=
    alignofAux_ge_one_gzFile_s tags n hgzf
  have hgzf_s : sizeofAux tags (n + 1) (.structTy "gzFile_s") = 24 :=
    sizeofAux_ge_one_gzFile_s tags n hgzf
  have hzs_a : alignofAux tags (n + 1) (.structTy "z_stream_s") = 8 := by
    rw [alignofAux, hzs]
    have hdef : headerTagEnv.lookup "z_stream_s" = some (.structDef [
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
      ]) := rfl
    rw [hdef]
    simp only [alignofFields_cons, alignofFields_nil, alignofAux_ptr, alignofAux_typedef,
      alignofAux_int, alignofAux_fnPtr, IntKind.align]
    rfl
  have hzs_s : sizeofAux tags (n + 1) (.structTy "z_stream_s") = 112 := by
    rw [sizeofAux, hzs]
    have hdef : headerTagEnv.lookup "z_stream_s" = some (.structDef [
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
      ]) := rfl
    rw [hdef]
    simp only [sizeofStructFields_cons, sizeofStructFields_nil, alignofAux_ptr, alignofAux_typedef,
      alignofAux_int, alignofAux_fnPtr, sizeofAux_ptr, sizeofAux_typedef, sizeofAux_int,
      sizeofAux_fnPtr, IntKind.align, IntKind.bytes, alignUp]
    rfl
  simp only [gzStateFields, sizeofStructFields_cons, sizeofStructFields_nil,
    alignofAux_int, alignofAux_ptr, alignofAux_typedef,
    sizeofAux_int, sizeofAux_ptr, sizeofAux_typedef,
    hgzf_a, hgzf_s, hzs_a, hzs_s, IntKind.align, IntKind.bytes, alignUp]
  rfl

theorem alignofTy_gz_state :
    alignofTy (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") = 8 := by
  unfold alignofTy
  have hge : 2 ≤ (progOfTUs Zlib.allFiles).tags.length + 1 := by
    rw [prog_tags_len]; decide
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hge
  rw [hk]
  exact alignofAux_ge_one_gz_state _ _ prog_tags_lookup_gz_state
    prog_tags_lookup_gzFile_s (prog_tags_lookup_header (by rfl))

theorem sizeofTy_gz_state :
    sizeofTy (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") = 248 := by
  unfold sizeofTy
  have hge : 2 ≤ (progOfTUs Zlib.allFiles).tags.length + 1 := by
    rw [prog_tags_len]; decide
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hge
  rw [hk]
  exact sizeofAux_ge_one_gz_state _ _ prog_tags_lookup_gz_state
    prog_tags_lookup_gzFile_s (prog_tags_lookup_header (by rfl))

end TagAndLayoutHelpers

/-! ### `fieldLayout?` Theorems for All ABI Structs & Unions -/

section FieldLayoutSection

open Lean Meta Elab Tactic in
local elab "unfold_head_lhs" : tactic => withMainContext do
  let tgt ← getMainTarget
  let some (_, lhs, rhs) := tgt.eq? | throwError "expected eq"
  let some lhs' ← unfoldDefinition? lhs | throwError "cannot unfold head of {lhs}"
  replaceMainGoal [← (← getMainGoal).change (← mkEq lhs' rhs)]

open Lean Meta Elab Tactic in
local elab "norm_findStructField_off" : tactic => withMainContext do
  let tgt ← getMainTarget
  let some (_, lhs, _) := tgt.eq? | throwError "expected eq"
  let args := lhs.getAppArgs
  if args.size < 2 then throwError "expected >=2 args"
  let offExpr := args[1]!
  let offVal ← withTransparency .all (whnf offExpr)
  let offNat ← match offVal.rawNatLit?.orElse (fun _ => offVal.nat?) with
    | some n => pure (mkNatLit n)
    | none => throwError "offExpr did not reduce to nat: {offVal}"
  let hEq ← mkEq offExpr offNat
  let rflPrf ← mkEqRefl offNat
  let goal ← getMainGoal
  let g1 ← goal.assert `h_off hEq rflPrf
  let (_, g2) ← g1.intro1P
  replaceMainGoal [g2]
  evalTactic (← `(tactic| rw [$(mkIdent `h_off):ident]; clear $(mkIdent `h_off):ident))

open Lean Meta Elab Tactic in
local elab "solve_struct_fields" fld:ident : tactic => do
  let rec loop : Nat → TacticM Unit
    | 0 => throwError "solve_struct_fields fuel exhausted"
    | fuel + 1 => withMainContext do
      evalTactic (← `(tactic| unfold_head_lhs))
      let tgt ← getMainTarget
      let some (_, _, rhs) := tgt.eq? | throwError "expected eq"
      if rhs.isAppOfArity ``Option.none 1 then
        evalTactic (← `(tactic| rfl))
      else if rhs.isAppOfArity ``ite 5 then
        let cond := rhs.getAppArgs[1]!
        let some (_, _, fnameExpr) := cond.eq? | throwError "expected eq cond: {cond}"
        let some fname := match fnameExpr with | .lit (.strVal s) => some s | _ => none
          | throwError "expected string literal: {fnameExpr}"
        let fnameStx := Syntax.mkStrLit fname
        let hfld := mkIdent (← MonadQuotation.addMacroScope `hfld)
        evalTactic (← `(tactic| by_cases $hfld : $fld = $fnameStx))
        let goals ← getGoals
        let [gPos, gNeg] := goals | throwError "expected 2 goals from by_cases"
        setGoals [gPos]
        evalTactic (← `(tactic|
          subst $hfld;
          rw [show ($fnameStx == $fnameStx) = true from rfl, ite_eq_left rfl, ite_eq_left rfl];
          simp only [alignofTy_int, alignofTy_ptr, alignofTy_typedef, alignofTy_array, alignofTy_fnPtr,
            alignofTy_const, alignofTy_codeCTy, alignofTy_codeAnon,
            alignofTy_ctDataFcUnion, alignofTy_ctDataDlUnion,
            alignofTy_ct_data_s, alignofTy_tree_desc_s, alignofTy_gzFile_s, alignofTy_z_stream_s,
            IntKind.align, alignUp];
          rfl))
        setGoals [gNeg]
        evalTactic (← `(tactic|
          rw [show ($fnameStx == $fld) = false from beq_false_of_ne (Ne.symm $hfld),
            ite_eq_right Bool.false_ne_true, ite_eq_right $hfld];
          simp only [alignofTy_int, alignofTy_ptr, alignofTy_typedef, alignofTy_array, alignofTy_fnPtr,
            alignofTy_const, alignofTy_codeCTy, alignofTy_codeAnon,
            alignofTy_ctDataFcUnion, alignofTy_ctDataDlUnion,
            alignofTy_ct_data_s, alignofTy_tree_desc_s, alignofTy_gzFile_s, alignofTy_z_stream_s,
            sizeofTy_int, sizeofTy_ptr, sizeofTy_typedef, sizeofTy_array_some, sizeofTy_fnPtr,
            sizeofTy_const, sizeofTy_codeCTy, sizeofTy_codeAnon,
            sizeofTy_ctDataFcUnion, sizeofTy_ctDataDlUnion,
            sizeofTy_ct_data_s, sizeofTy_tree_desc_s, sizeofTy_gzFile_s, sizeofTy_z_stream_s,
            IntKind.align, IntKind.bytes, alignUp];
          norm_findStructField_off))
        loop fuel
      else
        throwError "unexpected rhs in solve_struct_fields: {rhs}"
  loop 100

theorem fieldLayout_code_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "code") fld =
      (if fld = "op" then some (0, .int .u8)
       else if fld = "bits" then some (1, .int .u8)
       else if fld = "val" then some (2, .int .u16)
       else none) := by
  unfold fieldLayout?
  simp only [CTy.unqual, prog_tags_lookup_code, codeFields]
  solve_struct_fields fld

theorem fieldLayout_codeCTy_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags codeCTy fld =
      (if fld = "op" then some (0, .int .u8)
       else if fld = "bits" then some (1, .int .u8)
       else if fld = "val" then some (2, .int .u16)
       else none) := by
  unfold fieldLayout?
  simp only [codeCTy, CTy.unqual, codeFields]
  solve_struct_fields fld

theorem fieldLayout_code_op : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "code") "op" = some (0, .int .u8) := by
  rw [fieldLayout_code_eq]; rfl
theorem fieldLayout_code_bits : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "code") "bits" = some (1, .int .u8) := by
  rw [fieldLayout_code_eq]; rfl
theorem fieldLayout_code_val : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "code") "val" = some (2, .int .u16) := by
  rw [fieldLayout_code_eq]; rfl

theorem fieldLayout_codeCTy_op : fieldLayout? (progOfTUs Zlib.allFiles).tags codeCTy "op" = some (0, .int .u8) := by
  rw [fieldLayout_codeCTy_eq]; rfl
theorem fieldLayout_codeCTy_bits : fieldLayout? (progOfTUs Zlib.allFiles).tags codeCTy "bits" = some (1, .int .u8) := by
  rw [fieldLayout_codeCTy_eq]; rfl
theorem fieldLayout_codeCTy_val : fieldLayout? (progOfTUs Zlib.allFiles).tags codeCTy "val" = some (2, .int .u16) := by
  rw [fieldLayout_codeCTy_eq]; rfl

theorem fieldLayout_ct_data_s_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "ct_data_s") fld =
      (if fld = "fc" then some (0, ctDataFcUnionTy)
       else if fld = "dl" then some (2, ctDataDlUnionTy)
       else none) := by
  unfold fieldLayout?
  simp only [CTy.unqual, prog_tags_lookup_ct_data_s, ctDataFields]
  solve_struct_fields fld

theorem fieldLayout_ct_data_s_fc : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "ct_data_s") "fc" = some (0, ctDataFcUnionTy) := by
  rw [fieldLayout_ct_data_s_eq]; rfl
theorem fieldLayout_ct_data_s_dl : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "ct_data_s") "dl" = some (2, ctDataDlUnionTy) := by
  rw [fieldLayout_ct_data_s_eq]; rfl

theorem fieldLayout_ctDataFcUnion_freq :
    fieldLayout? (progOfTUs Zlib.allFiles).tags ctDataFcUnionTy "freq" = some (0, .typedef "ush" (.int .u16)) := by
  unfold fieldLayout?; simp only [ctDataFcUnionTy, CTy.unqual]; unfold_head_lhs; rfl
theorem fieldLayout_ctDataFcUnion_code :
    fieldLayout? (progOfTUs Zlib.allFiles).tags ctDataFcUnionTy "code" = some (0, .typedef "ush" (.int .u16)) := by
  unfold fieldLayout?; simp only [ctDataFcUnionTy, CTy.unqual]; unfold_head_lhs; unfold_head_lhs; rfl
theorem fieldLayout_ctDataDlUnion_dad :
    fieldLayout? (progOfTUs Zlib.allFiles).tags ctDataDlUnionTy "dad" = some (0, .typedef "ush" (.int .u16)) := by
  unfold fieldLayout?; simp only [ctDataDlUnionTy, CTy.unqual]; unfold_head_lhs; rfl
theorem fieldLayout_ctDataDlUnion_len :
    fieldLayout? (progOfTUs Zlib.allFiles).tags ctDataDlUnionTy "len" = some (0, .typedef "ush" (.int .u16)) := by
  unfold fieldLayout?; simp only [ctDataDlUnionTy, CTy.unqual]; unfold_head_lhs; unfold_head_lhs; rfl

theorem fieldLayout_static_tree_desc_s_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "static_tree_desc_s") fld =
      (if fld = "static_tree" then some (0, .ptr ctDataConstTy)
       else if fld = "extra_bits" then some (8, .ptr (.const_ (.typedef "intf" (.int .i32))))
       else if fld = "extra_base" then some (16, .int .i32)
       else if fld = "elems" then some (20, .int .i32)
       else if fld = "max_length" then some (24, .int .i32)
       else none) := by
  unfold fieldLayout?
  simp only [CTy.unqual, prog_tags_lookup_static_tree_desc_s, staticTreeDescFields]
  solve_struct_fields fld

theorem fieldLayout_static_tree_desc_s_static_tree :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "static_tree_desc_s") "static_tree" = some (0, .ptr ctDataConstTy) := by
  rw [fieldLayout_static_tree_desc_s_eq]; rfl
theorem fieldLayout_static_tree_desc_s_extra_bits :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "static_tree_desc_s") "extra_bits" = some (8, .ptr (.const_ (.typedef "intf" (.int .i32)))) := by
  rw [fieldLayout_static_tree_desc_s_eq]; rfl
theorem fieldLayout_static_tree_desc_s_extra_base :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "static_tree_desc_s") "extra_base" = some (16, .int .i32) := by
  rw [fieldLayout_static_tree_desc_s_eq]; rfl
theorem fieldLayout_static_tree_desc_s_elems :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "static_tree_desc_s") "elems" = some (20, .int .i32) := by
  rw [fieldLayout_static_tree_desc_s_eq]; rfl
theorem fieldLayout_static_tree_desc_s_max_length :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "static_tree_desc_s") "max_length" = some (24, .int .i32) := by
  rw [fieldLayout_static_tree_desc_s_eq]; rfl

theorem fieldLayout_tree_desc_s_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "tree_desc_s") fld =
      (if fld = "dyn_tree" then some (0, .ptr ctDataCTy)
       else if fld = "max_code" then some (8, .int .i32)
       else if fld = "stat_desc" then some (16, .ptr (.const_ (.typedef "static_tree_desc" (.structTy "static_tree_desc_s"))))
       else none) := by
  unfold fieldLayout?
  simp only [CTy.unqual, prog_tags_lookup_tree_desc_s, treeDescFields]
  solve_struct_fields fld

theorem fieldLayout_tree_desc_s_dyn_tree :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "tree_desc_s") "dyn_tree" = some (0, .ptr ctDataCTy) := by
  rw [fieldLayout_tree_desc_s_eq]; rfl
theorem fieldLayout_tree_desc_s_max_code :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "tree_desc_s") "max_code" = some (8, .int .i32) := by
  rw [fieldLayout_tree_desc_s_eq]; rfl
theorem fieldLayout_tree_desc_s_stat_desc :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "tree_desc_s") "stat_desc" =
      some (16, .ptr (.const_ (.typedef "static_tree_desc" (.structTy "static_tree_desc_s")))) := by
  rw [fieldLayout_tree_desc_s_eq]; rfl

theorem fieldLayout_config_s_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "config_s") fld =
      (if fld = "good_length" then some (0, .typedef "ush" (.int .u16))
       else if fld = "max_lazy" then some (2, .typedef "ush" (.int .u16))
       else if fld = "nice_length" then some (4, .typedef "ush" (.int .u16))
       else if fld = "max_chain" then some (6, .typedef "ush" (.int .u16))
       else if fld = "func" then some (8, .typedef "compress_func" (.fnPtr (.typedef "block_state" (.int .u32))
         [.ptr (.typedef "deflate_state" (.structTy "internal_state")), .int .i32] false))
       else none) := by
  unfold fieldLayout?
  simp only [CTy.unqual, prog_tags_lookup_config_s, configFields]
  solve_struct_fields fld

theorem fieldLayout_config_s_good_length :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "config_s") "good_length" = some (0, .typedef "ush" (.int .u16)) := by
  rw [fieldLayout_config_s_eq]; rfl
theorem fieldLayout_config_s_max_lazy :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "config_s") "max_lazy" = some (2, .typedef "ush" (.int .u16)) := by
  rw [fieldLayout_config_s_eq]; rfl
theorem fieldLayout_config_s_nice_length :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "config_s") "nice_length" = some (4, .typedef "ush" (.int .u16)) := by
  rw [fieldLayout_config_s_eq]; rfl
theorem fieldLayout_config_s_max_chain :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "config_s") "max_chain" = some (6, .typedef "ush" (.int .u16)) := by
  rw [fieldLayout_config_s_eq]; rfl
theorem fieldLayout_config_s_func :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "config_s") "func" =
      some (8, .typedef "compress_func" (.fnPtr (.typedef "block_state" (.int .u32))
        [.ptr (.typedef "deflate_state" (.structTy "internal_state")), .int .i32] false)) := by
  rw [fieldLayout_config_s_eq]; rfl

theorem fieldLayout_gzFile_s_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gzFile_s") fld =
      (if fld = "have" then some (0, .int .u32)
       else if fld = "next" then some (8, .ptr (.int .u8))
       else if fld = "pos" then some (16, .typedef "z_off64_t" (.int .i64))
       else none) := by
  unfold fieldLayout?
  simp only [CTy.unqual, prog_tags_lookup_gzFile_s, gzFileFields]
  solve_struct_fields fld

theorem fieldLayout_gzFile_s_have :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gzFile_s") "have" = some (0, .int .u32) := by
  rw [fieldLayout_gzFile_s_eq]; rfl
theorem fieldLayout_gzFile_s_next :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gzFile_s") "next" = some (8, .ptr (.int .u8)) := by
  rw [fieldLayout_gzFile_s_eq]; rfl
theorem fieldLayout_gzFile_s_pos :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gzFile_s") "pos" = some (16, .typedef "z_off64_t" (.int .i64)) := by
  rw [fieldLayout_gzFile_s_eq]; rfl

theorem fieldLayout_gz_header_s_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") fld =
      (if fld = "text" then some (0, .int .i32)
       else if fld = "time" then some (8, .typedef "uLong" (.int .u64))
       else if fld = "xflags" then some (16, .int .i32)
       else if fld = "os" then some (20, .int .i32)
       else if fld = "extra" then some (24, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8))))
       else if fld = "extra_len" then some (32, .typedef "uInt" (.int .u32))
       else if fld = "extra_max" then some (36, .typedef "uInt" (.int .u32))
       else if fld = "name" then some (40, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8))))
       else if fld = "name_max" then some (48, .typedef "uInt" (.int .u32))
       else if fld = "comment" then some (56, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8))))
       else if fld = "comm_max" then some (64, .typedef "uInt" (.int .u32))
       else if fld = "hcrc" then some (68, .int .i32)
       else if fld = "done" then some (72, .int .i32)
       else none) := by
  unfold fieldLayout?
  simp only [CTy.unqual, prog_tags_lookup_gz_header_s, gzHeaderFields]
  solve_struct_fields fld

theorem fieldLayout_gz_header_s_text : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "text" = some (0, .int .i32) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_time : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "time" = some (8, .typedef "uLong" (.int .u64)) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_xflags : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "xflags" = some (16, .int .i32) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_os : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "os" = some (20, .int .i32) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_extra : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "extra" = some (24, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_extra_len : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "extra_len" = some (32, .typedef "uInt" (.int .u32)) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_extra_max : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "extra_max" = some (36, .typedef "uInt" (.int .u32)) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_name : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "name" = some (40, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_name_max : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "name_max" = some (48, .typedef "uInt" (.int .u32)) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_comment : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "comment" = some (56, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_comm_max : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "comm_max" = some (64, .typedef "uInt" (.int .u32)) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_hcrc : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "hcrc" = some (68, .int .i32) := by
  rw [fieldLayout_gz_header_s_eq]; rfl
theorem fieldLayout_gz_header_s_done : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_header_s") "done" = some (72, .int .i32) := by
  rw [fieldLayout_gz_header_s_eq]; rfl

theorem fieldLayout_inflate_state_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") fld =
      (if fld = "strm" then some (0, .typedef "z_streamp" (.ptr (.typedef "z_stream" (.structTy "z_stream_s"))))
       else if fld = "mode" then some (8, .typedef "inflate_mode" (.int .u32))
       else if fld = "last" then some (12, .int .i32)
       else if fld = "wrap" then some (16, .int .i32)
       else if fld = "reqwrap" then some (20, .int .i32)
       else if fld = "havedict" then some (24, .int .i32)
       else if fld = "flags" then some (28, .int .i32)
       else if fld = "dmax" then some (32, .int .u32)
       else if fld = "check" then some (40, .int .u64)
       else if fld = "total" then some (48, .int .u64)
       else if fld = "head" then some (56, .typedef "gz_headerp" (.ptr (.typedef "gz_header" (.structTy "gz_header_s"))))
       else if fld = "reqbits" then some (64, .int .u32)
       else if fld = "wbits" then some (68, .int .u32)
       else if fld = "wsize" then some (72, .int .u32)
       else if fld = "whave" then some (76, .int .u32)
       else if fld = "wnext" then some (80, .int .u32)
       else if fld = "window" then some (88, .ptr (.int .u8))
       else if fld = "hold" then some (96, .int .u64)
       else if fld = "bits" then some (104, .int .u32)
       else if fld = "length" then some (108, .int .u32)
       else if fld = "offset" then some (112, .int .u32)
       else if fld = "extra" then some (116, .int .u32)
       else if fld = "lencode" then some (120, .ptr codeConstTy)
       else if fld = "distcode" then some (128, .ptr codeConstTy)
       else if fld = "lenbits" then some (136, .int .u32)
       else if fld = "distbits" then some (140, .int .u32)
       else if fld = "ncode" then some (144, .int .u32)
       else if fld = "nlen" then some (148, .int .u32)
       else if fld = "ndist" then some (152, .int .u32)
       else if fld = "have" then some (156, .int .u32)
       else if fld = "next" then some (160, .ptr codeCTy)
       else if fld = "lens" then some (168, .array (.int .u16) (some 320))
       else if fld = "work" then some (808, .array (.int .u16) (some 288))
       else if fld = "codes" then some (1384, .array codeCTy (some 1732))
       else if fld = "sane" then some (8312, .int .i32)
       else if fld = "back" then some (8316, .int .i32)
       else if fld = "was" then some (8320, .int .u32)
       else none) := by
  unfold fieldLayout?
  simp only [CTy.unqual, prog_tags_lookup_inflate_state, inflateStateFields]
  solve_struct_fields fld

theorem fieldLayout_inflate_state_strm : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "strm" = some (0, .typedef "z_streamp" (.ptr (.typedef "z_stream" (.structTy "z_stream_s")))) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_mode : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "mode" = some (8, .typedef "inflate_mode" (.int .u32)) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_last : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "last" = some (12, .int .i32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_wrap : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "wrap" = some (16, .int .i32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_reqwrap : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "reqwrap" = some (20, .int .i32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_havedict : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "havedict" = some (24, .int .i32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_flags : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "flags" = some (28, .int .i32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_dmax : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "dmax" = some (32, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_check : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "check" = some (40, .int .u64) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_total : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "total" = some (48, .int .u64) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_head : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "head" = some (56, .typedef "gz_headerp" (.ptr (.typedef "gz_header" (.structTy "gz_header_s")))) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_reqbits : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "reqbits" = some (64, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_wbits : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "wbits" = some (68, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_wsize : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "wsize" = some (72, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_whave : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "whave" = some (76, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_wnext : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "wnext" = some (80, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_window : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "window" = some (88, .ptr (.int .u8)) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_hold : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "hold" = some (96, .int .u64) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_bits : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "bits" = some (104, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_length : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "length" = some (108, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_offset : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "offset" = some (112, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_extra : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "extra" = some (116, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_lencode : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "lencode" = some (120, .ptr codeConstTy) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_distcode : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "distcode" = some (128, .ptr codeConstTy) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_lenbits : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "lenbits" = some (136, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_distbits : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "distbits" = some (140, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_ncode : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "ncode" = some (144, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_nlen : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "nlen" = some (148, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_ndist : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "ndist" = some (152, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_have : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "have" = some (156, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_next : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "next" = some (160, .ptr codeCTy) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_lens : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "lens" = some (168, .array (.int .u16) (some 320)) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_work : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "work" = some (808, .array (.int .u16) (some 288)) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_codes : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "codes" = some (1384, .array codeCTy (some 1732)) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_sane : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "sane" = some (8312, .int .i32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_back : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "back" = some (8316, .int .i32) := by rw [fieldLayout_inflate_state_eq]; rfl
theorem fieldLayout_inflate_state_was : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "inflate_state") "was" = some (8320, .int .u32) := by rw [fieldLayout_inflate_state_eq]; rfl

theorem fieldLayout_internal_state_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") fld =
      (if fld = "strm" then some (0, .typedef "z_streamp" (.ptr (.typedef "z_stream" (.structTy "z_stream_s"))))
       else if fld = "status" then some (8, .int .i32)
       else if fld = "pending_buf" then some (16, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8))))
       else if fld = "pending_buf_size" then some (24, .typedef "ulg" (.int .u64))
       else if fld = "pending_out" then some (32, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8))))
       else if fld = "pending" then some (40, .typedef "ulg" (.int .u64))
       else if fld = "wrap" then some (48, .int .i32)
       else if fld = "gzhead" then some (56, .typedef "gz_headerp" (.ptr (.typedef "gz_header" (.structTy "gz_header_s"))))
       else if fld = "gzindex" then some (64, .typedef "ulg" (.int .u64))
       else if fld = "method" then some (72, .typedef "Byte" (.int .u8))
       else if fld = "last_flush" then some (76, .int .i32)
       else if fld = "w_size" then some (80, .typedef "uInt" (.int .u32))
       else if fld = "w_bits" then some (84, .typedef "uInt" (.int .u32))
       else if fld = "w_mask" then some (88, .typedef "uInt" (.int .u32))
       else if fld = "window" then some (96, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8))))
       else if fld = "window_size" then some (104, .typedef "ulg" (.int .u64))
       else if fld = "prev" then some (112, .ptr (.typedef "Posf" (.typedef "Pos" (.typedef "ush" (.int .u16)))))
       else if fld = "head" then some (120, .ptr (.typedef "Posf" (.typedef "Pos" (.typedef "ush" (.int .u16)))))
       else if fld = "ins_h" then some (128, .typedef "uInt" (.int .u32))
       else if fld = "hash_size" then some (132, .typedef "uInt" (.int .u32))
       else if fld = "hash_bits" then some (136, .typedef "uInt" (.int .u32))
       else if fld = "hash_mask" then some (140, .typedef "uInt" (.int .u32))
       else if fld = "hash_shift" then some (144, .typedef "uInt" (.int .u32))
       else if fld = "block_start" then some (152, .int .i64)
       else if fld = "match_length" then some (160, .typedef "uInt" (.int .u32))
       else if fld = "prev_match" then some (164, .typedef "IPos" (.int .u32))
       else if fld = "match_available" then some (168, .int .i32)
       else if fld = "strstart" then some (172, .typedef "uInt" (.int .u32))
       else if fld = "match_start" then some (176, .typedef "uInt" (.int .u32))
       else if fld = "lookahead" then some (180, .typedef "uInt" (.int .u32))
       else if fld = "prev_length" then some (184, .typedef "uInt" (.int .u32))
       else if fld = "max_chain_length" then some (188, .typedef "uInt" (.int .u32))
       else if fld = "max_lazy_match" then some (192, .typedef "uInt" (.int .u32))
       else if fld = "level" then some (196, .int .i32)
       else if fld = "strategy" then some (200, .int .i32)
       else if fld = "good_match" then some (204, .typedef "uInt" (.int .u32))
       else if fld = "nice_match" then some (208, .int .i32)
       else if fld = "dyn_ltree" then some (212, .array (.structTy "ct_data_s") (some 573))
       else if fld = "dyn_dtree" then some (2504, .array (.structTy "ct_data_s") (some 61))
       else if fld = "bl_tree" then some (2748, .array (.structTy "ct_data_s") (some 39))
       else if fld = "l_desc" then some (2904, .structTy "tree_desc_s")
       else if fld = "d_desc" then some (2928, .structTy "tree_desc_s")
       else if fld = "bl_desc" then some (2952, .structTy "tree_desc_s")
       else if fld = "bl_count" then some (2976, .array (.typedef "ush" (.int .u16)) (some 16))
       else if fld = "heap" then some (3008, .array (.int .i32) (some 573))
       else if fld = "heap_len" then some (5300, .int .i32)
       else if fld = "heap_max" then some (5304, .int .i32)
       else if fld = "depth" then some (5308, .array (.typedef "uch" (.int .u8)) (some 573))
       else if fld = "sym_buf" then some (5888, .ptr (.typedef "uchf" (.typedef "uch" (.int .u8))))
       else if fld = "lit_bufsize" then some (5896, .typedef "uInt" (.int .u32))
       else if fld = "sym_next" then some (5900, .typedef "uInt" (.int .u32))
       else if fld = "sym_end" then some (5904, .typedef "uInt" (.int .u32))
       else if fld = "opt_len" then some (5912, .typedef "ulg" (.int .u64))
       else if fld = "static_len" then some (5920, .typedef "ulg" (.int .u64))
       else if fld = "matches" then some (5928, .typedef "uInt" (.int .u32))
       else if fld = "insert" then some (5932, .typedef "uInt" (.int .u32))
       else if fld = "bi_buf" then some (5936, .typedef "ush" (.int .u16))
       else if fld = "bi_valid" then some (5940, .int .i32)
       else if fld = "bi_used" then some (5944, .int .i32)
       else if fld = "high_water" then some (5952, .typedef "ulg" (.int .u64))
       else if fld = "slid" then some (5960, .int .i32)
       else none) := by
  unfold fieldLayout?
  simp only [CTy.unqual, prog_tags_lookup_internal_state, internalStateFields]
  solve_struct_fields fld

theorem fieldLayout_internal_state_strm : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "strm" = some (0, .typedef "z_streamp" (.ptr (.typedef "z_stream" (.structTy "z_stream_s")))) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_status : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "status" = some (8, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_pending_buf : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "pending_buf" = some (16, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_pending_buf_size : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "pending_buf_size" = some (24, .typedef "ulg" (.int .u64)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_pending_out : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "pending_out" = some (32, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_pending : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "pending" = some (40, .typedef "ulg" (.int .u64)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_wrap : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "wrap" = some (48, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_gzhead : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "gzhead" = some (56, .typedef "gz_headerp" (.ptr (.typedef "gz_header" (.structTy "gz_header_s")))) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_gzindex : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "gzindex" = some (64, .typedef "ulg" (.int .u64)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_method : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "method" = some (72, .typedef "Byte" (.int .u8)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_last_flush : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "last_flush" = some (76, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_w_size : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "w_size" = some (80, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_w_bits : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "w_bits" = some (84, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_w_mask : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "w_mask" = some (88, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_window : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "window" = some (96, .ptr (.typedef "Bytef" (.typedef "Byte" (.int .u8)))) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_window_size : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "window_size" = some (104, .typedef "ulg" (.int .u64)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_prev : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "prev" = some (112, .ptr (.typedef "Posf" (.typedef "Pos" (.typedef "ush" (.int .u16))))) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_head : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "head" = some (120, .ptr (.typedef "Posf" (.typedef "Pos" (.typedef "ush" (.int .u16))))) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_ins_h : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "ins_h" = some (128, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_hash_size : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "hash_size" = some (132, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_hash_bits : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "hash_bits" = some (136, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_hash_mask : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "hash_mask" = some (140, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_hash_shift : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "hash_shift" = some (144, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_block_start : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "block_start" = some (152, .int .i64) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_match_length : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "match_length" = some (160, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_prev_match : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "prev_match" = some (164, .typedef "IPos" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_match_available : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "match_available" = some (168, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_strstart : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "strstart" = some (172, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_match_start : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "match_start" = some (176, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_lookahead : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "lookahead" = some (180, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_prev_length : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "prev_length" = some (184, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_max_chain_length : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "max_chain_length" = some (188, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_max_lazy_match : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "max_lazy_match" = some (192, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_level : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "level" = some (196, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_strategy : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "strategy" = some (200, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_good_match : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "good_match" = some (204, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_nice_match : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "nice_match" = some (208, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_dyn_ltree : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "dyn_ltree" = some (212, .array (.structTy "ct_data_s") (some 573)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_dyn_dtree : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "dyn_dtree" = some (2504, .array (.structTy "ct_data_s") (some 61)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_bl_tree : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "bl_tree" = some (2748, .array (.structTy "ct_data_s") (some 39)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_l_desc : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "l_desc" = some (2904, .structTy "tree_desc_s") := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_d_desc : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "d_desc" = some (2928, .structTy "tree_desc_s") := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_bl_desc : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "bl_desc" = some (2952, .structTy "tree_desc_s") := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_bl_count : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "bl_count" = some (2976, .array (.typedef "ush" (.int .u16)) (some 16)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_heap : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "heap" = some (3008, .array (.int .i32) (some 573)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_heap_len : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "heap_len" = some (5300, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_heap_max : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "heap_max" = some (5304, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_depth : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "depth" = some (5308, .array (.typedef "uch" (.int .u8)) (some 573)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_sym_buf : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "sym_buf" = some (5888, .ptr (.typedef "uchf" (.typedef "uch" (.int .u8)))) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_lit_bufsize : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "lit_bufsize" = some (5896, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_sym_next : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "sym_next" = some (5900, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_sym_end : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "sym_end" = some (5904, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_opt_len : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "opt_len" = some (5912, .typedef "ulg" (.int .u64)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_static_len : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "static_len" = some (5920, .typedef "ulg" (.int .u64)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_matches : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "matches" = some (5928, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_insert : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "insert" = some (5932, .typedef "uInt" (.int .u32)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_bi_buf : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "bi_buf" = some (5936, .typedef "ush" (.int .u16)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_bi_valid : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "bi_valid" = some (5940, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_bi_used : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "bi_used" = some (5944, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_high_water : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "high_water" = some (5952, .typedef "ulg" (.int .u64)) := by rw [fieldLayout_internal_state_eq]; rfl
theorem fieldLayout_internal_state_slid : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "internal_state") "slid" = some (5960, .int .i32) := by rw [fieldLayout_internal_state_eq]; rfl

theorem fieldLayout_gz_state_eq (fld : String) :
    fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") fld =
      (if fld = "x" then some (0, .structTy "gzFile_s")
       else if fld = "mode" then some (24, .int .i32)
       else if fld = "fd" then some (28, .int .i32)
       else if fld = "path" then some (32, .ptr (.int .i8))
       else if fld = "size" then some (40, .int .u32)
       else if fld = "want" then some (44, .int .u32)
       else if fld = "in" then some (48, .ptr (.int .u8))
       else if fld = "out" then some (56, .ptr (.int .u8))
       else if fld = "direct" then some (64, .int .i32)
       else if fld = "junk" then some (68, .int .i32)
       else if fld = "how" then some (72, .int .i32)
       else if fld = "again" then some (76, .int .i32)
       else if fld = "start" then some (80, .typedef "z_off64_t" (.int .i64))
       else if fld = "eof" then some (88, .int .i32)
       else if fld = "past" then some (92, .int .i32)
       else if fld = "level" then some (96, .int .i32)
       else if fld = "strategy" then some (100, .int .i32)
       else if fld = "reset" then some (104, .int .i32)
       else if fld = "skip" then some (112, .typedef "z_off64_t" (.int .i64))
       else if fld = "err" then some (120, .int .i32)
       else if fld = "msg" then some (128, .ptr (.int .i8))
       else if fld = "strm" then some (136, .typedef "z_stream" (.structTy "z_stream_s"))
       else none) := by
  unfold fieldLayout?
  simp only [CTy.unqual, prog_tags_lookup_gz_state, gzStateFields]
  solve_struct_fields fld

theorem fieldLayout_gz_state_x : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "x" = some (0, .structTy "gzFile_s") := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_mode : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "mode" = some (24, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_fd : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "fd" = some (28, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_path : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "path" = some (32, .ptr (.int .i8)) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_size : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "size" = some (40, .int .u32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_want : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "want" = some (44, .int .u32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_in : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "in" = some (48, .ptr (.int .u8)) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_out : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "out" = some (56, .ptr (.int .u8)) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_direct : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "direct" = some (64, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_junk : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "junk" = some (68, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_how : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "how" = some (72, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_again : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "again" = some (76, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_start : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "start" = some (80, .typedef "z_off64_t" (.int .i64)) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_eof : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "eof" = some (88, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_past : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "past" = some (92, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_level : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "level" = some (96, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_strategy : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "strategy" = some (100, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_reset : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "reset" = some (104, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_skip : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "skip" = some (112, .typedef "z_off64_t" (.int .i64)) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_err : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "err" = some (120, .int .i32) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_msg : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "msg" = some (128, .ptr (.int .i8)) := by rw [fieldLayout_gz_state_eq]; rfl
theorem fieldLayout_gz_state_strm : fieldLayout? (progOfTUs Zlib.allFiles).tags (.structTy "gz_state") "strm" = some (136, .typedef "z_stream" (.structTy "z_stream_s")) := by rw [fieldLayout_gz_state_eq]; rfl

end FieldLayoutSection

/-! ## 2. Complete Function & Prototype Lookups (`prog0.fns`, `prog0.fnProtos`, `stdLibc`) -/

section ProgFnsAndProtos

private theorem allHeaders_fnEntries_eq : Zlib.allHeaders.flatMap tuFnEntries = [] := rfl

private theorem gzcloseTU_fnEntries : tuFnEntries Zlib.Gzclose.gzcloseTU = [
  ("gzclose", Zlib.Gzclose.gzcloseTU_fn_gzclose)
] := rfl

private theorem zutilTU_fnEntries : tuFnEntries Zlib.Zutil.zutilTU = [
  ("zlibVersion", Zlib.Zutil.zutilTU_fn_zlibVersion),
  ("zlibCompileFlags", Zlib.Zutil.zutilTU_fn_zlibCompileFlags),
  ("zError", Zlib.Zutil.zutilTU_fn_zError),
  ("zcalloc", Zlib.Zutil.zutilTU_fn_zcalloc),
  ("zcfree", Zlib.Zutil.zutilTU_fn_zcfree)
] := rfl

private theorem adler32TU_fnEntries : tuFnEntries Zlib.Adler32.adler32TU = [
  ("adler32_z", Zlib.Adler32.adler32TU_fn_adler32_z),
  ("adler32", Zlib.Adler32.adler32TU_fn_adler32),
  ("adler32_combine_", Zlib.Adler32.adler32TU_fn_adler32_combine_),
  ("adler32_combine", Zlib.Adler32.adler32TU_fn_adler32_combine),
  ("adler32_combine64", Zlib.Adler32.adler32TU_fn_adler32_combine64)
] := rfl

private theorem compressTU_fnEntries : tuFnEntries Zlib.Compress.compressTU = [
  ("compress2_z", Zlib.Compress.compressTU_fn_compress2_z),
  ("compress2", Zlib.Compress.compressTU_fn_compress2),
  ("compress_z", Zlib.Compress.compressTU_fn_compress_z),
  ("compress", Zlib.Compress.compressTU_fn_compress),
  ("compressBound_z", Zlib.Compress.compressTU_fn_compressBound_z),
  ("compressBound", Zlib.Compress.compressTU_fn_compressBound)
] := rfl

private theorem uncomprTU_fnEntries : tuFnEntries Zlib.Uncompr.uncomprTU = [
  ("uncompress2_z", Zlib.Uncompr.uncomprTU_fn_uncompress2_z),
  ("uncompress2", Zlib.Uncompr.uncomprTU_fn_uncompress2),
  ("uncompress_z", Zlib.Uncompr.uncomprTU_fn_uncompress_z),
  ("uncompress", Zlib.Uncompr.uncomprTU_fn_uncompress)
] := rfl

private theorem inftreesTU_fnEntries : tuFnEntries Zlib.Inftrees.inftreesTU = [
  ("inflate_table", Zlib.Inftrees.inftreesTU_fn_inflate_table),
  ("inflate_fixed", Zlib.Inftrees.inftreesTU_fn_inflate_fixed)
] := rfl

private theorem inffastTU_fnEntries : tuFnEntries Zlib.Inffast.inffastTU = [
  ("load64", Zlib.Inffast.inffastTU_fn_load64),
  ("copy_back", Zlib.Inffast.inffastTU_fn_copy_back),
  ("inflate_fast", Zlib.Inffast.inffastTU_fn_inflate_fast)
] := rfl

private theorem crc32TU_fnEntries : tuFnEntries Zlib.Crc32.crc32TU = [
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

private theorem treesTU_fnEntries : tuFnEntries Zlib.Trees.treesTU = [
  ("bi_reverse", Zlib.Trees.treesTU_fn_bi_reverse),
  ("bi_flush", Zlib.Trees.treesTU_fn_bi_flush),
  ("bi_windup", Zlib.Trees.treesTU_fn_bi_windup),
  ("gen_codes", Zlib.Trees.treesTU_fn_gen_codes),
  ("tr_static_init", Zlib.Trees.treesTU_fn_tr_static_init),
  ("init_block", Zlib.Trees.treesTU_fn_init_block),
  ("_tr_init", Zlib.Trees.treesTU_fn__tr_init),
  ("pqdownheap", Zlib.Trees.treesTU_fn_pqdownheap),
  ("gen_bitlen", Zlib.Trees.treesTU_fn_gen_bitlen),
  ("build_tree", Zlib.Trees.treesTU_fn_build_tree),
  ("scan_tree", Zlib.Trees.treesTU_fn_scan_tree),
  ("send_tree", Zlib.Trees.treesTU_fn_send_tree),
  ("build_bl_tree", Zlib.Trees.treesTU_fn_build_bl_tree),
  ("send_all_trees", Zlib.Trees.treesTU_fn_send_all_trees),
  ("_tr_stored_block", Zlib.Trees.treesTU_fn__tr_stored_block),
  ("_tr_flush_bits", Zlib.Trees.treesTU_fn__tr_flush_bits),
  ("_tr_align", Zlib.Trees.treesTU_fn__tr_align),
  ("compress_block", Zlib.Trees.treesTU_fn_compress_block),
  ("detect_data_type", Zlib.Trees.treesTU_fn_detect_data_type),
  ("_tr_flush_block", Zlib.Trees.treesTU_fn__tr_flush_block),
  ("_tr_tally", Zlib.Trees.treesTU_fn__tr_tally)
] := rfl

private theorem infbackTU_fnEntries : tuFnEntries Zlib.Infback.infbackTU = [
  ("inflateBackInit_", Zlib.Infback.infbackTU_fn_inflateBackInit_),
  ("inflateBack", Zlib.Infback.infbackTU_fn_inflateBack),
  ("inflateBackEnd", Zlib.Infback.infbackTU_fn_inflateBackEnd)
] := rfl

private theorem inflateTU_fnEntries : tuFnEntries Zlib.Inflate.inflateTU = [
  ("inflateStateCheck", Zlib.Inflate.inflateTU_fn_inflateStateCheck),
  ("inflateResetKeep", Zlib.Inflate.inflateTU_fn_inflateResetKeep),
  ("inflateReset", Zlib.Inflate.inflateTU_fn_inflateReset),
  ("inflateReset2", Zlib.Inflate.inflateTU_fn_inflateReset2),
  ("inflateInit2_", Zlib.Inflate.inflateTU_fn_inflateInit2_),
  ("inflateInit_", Zlib.Inflate.inflateTU_fn_inflateInit_),
  ("inflatePrime", Zlib.Inflate.inflateTU_fn_inflatePrime),
  ("updatewindow", Zlib.Inflate.inflateTU_fn_updatewindow),
  ("inflate", Zlib.Inflate.inflateTU_fn_inflate),
  ("inflateEnd", Zlib.Inflate.inflateTU_fn_inflateEnd),
  ("inflateGetDictionary", Zlib.Inflate.inflateTU_fn_inflateGetDictionary),
  ("inflateSetDictionary", Zlib.Inflate.inflateTU_fn_inflateSetDictionary),
  ("inflateGetHeader", Zlib.Inflate.inflateTU_fn_inflateGetHeader),
  ("syncsearch", Zlib.Inflate.inflateTU_fn_syncsearch),
  ("inflateSync", Zlib.Inflate.inflateTU_fn_inflateSync),
  ("inflateSyncPoint", Zlib.Inflate.inflateTU_fn_inflateSyncPoint),
  ("inflateCopy", Zlib.Inflate.inflateTU_fn_inflateCopy),
  ("inflateUndermine", Zlib.Inflate.inflateTU_fn_inflateUndermine),
  ("inflateValidate", Zlib.Inflate.inflateTU_fn_inflateValidate),
  ("inflateMark", Zlib.Inflate.inflateTU_fn_inflateMark),
  ("inflateCodesUsed", Zlib.Inflate.inflateTU_fn_inflateCodesUsed)
] := rfl

private theorem deflateTU_fnEntries : tuFnEntries Zlib.Deflate.deflateTU = [
  ("slide_hash", Zlib.Deflate.deflateTU_fn_slide_hash),
  ("read_buf", Zlib.Deflate.deflateTU_fn_read_buf),
  ("fill_window", Zlib.Deflate.deflateTU_fn_fill_window),
  ("deflateInit_", Zlib.Deflate.deflateTU_fn_deflateInit_),
  ("deflateInit2_", Zlib.Deflate.deflateTU_fn_deflateInit2_),
  ("deflateStateCheck", Zlib.Deflate.deflateTU_fn_deflateStateCheck),
  ("deflateSetDictionary", Zlib.Deflate.deflateTU_fn_deflateSetDictionary),
  ("deflateGetDictionary", Zlib.Deflate.deflateTU_fn_deflateGetDictionary),
  ("deflateResetKeep", Zlib.Deflate.deflateTU_fn_deflateResetKeep),
  ("lm_init", Zlib.Deflate.deflateTU_fn_lm_init),
  ("deflateReset", Zlib.Deflate.deflateTU_fn_deflateReset),
  ("deflateSetHeader", Zlib.Deflate.deflateTU_fn_deflateSetHeader),
  ("deflatePending", Zlib.Deflate.deflateTU_fn_deflatePending),
  ("deflateUsed", Zlib.Deflate.deflateTU_fn_deflateUsed),
  ("deflatePrime", Zlib.Deflate.deflateTU_fn_deflatePrime),
  ("deflateParams", Zlib.Deflate.deflateTU_fn_deflateParams),
  ("deflateTune", Zlib.Deflate.deflateTU_fn_deflateTune),
  ("deflateBound_z", Zlib.Deflate.deflateTU_fn_deflateBound_z),
  ("deflateBound", Zlib.Deflate.deflateTU_fn_deflateBound),
  ("putShortMSB", Zlib.Deflate.deflateTU_fn_putShortMSB),
  ("flush_pending", Zlib.Deflate.deflateTU_fn_flush_pending),
  ("deflate", Zlib.Deflate.deflateTU_fn_deflate),
  ("deflateEnd", Zlib.Deflate.deflateTU_fn_deflateEnd),
  ("deflateCopy", Zlib.Deflate.deflateTU_fn_deflateCopy),
  ("longest_match", Zlib.Deflate.deflateTU_fn_longest_match),
  ("deflate_stored", Zlib.Deflate.deflateTU_fn_deflate_stored),
  ("deflate_fast", Zlib.Deflate.deflateTU_fn_deflate_fast),
  ("deflate_slow", Zlib.Deflate.deflateTU_fn_deflate_slow),
  ("deflate_rle", Zlib.Deflate.deflateTU_fn_deflate_rle),
  ("deflate_huff", Zlib.Deflate.deflateTU_fn_deflate_huff)
] := rfl

private theorem gzlibTU_fnEntries : tuFnEntries Zlib.Gzlib.gzlibTU = [
  ("gz_reset", Zlib.Gzlib.gzlibTU_fn_gz_reset),
  ("gz_open", Zlib.Gzlib.gzlibTU_fn_gz_open),
  ("gzopen", Zlib.Gzlib.gzlibTU_fn_gzopen),
  ("gzopen64", Zlib.Gzlib.gzlibTU_fn_gzopen64),
  ("gzdopen", Zlib.Gzlib.gzlibTU_fn_gzdopen),
  ("gzbuffer", Zlib.Gzlib.gzlibTU_fn_gzbuffer),
  ("gzrewind", Zlib.Gzlib.gzlibTU_fn_gzrewind),
  ("gzseek64", Zlib.Gzlib.gzlibTU_fn_gzseek64),
  ("gzseek", Zlib.Gzlib.gzlibTU_fn_gzseek),
  ("gztell64", Zlib.Gzlib.gzlibTU_fn_gztell64),
  ("gztell", Zlib.Gzlib.gzlibTU_fn_gztell),
  ("gzoffset64", Zlib.Gzlib.gzlibTU_fn_gzoffset64),
  ("gzoffset", Zlib.Gzlib.gzlibTU_fn_gzoffset),
  ("gzeof", Zlib.Gzlib.gzlibTU_fn_gzeof),
  ("gzerror", Zlib.Gzlib.gzlibTU_fn_gzerror),
  ("gzclearerr", Zlib.Gzlib.gzlibTU_fn_gzclearerr),
  ("gz_error", Zlib.Gzlib.gzlibTU_fn_gz_error),
  ("gz_intmax", Zlib.Gzlib.gzlibTU_fn_gz_intmax)
] := rfl

private theorem gzreadTU_fnEntries : tuFnEntries Zlib.Gzread.gzreadTU = [
  ("gz_load", Zlib.Gzread.gzreadTU_fn_gz_load),
  ("gz_avail", Zlib.Gzread.gzreadTU_fn_gz_avail),
  ("gz_room", Zlib.Gzread.gzreadTU_fn_gz_room),
  ("gz_look", Zlib.Gzread.gzreadTU_fn_gz_look),
  ("gz_decomp", Zlib.Gzread.gzreadTU_fn_gz_decomp),
  ("gz_fetch", Zlib.Gzread.gzreadTU_fn_gz_fetch),
  ("gz_skip_have", Zlib.Gzread.gzreadTU_fn_gz_skip_have),
  ("gz_skip", Zlib.Gzread.gzreadTU_fn_gz_skip),
  ("gz_read", Zlib.Gzread.gzreadTU_fn_gz_read),
  ("gzread", Zlib.Gzread.gzreadTU_fn_gzread),
  ("gzfread", Zlib.Gzread.gzreadTU_fn_gzfread),
  ("gzgetc", Zlib.Gzread.gzreadTU_fn_gzgetc),
  ("gzgetc_", Zlib.Gzread.gzreadTU_fn_gzgetc_),
  ("gzungetc", Zlib.Gzread.gzreadTU_fn_gzungetc),
  ("gzgets", Zlib.Gzread.gzreadTU_fn_gzgets),
  ("gzdirect", Zlib.Gzread.gzreadTU_fn_gzdirect),
  ("gzclose_r", Zlib.Gzread.gzreadTU_fn_gzclose_r)
] := rfl

private theorem gzwriteTU_fnEntries : tuFnEntries Zlib.Gzwrite.gzwriteTU = [
  ("gz_init", Zlib.Gzwrite.gzwriteTU_fn_gz_init),
  ("gz_comp", Zlib.Gzwrite.gzwriteTU_fn_gz_comp),
  ("gz_zero", Zlib.Gzwrite.gzwriteTU_fn_gz_zero),
  ("gz_write", Zlib.Gzwrite.gzwriteTU_fn_gz_write),
  ("gzwrite", Zlib.Gzwrite.gzwriteTU_fn_gzwrite),
  ("gzfwrite", Zlib.Gzwrite.gzwriteTU_fn_gzfwrite),
  ("gzputc", Zlib.Gzwrite.gzwriteTU_fn_gzputc),
  ("gzputs", Zlib.Gzwrite.gzwriteTU_fn_gzputs),
  ("gz_vacate", Zlib.Gzwrite.gzwriteTU_fn_gz_vacate),
  ("gzvprintf", Zlib.Gzwrite.gzwriteTU_fn_gzvprintf),
  ("gzprintf", Zlib.Gzwrite.gzwriteTU_fn_gzprintf),
  ("gzflush", Zlib.Gzwrite.gzwriteTU_fn_gzflush),
  ("gzsetparams", Zlib.Gzwrite.gzwriteTU_fn_gzsetparams),
  ("gzclose_w", Zlib.Gzwrite.gzwriteTU_fn_gzclose_w)
] := rfl

private theorem allTUs_fnEntries_eq :
    Zlib.allTUs.flatMap tuFnEntries =
      tuFnEntries Zlib.Gzclose.gzcloseTU ++
      tuFnEntries Zlib.Zutil.zutilTU ++
      tuFnEntries Zlib.Adler32.adler32TU ++
      tuFnEntries Zlib.Compress.compressTU ++
      tuFnEntries Zlib.Uncompr.uncomprTU ++
      tuFnEntries Zlib.Inftrees.inftreesTU ++
      tuFnEntries Zlib.Inffast.inffastTU ++
      tuFnEntries Zlib.Crc32.crc32TU ++
      tuFnEntries Zlib.Trees.treesTU ++
      tuFnEntries Zlib.Infback.infbackTU ++
      tuFnEntries Zlib.Inflate.inflateTU ++
      tuFnEntries Zlib.Deflate.deflateTU ++
      tuFnEntries Zlib.Gzlib.gzlibTU ++
      tuFnEntries Zlib.Gzread.gzreadTU ++
      tuFnEntries Zlib.Gzwrite.gzwriteTU := by
  simp only [Zlib.allTUs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

private theorem mem_tuFnNames_of_lookup {tu : TU} {sym : String} {fn : FnDef}
    (h : (tuFnEntries tu).lookup sym = some fn) : sym ∈ tuFnNames tu := by
  rcases tu with ⟨_, items⟩
  unfold tuFnEntries tuFnNames at *
  dsimp only at *
  induction items with
  | nil => simp at h
  | cons hd tl ih =>
    cases hd with
    | fnDef f =>
      simp only [List.filterMap_cons, List.lookup] at h
      simp only [List.filterMap_cons, List.mem_cons]
      cases hbeq : (sym == f.name)
      · rw [hbeq] at h; exact Or.inr (ih h)
      · exact Or.inl (beq_iff_eq.mp hbeq)
    | _ => exact ih h

private theorem mem_tuProtoNames_of_lookup {tu : TU} {sym : String} {sig : FnSig}
    (h : (tuProtoEntries tu).lookup sym = some sig) : sym ∈ tuProtoNames tu := by
  rcases tu with ⟨_, items⟩
  unfold tuProtoEntries tuProtoNames at *
  dsimp only at *
  induction items with
  | nil => simp at h
  | cons hd tl ih =>
    cases hd with
    | fnDef f =>
      simp only [List.filterMap_cons, List.lookup] at h
      simp only [List.filterMap_cons, List.mem_cons]
      cases hbeq : (sym == f.name)
      · rw [hbeq] at h; exact Or.inr (ih h)
      · exact Or.inl (beq_iff_eq.mp hbeq)
    | fnProto _ _ n _ _ =>
      simp only [List.filterMap_cons, List.lookup] at h
      simp only [List.filterMap_cons, List.mem_cons]
      cases hbeq : (sym == n)
      · rw [hbeq] at h; exact Or.inr (ih h)
      · exact Or.inl (beq_iff_eq.mp hbeq)
    | _ => exact ih h

private theorem tuFnEntries_none_of_not_mem {tu : TU} {sym : String}
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

private theorem tuProtoEntries_none_of_not_mem {tu : TU} {sym : String}
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

private def listAllDistinct (xs : List String) : Bool :=
  match xs with
  | [] => true
  | x :: xs => !(xs.contains x) && listAllDistinct xs

private theorem nodup_of_listAllDistinct {xs : List String} (h : listAllDistinct xs = true) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [listAllDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact List.nodup_cons.mpr ⟨fun hx => by rw [List.contains_iff_mem.mpr hx] at h; exact Bool.noConfusion h.1, ih h.2⟩

private theorem fnNames_gzclose : tuFnNames Zlib.Gzclose.gzcloseTU = ["gzclose"] := rfl
private theorem fnNames_zutil : tuFnNames Zlib.Zutil.zutilTU = ["zlibVersion", "zlibCompileFlags", "zError", "zcalloc", "zcfree"] := rfl
private theorem fnNames_adler32 : tuFnNames Zlib.Adler32.adler32TU = ["adler32_z", "adler32", "adler32_combine_", "adler32_combine", "adler32_combine64"] := rfl
private theorem fnNames_compress : tuFnNames Zlib.Compress.compressTU = ["compress2_z", "compress2", "compress_z", "compress", "compressBound_z", "compressBound"] := rfl
private theorem fnNames_uncompr : tuFnNames Zlib.Uncompr.uncomprTU = ["uncompress2_z", "uncompress2", "uncompress_z", "uncompress"] := rfl
private theorem fnNames_inftrees : tuFnNames Zlib.Inftrees.inftreesTU = ["inflate_table", "inflate_fixed"] := rfl
private theorem fnNames_inffast : tuFnNames Zlib.Inffast.inffastTU = ["load64", "copy_back", "inflate_fast"] := rfl
private theorem fnNames_crc32 : tuFnNames Zlib.Crc32.crc32TU = ["byte_swap", "multmodp", "x2nmodp", "get_crc_table", "crc_word", "crc_word_big", "crc32_braid", "crc32_z", "crc32", "crc32_combine_gen64", "crc32_combine_gen", "crc32_combine_op", "crc32_combine64", "crc32_combine"] := rfl
private theorem fnNames_trees : tuFnNames Zlib.Trees.treesTU = ["bi_reverse", "bi_flush", "bi_windup", "gen_codes", "tr_static_init", "init_block", "_tr_init", "pqdownheap", "gen_bitlen", "build_tree", "scan_tree", "send_tree", "build_bl_tree", "send_all_trees", "_tr_stored_block", "_tr_flush_bits", "_tr_align", "compress_block", "detect_data_type", "_tr_flush_block", "_tr_tally"] := rfl
private theorem fnNames_infback : tuFnNames Zlib.Infback.infbackTU = ["inflateBackInit_", "inflateBack", "inflateBackEnd"] := rfl
private theorem fnNames_inflate : tuFnNames Zlib.Inflate.inflateTU = ["inflateStateCheck", "inflateResetKeep", "inflateReset", "inflateReset2", "inflateInit2_", "inflateInit_", "inflatePrime", "updatewindow", "inflate", "inflateEnd", "inflateGetDictionary", "inflateSetDictionary", "inflateGetHeader", "syncsearch", "inflateSync", "inflateSyncPoint", "inflateCopy", "inflateUndermine", "inflateValidate", "inflateMark", "inflateCodesUsed"] := rfl
private theorem fnNames_deflate : tuFnNames Zlib.Deflate.deflateTU = ["slide_hash", "read_buf", "fill_window", "deflateInit_", "deflateInit2_", "deflateStateCheck", "deflateSetDictionary", "deflateGetDictionary", "deflateResetKeep", "lm_init", "deflateReset", "deflateSetHeader", "deflatePending", "deflateUsed", "deflatePrime", "deflateParams", "deflateTune", "deflateBound_z", "deflateBound", "putShortMSB", "flush_pending", "deflate", "deflateEnd", "deflateCopy", "longest_match", "deflate_stored", "deflate_fast", "deflate_slow", "deflate_rle", "deflate_huff"] := rfl
private theorem fnNames_gzlib : tuFnNames Zlib.Gzlib.gzlibTU = ["gz_reset", "gz_open", "gzopen", "gzopen64", "gzdopen", "gzbuffer", "gzrewind", "gzseek64", "gzseek", "gztell64", "gztell", "gzoffset64", "gzoffset", "gzeof", "gzerror", "gzclearerr", "gz_error", "gz_intmax"] := rfl
private theorem fnNames_gzread : tuFnNames Zlib.Gzread.gzreadTU = ["gz_load", "gz_avail", "gz_room", "gz_look", "gz_decomp", "gz_fetch", "gz_skip_have", "gz_skip", "gz_read", "gzread", "gzfread", "gzgetc", "gzgetc_", "gzungetc", "gzgets", "gzdirect", "gzclose_r"] := rfl
private theorem fnNames_gzwrite : tuFnNames Zlib.Gzwrite.gzwriteTU = ["gz_init", "gz_comp", "gz_zero", "gz_write", "gzwrite", "gzfwrite", "gzputc", "gzputs", "gz_vacate", "gzvprintf", "gzprintf", "gzflush", "gzsetparams", "gzclose_w"] := rfl

private theorem allTUs_fnNames_eq :
    Zlib.allTUs.flatMap tuFnNames =
      ["gzclose"] ++
      ["zlibVersion", "zlibCompileFlags", "zError", "zcalloc", "zcfree"] ++
      ["adler32_z", "adler32", "adler32_combine_", "adler32_combine", "adler32_combine64"] ++
      ["compress2_z", "compress2", "compress_z", "compress", "compressBound_z", "compressBound"] ++
      ["uncompress2_z", "uncompress2", "uncompress_z", "uncompress"] ++
      ["inflate_table", "inflate_fixed"] ++
      ["load64", "copy_back", "inflate_fast"] ++
      ["byte_swap", "multmodp", "x2nmodp", "get_crc_table", "crc_word", "crc_word_big", "crc32_braid", "crc32_z", "crc32", "crc32_combine_gen64", "crc32_combine_gen", "crc32_combine_op", "crc32_combine64", "crc32_combine"] ++
      ["bi_reverse", "bi_flush", "bi_windup", "gen_codes", "tr_static_init", "init_block", "_tr_init", "pqdownheap", "gen_bitlen", "build_tree", "scan_tree", "send_tree", "build_bl_tree", "send_all_trees", "_tr_stored_block", "_tr_flush_bits", "_tr_align", "compress_block", "detect_data_type", "_tr_flush_block", "_tr_tally"] ++
      ["inflateBackInit_", "inflateBack", "inflateBackEnd"] ++
      ["inflateStateCheck", "inflateResetKeep", "inflateReset", "inflateReset2", "inflateInit2_", "inflateInit_", "inflatePrime", "updatewindow", "inflate", "inflateEnd", "inflateGetDictionary", "inflateSetDictionary", "inflateGetHeader", "syncsearch", "inflateSync", "inflateSyncPoint", "inflateCopy", "inflateUndermine", "inflateValidate", "inflateMark", "inflateCodesUsed"] ++
      ["slide_hash", "read_buf", "fill_window", "deflateInit_", "deflateInit2_", "deflateStateCheck", "deflateSetDictionary", "deflateGetDictionary", "deflateResetKeep", "lm_init", "deflateReset", "deflateSetHeader", "deflatePending", "deflateUsed", "deflatePrime", "deflateParams", "deflateTune", "deflateBound_z", "deflateBound", "putShortMSB", "flush_pending", "deflate", "deflateEnd", "deflateCopy", "longest_match", "deflate_stored", "deflate_fast", "deflate_slow", "deflate_rle", "deflate_huff"] ++
      ["gz_reset", "gz_open", "gzopen", "gzopen64", "gzdopen", "gzbuffer", "gzrewind", "gzseek64", "gzseek", "gztell64", "gztell", "gzoffset64", "gzoffset", "gzeof", "gzerror", "gzclearerr", "gz_error", "gz_intmax"] ++
      ["gz_load", "gz_avail", "gz_room", "gz_look", "gz_decomp", "gz_fetch", "gz_skip_have", "gz_skip", "gz_read", "gzread", "gzfread", "gzgetc", "gzgetc_", "gzungetc", "gzgets", "gzdirect", "gzclose_r"] ++
      ["gz_init", "gz_comp", "gz_zero", "gz_write", "gzwrite", "gzfwrite", "gzputc", "gzputs", "gz_vacate", "gzvprintf", "gzprintf", "gzflush", "gzsetparams", "gzclose_w"] := by
  simp only [Zlib.allTUs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
    fnNames_gzclose, fnNames_zutil, fnNames_adler32, fnNames_compress, fnNames_uncompr,
    fnNames_inftrees, fnNames_inffast, fnNames_crc32, fnNames_trees, fnNames_infback,
    fnNames_inflate, fnNames_deflate, fnNames_gzlib, fnNames_gzread, fnNames_gzwrite]

private theorem allTUs_fnNames_nodup : (Zlib.allTUs.flatMap tuFnNames).Nodup := by
  rw [allTUs_fnNames_eq]
  exact nodup_of_listAllDistinct (by decide)

private theorem pn_gzclose : tuProtoNames Zlib.Gzclose.gzcloseTU = tuFnNames Zlib.Gzclose.gzcloseTU := rfl
private theorem pn_zutil : tuProtoNames Zlib.Zutil.zutilTU = tuFnNames Zlib.Zutil.zutilTU := rfl
private theorem pn_adler32 : tuProtoNames Zlib.Adler32.adler32TU = tuFnNames Zlib.Adler32.adler32TU := rfl
private theorem pn_compress : tuProtoNames Zlib.Compress.compressTU = tuFnNames Zlib.Compress.compressTU := rfl
private theorem pn_uncompr : tuProtoNames Zlib.Uncompr.uncomprTU = tuFnNames Zlib.Uncompr.uncomprTU := rfl
private theorem pn_inftrees : tuProtoNames Zlib.Inftrees.inftreesTU = tuFnNames Zlib.Inftrees.inftreesTU := rfl
private theorem pn_inffast : tuProtoNames Zlib.Inffast.inffastTU = tuFnNames Zlib.Inffast.inffastTU := rfl
private theorem pn_crc32 : tuProtoNames Zlib.Crc32.crc32TU = tuFnNames Zlib.Crc32.crc32TU := rfl
private theorem pn_trees : tuProtoNames Zlib.Trees.treesTU = tuFnNames Zlib.Trees.treesTU := rfl
private theorem pn_infback : tuProtoNames Zlib.Infback.infbackTU = tuFnNames Zlib.Infback.infbackTU := rfl
private theorem pn_inflate : tuProtoNames Zlib.Inflate.inflateTU = tuFnNames Zlib.Inflate.inflateTU := rfl
private theorem pn_deflate : tuProtoNames Zlib.Deflate.deflateTU =
    ["deflate_stored", "deflate_fast", "deflate_slow", "deflate_rle", "deflate_huff"] ++
      tuFnNames Zlib.Deflate.deflateTU := rfl
private theorem pn_gzlib : tuProtoNames Zlib.Gzlib.gzlibTU = tuFnNames Zlib.Gzlib.gzlibTU := rfl
private theorem pn_gzread : tuProtoNames Zlib.Gzread.gzreadTU = tuFnNames Zlib.Gzread.gzreadTU := rfl
private theorem pn_gzwrite : tuProtoNames Zlib.Gzwrite.gzwriteTU = tuFnNames Zlib.Gzwrite.gzwriteTU := rfl

private theorem tuProtoNames_subset_tuFnNames {tu : TU} (htu : tu ∈ Zlib.allTUs)
    {sym : String} (h : sym ∈ tuProtoNames tu) : sym ∈ tuFnNames tu := by
  simp only [Zlib.allTUs, List.mem_cons, List.not_mem_nil, or_false] at htu
  rcases htu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rwa [pn_gzclose] at h
  · rwa [pn_zutil] at h
  · rwa [pn_adler32] at h
  · rwa [pn_compress] at h
  · rwa [pn_uncompr] at h
  · rwa [pn_inftrees] at h
  · rwa [pn_inffast] at h
  · rwa [pn_crc32] at h
  · rwa [pn_trees] at h
  · rwa [pn_infback] at h
  · rwa [pn_inflate] at h
  · rw [pn_deflate, List.mem_append] at h
    rcases h with hpre | hfn
    · rw [fnNames_deflate]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hpre ⊢
      rcases hpre with rfl | rfl | rfl | rfl | rfl <;> decide
    · exact hfn
  · rwa [pn_gzlib] at h
  · rwa [pn_gzread] at h
  · rwa [pn_gzwrite] at h

private theorem flatMap_fnEntries_lookup_of_tu_mem
    {pre mid post : List TU} {tu : TU} {sym : String} {fn : FnDef}
    (hsplit : Zlib.allTUs = pre ++ tu :: post)
    (heq : mid = [tu])
    (hlook : (tuFnEntries tu).lookup sym = some fn) :
    (progOfTUs Zlib.allFiles).fns sym = some fn := by
  have _ := heq
  rw [progOfTUs_fns, Zlib.allFiles, List.flatMap_append, allHeaders_fnEntries_eq, List.nil_append,
    hsplit, List.flatMap_append, List.flatMap_cons]
  have hnodup := allTUs_fnNames_nodup
  rw [hsplit, List.flatMap_append, List.flatMap_cons] at hnodup
  have hmem : sym ∈ tuFnNames tu := mem_tuFnNames_of_lookup hlook
  have hdisj := (List.nodup_append.mp hnodup).2.2
  have hnot_pre : sym ∉ pre.flatMap tuFnNames :=
    fun hpre => hdisj sym hpre sym (List.mem_append_left _ hmem) rfl
  have hnone_pre : (pre.flatMap tuFnEntries).lookup sym = none := by
    clear hsplit hnodup hmem hdisj
    induction pre with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.flatMap_cons, List.mem_append, not_or] at hnot_pre
      simp only [List.flatMap_cons]
      exact lookup_append_none (tuFnEntries_none_of_not_mem hnot_pre.1) |>.trans (ih hnot_pre.2)
  rw [lookup_append_none hnone_pre]
  exact lookup_append_some hlook

private theorem allHeaders_protoEntries_lookup_some {sym : String} {sig : FnSig}
    (h : (Zlib.allHeaders.flatMap tuProtoEntries).lookup sym = some sig) :
    (progOfTUs Zlib.allFiles).fnProtos sym = some sig := by
  rw [progOfTUs_fnProtos, Zlib.allFiles, List.flatMap_append, List.append_assoc]
  exact lookup_append_some h

private theorem tu_protoEntries_of_mem
    {pre post : List TU} {tu : TU} {sym : String} {sig : FnSig}
    (hsplit : Zlib.allTUs = pre ++ tu :: post)
    (hhdr : (Zlib.allHeaders.flatMap tuProtoEntries).lookup sym = none)
    (hlook : (tuProtoEntries tu).lookup sym = some sig) :
    (progOfTUs Zlib.allFiles).fnProtos sym = some sig := by
  rw [progOfTUs_fnProtos, Zlib.allFiles, List.flatMap_append, List.append_assoc,
    lookup_append_none hhdr, hsplit, List.flatMap_append, List.flatMap_cons,
    List.append_assoc, List.append_assoc]
  have htu_mem : tu ∈ Zlib.allTUs := by rw [hsplit]; simp
  have hmem_fn : sym ∈ tuFnNames tu :=
    tuProtoNames_subset_tuFnNames htu_mem (mem_tuProtoNames_of_lookup hlook)
  have hnodup := allTUs_fnNames_nodup
  rw [hsplit, List.flatMap_append, List.flatMap_cons] at hnodup
  have hdisj := (List.nodup_append.mp hnodup).2.2
  have hnot_pre_fn : sym ∉ pre.flatMap tuFnNames :=
    fun hpre => hdisj sym hpre sym (List.mem_append_left _ hmem_fn) rfl
  have hnot_pre : sym ∉ pre.flatMap tuProtoNames := by
    intro hcontra
    simp only [List.mem_flatMap] at hcontra
    rcases hcontra with ⟨p, hp, hpsym⟩
    have hp_all : p ∈ Zlib.allTUs := by rw [hsplit]; exact List.mem_append_left _ hp
    have hp_fn : sym ∈ pre.flatMap tuFnNames :=
      List.mem_flatMap.mpr ⟨p, hp, tuProtoNames_subset_tuFnNames hp_all hpsym⟩
    exact hnot_pre_fn hp_fn
  have hnone_pre : (pre.flatMap tuProtoEntries).lookup sym = none := by
    clear hsplit htu_mem hmem_fn hnodup hdisj hnot_pre_fn
    induction pre with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.flatMap_cons, List.mem_append, not_or] at hnot_pre
      simp only [List.flatMap_cons]
      exact lookup_append_none (tuProtoEntries_none_of_not_mem hnot_pre.1) |>.trans (ih hnot_pre.2)
  rw [lookup_append_none hnone_pre]
  exact lookup_append_some hlook

private theorem tu_protoEntries_eq_map_gzclose :
    tuProtoEntries Zlib.Gzclose.gzcloseTU = (tuFnEntries Zlib.Gzclose.gzcloseTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
private theorem tu_protoEntries_eq_map_uncompr :
    tuProtoEntries Zlib.Uncompr.uncomprTU = (tuFnEntries Zlib.Uncompr.uncomprTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
private theorem tu_protoEntries_eq_map_inftrees :
    tuProtoEntries Zlib.Inftrees.inftreesTU = (tuFnEntries Zlib.Inftrees.inftreesTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
private theorem tu_protoEntries_eq_map_inffast :
    tuProtoEntries Zlib.Inffast.inffastTU = (tuFnEntries Zlib.Inffast.inffastTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
private theorem tu_protoEntries_eq_map_trees :
    tuProtoEntries Zlib.Trees.treesTU = (tuFnEntries Zlib.Trees.treesTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
private theorem tu_protoEntries_eq_map_infback :
    tuProtoEntries Zlib.Infback.infbackTU = (tuFnEntries Zlib.Infback.infbackTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
private theorem tu_protoEntries_eq_map_inflate :
    tuProtoEntries Zlib.Inflate.inflateTU = (tuFnEntries Zlib.Inflate.inflateTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
private theorem tu_protoEntries_eq_map_gzlib :
    tuProtoEntries Zlib.Gzlib.gzlibTU = (tuFnEntries Zlib.Gzlib.gzlibTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
private theorem tu_protoEntries_eq_map_gzread :
    tuProtoEntries Zlib.Gzread.gzreadTU = (tuFnEntries Zlib.Gzread.gzreadTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
private theorem tu_protoEntries_eq_map_gzwrite :
    tuProtoEntries Zlib.Gzwrite.gzwriteTU = (tuFnEntries Zlib.Gzwrite.gzwriteTU).map (fun (n, f) => (n, fnDefSig f)) := rfl
private theorem tu_protoEntries_deflate :
    tuProtoEntries Zlib.Deflate.deflateTU =
      [ ("deflate_stored", fnDefSig Zlib.Deflate.deflateTU_fn_deflate_stored),
        ("deflate_fast", fnDefSig Zlib.Deflate.deflateTU_fn_deflate_fast),
        ("deflate_slow", fnDefSig Zlib.Deflate.deflateTU_fn_deflate_slow),
        ("deflate_rle", fnDefSig Zlib.Deflate.deflateTU_fn_deflate_rle),
        ("deflate_huff", fnDefSig Zlib.Deflate.deflateTU_fn_deflate_huff) ] ++
      (tuFnEntries Zlib.Deflate.deflateTU).map (fun (n, f) => (n, fnDefSig f)) := rfl

private theorem allTUs_split_gzclose :
    Zlib.allTUs = [] ++ Zlib.Gzclose.gzcloseTU ::
      [Zlib.Zutil.zutilTU, Zlib.Adler32.adler32TU, Zlib.Compress.compressTU, Zlib.Uncompr.uncomprTU,
       Zlib.Inftrees.inftreesTU, Zlib.Inffast.inffastTU, Zlib.Crc32.crc32TU, Zlib.Trees.treesTU,
       Zlib.Infback.infbackTU, Zlib.Inflate.inflateTU, Zlib.Deflate.deflateTU, Zlib.Gzlib.gzlibTU,
       Zlib.Gzread.gzreadTU, Zlib.Gzwrite.gzwriteTU] := rfl
private theorem allTUs_split_uncompr :
    Zlib.allTUs = [Zlib.Gzclose.gzcloseTU, Zlib.Zutil.zutilTU, Zlib.Adler32.adler32TU, Zlib.Compress.compressTU] ++
      Zlib.Uncompr.uncomprTU ::
      [Zlib.Inftrees.inftreesTU, Zlib.Inffast.inffastTU, Zlib.Crc32.crc32TU, Zlib.Trees.treesTU,
       Zlib.Infback.infbackTU, Zlib.Inflate.inflateTU, Zlib.Deflate.deflateTU, Zlib.Gzlib.gzlibTU,
       Zlib.Gzread.gzreadTU, Zlib.Gzwrite.gzwriteTU] := rfl
private theorem allTUs_split_inftrees :
    Zlib.allTUs = [Zlib.Gzclose.gzcloseTU, Zlib.Zutil.zutilTU, Zlib.Adler32.adler32TU,
      Zlib.Compress.compressTU, Zlib.Uncompr.uncomprTU] ++
      Zlib.Inftrees.inftreesTU ::
      [Zlib.Inffast.inffastTU, Zlib.Crc32.crc32TU, Zlib.Trees.treesTU,
       Zlib.Infback.infbackTU, Zlib.Inflate.inflateTU, Zlib.Deflate.deflateTU, Zlib.Gzlib.gzlibTU,
       Zlib.Gzread.gzreadTU, Zlib.Gzwrite.gzwriteTU] := rfl
private theorem allTUs_split_inffast :
    Zlib.allTUs = [Zlib.Gzclose.gzcloseTU, Zlib.Zutil.zutilTU, Zlib.Adler32.adler32TU,
      Zlib.Compress.compressTU, Zlib.Uncompr.uncomprTU, Zlib.Inftrees.inftreesTU] ++
      Zlib.Inffast.inffastTU ::
      [Zlib.Crc32.crc32TU, Zlib.Trees.treesTU,
       Zlib.Infback.infbackTU, Zlib.Inflate.inflateTU, Zlib.Deflate.deflateTU, Zlib.Gzlib.gzlibTU,
       Zlib.Gzread.gzreadTU, Zlib.Gzwrite.gzwriteTU] := rfl
private theorem allTUs_split_trees :
    Zlib.allTUs = [Zlib.Gzclose.gzcloseTU, Zlib.Zutil.zutilTU, Zlib.Adler32.adler32TU,
      Zlib.Compress.compressTU, Zlib.Uncompr.uncomprTU, Zlib.Inftrees.inftreesTU,
      Zlib.Inffast.inffastTU, Zlib.Crc32.crc32TU] ++
      Zlib.Trees.treesTU ::
      [Zlib.Infback.infbackTU, Zlib.Inflate.inflateTU, Zlib.Deflate.deflateTU, Zlib.Gzlib.gzlibTU,
       Zlib.Gzread.gzreadTU, Zlib.Gzwrite.gzwriteTU] := rfl
private theorem allTUs_split_infback :
    Zlib.allTUs = [Zlib.Gzclose.gzcloseTU, Zlib.Zutil.zutilTU, Zlib.Adler32.adler32TU,
      Zlib.Compress.compressTU, Zlib.Uncompr.uncomprTU, Zlib.Inftrees.inftreesTU,
      Zlib.Inffast.inffastTU, Zlib.Crc32.crc32TU, Zlib.Trees.treesTU] ++
      Zlib.Infback.infbackTU ::
      [Zlib.Inflate.inflateTU, Zlib.Deflate.deflateTU, Zlib.Gzlib.gzlibTU,
       Zlib.Gzread.gzreadTU, Zlib.Gzwrite.gzwriteTU] := rfl
private theorem allTUs_split_inflate :
    Zlib.allTUs = [Zlib.Gzclose.gzcloseTU, Zlib.Zutil.zutilTU, Zlib.Adler32.adler32TU,
      Zlib.Compress.compressTU, Zlib.Uncompr.uncomprTU, Zlib.Inftrees.inftreesTU,
      Zlib.Inffast.inffastTU, Zlib.Crc32.crc32TU, Zlib.Trees.treesTU, Zlib.Infback.infbackTU] ++
      Zlib.Inflate.inflateTU ::
      [Zlib.Deflate.deflateTU, Zlib.Gzlib.gzlibTU, Zlib.Gzread.gzreadTU, Zlib.Gzwrite.gzwriteTU] := rfl
private theorem allTUs_split_deflate :
    Zlib.allTUs = [Zlib.Gzclose.gzcloseTU, Zlib.Zutil.zutilTU, Zlib.Adler32.adler32TU,
      Zlib.Compress.compressTU, Zlib.Uncompr.uncomprTU, Zlib.Inftrees.inftreesTU,
      Zlib.Inffast.inffastTU, Zlib.Crc32.crc32TU, Zlib.Trees.treesTU, Zlib.Infback.infbackTU,
      Zlib.Inflate.inflateTU] ++
      Zlib.Deflate.deflateTU ::
      [Zlib.Gzlib.gzlibTU, Zlib.Gzread.gzreadTU, Zlib.Gzwrite.gzwriteTU] := rfl
private theorem allTUs_split_gzlib :
    Zlib.allTUs = [Zlib.Gzclose.gzcloseTU, Zlib.Zutil.zutilTU, Zlib.Adler32.adler32TU,
      Zlib.Compress.compressTU, Zlib.Uncompr.uncomprTU, Zlib.Inftrees.inftreesTU,
      Zlib.Inffast.inffastTU, Zlib.Crc32.crc32TU, Zlib.Trees.treesTU, Zlib.Infback.infbackTU,
      Zlib.Inflate.inflateTU, Zlib.Deflate.deflateTU] ++
      Zlib.Gzlib.gzlibTU ::
      [Zlib.Gzread.gzreadTU, Zlib.Gzwrite.gzwriteTU] := rfl
private theorem allTUs_split_gzread :
    Zlib.allTUs = [Zlib.Gzclose.gzcloseTU, Zlib.Zutil.zutilTU, Zlib.Adler32.adler32TU,
      Zlib.Compress.compressTU, Zlib.Uncompr.uncomprTU, Zlib.Inftrees.inftreesTU,
      Zlib.Inffast.inffastTU, Zlib.Crc32.crc32TU, Zlib.Trees.treesTU, Zlib.Infback.infbackTU,
      Zlib.Inflate.inflateTU, Zlib.Deflate.deflateTU, Zlib.Gzlib.gzlibTU] ++
      Zlib.Gzread.gzreadTU ::
      [Zlib.Gzwrite.gzwriteTU] := rfl
private theorem allTUs_split_gzwrite :
    Zlib.allTUs = [Zlib.Gzclose.gzcloseTU, Zlib.Zutil.zutilTU, Zlib.Adler32.adler32TU,
      Zlib.Compress.compressTU, Zlib.Uncompr.uncomprTU, Zlib.Inftrees.inftreesTU,
      Zlib.Inffast.inffastTU, Zlib.Crc32.crc32TU, Zlib.Trees.treesTU, Zlib.Infback.infbackTU,
      Zlib.Inflate.inflateTU, Zlib.Deflate.deflateTU, Zlib.Gzlib.gzlibTU, Zlib.Gzread.gzreadTU] ++
      Zlib.Gzwrite.gzwriteTU :: [] := rfl

/-! ### Exact `prog0.fns` Theorems (134 remaining functions) -/

-- gzclose.c
theorem prog0_fns_gzclose : (progOfTUs Zlib.allFiles).fns "gzclose" = some Zlib.Gzclose.gzcloseTU_fn_gzclose :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzclose rfl (by rw [gzcloseTU_fnEntries]; rfl)

-- uncompr.c
theorem prog0_fns_uncompress2_z : (progOfTUs Zlib.allFiles).fns "uncompress2_z" = some Zlib.Uncompr.uncomprTU_fn_uncompress2_z :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_uncompr rfl (by rw [uncomprTU_fnEntries]; rfl)
theorem prog0_fns_uncompress2 : (progOfTUs Zlib.allFiles).fns "uncompress2" = some Zlib.Uncompr.uncomprTU_fn_uncompress2 :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_uncompr rfl (by rw [uncomprTU_fnEntries]; rfl)
theorem prog0_fns_uncompress_z : (progOfTUs Zlib.allFiles).fns "uncompress_z" = some Zlib.Uncompr.uncomprTU_fn_uncompress_z :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_uncompr rfl (by rw [uncomprTU_fnEntries]; rfl)
theorem prog0_fns_uncompress : (progOfTUs Zlib.allFiles).fns "uncompress" = some Zlib.Uncompr.uncomprTU_fn_uncompress :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_uncompr rfl (by rw [uncomprTU_fnEntries]; rfl)

-- inftrees.c
theorem prog0_fns_inflate_table : (progOfTUs Zlib.allFiles).fns "inflate_table" = some Zlib.Inftrees.inftreesTU_fn_inflate_table :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inftrees rfl (by rw [inftreesTU_fnEntries]; rfl)
theorem prog0_fns_inflate_fixed : (progOfTUs Zlib.allFiles).fns "inflate_fixed" = some Zlib.Inftrees.inftreesTU_fn_inflate_fixed :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inftrees rfl (by rw [inftreesTU_fnEntries]; rfl)

-- inffast.c
theorem prog0_fns_load64 : (progOfTUs Zlib.allFiles).fns "load64" = some Zlib.Inffast.inffastTU_fn_load64 :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inffast rfl (by rw [inffastTU_fnEntries]; rfl)
theorem prog0_fns_copy_back : (progOfTUs Zlib.allFiles).fns "copy_back" = some Zlib.Inffast.inffastTU_fn_copy_back :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inffast rfl (by rw [inffastTU_fnEntries]; rfl)
theorem prog0_fns_inflate_fast : (progOfTUs Zlib.allFiles).fns "inflate_fast" = some Zlib.Inffast.inffastTU_fn_inflate_fast :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inffast rfl (by rw [inffastTU_fnEntries]; rfl)

-- trees.c (21)
theorem prog0_fns_bi_reverse : (progOfTUs Zlib.allFiles).fns "bi_reverse" = some Zlib.Trees.treesTU_fn_bi_reverse :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_bi_flush : (progOfTUs Zlib.allFiles).fns "bi_flush" = some Zlib.Trees.treesTU_fn_bi_flush :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_bi_windup : (progOfTUs Zlib.allFiles).fns "bi_windup" = some Zlib.Trees.treesTU_fn_bi_windup :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_gen_codes : (progOfTUs Zlib.allFiles).fns "gen_codes" = some Zlib.Trees.treesTU_fn_gen_codes :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_tr_static_init : (progOfTUs Zlib.allFiles).fns "tr_static_init" = some Zlib.Trees.treesTU_fn_tr_static_init :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_init_block : (progOfTUs Zlib.allFiles).fns "init_block" = some Zlib.Trees.treesTU_fn_init_block :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns__tr_init : (progOfTUs Zlib.allFiles).fns "_tr_init" = some Zlib.Trees.treesTU_fn__tr_init :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_pqdownheap : (progOfTUs Zlib.allFiles).fns "pqdownheap" = some Zlib.Trees.treesTU_fn_pqdownheap :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_gen_bitlen : (progOfTUs Zlib.allFiles).fns "gen_bitlen" = some Zlib.Trees.treesTU_fn_gen_bitlen :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_build_tree : (progOfTUs Zlib.allFiles).fns "build_tree" = some Zlib.Trees.treesTU_fn_build_tree :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_scan_tree : (progOfTUs Zlib.allFiles).fns "scan_tree" = some Zlib.Trees.treesTU_fn_scan_tree :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_send_tree : (progOfTUs Zlib.allFiles).fns "send_tree" = some Zlib.Trees.treesTU_fn_send_tree :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_build_bl_tree : (progOfTUs Zlib.allFiles).fns "build_bl_tree" = some Zlib.Trees.treesTU_fn_build_bl_tree :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_send_all_trees : (progOfTUs Zlib.allFiles).fns "send_all_trees" = some Zlib.Trees.treesTU_fn_send_all_trees :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns__tr_stored_block : (progOfTUs Zlib.allFiles).fns "_tr_stored_block" = some Zlib.Trees.treesTU_fn__tr_stored_block :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns__tr_flush_bits : (progOfTUs Zlib.allFiles).fns "_tr_flush_bits" = some Zlib.Trees.treesTU_fn__tr_flush_bits :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns__tr_align : (progOfTUs Zlib.allFiles).fns "_tr_align" = some Zlib.Trees.treesTU_fn__tr_align :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_compress_block : (progOfTUs Zlib.allFiles).fns "compress_block" = some Zlib.Trees.treesTU_fn_compress_block :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns_detect_data_type : (progOfTUs Zlib.allFiles).fns "detect_data_type" = some Zlib.Trees.treesTU_fn_detect_data_type :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns__tr_flush_block : (progOfTUs Zlib.allFiles).fns "_tr_flush_block" = some Zlib.Trees.treesTU_fn__tr_flush_block :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)
theorem prog0_fns__tr_tally : (progOfTUs Zlib.allFiles).fns "_tr_tally" = some Zlib.Trees.treesTU_fn__tr_tally :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_trees rfl (by rw [treesTU_fnEntries]; rfl)

-- infback.c (3)
theorem prog0_fns_inflateBackInit_ : (progOfTUs Zlib.allFiles).fns "inflateBackInit_" = some Zlib.Infback.infbackTU_fn_inflateBackInit_ :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_infback rfl (by rw [infbackTU_fnEntries]; rfl)
theorem prog0_fns_inflateBack : (progOfTUs Zlib.allFiles).fns "inflateBack" = some Zlib.Infback.infbackTU_fn_inflateBack :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_infback rfl (by rw [infbackTU_fnEntries]; rfl)
theorem prog0_fns_inflateBackEnd : (progOfTUs Zlib.allFiles).fns "inflateBackEnd" = some Zlib.Infback.infbackTU_fn_inflateBackEnd :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_infback rfl (by rw [infbackTU_fnEntries]; rfl)

-- inflate.c (21)
theorem prog0_fns_inflateStateCheck : (progOfTUs Zlib.allFiles).fns "inflateStateCheck" = some Zlib.Inflate.inflateTU_fn_inflateStateCheck :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateResetKeep : (progOfTUs Zlib.allFiles).fns "inflateResetKeep" = some Zlib.Inflate.inflateTU_fn_inflateResetKeep :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateReset : (progOfTUs Zlib.allFiles).fns "inflateReset" = some Zlib.Inflate.inflateTU_fn_inflateReset :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateReset2 : (progOfTUs Zlib.allFiles).fns "inflateReset2" = some Zlib.Inflate.inflateTU_fn_inflateReset2 :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateInit2_ : (progOfTUs Zlib.allFiles).fns "inflateInit2_" = some Zlib.Inflate.inflateTU_fn_inflateInit2_ :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateInit_ : (progOfTUs Zlib.allFiles).fns "inflateInit_" = some Zlib.Inflate.inflateTU_fn_inflateInit_ :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflatePrime : (progOfTUs Zlib.allFiles).fns "inflatePrime" = some Zlib.Inflate.inflateTU_fn_inflatePrime :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_updatewindow : (progOfTUs Zlib.allFiles).fns "updatewindow" = some Zlib.Inflate.inflateTU_fn_updatewindow :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflate : (progOfTUs Zlib.allFiles).fns "inflate" = some Zlib.Inflate.inflateTU_fn_inflate :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateEnd : (progOfTUs Zlib.allFiles).fns "inflateEnd" = some Zlib.Inflate.inflateTU_fn_inflateEnd :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateGetDictionary : (progOfTUs Zlib.allFiles).fns "inflateGetDictionary" = some Zlib.Inflate.inflateTU_fn_inflateGetDictionary :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateSetDictionary : (progOfTUs Zlib.allFiles).fns "inflateSetDictionary" = some Zlib.Inflate.inflateTU_fn_inflateSetDictionary :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateGetHeader : (progOfTUs Zlib.allFiles).fns "inflateGetHeader" = some Zlib.Inflate.inflateTU_fn_inflateGetHeader :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_syncsearch : (progOfTUs Zlib.allFiles).fns "syncsearch" = some Zlib.Inflate.inflateTU_fn_syncsearch :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateSync : (progOfTUs Zlib.allFiles).fns "inflateSync" = some Zlib.Inflate.inflateTU_fn_inflateSync :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateSyncPoint : (progOfTUs Zlib.allFiles).fns "inflateSyncPoint" = some Zlib.Inflate.inflateTU_fn_inflateSyncPoint :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateCopy : (progOfTUs Zlib.allFiles).fns "inflateCopy" = some Zlib.Inflate.inflateTU_fn_inflateCopy :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateUndermine : (progOfTUs Zlib.allFiles).fns "inflateUndermine" = some Zlib.Inflate.inflateTU_fn_inflateUndermine :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateValidate : (progOfTUs Zlib.allFiles).fns "inflateValidate" = some Zlib.Inflate.inflateTU_fn_inflateValidate :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateMark : (progOfTUs Zlib.allFiles).fns "inflateMark" = some Zlib.Inflate.inflateTU_fn_inflateMark :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)
theorem prog0_fns_inflateCodesUsed : (progOfTUs Zlib.allFiles).fns "inflateCodesUsed" = some Zlib.Inflate.inflateTU_fn_inflateCodesUsed :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_inflate rfl (by rw [inflateTU_fnEntries]; rfl)

-- deflate.c (30)
theorem prog0_fns_slide_hash : (progOfTUs Zlib.allFiles).fns "slide_hash" = some Zlib.Deflate.deflateTU_fn_slide_hash :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_read_buf : (progOfTUs Zlib.allFiles).fns "read_buf" = some Zlib.Deflate.deflateTU_fn_read_buf :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_fill_window : (progOfTUs Zlib.allFiles).fns "fill_window" = some Zlib.Deflate.deflateTU_fn_fill_window :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateInit_ : (progOfTUs Zlib.allFiles).fns "deflateInit_" = some Zlib.Deflate.deflateTU_fn_deflateInit_ :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateInit2_ : (progOfTUs Zlib.allFiles).fns "deflateInit2_" = some Zlib.Deflate.deflateTU_fn_deflateInit2_ :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateStateCheck : (progOfTUs Zlib.allFiles).fns "deflateStateCheck" = some Zlib.Deflate.deflateTU_fn_deflateStateCheck :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateSetDictionary : (progOfTUs Zlib.allFiles).fns "deflateSetDictionary" = some Zlib.Deflate.deflateTU_fn_deflateSetDictionary :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateGetDictionary : (progOfTUs Zlib.allFiles).fns "deflateGetDictionary" = some Zlib.Deflate.deflateTU_fn_deflateGetDictionary :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateResetKeep : (progOfTUs Zlib.allFiles).fns "deflateResetKeep" = some Zlib.Deflate.deflateTU_fn_deflateResetKeep :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_lm_init : (progOfTUs Zlib.allFiles).fns "lm_init" = some Zlib.Deflate.deflateTU_fn_lm_init :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateReset : (progOfTUs Zlib.allFiles).fns "deflateReset" = some Zlib.Deflate.deflateTU_fn_deflateReset :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateSetHeader : (progOfTUs Zlib.allFiles).fns "deflateSetHeader" = some Zlib.Deflate.deflateTU_fn_deflateSetHeader :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflatePending : (progOfTUs Zlib.allFiles).fns "deflatePending" = some Zlib.Deflate.deflateTU_fn_deflatePending :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateUsed : (progOfTUs Zlib.allFiles).fns "deflateUsed" = some Zlib.Deflate.deflateTU_fn_deflateUsed :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflatePrime : (progOfTUs Zlib.allFiles).fns "deflatePrime" = some Zlib.Deflate.deflateTU_fn_deflatePrime :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateParams : (progOfTUs Zlib.allFiles).fns "deflateParams" = some Zlib.Deflate.deflateTU_fn_deflateParams :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateTune : (progOfTUs Zlib.allFiles).fns "deflateTune" = some Zlib.Deflate.deflateTU_fn_deflateTune :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateBound_z : (progOfTUs Zlib.allFiles).fns "deflateBound_z" = some Zlib.Deflate.deflateTU_fn_deflateBound_z :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateBound : (progOfTUs Zlib.allFiles).fns "deflateBound" = some Zlib.Deflate.deflateTU_fn_deflateBound :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_putShortMSB : (progOfTUs Zlib.allFiles).fns "putShortMSB" = some Zlib.Deflate.deflateTU_fn_putShortMSB :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_flush_pending : (progOfTUs Zlib.allFiles).fns "flush_pending" = some Zlib.Deflate.deflateTU_fn_flush_pending :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflate : (progOfTUs Zlib.allFiles).fns "deflate" = some Zlib.Deflate.deflateTU_fn_deflate :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateEnd : (progOfTUs Zlib.allFiles).fns "deflateEnd" = some Zlib.Deflate.deflateTU_fn_deflateEnd :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflateCopy : (progOfTUs Zlib.allFiles).fns "deflateCopy" = some Zlib.Deflate.deflateTU_fn_deflateCopy :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_longest_match : (progOfTUs Zlib.allFiles).fns "longest_match" = some Zlib.Deflate.deflateTU_fn_longest_match :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflate_stored : (progOfTUs Zlib.allFiles).fns "deflate_stored" = some Zlib.Deflate.deflateTU_fn_deflate_stored :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflate_fast : (progOfTUs Zlib.allFiles).fns "deflate_fast" = some Zlib.Deflate.deflateTU_fn_deflate_fast :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflate_slow : (progOfTUs Zlib.allFiles).fns "deflate_slow" = some Zlib.Deflate.deflateTU_fn_deflate_slow :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflate_rle : (progOfTUs Zlib.allFiles).fns "deflate_rle" = some Zlib.Deflate.deflateTU_fn_deflate_rle :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)
theorem prog0_fns_deflate_huff : (progOfTUs Zlib.allFiles).fns "deflate_huff" = some Zlib.Deflate.deflateTU_fn_deflate_huff :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_deflate rfl (by rw [deflateTU_fnEntries]; rfl)

-- gzlib.c (18)
theorem prog0_fns_gz_reset : (progOfTUs Zlib.allFiles).fns "gz_reset" = some Zlib.Gzlib.gzlibTU_fn_gz_reset :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gz_open : (progOfTUs Zlib.allFiles).fns "gz_open" = some Zlib.Gzlib.gzlibTU_fn_gz_open :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzopen : (progOfTUs Zlib.allFiles).fns "gzopen" = some Zlib.Gzlib.gzlibTU_fn_gzopen :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzopen64 : (progOfTUs Zlib.allFiles).fns "gzopen64" = some Zlib.Gzlib.gzlibTU_fn_gzopen64 :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzdopen : (progOfTUs Zlib.allFiles).fns "gzdopen" = some Zlib.Gzlib.gzlibTU_fn_gzdopen :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzbuffer : (progOfTUs Zlib.allFiles).fns "gzbuffer" = some Zlib.Gzlib.gzlibTU_fn_gzbuffer :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzrewind : (progOfTUs Zlib.allFiles).fns "gzrewind" = some Zlib.Gzlib.gzlibTU_fn_gzrewind :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzseek64 : (progOfTUs Zlib.allFiles).fns "gzseek64" = some Zlib.Gzlib.gzlibTU_fn_gzseek64 :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzseek : (progOfTUs Zlib.allFiles).fns "gzseek" = some Zlib.Gzlib.gzlibTU_fn_gzseek :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gztell64 : (progOfTUs Zlib.allFiles).fns "gztell64" = some Zlib.Gzlib.gzlibTU_fn_gztell64 :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gztell : (progOfTUs Zlib.allFiles).fns "gztell" = some Zlib.Gzlib.gzlibTU_fn_gztell :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzoffset64 : (progOfTUs Zlib.allFiles).fns "gzoffset64" = some Zlib.Gzlib.gzlibTU_fn_gzoffset64 :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzoffset : (progOfTUs Zlib.allFiles).fns "gzoffset" = some Zlib.Gzlib.gzlibTU_fn_gzoffset :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzeof : (progOfTUs Zlib.allFiles).fns "gzeof" = some Zlib.Gzlib.gzlibTU_fn_gzeof :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzerror : (progOfTUs Zlib.allFiles).fns "gzerror" = some Zlib.Gzlib.gzlibTU_fn_gzerror :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gzclearerr : (progOfTUs Zlib.allFiles).fns "gzclearerr" = some Zlib.Gzlib.gzlibTU_fn_gzclearerr :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gz_error : (progOfTUs Zlib.allFiles).fns "gz_error" = some Zlib.Gzlib.gzlibTU_fn_gz_error :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)
theorem prog0_fns_gz_intmax : (progOfTUs Zlib.allFiles).fns "gz_intmax" = some Zlib.Gzlib.gzlibTU_fn_gz_intmax :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzlib rfl (by rw [gzlibTU_fnEntries]; rfl)

-- gzread.c (17)
theorem prog0_fns_gz_load : (progOfTUs Zlib.allFiles).fns "gz_load" = some Zlib.Gzread.gzreadTU_fn_gz_load :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gz_avail : (progOfTUs Zlib.allFiles).fns "gz_avail" = some Zlib.Gzread.gzreadTU_fn_gz_avail :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gz_room : (progOfTUs Zlib.allFiles).fns "gz_room" = some Zlib.Gzread.gzreadTU_fn_gz_room :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gz_look : (progOfTUs Zlib.allFiles).fns "gz_look" = some Zlib.Gzread.gzreadTU_fn_gz_look :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gz_decomp : (progOfTUs Zlib.allFiles).fns "gz_decomp" = some Zlib.Gzread.gzreadTU_fn_gz_decomp :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gz_fetch : (progOfTUs Zlib.allFiles).fns "gz_fetch" = some Zlib.Gzread.gzreadTU_fn_gz_fetch :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gz_skip_have : (progOfTUs Zlib.allFiles).fns "gz_skip_have" = some Zlib.Gzread.gzreadTU_fn_gz_skip_have :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gz_skip : (progOfTUs Zlib.allFiles).fns "gz_skip" = some Zlib.Gzread.gzreadTU_fn_gz_skip :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gz_read : (progOfTUs Zlib.allFiles).fns "gz_read" = some Zlib.Gzread.gzreadTU_fn_gz_read :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gzread : (progOfTUs Zlib.allFiles).fns "gzread" = some Zlib.Gzread.gzreadTU_fn_gzread :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gzfread : (progOfTUs Zlib.allFiles).fns "gzfread" = some Zlib.Gzread.gzreadTU_fn_gzfread :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gzgetc : (progOfTUs Zlib.allFiles).fns "gzgetc" = some Zlib.Gzread.gzreadTU_fn_gzgetc :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gzgetc_ : (progOfTUs Zlib.allFiles).fns "gzgetc_" = some Zlib.Gzread.gzreadTU_fn_gzgetc_ :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gzungetc : (progOfTUs Zlib.allFiles).fns "gzungetc" = some Zlib.Gzread.gzreadTU_fn_gzungetc :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gzgets : (progOfTUs Zlib.allFiles).fns "gzgets" = some Zlib.Gzread.gzreadTU_fn_gzgets :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gzdirect : (progOfTUs Zlib.allFiles).fns "gzdirect" = some Zlib.Gzread.gzreadTU_fn_gzdirect :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)
theorem prog0_fns_gzclose_r : (progOfTUs Zlib.allFiles).fns "gzclose_r" = some Zlib.Gzread.gzreadTU_fn_gzclose_r :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzread rfl (by rw [gzreadTU_fnEntries]; rfl)

-- gzwrite.c (14)
theorem prog0_fns_gz_init : (progOfTUs Zlib.allFiles).fns "gz_init" = some Zlib.Gzwrite.gzwriteTU_fn_gz_init :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gz_comp : (progOfTUs Zlib.allFiles).fns "gz_comp" = some Zlib.Gzwrite.gzwriteTU_fn_gz_comp :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gz_zero : (progOfTUs Zlib.allFiles).fns "gz_zero" = some Zlib.Gzwrite.gzwriteTU_fn_gz_zero :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gz_write : (progOfTUs Zlib.allFiles).fns "gz_write" = some Zlib.Gzwrite.gzwriteTU_fn_gz_write :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gzwrite : (progOfTUs Zlib.allFiles).fns "gzwrite" = some Zlib.Gzwrite.gzwriteTU_fn_gzwrite :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gzfwrite : (progOfTUs Zlib.allFiles).fns "gzfwrite" = some Zlib.Gzwrite.gzwriteTU_fn_gzfwrite :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gzputc : (progOfTUs Zlib.allFiles).fns "gzputc" = some Zlib.Gzwrite.gzwriteTU_fn_gzputc :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gzputs : (progOfTUs Zlib.allFiles).fns "gzputs" = some Zlib.Gzwrite.gzwriteTU_fn_gzputs :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gz_vacate : (progOfTUs Zlib.allFiles).fns "gz_vacate" = some Zlib.Gzwrite.gzwriteTU_fn_gz_vacate :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gzvprintf : (progOfTUs Zlib.allFiles).fns "gzvprintf" = some Zlib.Gzwrite.gzwriteTU_fn_gzvprintf :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gzprintf : (progOfTUs Zlib.allFiles).fns "gzprintf" = some Zlib.Gzwrite.gzwriteTU_fn_gzprintf :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gzflush : (progOfTUs Zlib.allFiles).fns "gzflush" = some Zlib.Gzwrite.gzwriteTU_fn_gzflush :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gzsetparams : (progOfTUs Zlib.allFiles).fns "gzsetparams" = some Zlib.Gzwrite.gzwriteTU_fn_gzsetparams :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)
theorem prog0_fns_gzclose_w : (progOfTUs Zlib.allFiles).fns "gzclose_w" = some Zlib.Gzwrite.gzwriteTU_fn_gzclose_w :=
  flatMap_fnEntries_lookup_of_tu_mem allTUs_split_gzwrite rfl (by rw [gzwriteTU_fnEntries]; rfl)

/-! ### Exact `prog0.fnProtos` Theorems (134 remaining functions) -/

-- gzclose.c
theorem prog0_fnProtos_gzclose : (progOfTUs Zlib.allFiles).fnProtos "gzclose" = some (fnDefSig Zlib.Gzclose.gzcloseTU_fn_gzclose) :=
  tu_protoEntries_of_mem allTUs_split_gzclose (by rfl) (by rw [tu_protoEntries_eq_map_gzclose, gzcloseTU_fnEntries]; rfl)

-- uncompr.c
theorem prog0_fnProtos_uncompress2_z : (progOfTUs Zlib.allFiles).fnProtos "uncompress2_z" = some (fnDefSig Zlib.Uncompr.uncomprTU_fn_uncompress2_z) :=
  tu_protoEntries_of_mem allTUs_split_uncompr (by rfl) (by rw [tu_protoEntries_eq_map_uncompr, uncomprTU_fnEntries]; rfl)
theorem prog0_fnProtos_uncompress2 : (progOfTUs Zlib.allFiles).fnProtos "uncompress2" = some (fnDefSig Zlib.Uncompr.uncomprTU_fn_uncompress2) :=
  tu_protoEntries_of_mem allTUs_split_uncompr (by rfl) (by rw [tu_protoEntries_eq_map_uncompr, uncomprTU_fnEntries]; rfl)
theorem prog0_fnProtos_uncompress_z : (progOfTUs Zlib.allFiles).fnProtos "uncompress_z" = some (fnDefSig Zlib.Uncompr.uncomprTU_fn_uncompress_z) :=
  tu_protoEntries_of_mem allTUs_split_uncompr (by rfl) (by rw [tu_protoEntries_eq_map_uncompr, uncomprTU_fnEntries]; rfl)
theorem prog0_fnProtos_uncompress : (progOfTUs Zlib.allFiles).fnProtos "uncompress" = some (fnDefSig Zlib.Uncompr.uncomprTU_fn_uncompress) :=
  tu_protoEntries_of_mem allTUs_split_uncompr (by rfl) (by rw [tu_protoEntries_eq_map_uncompr, uncomprTU_fnEntries]; rfl)

-- inftrees.c
theorem prog0_fnProtos_inflate_table : (progOfTUs Zlib.allFiles).fnProtos "inflate_table" = some (fnDefSig Zlib.Inftrees.inftreesTU_fn_inflate_table) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_inflate_fixed : (progOfTUs Zlib.allFiles).fnProtos "inflate_fixed" = some (fnDefSig Zlib.Inftrees.inftreesTU_fn_inflate_fixed) :=
  allHeaders_protoEntries_lookup_some (by rfl)

-- inffast.c
theorem prog0_fnProtos_load64 : (progOfTUs Zlib.allFiles).fnProtos "load64" = some (fnDefSig Zlib.Inffast.inffastTU_fn_load64) :=
  tu_protoEntries_of_mem allTUs_split_inffast (by rfl) (by rw [tu_protoEntries_eq_map_inffast, inffastTU_fnEntries]; rfl)
theorem prog0_fnProtos_copy_back : (progOfTUs Zlib.allFiles).fnProtos "copy_back" = some (fnDefSig Zlib.Inffast.inffastTU_fn_copy_back) :=
  tu_protoEntries_of_mem allTUs_split_inffast (by rfl) (by rw [tu_protoEntries_eq_map_inffast, inffastTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflate_fast : (progOfTUs Zlib.allFiles).fnProtos "inflate_fast" = some (fnDefSig Zlib.Inffast.inffastTU_fn_inflate_fast) :=
  allHeaders_protoEntries_lookup_some (by rfl)

-- trees.c
theorem prog0_fnProtos_bi_reverse : (progOfTUs Zlib.allFiles).fnProtos "bi_reverse" = some (fnDefSig Zlib.Trees.treesTU_fn_bi_reverse) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_bi_flush : (progOfTUs Zlib.allFiles).fnProtos "bi_flush" = some (fnDefSig Zlib.Trees.treesTU_fn_bi_flush) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_bi_windup : (progOfTUs Zlib.allFiles).fnProtos "bi_windup" = some (fnDefSig Zlib.Trees.treesTU_fn_bi_windup) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_gen_codes : (progOfTUs Zlib.allFiles).fnProtos "gen_codes" = some (fnDefSig Zlib.Trees.treesTU_fn_gen_codes) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_tr_static_init : (progOfTUs Zlib.allFiles).fnProtos "tr_static_init" = some (fnDefSig Zlib.Trees.treesTU_fn_tr_static_init) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_init_block : (progOfTUs Zlib.allFiles).fnProtos "init_block" = some (fnDefSig Zlib.Trees.treesTU_fn_init_block) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos__tr_init : (progOfTUs Zlib.allFiles).fnProtos "_tr_init" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_init) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_pqdownheap : (progOfTUs Zlib.allFiles).fnProtos "pqdownheap" = some (fnDefSig Zlib.Trees.treesTU_fn_pqdownheap) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_gen_bitlen : (progOfTUs Zlib.allFiles).fnProtos "gen_bitlen" = some (fnDefSig Zlib.Trees.treesTU_fn_gen_bitlen) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_build_tree : (progOfTUs Zlib.allFiles).fnProtos "build_tree" = some (fnDefSig Zlib.Trees.treesTU_fn_build_tree) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_scan_tree : (progOfTUs Zlib.allFiles).fnProtos "scan_tree" = some (fnDefSig Zlib.Trees.treesTU_fn_scan_tree) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_send_tree : (progOfTUs Zlib.allFiles).fnProtos "send_tree" = some (fnDefSig Zlib.Trees.treesTU_fn_send_tree) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_build_bl_tree : (progOfTUs Zlib.allFiles).fnProtos "build_bl_tree" = some (fnDefSig Zlib.Trees.treesTU_fn_build_bl_tree) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_send_all_trees : (progOfTUs Zlib.allFiles).fnProtos "send_all_trees" = some (fnDefSig Zlib.Trees.treesTU_fn_send_all_trees) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos__tr_stored_block : (progOfTUs Zlib.allFiles).fnProtos "_tr_stored_block" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_stored_block) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos__tr_flush_bits : (progOfTUs Zlib.allFiles).fnProtos "_tr_flush_bits" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_flush_bits) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos__tr_align : (progOfTUs Zlib.allFiles).fnProtos "_tr_align" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_align) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_compress_block : (progOfTUs Zlib.allFiles).fnProtos "compress_block" = some (fnDefSig Zlib.Trees.treesTU_fn_compress_block) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos_detect_data_type : (progOfTUs Zlib.allFiles).fnProtos "detect_data_type" = some (fnDefSig Zlib.Trees.treesTU_fn_detect_data_type) :=
  tu_protoEntries_of_mem allTUs_split_trees (by rfl) (by rw [tu_protoEntries_eq_map_trees, treesTU_fnEntries]; rfl)
theorem prog0_fnProtos__tr_flush_block : (progOfTUs Zlib.allFiles).fnProtos "_tr_flush_block" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_flush_block) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos__tr_tally : (progOfTUs Zlib.allFiles).fnProtos "_tr_tally" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_tally) :=
  allHeaders_protoEntries_lookup_some (by rfl)

-- infback.c
theorem prog0_fnProtos_inflateBackInit_ : (progOfTUs Zlib.allFiles).fnProtos "inflateBackInit_" = some (fnDefSig Zlib.Infback.infbackTU_fn_inflateBackInit_) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_inflateBack : (progOfTUs Zlib.allFiles).fnProtos "inflateBack" = some (fnDefSig Zlib.Infback.infbackTU_fn_inflateBack) :=
  tu_protoEntries_of_mem allTUs_split_infback (by rfl) (by rw [tu_protoEntries_eq_map_infback, infbackTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflateBackEnd : (progOfTUs Zlib.allFiles).fnProtos "inflateBackEnd" = some (fnDefSig Zlib.Infback.infbackTU_fn_inflateBackEnd) :=
  tu_protoEntries_of_mem allTUs_split_infback (by rfl) (by rw [tu_protoEntries_eq_map_infback, infbackTU_fnEntries]; rfl)

-- inflate.c
theorem prog0_fnProtos_inflateStateCheck : (progOfTUs Zlib.allFiles).fnProtos "inflateStateCheck" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateStateCheck) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflateResetKeep : (progOfTUs Zlib.allFiles).fnProtos "inflateResetKeep" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateResetKeep) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_inflateReset : (progOfTUs Zlib.allFiles).fnProtos "inflateReset" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateReset) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_inflateReset2 : (progOfTUs Zlib.allFiles).fnProtos "inflateReset2" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateReset2) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_inflateInit2_ : (progOfTUs Zlib.allFiles).fnProtos "inflateInit2_" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateInit2_) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_inflateInit_ : (progOfTUs Zlib.allFiles).fnProtos "inflateInit_" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateInit_) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_inflatePrime : (progOfTUs Zlib.allFiles).fnProtos "inflatePrime" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflatePrime) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_updatewindow : (progOfTUs Zlib.allFiles).fnProtos "updatewindow" = some (fnDefSig Zlib.Inflate.inflateTU_fn_updatewindow) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflate : (progOfTUs Zlib.allFiles).fnProtos "inflate" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflate) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_inflateEnd : (progOfTUs Zlib.allFiles).fnProtos "inflateEnd" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateEnd) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_inflateGetDictionary : (progOfTUs Zlib.allFiles).fnProtos "inflateGetDictionary" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateGetDictionary) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflateSetDictionary : (progOfTUs Zlib.allFiles).fnProtos "inflateSetDictionary" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateSetDictionary) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflateGetHeader : (progOfTUs Zlib.allFiles).fnProtos "inflateGetHeader" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateGetHeader) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_syncsearch : (progOfTUs Zlib.allFiles).fnProtos "syncsearch" = some (fnDefSig Zlib.Inflate.inflateTU_fn_syncsearch) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflateSync : (progOfTUs Zlib.allFiles).fnProtos "inflateSync" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateSync) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflateSyncPoint : (progOfTUs Zlib.allFiles).fnProtos "inflateSyncPoint" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateSyncPoint) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflateCopy : (progOfTUs Zlib.allFiles).fnProtos "inflateCopy" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateCopy) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_inflateUndermine : (progOfTUs Zlib.allFiles).fnProtos "inflateUndermine" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateUndermine) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflateValidate : (progOfTUs Zlib.allFiles).fnProtos "inflateValidate" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateValidate) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflateMark : (progOfTUs Zlib.allFiles).fnProtos "inflateMark" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateMark) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_inflateCodesUsed : (progOfTUs Zlib.allFiles).fnProtos "inflateCodesUsed" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateCodesUsed) :=
  tu_protoEntries_of_mem allTUs_split_inflate (by rfl) (by rw [tu_protoEntries_eq_map_inflate, inflateTU_fnEntries]; rfl)

-- deflate.c
theorem prog0_fnProtos_slide_hash : (progOfTUs Zlib.allFiles).fnProtos "slide_hash" = some (fnDefSig Zlib.Deflate.deflateTU_fn_slide_hash) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_read_buf : (progOfTUs Zlib.allFiles).fnProtos "read_buf" = some (fnDefSig Zlib.Deflate.deflateTU_fn_read_buf) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_fill_window : (progOfTUs Zlib.allFiles).fnProtos "fill_window" = some (fnDefSig Zlib.Deflate.deflateTU_fn_fill_window) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflateInit_ : (progOfTUs Zlib.allFiles).fnProtos "deflateInit_" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateInit_) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_deflateInit2_ : (progOfTUs Zlib.allFiles).fnProtos "deflateInit2_" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateInit2_) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_deflateStateCheck : (progOfTUs Zlib.allFiles).fnProtos "deflateStateCheck" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateStateCheck) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflateSetDictionary : (progOfTUs Zlib.allFiles).fnProtos "deflateSetDictionary" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateSetDictionary) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflateGetDictionary : (progOfTUs Zlib.allFiles).fnProtos "deflateGetDictionary" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateGetDictionary) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflateResetKeep : (progOfTUs Zlib.allFiles).fnProtos "deflateResetKeep" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateResetKeep) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_lm_init : (progOfTUs Zlib.allFiles).fnProtos "lm_init" = some (fnDefSig Zlib.Deflate.deflateTU_fn_lm_init) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflateReset : (progOfTUs Zlib.allFiles).fnProtos "deflateReset" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateReset) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_deflateSetHeader : (progOfTUs Zlib.allFiles).fnProtos "deflateSetHeader" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateSetHeader) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflatePending : (progOfTUs Zlib.allFiles).fnProtos "deflatePending" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflatePending) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflateUsed : (progOfTUs Zlib.allFiles).fnProtos "deflateUsed" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateUsed) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflatePrime : (progOfTUs Zlib.allFiles).fnProtos "deflatePrime" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflatePrime) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflateParams : (progOfTUs Zlib.allFiles).fnProtos "deflateParams" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateParams) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_deflateTune : (progOfTUs Zlib.allFiles).fnProtos "deflateTune" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateTune) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflateBound_z : (progOfTUs Zlib.allFiles).fnProtos "deflateBound_z" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateBound_z) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_deflateBound : (progOfTUs Zlib.allFiles).fnProtos "deflateBound" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateBound) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_putShortMSB : (progOfTUs Zlib.allFiles).fnProtos "putShortMSB" = some (fnDefSig Zlib.Deflate.deflateTU_fn_putShortMSB) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_flush_pending : (progOfTUs Zlib.allFiles).fnProtos "flush_pending" = some (fnDefSig Zlib.Deflate.deflateTU_fn_flush_pending) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflate : (progOfTUs Zlib.allFiles).fnProtos "deflate" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_deflateEnd : (progOfTUs Zlib.allFiles).fnProtos "deflateEnd" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateEnd) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_deflateCopy : (progOfTUs Zlib.allFiles).fnProtos "deflateCopy" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateCopy) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_longest_match : (progOfTUs Zlib.allFiles).fnProtos "longest_match" = some (fnDefSig Zlib.Deflate.deflateTU_fn_longest_match) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate, deflateTU_fnEntries]; rfl)
theorem prog0_fnProtos_deflate_stored : (progOfTUs Zlib.allFiles).fnProtos "deflate_stored" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate_stored) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate]; rfl)
theorem prog0_fnProtos_deflate_fast : (progOfTUs Zlib.allFiles).fnProtos "deflate_fast" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate_fast) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate]; rfl)
theorem prog0_fnProtos_deflate_slow : (progOfTUs Zlib.allFiles).fnProtos "deflate_slow" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate_slow) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate]; rfl)
theorem prog0_fnProtos_deflate_rle : (progOfTUs Zlib.allFiles).fnProtos "deflate_rle" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate_rle) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate]; rfl)
theorem prog0_fnProtos_deflate_huff : (progOfTUs Zlib.allFiles).fnProtos "deflate_huff" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate_huff) :=
  tu_protoEntries_of_mem allTUs_split_deflate (by rfl) (by rw [tu_protoEntries_deflate]; rfl)

-- gzlib.c
theorem prog0_fnProtos_gz_reset : (progOfTUs Zlib.allFiles).fnProtos "gz_reset" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gz_reset) :=
  tu_protoEntries_of_mem allTUs_split_gzlib (by rfl) (by rw [tu_protoEntries_eq_map_gzlib, gzlibTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_open : (progOfTUs Zlib.allFiles).fnProtos "gz_open" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gz_open) :=
  tu_protoEntries_of_mem allTUs_split_gzlib (by rfl) (by rw [tu_protoEntries_eq_map_gzlib, gzlibTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzopen : (progOfTUs Zlib.allFiles).fnProtos "gzopen" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzopen) :=
  tu_protoEntries_of_mem allTUs_split_gzlib (by rfl) (by rw [tu_protoEntries_eq_map_gzlib, gzlibTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzopen64 : (progOfTUs Zlib.allFiles).fnProtos "gzopen64" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzopen64) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_gzdopen : (progOfTUs Zlib.allFiles).fnProtos "gzdopen" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzdopen) :=
  tu_protoEntries_of_mem allTUs_split_gzlib (by rfl) (by rw [tu_protoEntries_eq_map_gzlib, gzlibTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzbuffer : (progOfTUs Zlib.allFiles).fnProtos "gzbuffer" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzbuffer) :=
  tu_protoEntries_of_mem allTUs_split_gzlib (by rfl) (by rw [tu_protoEntries_eq_map_gzlib, gzlibTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzrewind : (progOfTUs Zlib.allFiles).fnProtos "gzrewind" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzrewind) :=
  tu_protoEntries_of_mem allTUs_split_gzlib (by rfl) (by rw [tu_protoEntries_eq_map_gzlib, gzlibTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzseek64 : (progOfTUs Zlib.allFiles).fnProtos "gzseek64" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzseek64) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_gzseek : (progOfTUs Zlib.allFiles).fnProtos "gzseek" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzseek) :=
  tu_protoEntries_of_mem allTUs_split_gzlib (by rfl) (by rw [tu_protoEntries_eq_map_gzlib, gzlibTU_fnEntries]; rfl)
theorem prog0_fnProtos_gztell64 : (progOfTUs Zlib.allFiles).fnProtos "gztell64" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gztell64) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_gztell : (progOfTUs Zlib.allFiles).fnProtos "gztell" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gztell) :=
  tu_protoEntries_of_mem allTUs_split_gzlib (by rfl) (by rw [tu_protoEntries_eq_map_gzlib, gzlibTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzoffset64 : (progOfTUs Zlib.allFiles).fnProtos "gzoffset64" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzoffset64) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_gzoffset : (progOfTUs Zlib.allFiles).fnProtos "gzoffset" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzoffset) :=
  tu_protoEntries_of_mem allTUs_split_gzlib (by rfl) (by rw [tu_protoEntries_eq_map_gzlib, gzlibTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzeof : (progOfTUs Zlib.allFiles).fnProtos "gzeof" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzeof) :=
  tu_protoEntries_of_mem allTUs_split_gzlib (by rfl) (by rw [tu_protoEntries_eq_map_gzlib, gzlibTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzerror : (progOfTUs Zlib.allFiles).fnProtos "gzerror" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzerror) :=
  tu_protoEntries_of_mem allTUs_split_gzlib (by rfl) (by rw [tu_protoEntries_eq_map_gzlib, gzlibTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzclearerr : (progOfTUs Zlib.allFiles).fnProtos "gzclearerr" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzclearerr) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_gz_error : (progOfTUs Zlib.allFiles).fnProtos "gz_error" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gz_error) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_gz_intmax : (progOfTUs Zlib.allFiles).fnProtos "gz_intmax" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gz_intmax) :=
  allHeaders_protoEntries_lookup_some (by rfl)

-- gzread.c
theorem prog0_fnProtos_gz_load : (progOfTUs Zlib.allFiles).fnProtos "gz_load" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_load) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_avail : (progOfTUs Zlib.allFiles).fnProtos "gz_avail" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_avail) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_room : (progOfTUs Zlib.allFiles).fnProtos "gz_room" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_room) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_look : (progOfTUs Zlib.allFiles).fnProtos "gz_look" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_look) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_decomp : (progOfTUs Zlib.allFiles).fnProtos "gz_decomp" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_decomp) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_fetch : (progOfTUs Zlib.allFiles).fnProtos "gz_fetch" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_fetch) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_skip_have : (progOfTUs Zlib.allFiles).fnProtos "gz_skip_have" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_skip_have) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_skip : (progOfTUs Zlib.allFiles).fnProtos "gz_skip" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_skip) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_read : (progOfTUs Zlib.allFiles).fnProtos "gz_read" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_read) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzread : (progOfTUs Zlib.allFiles).fnProtos "gzread" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzread) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_gzfread : (progOfTUs Zlib.allFiles).fnProtos "gzfread" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzfread) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzgetc : (progOfTUs Zlib.allFiles).fnProtos "gzgetc" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzgetc) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzgetc_ : (progOfTUs Zlib.allFiles).fnProtos "gzgetc_" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzgetc_) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzungetc : (progOfTUs Zlib.allFiles).fnProtos "gzungetc" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzungetc) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzgets : (progOfTUs Zlib.allFiles).fnProtos "gzgets" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzgets) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzdirect : (progOfTUs Zlib.allFiles).fnProtos "gzdirect" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzdirect) :=
  tu_protoEntries_of_mem allTUs_split_gzread (by rfl) (by rw [tu_protoEntries_eq_map_gzread, gzreadTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzclose_r : (progOfTUs Zlib.allFiles).fnProtos "gzclose_r" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzclose_r) :=
  allHeaders_protoEntries_lookup_some (by rfl)

-- gzwrite.c
theorem prog0_fnProtos_gz_init : (progOfTUs Zlib.allFiles).fnProtos "gz_init" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gz_init) :=
  tu_protoEntries_of_mem allTUs_split_gzwrite (by rfl) (by rw [tu_protoEntries_eq_map_gzwrite, gzwriteTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_comp : (progOfTUs Zlib.allFiles).fnProtos "gz_comp" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gz_comp) :=
  tu_protoEntries_of_mem allTUs_split_gzwrite (by rfl) (by rw [tu_protoEntries_eq_map_gzwrite, gzwriteTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_zero : (progOfTUs Zlib.allFiles).fnProtos "gz_zero" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gz_zero) :=
  tu_protoEntries_of_mem allTUs_split_gzwrite (by rfl) (by rw [tu_protoEntries_eq_map_gzwrite, gzwriteTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_write : (progOfTUs Zlib.allFiles).fnProtos "gz_write" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gz_write) :=
  tu_protoEntries_of_mem allTUs_split_gzwrite (by rfl) (by rw [tu_protoEntries_eq_map_gzwrite, gzwriteTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzwrite : (progOfTUs Zlib.allFiles).fnProtos "gzwrite" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzwrite) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_gzfwrite : (progOfTUs Zlib.allFiles).fnProtos "gzfwrite" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzfwrite) :=
  tu_protoEntries_of_mem allTUs_split_gzwrite (by rfl) (by rw [tu_protoEntries_eq_map_gzwrite, gzwriteTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzputc : (progOfTUs Zlib.allFiles).fnProtos "gzputc" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzputc) :=
  tu_protoEntries_of_mem allTUs_split_gzwrite (by rfl) (by rw [tu_protoEntries_eq_map_gzwrite, gzwriteTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzputs : (progOfTUs Zlib.allFiles).fnProtos "gzputs" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzputs) :=
  tu_protoEntries_of_mem allTUs_split_gzwrite (by rfl) (by rw [tu_protoEntries_eq_map_gzwrite, gzwriteTU_fnEntries]; rfl)
theorem prog0_fnProtos_gz_vacate : (progOfTUs Zlib.allFiles).fnProtos "gz_vacate" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gz_vacate) :=
  tu_protoEntries_of_mem allTUs_split_gzwrite (by rfl) (by rw [tu_protoEntries_eq_map_gzwrite, gzwriteTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzvprintf : (progOfTUs Zlib.allFiles).fnProtos "gzvprintf" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzvprintf) :=
  allHeaders_protoEntries_lookup_some (by rfl)
theorem prog0_fnProtos_gzprintf : (progOfTUs Zlib.allFiles).fnProtos "gzprintf" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzprintf) :=
  tu_protoEntries_of_mem allTUs_split_gzwrite (by rfl) (by rw [tu_protoEntries_eq_map_gzwrite, gzwriteTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzflush : (progOfTUs Zlib.allFiles).fnProtos "gzflush" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzflush) :=
  tu_protoEntries_of_mem allTUs_split_gzwrite (by rfl) (by rw [tu_protoEntries_eq_map_gzwrite, gzwriteTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzsetparams : (progOfTUs Zlib.allFiles).fnProtos "gzsetparams" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzsetparams) :=
  tu_protoEntries_of_mem allTUs_split_gzwrite (by rfl) (by rw [tu_protoEntries_eq_map_gzwrite, gzwriteTU_fnEntries]; rfl)
theorem prog0_fnProtos_gzclose_w : (progOfTUs Zlib.allFiles).fnProtos "gzclose_w" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzclose_w) :=
  allHeaders_protoEntries_lookup_some (by rfl)

/-! ### `stdLibc` (`prog0.fns = none`, `prog0.fnProtos = some ...`) -/

def allStdLibcNames : List String := [
  "malloc", "calloc", "free", "memcpy", "memmove", "memset", "memcmp", "strlen", "memchr",
  "open", "close", "fcntl", "lseek", "lseek64", "LSEEK", "read", "write",
  "strerror", "snprintf", "vsnprintf"
]

private theorem stdLibcNames_not_in_protoNames_bool :
    (Zlib.allFiles.all fun tu => allStdLibcNames.all fun s => !(tuProtoNames tu).contains s) = true := by
  decide

private theorem mem_tuProtoNames_of_mem_tuFnNames {tu : TU} {sym : String}
    (h : sym ∈ tuFnNames tu) : sym ∈ tuProtoNames tu := by
  rcases tu with ⟨_, items⟩
  unfold tuProtoNames tuFnNames at *
  dsimp only at *
  induction items with
  | nil => exact h
  | cons hd tl ih =>
    cases hd with
    | fnDef f =>
      simp only [List.filterMap_cons, List.mem_cons] at h ⊢
      exact h.imp id ih
    | fnProto _ _ n _ _ =>
      simp only [List.filterMap_cons, List.mem_cons]
      exact Or.inr (ih h)
    | _ => exact ih h

theorem stdLibc_not_mem_allFiles_protoNames {sym : String} (hs : sym ∈ allStdLibcNames) :
    sym ∉ Zlib.allFiles.flatMap tuProtoNames := by
  intro hcontra
  simp only [List.mem_flatMap] at hcontra
  rcases hcontra with ⟨tu, htu, hmem⟩
  have h1 := List.all_eq_true.mp stdLibcNames_not_in_protoNames_bool tu htu
  have h2 := List.all_eq_true.mp h1 sym hs
  simp [hmem] at h2

theorem stdLibc_not_mem_allFiles_fnNames {sym : String} (hs : sym ∈ allStdLibcNames) :
    sym ∉ Zlib.allFiles.flatMap tuFnNames := by
  have hp := stdLibc_not_mem_allFiles_protoNames hs
  intro hcontra
  simp only [List.mem_flatMap] at hcontra
  rcases hcontra with ⟨tu, htu, hmem⟩
  exact hp (List.mem_flatMap.mpr ⟨tu, htu, mem_tuProtoNames_of_mem_tuFnNames hmem⟩)

theorem prog0_fns_memcpy : (progOfTUs Zlib.allFiles).fns "memcpy" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_memmove : (progOfTUs Zlib.allFiles).fns "memmove" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_memset : (progOfTUs Zlib.allFiles).fns "memset" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_memcmp : (progOfTUs Zlib.allFiles).fns "memcmp" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_strlen : (progOfTUs Zlib.allFiles).fns "strlen" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_memchr : (progOfTUs Zlib.allFiles).fns "memchr" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_open : (progOfTUs Zlib.allFiles).fns "open" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_close : (progOfTUs Zlib.allFiles).fns "close" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_fcntl : (progOfTUs Zlib.allFiles).fns "fcntl" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_lseek : (progOfTUs Zlib.allFiles).fns "lseek" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_lseek64 : (progOfTUs Zlib.allFiles).fns "lseek64" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_LSEEK : (progOfTUs Zlib.allFiles).fns "LSEEK" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_read : (progOfTUs Zlib.allFiles).fns "read" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_write : (progOfTUs Zlib.allFiles).fns "write" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_strerror : (progOfTUs Zlib.allFiles).fns "strerror" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_snprintf : (progOfTUs Zlib.allFiles).fns "snprintf" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))
theorem prog0_fns_vsnprintf : (progOfTUs Zlib.allFiles).fns "vsnprintf" = none :=
  prog0_fns_none_of_not_mem (stdLibc_not_mem_allFiles_fnNames (by decide))

theorem prog0_fnProtos_memcpy :
    (progOfTUs Zlib.allFiles).fnProtos "memcpy" =
      some (.ptr .void, [.ptr .void, .ptr (.const_ .void), .int .u64], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_memmove :
    (progOfTUs Zlib.allFiles).fnProtos "memmove" =
      some (.ptr .void, [.ptr .void, .ptr (.const_ .void), .int .u64], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_memset :
    (progOfTUs Zlib.allFiles).fnProtos "memset" =
      some (.ptr .void, [.ptr .void, .int .i32, .int .u64], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_memcmp :
    (progOfTUs Zlib.allFiles).fnProtos "memcmp" =
      some (.int .i32, [.ptr (.const_ .void), .ptr (.const_ .void), .int .u64], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_strlen :
    (progOfTUs Zlib.allFiles).fnProtos "strlen" =
      some (.int .u64, [.ptr (.const_ (.int .i8))], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_memchr :
    (progOfTUs Zlib.allFiles).fnProtos "memchr" =
      some (.ptr .void, [.ptr (.const_ .void), .int .i32, .int .u64], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_open :
    (progOfTUs Zlib.allFiles).fnProtos "open" =
      some (.int .i32, [.ptr (.const_ (.int .i8)), .int .i32], true) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_close :
    (progOfTUs Zlib.allFiles).fnProtos "close" =
      some (.int .i32, [.int .i32], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_fcntl :
    (progOfTUs Zlib.allFiles).fnProtos "fcntl" =
      some (.int .i32, [.int .i32, .int .i32], true) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_lseek :
    (progOfTUs Zlib.allFiles).fnProtos "lseek" =
      some (.int .i64, [.int .i32, .int .i64, .int .i32], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_lseek64 :
    (progOfTUs Zlib.allFiles).fnProtos "lseek64" =
      some (.int .i64, [.int .i32, .int .i64, .int .i32], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_read :
    (progOfTUs Zlib.allFiles).fnProtos "read" =
      some (.int .i64, [.int .i32, .ptr .void, .int .u64], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_write :
    (progOfTUs Zlib.allFiles).fnProtos "write" =
      some (.int .i64, [.int .i32, .ptr (.const_ .void), .int .u64], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_strerror :
    (progOfTUs Zlib.allFiles).fnProtos "strerror" =
      some (.ptr (.int .i8), [.int .i32], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_snprintf :
    (progOfTUs Zlib.allFiles).fnProtos "snprintf" =
      some (.int .i32, [.ptr (.int .i8), .int .u64, .ptr (.const_ (.int .i8))], true) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)
theorem prog0_fnProtos_vsnprintf :
    (progOfTUs Zlib.allFiles).fnProtos "vsnprintf" =
      some (.int .i32, [.ptr (.int .i8), .int .u64, .ptr (.const_ (.int .i8)), .vaList], false) :=
  prog0_fnProtos_stdLibc (stdLibc_not_mem_allFiles_protoNames (by decide)) (by rfl)

end ProgFnsAndProtos

/-! ## 3. Complete `prog.fnStatics` Lemmas -/

section ProgFnStaticsSection

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

private theorem int64_ofNat_toInt {n : Nat} (hn : n < ptrDiffLimit) :
    (Int64.ofNat n).toInt = (n : Int) := by
  change (Int64.ofInt (n : Nat)).toInt = (n : Int)
  rw [ptrDiffLimit_val] at hn
  exact int64_ofInt_toInt (by omega) (by omega)

private theorem int64_ofNat_add {a b : Nat} (hab : a + b < ptrDiffLimit) :
    Int64.ofInt ((Int64.ofNat a).toInt + (b : Int)) = Int64.ofNat (a + b) := by
  apply Int64.toInt_inj.mp
  rw [int64_ofNat_toInt (by omega), int64_ofNat_toInt hab]
  change (Int64.ofInt ((a : Int) + (b : Int))).toInt = ((a + b : Nat) : Int)
  rw [ptrDiffLimit_val] at hab
  rw [int64_ofInt_toInt (by omega) (by omega)]
  omega

private theorem stripConst_isConst (ty : CTy) : ty.stripConst.isConst = false := by
  match ty with
  | .const_ t => exact stripConst_isConst t
  | .typedef _ t => exact stripConst_isConst t
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

private theorem stripConst_unqual (ty : CTy) : ty.stripConst.unqual = ty.unqual := by
  match ty with
  | .const_ t => exact stripConst_unqual t
  | .typedef _ t => exact stripConst_unqual t
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

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
  have hoff_eq := int64_ofNat_toInt hoff_lt
  have hoff_nat : (Int64.ofNat off).toInt.toNat = off := by rw [hoff_eq]; omega
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun j hj => ?_⟩
  have hnot : ¬ (off ≤ j ∧ j < off + bs.length) := by omega
  dsimp only
  rw [hoff_nat]
  simp only [hnot, ↓reduceIte]

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

private theorem readVal_int_eq_of_bytes {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId}
    {blk1 blk2 : Block} {off : Nat} {k : IntKind}
    (hb1 : m1.blocks b = some blk1) (hb2 : m2.blocks b = some blk2)
    (hsz : blk2.size = blk1.size) (hba : blk2.baseAddr = blk1.baseAddr)
    (hoff : off < ptrDiffLimit)
    (hbytes : ∀ j, off ≤ j → j < off + k.bytes → blk2.bytes j = blk1.bytes j) :
    Sem.readVal tags m2 b (Int64.ofNat off) (.int k) =
      Sem.readVal tags m1 b (Int64.ofNat off) (.int k) := by
  unfold Sem.readVal Mem.readBytes
  simp only [CTy.unqual, CTy.intKind?, hb1, hb2, bind, Option.bind]
  have h1 : Mem.isAligned blk2 (Int64.ofNat off) k.align = Mem.isAligned blk1 (Int64.ofNat off) k.align := by
    simp [Mem.isAligned, hba]
  have h2 : Mem.inBounds blk2 (Int64.ofNat off) k.bytes = Mem.inBounds blk1 (Int64.ofNat off) k.bytes := by
    simp [Mem.inBounds, hsz]
  rw [h1, h2]
  cases ha : Mem.isAligned blk1 (Int64.ofNat off) k.align
  · rfl
  · cases hin : Mem.inBounds blk1 (Int64.ofNat off) k.bytes
    · rfl
    · have hoff_eq := int64_ofNat_toInt hoff
      have hoff_nat : (Int64.ofNat off).toInt.toNat = off := by rw [hoff_eq]; omega
      have hmap : ((List.range k.bytes).map fun i => blk2.bytes (off + i)) =
          ((List.range k.bytes).map fun i => blk1.bytes (off + i)) := by
        apply List.map_congr_left
        intro i hi
        have hik : i < k.bytes := List.mem_range.mp hi
        exact hbytes (off + i) (by omega) (by omega)
      simp only [guard, ↓reduceIte, hoff_nat, pure, Pure.pure]
      rw [hmap]

private theorem readVal_writeBytes_int_same (tags : TypeEnv) {m m' : Mem} {b : BlockId}
    {blk : Block} {off : Nat} {k : IntKind} {bv : BitVec k.bits}
    (hb : m.blocks b = some blk)
    (hal : Mem.isAligned blk (Int64.ofNat off) k.align = true)
    (hwb : m.writeBytes b (Int64.ofNat off) (Mem.encodeInt k bv) = some m') :
    Sem.readVal tags m' b (Int64.ofNat off) (.int k) = some (.int k bv) := by
  have hrd := readBytes_writeBytes_same hb hwb
  have hblk' := writeBytes_blocks_eq hb hwb
  have hal' : Mem.isAligned { blk with bytes := (fun i =>
      if (Int64.ofNat off).toInt.toNat ≤ i ∧
         i < (Int64.ofNat off).toInt.toNat + (Mem.encodeInt k bv).length then
        (Mem.encodeInt k bv)[i - (Int64.ofNat off).toInt.toNat]?.getD .undef
      else blk.bytes i) } (Int64.ofNat off) k.align = true := by
    simpa [Mem.isAligned] using hal
  unfold Sem.readVal
  simp only [CTy.unqual, CTy.intKind?, hblk', hal', guard_true, bind, Option.bind]
  rw [← encodeInt_length k bv, hrd]
  dsimp [pure]
  rw [decodeInt_encodeInt]

private theorem writeVal_int_inv {m m' : Mem} {b : BlockId} {blk : Block} {off : Int64}
    {ty : CTy} {k : IntKind} {v : Val} {k1 : IntKind} {iv : Int}
    (hnc : ty.isConst = false) (htyu : ty.unqual = .int k)
    (hvi : valAsInt? v = some (k1, iv))
    (hb : m.blocks b = some blk)
    (hw : writeVal m b off ty v = some m') :
    Mem.isAligned blk off k.align = true ∧
    m.writeBytes b off (Mem.encodeInt k (BitVec.ofInt k.bits iv)) = some m' := by
  unfold writeVal at hw
  simp only [hnc, Bool.not_false, guard_true, hb, htyu, CTy.intKind?, hvi, bind, Option.bind] at hw
  dsimp only [CTy.unqual, CTy.intKind?, guard, Pure.pure] at hw
  cases hal : Mem.isAligned blk off k.align
  · rw [hal] at hw; cases hw
  · rw [hal] at hw; exact ⟨rfl, hw⟩

def evalPureLit? : CExpr → Option Int
  | .lit v k _ _ _ =>
    let bv := BitVec.ofInt k.bits v
    some (if k.signed then bv.toInt else (bv.toNat : Int))
  | .paren e => evalPureLit? e
  | _ => none

def parseIntInit? : InitVal → Option Int
  | .expr e => evalPureLit? e
  | _ => none

private theorem evalConstExpr_of_evalPureLit {prog : Prog} {env : Env} {m : Mem}
    {strBase : Nat → UInt64} {ns : Nat} {e : CExpr} {iv : Int}
    (h : evalPureLit? e = some iv) :
    ∃ k bv, evalConstExpr prog env m strBase ns e = some (.int k bv, .int k, m, ns) ∧
      valAsInt? (.int k bv) = some (k, iv) := by
  match e with
  | .paren e0 => exact evalConstExpr_of_evalPureLit (e := e0) h
  | .lit v k _ _ _ =>
    simp only [evalPureLit?, Option.some.injEq] at h
    refine ⟨k, BitVec.ofInt k.bits v, rfl, ?_⟩
    rw [valAsInt?, h]
  | .strLit _ | .var _ | .sizeOfTy _ | .sizeOfExpr _ | .unary _ _ | .binary _ _ _
  | .logAnd _ _ | .logOr _ _ | .cond _ _ _ | .comma _ _ | .cast _ _ | .deref _
  | .addrOf _ | .index _ _ | .member _ _ | .arrow _ _ | .assign _ _ _ | .incDec _ _
  | .call _ _ | .vaStart _ _ | .vaEnd _ => cases h
termination_by sizeOf e

private theorem writeInitVal_expr_not_strLit {prog : Prog} {env : Env} {m : Mem}
    {strBase : Nat → UInt64} {b : BlockId} {off : Int64} {ty : CTy} {e : CExpr} {ns : Nat}
    (h : ∀ s, e ≠ .strLit s) :
    writeInitVal prog env m strBase b off ty (.expr e) ns =
      (do let (v, _, m1, ns1) ← evalConstExpr prog env m strBase ns e
          (writeVal m1 b off ty.stripConst v).map (·, ns1)) := by
  cases e with
  | strLit s => exact False.elim (h s rfl)
  | _ => rfl

private theorem writeInitVal_int_step {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {b : BlockId} {off : Nat} {elemTy : CTy} {ek : IntKind} {e : CExpr} {iv : Int}
    {m m' : Mem} {ns ns' : Nat} {blk : Block}
    (htyu : elemTy.unqual = .int ek)
    (hev : evalPureLit? e = some iv)
    (hb : m.blocks b = some blk)
    (hwr : writeInitVal prog env m strBase b (Int64.ofNat off) elemTy (.expr e) ns = some (m', ns')) :
    ns' = ns ∧
    Mem.isAligned blk (Int64.ofNat off) ek.align = true ∧
    m.writeBytes b (Int64.ofNat off) (Mem.encodeInt ek (BitVec.ofInt ek.bits iv)) = some m' ∧
    Sem.readVal prog.tags m' b (Int64.ofNat off) (.int ek) =
      some (.int ek (BitVec.ofInt ek.bits iv)) := by
  have hnotstr : ∀ s, e ≠ .strLit s := fun s heq => by subst heq; cases hev
  rw [writeInitVal_expr_not_strLit hnotstr] at hwr
  obtain ⟨k, bv, hec, hvi⟩ := evalConstExpr_of_evalPureLit (prog := prog) (env := env)
    (m := m) (strBase := strBase) (ns := ns) hev
  rw [hec] at hwr
  dsimp only [bind, Option.bind] at hwr
  cases hwv : writeVal m b (Int64.ofNat off) elemTy.stripConst (.int k bv) with
  | none => rw [hwv] at hwr; cases hwr
  | some m2 =>
    rw [hwv] at hwr
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨rfl, rfl⟩ := hwr
    obtain ⟨hal, hwb⟩ := writeVal_int_inv (stripConst_isConst elemTy)
      ((stripConst_unqual elemTy).trans htyu) hvi hb hwv
    exact ⟨rfl, hal, hwb, readVal_writeBytes_int_same prog.tags hb hal hwb⟩

private theorem writeInitList_int_inv {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {b : BlockId} {elemTy : CTy} {ek : IntKind} {idx : Nat} {xs : List InitVal}
    {m m' : Mem} {ns ns' : Nat} {blk : Block}
    (htyu : elemTy.unqual = .int ek)
    (hsz_el : sizeofTy prog.tags elemTy = ek.bytes)
    (hb : m.blocks b = some blk)
    (hconcr : ∀ i, ∃ u : UInt8, blk.bytes i = .byte u)
    (hsz_blk : ek.bytes * (idx + xs.length) ≤ blk.size)
    (hall : xs.all (fun x => (parseIntInit? x).isSome) = true)
    (hwr : writeInitList prog env m strBase b 0 elemTy idx xs ns = some (m', ns')) :
    ns' = ns ∧ m'.nextBlock = m.nextBlock ∧
    (∀ x, x ≠ b → m'.blocks x = m.blocks x) ∧
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.perm = blk.perm ∧
      blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr ∧
      (∀ j < ek.bytes * idx, blk'.bytes j = blk.bytes j) ∧
      (∀ i, ∃ u : UInt8, blk'.bytes i = .byte u) ∧
      (∀ (i : Nat) (hi : i < (xs.filterMap parseIntInit?).length),
        Sem.readVal prog.tags m' b (Int64.ofNat (ek.bytes * (idx + i))) (.int ek) =
          some (.int ek (BitVec.ofInt ek.bits (xs.filterMap parseIntInit?)[i]))) := by
  induction xs generalizing idx m ns blk with
  | nil =>
    simp only [writeInitList, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨rfl, rfl⟩ := hwr
    refine ⟨rfl, rfl, fun _ _ => rfl, blk, hb, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, hconcr, ?_⟩
    intro i hi; simp at hi
  | cons x rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hx_some, hrest_all⟩ := hall
    obtain ⟨iv, hiv⟩ := Option.isSome_iff_exists.mp hx_some
    have hx_expr : ∃ e, x = .expr e ∧ evalPureLit? e = some iv := by
      cases x with
      | expr e => exact ⟨e, rfl, hiv⟩
      | list _ | intSeq _ _ => cases hiv
    obtain ⟨e, rfl, hev⟩ := hx_expr
    unfold writeInitList at hwr
    dsimp only [bind, Option.bind] at hwr
    rw [hsz_el] at hwr
    have hlt_blk : ek.bytes * idx < ptrDiffLimit := by
      have hszlt := blk.sizeLt
      simp only [List.length_cons] at hsz_blk
      have hkpos : 0 < ek.bytes := by cases ek <;> decide
      have hle1 : ek.bytes * idx < ek.bytes * (idx + (rest.length + 1)) :=
        Nat.mul_lt_mul_of_pos_left (by omega) hkpos
      omega
    have hoff_eq : Int64.ofInt ((0 : Int64).toInt + (idx : Int) * (ek.bytes : Int)) =
        Int64.ofNat (ek.bytes * idx) := by
      have h0 : (0 : Int64).toInt = 0 := rfl
      rw [h0, Int.zero_add, Int.mul_comm]
      apply Int64.toInt_inj.mp
      rw [int64_ofNat_toInt hlt_blk]
      change (Int64.ofInt (ek.bytes * idx : Nat)).toInt = (ek.bytes * idx : Int)
      rw [ptrDiffLimit_val] at hlt_blk
      exact int64_ofInt_toInt (by omega) (by omega)
    rw [hoff_eq] at hwr
    cases hstep : writeInitVal prog env m strBase b (Int64.ofNat (ek.bytes * idx)) elemTy (.expr e) ns with
    | none => rw [hstep] at hwr; cases hwr
    | some p1 =>
      rcases p1 with ⟨m1, ns1⟩
      rw [hstep] at hwr
      dsimp only at hwr
      obtain ⟨hns1, hal1, hwb1, hrd1⟩ := writeInitVal_int_step htyu hev hb hstep
      obtain ⟨blk1, hb1, hsz1, hal_blk1, hperm1, hk1, hba1, hconcr1⟩ :=
        writeBytes_allBytes_total hb hwb1 hconcr (fun _ hmem => mem_encodeInt_isByte hmem)
      have hpres1 := writeBytes_blocks_preserve_lt (off := ek.bytes * idx) hb hwb1 hb1 hlt_blk
      have hsz_rest : ek.bytes * (idx + 1 + rest.length) ≤ blk1.size := by
        rw [hsz1]; simp only [List.length_cons] at hsz_blk
        have hidx_eq : idx + 1 + rest.length = idx + (rest.length + 1) := by omega
        rw [hidx_eq]; exact hsz_blk
      obtain ⟨hns_eq, hm_next, hm_ne, blk', hb', hsz', hal', hperm', hk', hba', hlt_bytes, hconcr', hread_rest⟩ :=
        ih (idx := idx + 1) (m := m1) (ns := ns1) (blk := blk1) hb1 hconcr1 hsz_rest hrest_all hwr
      refine ⟨hns_eq.trans hns1, hm_next.trans (writeBytes_nextBlock hwb1), fun y hy => ?_,
        blk', hb', hsz'.trans hsz1, hal'.trans hal_blk1, hperm'.trans hperm1, hk'.trans hk1, hba'.trans hba1,
        fun j hj => ?_, hconcr', ?_⟩
      · rw [hm_ne y hy, writeBytes_blocks_ne hwb1 hy]
      · rw [hlt_bytes j (by rw [Nat.mul_add, Nat.mul_one]; omega), hpres1.2.2.2.2.2 j hj]
      · intro i hi
        have hfm : ((InitVal.expr e) :: rest).filterMap parseIntInit? = iv :: rest.filterMap parseIntInit? := by
          simp only [List.filterMap_cons, parseIntInit?, hev]
        cases i with
        | zero =>
          simp only [Nat.add_zero, hfm, List.getElem_cons_zero]
          rw [readVal_int_eq_of_bytes hb1 hb' hsz' hba' hlt_blk (fun j hj1 hj2 => by
            apply hlt_bytes
            rw [Nat.mul_add, Nat.mul_one]
            exact hj2)]
          exact hrd1
        | succ i' =>
          have hi' : i' < (rest.filterMap parseIntInit?).length := by
            rw [hfm, List.length_cons] at hi
            exact Nat.lt_of_succ_lt_succ hi
          have hidx_eq : idx + (i' + 1) = idx + 1 + i' := by omega
          have hget_eq : (((InitVal.expr e) :: rest).filterMap parseIntInit?)[i' + 1] =
              (rest.filterMap parseIntInit?)[i'] := by
            simp only [hfm, List.getElem_cons_succ]
          rw [hidx_eq, hget_eq]
          exact hread_rest i' hi'

theorem allocVarInit_intList_inv {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {el : CTy} {ek : IntKind} {n : Nat} {xs : List InitVal}
    (hty : d.ty = .array el (some n))
    (hxlen : xs.length = n)
    (htyu : el.unqual = .int ek)
    (hsz_el : sizeofTy prog.tags el = ek.bytes)
    (hal_el : alignofTy prog.tags el = ek.align)
    (_hal_eq : ek.align = ek.bytes)
    (hinit : d.init? = some (.list xs))
    (hall : xs.all (fun x => (parseIntInit? x).isSome) = true)
    {bid : BlockId} {ty : CTy}
    (h : allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns')) :
    bid = m.nextBlock ∧ ty = .array el (some n) ∧ ns' = ns ∧
    MemPreservedBelow m.nextBlock m m' ∧
    ∃ blk, m'.blocks bid = some blk ∧
      blk.size = max 1 (n * ek.bytes) ∧ blk.align = max 1 ek.align ∧
      blk.kind = .global ∧ blk.perm = (if ty.isReadOnly then .ro else .rw) ∧
      (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
      (∀ (i : Nat) (hi : i < (xs.filterMap parseIntInit?).length),
        Sem.readVal prog.tags m' bid (Int64.ofNat (ek.bytes * i)) (.int ek) =
          some (.int ek (BitVec.ofInt ek.bits (xs.filterMap parseIntInit?)[i]))) := by
  have hres : resolveDeclTy d.ty d.init? = .array el (some n) := by rw [hty]; rfl
  have hsz_ty : max 1 (sizeofTy prog.tags (resolveDeclTy d.ty d.init?)) = max 1 (n * ek.bytes) := by
    rw [hres, sizeofTy_array_some, hsz_el]
  have hal_ty : max 1 (alignofTy prog.tags (resolveDeclTy d.ty d.init?)) = max 1 ek.align := by
    rw [hres, alignofTy_array, hal_el]
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
          blk1.size = max 1 (n * ek.bytes) ∧ blk1.align = max 1 ek.align ∧
          blk1.perm = .rw ∧ blk1.kind = .global ∧ (∀ i, blk1.bytes i = .byte 0) := by
      split at halloc
      · split at halloc
        · split at halloc
          · cases halloc
            refine ⟨rfl, rfl, fun x hx => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hx),
              _, alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, hsz_ty, hal_ty, rfl, rfl, fun _ => rfl⟩
          · cases halloc
        · cases halloc
      · cases halloc
    rcases ha with ⟨rfl, hm1next, hm1lt, blk1, hblk1, hsz1, hal1, hperm1, hk1, hbytes1⟩
    rw [hinit] at h
    dsimp only at h
    split at h
    · cases h
    · next p hwr =>
      rcases p with ⟨m2, ns2⟩
      dsimp only at h
      have hres' := hres
      rw [hinit] at hres'
      unfold writeInitVal at hwr
      rw [hres'] at hwr
      simp only [CTy.unqual] at hwr
      have hsz_le : ek.bytes * (0 + xs.length) ≤ blk1.size := by
        rw [hsz1, hxlen, Nat.zero_add, Nat.mul_comm]
        exact Nat.le_max_right _ _
      obtain ⟨rfl, hm2next, hm2ne, blk2, hblk2, hsz2, hal2, hperm2, hk2, hba2, _, hconcr2, hread2⟩ :=
        writeInitList_int_inv htyu hsz_el hblk1 (fun i => ⟨0, hbytes1 i⟩) hsz_le hall hwr
      rw [hres'] at h
      split at h <;> rename_i hro <;> cases h
      · refine ⟨rfl, rfl, rfl, ⟨by simp [hm2next, hm1next], fun x hx => ?_⟩, ?_⟩
        · have hne : x ≠ m.nextBlock := Nat.ne_of_lt hx
          simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
          rw [hm2ne x hne, hm1lt x hx]
        · refine ⟨{ blk2 with perm := .ro }, by simp [hblk2], by rw [hsz2, hsz1], by rw [hal2, hal1],
            by rw [hk2, hk1], ?_, hconcr2, ?_⟩
          · rw [ite_eq_left hro]
          · intro i hi
            have hr := hread2 i hi
            rw [Nat.zero_add] at hr
            unfold Sem.readVal Mem.readBytes at hr ⊢
            rw [hblk2] at hr
            simp only [beq_self_eq_true, ↓reduceIte, hblk2, Option.map_some]
            exact hr
      · refine ⟨rfl, rfl, rfl, ⟨by rw [hm2next, hm1next]; exact Nat.le_succ _, fun x hx => ?_⟩, ?_⟩
        · rw [hm2ne x (Nat.ne_of_lt hx), hm1lt x hx]
        · refine ⟨blk2, hblk2, by rw [hsz2, hsz1], by rw [hal2, hal1], by rw [hk2, hk1], ?_,
            hconcr2, ?_⟩
          · rw [ite_eq_right hro, hperm2, hperm1]
          · intro i hi
            have hr := hread2 i hi
            rw [Nat.zero_add] at hr
            exact hr

private theorem strlenAt_go_congr {b1 b2 : Block} {start i : Nat}
    (hsz : b1.size = b2.size) (hbytes : ∀ k < b1.size, b1.bytes k = b2.bytes k) :
    Mem.strlenAt.go b1 start i = Mem.strlenAt.go b2 start i := by
  by_cases hlt : i < b1.size
  · have hlt2 : i < b2.size := hsz ▸ hlt
    have h1 := Mem.strlenAt.go.eq_1 b1 start i
    have h2 := Mem.strlenAt.go.eq_1 b2 start i
    rw [h1, h2]
    simp only [hlt, hlt2, ↓reduceDIte, hbytes i hlt]
    cases hb2 : b2.bytes i with
    | byte u =>
      by_cases hu : u = 0
      · subst hu; rfl
      · rcases u with ⟨v⟩
        split
        · next heq => exfalso; apply hu; cases heq; rfl
        · exact strlenAt_go_congr hsz hbytes
        · next hne => exfalso; exact hne ⟨v⟩ rfl
    | ptrFrag | fnFrag | undef => rfl
  · have hlt2 : ¬ i < b2.size := by omega
    have h1 := Mem.strlenAt.go.eq_1 b1 start i
    have h2 := Mem.strlenAt.go.eq_1 b2 start i
    rw [h1, h2]
    simp only [hlt, hlt2, ↓reduceDIte]
termination_by b1.size - i

theorem allocVarInit_strLit_inv {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {s : String}
    (hty : d.ty = .array (.const_ (.int .i8)) none)
    (hinit : d.init? = some (.expr (.strLit s)))
    (hok : CStringLitOk s = true)
    {bid : BlockId} {ty : CTy}
    (h : allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns')) :
    bid = m.nextBlock ∧ ty = .array (.const_ (.int .i8)) (some (s.utf8ByteSize + 1)) ∧
    ns' = ns ∧ MemPreservedBelow m.nextBlock m m' ∧
    ∃ blk, m'.blocks bid = some blk ∧
      blk.size = s.utf8ByteSize + 1 ∧ blk.align = 1 ∧
      blk.kind = .global ∧ blk.perm = .ro ∧
      (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
      m'.strlenAt bid 0 = some s.utf8ByteSize ∧
      (∀ i < s.utf8ByteSize + 1,
        Sem.readVal prog.tags m' bid (Int64.ofNat i) (.int .i8) =
          some (.int .i8 (BitVec.ofNat 8 ((s.toUTF8[i]?).getD 0).toNat))) := by
  have hres : resolveDeclTy d.ty d.init? = .array (.const_ (.int .i8)) (some (s.utf8ByteSize + 1)) := by
    rw [hty, hinit]; rfl
  have hsz_eq : max 1 (sizeofTy prog.tags (resolveDeclTy d.ty d.init?)) = s.utf8ByteSize + 1 := by
    rw [hres, sizeofTy_array_some, sizeofTy_const, sizeofTy_int,
      show IntKind.i8.bytes = 1 from rfl, Nat.mul_one]
    exact Nat.max_eq_right (Nat.succ_le_succ (Nat.zero_le _))
  have hal_eq : max 1 (alignofTy prog.tags (resolveDeclTy d.ty d.init?)) = 1 := by
    rw [hres, alignofTy_array, alignofTy_const, alignofTy_int]; rfl
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
          blk1.size = s.utf8ByteSize + 1 ∧ blk1.align = 1 ∧
          blk1.perm = .rw ∧ blk1.kind = .global ∧ (∀ i, blk1.bytes i = .byte 0) := by
      split at halloc
      · split at halloc
        · split at halloc
          · cases halloc
            refine ⟨rfl, rfl, fun x hx => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hx),
              _, alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, hsz_eq, hal_eq, rfl, rfl, fun _ => rfl⟩
          · cases halloc
        · cases halloc
      · cases halloc
    rcases ha with ⟨rfl, hm1next, hm1lt, blk1, hblk1, hsz1, hal1, hperm1, hk1, hbytes1⟩
    rw [hinit] at h
    dsimp only at h
    split at h
    · cases h
    · next p hwr =>
      rcases p with ⟨m2, ns2⟩
      dsimp only at h
      have hres' := hres
      rw [hinit] at hres'
      unfold writeInitVal at hwr
      rw [hres'] at hwr
      simp only [CTy.unqual] at hwr
      let bs : List MemByte :=
        (List.range s.utf8ByteSize).map (fun i => MemByte.byte ((s.toUTF8[i]?).getD 0)) ++ [.byte 0]
      have hwr' : (m1.writeBytes m.nextBlock 0 bs).map (·, ns) = some (m2, ns2) := hwr
      cases hwb : m1.writeBytes m.nextBlock 0 bs with
      | none => rw [hwb] at hwr'; cases hwr'
      | some m2' =>
        rw [hwb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwr'
        rcases hwr' with ⟨rfl, rfl⟩
        have hbs_concr : ∀ x ∈ bs, ∃ u : UInt8, x = .byte u := by
          intro x hx
          rcases List.mem_append.mp hx with h1 | h2
          · rw [List.mem_map] at h1; rcases h1 with ⟨_, _, rfl⟩; exact ⟨_, rfl⟩
          · simp at h2; subst h2; exact ⟨0, rfl⟩
        obtain ⟨blk2, hblk2, hsz2, hal2, _, hk2, _, hconcr2⟩ :=
          writeBytes_allBytes_total hblk1 hwb (fun i => ⟨0, hbytes1 i⟩) hbs_concr
        have hlit : (∀ i < s.utf8ByteSize, (s.toUTF8[i]?).getD 0 ≠ 0) ∧
            (s.toUTF8[s.utf8ByteSize]?).getD 0 = 0 := by
          unfold CStringLitOk at hok
          obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hok
          exact ⟨fun i hi => bne_iff_ne.mp (List.all_eq_true.mp h1 i (List.mem_range.mpr hi)),
            beq_iff_eq.mp h2⟩
        have hbs_len : bs.length = s.utf8ByteSize + 1 := by simp [bs]
        have hblk2_eq := writeBytes_blocks_eq hblk1 hwb
        rw [hblk2, Option.some.injEq] at hblk2_eq
        have hbyte_i : ∀ i < s.utf8ByteSize + 1, blk2.bytes i = .byte ((s.toUTF8[i]?).getD 0) := by
          intro i hi
          have hrange : (0 : Int64).toInt.toNat ≤ i ∧ i < (0 : Int64).toInt.toNat + bs.length := by
            change 0 ≤ i ∧ i < 0 + bs.length; rw [hbs_len]; omega
          rw [hblk2_eq]
          dsimp only
          rw [ite_eq_left hrange]
          have hi_bs : i - (0 : Int64).toInt.toNat < bs.length := by
            change i - 0 < bs.length; rw [hbs_len]; omega
          rw [List.getElem?_eq_getElem hi_bs, Option.getD_some]
          have h0 : (0 : Int64).toInt.toNat = 0 := rfl
          simp only [h0, Nat.sub_zero]
          rcases Nat.lt_or_ge i s.utf8ByteSize with hi1 | hi2
          · rw [List.getElem_append_left
              (by simp only [List.length_map, List.length_range]; exact hi1),
              List.getElem_map, List.getElem_range]
          · have hi_eq : i = s.utf8ByteSize := by omega
            subst hi_eq
            dsimp only [bs]
            rw [List.getElem_append_right
              (by simp only [List.length_map, List.length_range]; exact Nat.le_refl _)]
            simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem_singleton, hlit.2]
        have hread_i : ∀ i < s.utf8ByteSize + 1,
            Sem.readVal prog.tags m2' m.nextBlock (Int64.ofNat i) (.int .i8) =
              some (.int .i8 (BitVec.ofNat 8 ((s.toUTF8[i]?).getD 0).toNat)) := by
          intro i hi
          have hsz_lim : blk1.size < ptrDiffLimit := blk1.sizeLt
          have hlt_lim : i < ptrDiffLimit := by rw [hsz1] at hsz_lim; omega
          have hi_nat : (Int64.ofNat i).toInt.toNat = i := by rw [int64_ofNat_toInt hlt_lim]; omega
          have hin : Mem.inBounds blk2 (Int64.ofNat i) 1 = true := by
            rw [inBounds_iff, int64_ofNat_toInt hlt_lim]; omega
          have hal_i : Mem.isAligned blk2 (Int64.ofNat i) IntKind.i8.align = true :=
            isAligned_one (by rw [int64_ofNat_toInt hlt_lim]; omega)
          have hrb := readBytes_of_bounds hblk2 hin
          have hbytes_i8 : IntKind.i8.bytes = 1 := rfl
          unfold Sem.readVal
          simp only [CTy.unqual, CTy.intKind?, hblk2, hal_i, guard_true, bind, Option.bind]
          rw [hbytes_i8, hrb]
          simp only [List.range_one, List.map_singleton, hi_nat, Nat.add_zero, hbyte_i i hi]
          dsimp [pure]
          have hdec : Mem.decodeInt .i8 [.byte ((s.toUTF8[i]?).getD 0)] =
              some (BitVec.ofNat 8 ((s.toUTF8[i]?).getD 0).toNat) := by
            unfold Mem.decodeInt
            simp only [List.length_singleton, IntKind.bytes, IntKind.bits, beq_self_eq_true, guard_true,
              Mem.decodeInt.go, Nat.shiftLeft_zero, Nat.zero_or, bind, Option.bind]
            rfl
          rw [hdec]
        rw [hres'] at h
        have hro : (CTy.array (.const_ (.int .i8)) (some (s.utf8ByteSize + 1))).isReadOnly = true := rfl
        rw [ite_eq_left hro] at h
        cases h
        refine ⟨rfl, rfl, rfl, ⟨?_, fun x hx => ?_⟩, ?_⟩
        · simp [writeBytes_nextBlock hwb, hm1next]
        · have hne : x ≠ m.nextBlock := Nat.ne_of_lt hx
          simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
          rw [writeBytes_blocks_ne hwb hne, hm1lt x hx]
        · refine ⟨{ blk2 with perm := .ro }, by simp [hblk2], by rw [hsz2, hsz1], by rw [hal2, hal1],
            by rw [hk2, hk1], rfl, hconcr2, ?_, ?_⟩
          · have hsz_lim : s.utf8ByteSize + 1 < ptrDiffLimit := by rw [← hsz1]; exact blk1.sizeLt
            have hm_alloc : (m.alloc (s.utf8ByteSize + 1) 1 .ro .global 0
                (fun i => .byte ((s.toUTF8[i]?).getD 0)) hsz_lim
                (by decide) (Nat.mod_one _)) = (m.nextBlock, _) := rfl
            have hstr_alloc := strlenAt_alloc_strLit (m := m) (base := 0)
              (hsz := hsz_lim) hm_alloc hlit.1 hlit.2
            unfold Mem.strlenAt at hstr_alloc ⊢
            dsimp only at hstr_alloc ⊢
            have hstart0 : (0 : Int64).toInt = 0 := rfl
            simp only [beq_self_eq_true, ↓reduceIte, hblk2, Option.map_some, hstart0, Int.le_refl,
              decide_true, Int.toNat_zero, Nat.zero_le, Bool.true_and, guard_true, bind, Option.bind]
              at hstr_alloc ⊢
            have hgo := strlenAt_go_congr
              (b1 := { blk2 with perm := .ro })
              (b2 := ⟨s.utf8ByteSize + 1, 1, .ro, .global, 0,
                fun i => .byte ((s.toUTF8[i]?).getD 0), hsz_lim, by decide, Nat.mod_one _⟩)
              (start := 0) (i := 0)
              (by dsimp only; rw [hsz2, hsz1])
              (fun k hk => hbyte_i k (by dsimp only at hk; rw [← hsz1, ← hsz2]; exact hk))
            exact hgo.trans hstr_alloc
          · intro i hi
            have hr := hread_i i hi
            unfold Sem.readVal Mem.readBytes at hr ⊢
            rw [hblk2] at hr
            simp only [beq_self_eq_true, ↓reduceIte, hblk2, Option.map_some]
            exact hr

/-! ### `noStaticsStmt` across all 15 TUs & `initStatics` Split Helpers -/

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

def staticFnNames : List String := ["inflate_table", "inflateBack", "inflate", "deflateInit2_"]

private def tuNonStaticFnStaticsEmpty (tu : TU) : Bool :=
  (tuFnEntries tu).all fun (n, f) => staticFnNames.contains n || noStaticsStmt f.body

private theorem ns_gzclose : tuNonStaticFnStaticsEmpty Zlib.Gzclose.gzcloseTU = true := by decide
private theorem ns_zutil : tuNonStaticFnStaticsEmpty Zlib.Zutil.zutilTU = true := by decide
private theorem ns_adler32 : tuNonStaticFnStaticsEmpty Zlib.Adler32.adler32TU = true := by decide
private theorem ns_compress : tuNonStaticFnStaticsEmpty Zlib.Compress.compressTU = true := by decide
private theorem ns_uncompr : tuNonStaticFnStaticsEmpty Zlib.Uncompr.uncomprTU = true := by decide
private theorem ns_inftrees : tuNonStaticFnStaticsEmpty Zlib.Inftrees.inftreesTU = true := by decide
private theorem ns_inffast : tuNonStaticFnStaticsEmpty Zlib.Inffast.inffastTU = true := by decide
private theorem ns_crc32 : tuNonStaticFnStaticsEmpty Zlib.Crc32.crc32TU = true := by decide
private theorem ns_trees : tuNonStaticFnStaticsEmpty Zlib.Trees.treesTU = true := by decide
private theorem ns_infback : tuNonStaticFnStaticsEmpty Zlib.Infback.infbackTU = true := by decide
private theorem ns_inflate : tuNonStaticFnStaticsEmpty Zlib.Inflate.inflateTU = true := by decide
private theorem ns_deflate : tuNonStaticFnStaticsEmpty Zlib.Deflate.deflateTU = true := by decide
private theorem ns_gzlib : tuNonStaticFnStaticsEmpty Zlib.Gzlib.gzlibTU = true := by decide
private theorem ns_gzread : tuNonStaticFnStaticsEmpty Zlib.Gzread.gzreadTU = true := by decide
private theorem ns_gzwrite : tuNonStaticFnStaticsEmpty Zlib.Gzwrite.gzwriteTU = true := by decide

private theorem collectFnStatics_empty_of_nonStatic {sym : String} (hsym : sym ∉ staticFnNames) :
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
    have hok_tu : ∀ {tu' : TU}, tuNonStaticFnStaticsEmpty tu' = true →
        f ∈ (tuFnEntries tu').map (·.2) → f.name = sym → collectFnStatics f.body = [] := by
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
      have hnotc : staticFnNames.contains sym = false := by
        cases hc : staticFnNames.contains sym
        · rfl
        · exact False.elim (hsym (List.elem_iff.mp hc))
      simp only [hnotc, Bool.false_or] at hall_st
      exact collectFnStatics_eq_nil_of_noStatics g.body hall_st
    have hhdr : ∀ tu' ∈ Zlib.allHeaders, tuFnEntries tu' = [] := by
      intro tu' htu'
      unfold Zlib.allHeaders Zlib.Headers.allABIHeaders at htu'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at htu'
      rcases htu' with rfl | rfl | rfl | rfl <;> rfl
    rcases List.mem_append.mp htu with hh | ht
    · rw [hhdr tu hh] at hmem; cases hmem
    · simp only [Zlib.allTUs, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hok_tu ns_gzclose hmem hfn
      · exact hok_tu ns_zutil hmem hfn
      · exact hok_tu ns_adler32 hmem hfn
      · exact hok_tu ns_compress hmem hfn
      · exact hok_tu ns_uncompr hmem hfn
      · exact hok_tu ns_inftrees hmem hfn
      · exact hok_tu ns_inffast hmem hfn
      · exact hok_tu ns_crc32 hmem hfn
      · exact hok_tu ns_trees hmem hfn
      · exact hok_tu ns_infback hmem hfn
      · exact hok_tu ns_inflate hmem hfn
      · exact hok_tu ns_deflate hmem hfn
      · exact hok_tu ns_gzlib hmem hfn
      · exact hok_tu ns_gzread hmem hfn
      · exact hok_tu ns_gzwrite hmem hfn
  intro f hf hfn
  simp only [List.mem_filterMap, List.mem_flatMap] at hf
  rcases hf with ⟨it, ⟨tu, htu, hit⟩, hfit⟩
  exact hall tu htu f (List.mem_filterMap.mpr ⟨it, hit, hfit⟩) hfn

private theorem initStatics_append {staticBase strBase : Nat → UInt64} {prog0 : Prog} {gEnv : Env}
    {idx ns : Nat} {m m' : Mem} {fnAcc fnList : List (String × Env)}
    {pre post : List FnDef}
    (hinit : initProg.initStatics staticBase strBase prog0 gEnv idx ns m fnAcc (pre ++ post) = some (fnList, m')) :
    ∃ idx1 ns1 m1 fnAcc1,
      MemPreservedBelow m.nextBlock m m1 ∧
      initProg.initStatics staticBase strBase prog0 gEnv idx1 ns1 m1 fnAcc1 post = some (fnList, m') := by
  induction pre generalizing idx ns m fnAcc with
  | nil => exact ⟨idx, ns, m, fnAcc, MemPreservedBelow.refl _ _, hinit⟩
  | cons f frest ih =>
    simp only [List.cons_append] at hinit
    unfold initProg.initStatics at hinit
    simp only [bind, Option.bind] at hinit
    split at hinit
    · cases hinit
    · next a hfold =>
      rcases a with ⟨sEnv, m1, idx1, ns1⟩
      dsimp only at hinit
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
      obtain ⟨idx2, ns2, m2, fnAcc2, hp2, hrest⟩ := ih hinit
      exact ⟨idx2, ns2, m2, fnAcc2, hp1.trans (hp2.mono hp1.1), hrest⟩

private theorem initStatics_lookup_acc {staticBase strBase : Nat → UInt64} {prog0 : Prog} {gEnv : Env}
    {idx ns : Nat} {m m' : Mem} {fnAcc fnList : List (String × Env)}
    {fns : List FnDef} {sym : String}
    (hnot : sym ∉ fns.map (·.name))
    (hinit : initProg.initStatics staticBase strBase prog0 gEnv idx ns m fnAcc fns = some (fnList, m')) :
    fnList.lookup sym = fnAcc.lookup sym := by
  induction fns generalizing idx ns m fnAcc with
  | nil =>
    simp only [initProg.initStatics, Option.some.injEq, Prod.mk.injEq] at hinit
    obtain ⟨rfl, _⟩ := hinit
    rfl
  | cons f frest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    unfold initProg.initStatics at hinit
    simp only [bind, Option.bind] at hinit
    split at hinit
    · cases hinit
    · next a _ =>
      rcases a with ⟨sEnv, m1, idx1, ns1⟩
      dsimp only at hinit
      rw [ih hnot.2 hinit]
      exact lookup_cons_ne _ hnot.1

private theorem initStatics_split_mem {staticBase strBase : Nat → UInt64} {prog0 : Prog} {gEnv : Env}
    {idx ns : Nat} {m m' : Mem} {fnAcc fnList : List (String × Env)}
    {pre post : List FnDef} {f : FnDef}
    (hnodup : f.name ∉ post.map (·.name))
    (hinit : initProg.initStatics staticBase strBase prog0 gEnv idx ns m fnAcc (pre ++ f :: post) = some (fnList, m')) :
    ∃ idx1 ns1 m1 sEnv m2 idx2 ns2,
      MemPreservedBelow m.nextBlock m m1 ∧
      (collectFnStatics f.body).foldlM (fun (sE, mA, iA, nA) d => do
        let (bid, ty, mB, nB) ← allocVarInit prog0 gEnv mA staticBase strBase iA nA d
        return ((d.name, bid, ty) :: sE, mB, iA + 1, nB)) ([], m1, idx1, ns1) = some (sEnv, m2, idx2, ns2) ∧
      MemPreservedBelow m2.nextBlock m2 m' ∧
      fnList.lookup f.name = some sEnv := by
  obtain ⟨idx1, ns1, m1, fnAcc1, hp1, hrest⟩ := initStatics_append hinit
  unfold initProg.initStatics at hrest
  simp only [bind, Option.bind] at hrest
  split at hrest
  · cases hrest
  · next a hfold =>
    rcases a with ⟨sEnv, m2, idx2, ns2⟩
    dsimp only at hrest
    have hp2 := initStatics_preserves hrest
    have hlu := initStatics_lookup_acc hnodup hrest
    rw [lookup_cons_eq] at hlu
    exact ⟨idx1, ns1, m1, sEnv, m2, idx2, ns2, hp1, hfold, hp2, hlu⟩

private theorem tu_fnDefs_eq (tu : TU) :
    (tu.items.filterMap fun | .fnDef f => some f | _ => none) = (tuFnEntries tu).map (·.2) := by
  rcases tu with ⟨_, items⟩
  unfold tuFnEntries
  dsimp only
  induction items with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | fnDef f => simp only [List.filterMap_cons, List.map_cons, ih]
    | _ => simp only [List.filterMap_cons]; exact ih

private theorem tu_fnNames_eq_map (tu : TU) :
    tuFnNames tu = ((tuFnEntries tu).map (·.2)).map (·.name) := by
  rcases tu with ⟨_, items⟩
  unfold tuFnNames tuFnEntries
  dsimp only
  induction items with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | fnDef f => simp only [List.filterMap_cons, List.map_cons, ih]
    | _ => simp only [List.filterMap_cons]; exact ih

private theorem fnDefs_split_of_tu {preTUs postTUs : List TU} {tu : TU}
    {preFns postFns : List (String × FnDef)} {nm : String} {f : FnDef}
    (hsplitTU : Zlib.allTUs = preTUs ++ tu :: postTUs)
    (hsplitFn : tuFnEntries tu = preFns ++ (nm, f) :: postFns) :
    ∃ pre post,
      ((Zlib.allFiles.flatMap (·.items)).filterMap fun | .fnDef g => some g | _ => none) = pre ++ f :: post ∧
      f.name ∉ post.map (·.name) := by
  have hfnDefs :
      ((Zlib.allFiles.flatMap (·.items)).filterMap fun | .fnDef g => some g | _ => none) =
        Zlib.allTUs.flatMap fun t => (tuFnEntries t).map (·.2) := by
    rw [filterMap_flatMap, Zlib.allFiles, List.flatMap_append]
    have hhdr : (Zlib.allHeaders.map fun t => t.items.filterMap fun | .fnDef g => some g | _ => none) = [[], [], [], []] := rfl
    have hhdr0 : (Zlib.allHeaders.flatMap fun t => t.items.filterMap fun | .fnDef g => some g | _ => none) = [] := by
      unfold List.flatMap; rw [hhdr]; rfl
    rw [hhdr0, List.nil_append]
    congr 1
    funext t
    exact tu_fnDefs_eq t
  have hsplit : Zlib.allTUs.flatMap (fun t => (tuFnEntries t).map (·.2)) =
      (preTUs.flatMap (fun t => (tuFnEntries t).map (·.2)) ++ preFns.map (·.2)) ++
      f :: (postFns.map (·.2) ++ postTUs.flatMap (fun t => (tuFnEntries t).map (·.2))) := by
    rw [hsplitTU, List.flatMap_append, List.flatMap_cons, hsplitFn, List.map_append, List.map_cons,
      List.append_assoc, List.cons_append, List.append_assoc]
  have hnodup : (Zlib.allTUs.flatMap fun t => ((tuFnEntries t).map (·.2)).map (·.name)).Nodup := by
    have heq : (Zlib.allTUs.flatMap fun t => ((tuFnEntries t).map (·.2)).map (·.name)) =
        Zlib.allTUs.flatMap tuFnNames := by
      congr 1
      funext t
      exact (tu_fnNames_eq_map t).symm
    rw [heq]
    exact allTUs_fnNames_nodup
  have hnodup' :
      ((preTUs.flatMap (fun t => (tuFnEntries t).map (·.2)) ++ preFns.map (·.2)).map (·.name) ++
       f.name :: (postFns.map (·.2) ++ postTUs.flatMap (fun t => (tuFnEntries t).map (·.2))).map (·.name)).Nodup := by
    have hmap : ((Zlib.allTUs.flatMap fun t => (tuFnEntries t).map (·.2)).map (·.name)) =
        Zlib.allTUs.flatMap fun t => ((tuFnEntries t).map (·.2)).map (·.name) := List.map_flatMap
    rw [hsplit, List.map_append, List.map_cons] at hmap
    rw [hmap]
    exact hnodup
  exact ⟨_, _, hfnDefs.trans hsplit, (List.nodup_cons.mp (List.nodup_append.mp hnodup').2.1).1⟩

/-! ### Exact Local-Static Extraction for `inflate_table`, `inflateBack`, `inflate`, `deflateInit2_` -/

private def u16ArrTy (n : Nat) : CTy := .array (.const_ (.int .u16)) (some n)

private theorem u16_unqual : (CTy.const_ (.int .u16)).unqual = .int .u16 := rfl
private theorem u16_sizeof (tags : TypeEnv) : sizeofTy tags (.const_ (.int .u16)) = 2 := by simp; rfl
private theorem u16_alignof (tags : TypeEnv) : alignofTy tags (.const_ (.int .u16)) = 2 := by simp; rfl

private theorem option_split {α : Type _} (x : Option α) : x = none ∨ ∃ a, x = some a := by
  cases x
  · exact .inl rfl
  · exact .inr ⟨_, rfl⟩

private theorem foldlM_one_allocVarInit {prog0 : Prog} {gEnv : Env} {staticBase strBase : Nat → UInt64}
    {d : VarDecl} {m1 m2 : Mem} {idx1 ns1 idx2 ns2 : Nat} {sEnv : Env}
    (h : [d].foldlM (fun (sE, mA, iA, nA) x => do
      let (bid, ty, mB, nB) ← allocVarInit prog0 gEnv mA staticBase strBase iA nA x
      return ((x.name, bid, ty) :: sE, mB, iA + 1, nB)) ([], m1, idx1, ns1) = some (sEnv, m2, idx2, ns2)) :
    ∃ bid ty, allocVarInit prog0 gEnv m1 staticBase strBase idx1 ns1 d = some (bid, ty, m2, ns2) ∧
      sEnv = [(d.name, bid, ty)] := by
  simp only [List.foldlM_cons, List.foldlM_nil, bind, Option.bind, pure, Pure.pure] at h
  rcases option_split (allocVarInit prog0 gEnv m1 staticBase strBase idx1 ns1 d) with hal | ⟨⟨bid, ty, mB, nB⟩, hal⟩
  · rw [hal] at h; cases h
  · rw [hal] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨bid, ty, hal, rfl⟩

private theorem foldlM_four_allocVarInit {prog0 : Prog} {gEnv : Env} {staticBase strBase : Nat → UInt64}
    {d1 d2 d3 d4 : VarDecl} {m1 m2 : Mem} {idx1 ns1 idx2 ns2 : Nat} {sEnv : Env}
    (h : [d1, d2, d3, d4].foldlM (fun (sE, mA, iA, nA) x => do
      let (bid, ty, mB, nB) ← allocVarInit prog0 gEnv mA staticBase strBase iA nA x
      return ((x.name, bid, ty) :: sE, mB, iA + 1, nB)) ([], m1, idx1, ns1) = some (sEnv, m2, idx2, ns2)) :
    ∃ b1 t1 ma nsa b2 t2 mb nsb b3 t3 mc nsc b4 t4,
      allocVarInit prog0 gEnv m1 staticBase strBase idx1 ns1 d1 = some (b1, t1, ma, nsa) ∧
      allocVarInit prog0 gEnv ma staticBase strBase (idx1 + 1) nsa d2 = some (b2, t2, mb, nsb) ∧
      allocVarInit prog0 gEnv mb staticBase strBase (idx1 + 1 + 1) nsb d3 = some (b3, t3, mc, nsc) ∧
      allocVarInit prog0 gEnv mc staticBase strBase (idx1 + 1 + 1 + 1) nsc d4 = some (b4, t4, m2, ns2) ∧
      sEnv = [(d4.name, b4, t4), (d3.name, b3, t3), (d2.name, b2, t2), (d1.name, b1, t1)] := by
  simp only [List.foldlM_cons, List.foldlM_nil, bind, Option.bind, pure, Pure.pure] at h
  rcases option_split (allocVarInit prog0 gEnv m1 staticBase strBase idx1 ns1 d1) with h1 | ⟨⟨b1, t1, ma, nsa⟩, h1⟩
  · rw [h1] at h; cases h
  · rw [h1] at h; dsimp only at h
    rcases option_split (allocVarInit prog0 gEnv ma staticBase strBase (idx1 + 1) nsa d2) with h2 | ⟨⟨b2, t2, mb, nsb⟩, h2⟩
    · rw [h2] at h; cases h
    · rw [h2] at h; dsimp only at h
      rcases option_split (allocVarInit prog0 gEnv mb staticBase strBase (idx1 + 1 + 1) nsb d3) with h3 | ⟨⟨b3, t3, mc, nsc⟩, h3⟩
      · rw [h3] at h; cases h
      · rw [h3] at h; dsimp only at h
        rcases option_split (allocVarInit prog0 gEnv mc staticBase strBase (idx1 + 1 + 1 + 1) nsc d4) with h4 | ⟨⟨b4, t4, md, nsd⟩, h4⟩
        · rw [h4] at h; cases h
        · rw [h4] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨b1, t1, ma, nsa, b2, t2, mb, nsb, b3, t3, mc, nsc, b4, t4, h1, h2, h3, h4, rfl⟩

mutual
private def collectFnStaticsFast : CStmt → List VarDecl
  | .decl d => if d.isStatic then [d] else []
  | .decls ds => ds.filter (·.isStatic)
  | .block ss => collectFnStaticsFastList ss
  | .ifStmt _ t f? => collectFnStaticsFast t ++ match f? with | some f => collectFnStaticsFast f | none => []
  | .whileStmt _ b | .doWhileStmt b _ | .forStmt _ _ _ b | .switchStmt _ b
  | .caseStmt _ b | .defaultStmt b | .labelStmt _ b => collectFnStaticsFast b
  | _ => []

private def collectFnStaticsFastList : List CStmt → List VarDecl
  | [] => []
  | s :: ss => collectFnStaticsFast s ++ collectFnStaticsFastList ss
end

mutual
private theorem collectFnStatics_eq_fast (s : CStmt) :
    collectFnStatics s = collectFnStaticsFast s := by
  match s with
  | .decl d => unfold collectFnStatics collectFnStaticsFast; rfl
  | .decls ds => unfold collectFnStatics collectFnStaticsFast; rfl
  | .block ss =>
    unfold collectFnStatics collectFnStaticsFast
    exact collectFnStatics_list_eq_fast ss
  | .ifStmt c t f? =>
    unfold collectFnStatics collectFnStaticsFast
    rw [collectFnStatics_eq_fast t]
    cases f? with
    | none => rfl
    | some f => simp [collectFnStatics_eq_fast f]
  | .whileStmt _ b => unfold collectFnStatics collectFnStaticsFast; exact collectFnStatics_eq_fast b
  | .doWhileStmt b _ => unfold collectFnStatics collectFnStaticsFast; exact collectFnStatics_eq_fast b
  | .forStmt _ _ _ b => unfold collectFnStatics collectFnStaticsFast; exact collectFnStatics_eq_fast b
  | .switchStmt _ b => unfold collectFnStatics collectFnStaticsFast; exact collectFnStatics_eq_fast b
  | .caseStmt _ b => unfold collectFnStatics collectFnStaticsFast; exact collectFnStatics_eq_fast b
  | .defaultStmt b => unfold collectFnStatics collectFnStaticsFast; exact collectFnStatics_eq_fast b
  | .labelStmt _ b => unfold collectFnStatics collectFnStaticsFast; exact collectFnStatics_eq_fast b
  | .nop | .expr _ | .breakStmt | .continueStmt | .returnStmt _ | .gotoStmt _ =>
    unfold collectFnStatics collectFnStaticsFast; rfl

private theorem collectFnStatics_list_eq_fast (ss : List CStmt) :
    ss.flatMap collectFnStatics = collectFnStaticsFastList ss := by
  match ss with
  | [] => rfl
  | s :: rest =>
    simp only [List.flatMap_cons, collectFnStaticsFastList,
      collectFnStatics_eq_fast s, collectFnStatics_list_eq_fast rest]
end

def inflateTableLbaseVals : List Int :=
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
   35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258, 0, 0]

def inflateTableLextVals : List Int :=
  [16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18,
   19, 19, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 16, 199, 192]

def inflateTableDbaseVals : List Int :=
  [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
   257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
   8193, 12289, 16385, 24577, 0, 0]

def inflateTableDextVals : List Int :=
  [16, 16, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 22,
   23, 23, 24, 24, 25, 25, 26, 26, 27, 27,
   28, 28, 29, 29, 64, 64]

def inflateOrderVals : List Int :=
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

private def mkU16StaticDecl (nm : String) (n : Nat) (vals : List Int) : VarDecl :=
  { name := nm
    ty := u16ArrTy n
    isStatic := true
    init? := some (.list (vals.map fun v => .expr (.lit v .i32 .none .dec none))) }

private def inflateTableStaticDecls : List VarDecl := [
  mkU16StaticDecl "lbase" 31 inflateTableLbaseVals,
  mkU16StaticDecl "lext" 31 inflateTableLextVals,
  mkU16StaticDecl "dbase" 32 inflateTableDbaseVals,
  mkU16StaticDecl "dext" 32 inflateTableDextVals
]

private def orderStaticDecl : VarDecl :=
  mkU16StaticDecl "order" 19 inflateOrderVals

private def myVersionStaticDecl : VarDecl :=
  { name := "my_version"
    ty := .array (.const_ (.int .i8)) none
    isStatic := true
    init? := some (.expr (.strLit "1.4.0.1-motley")) }

private theorem collectFnStatics_inflate_table :
    collectFnStatics Zlib.Inftrees.inftreesTU_fn_inflate_table.body = inflateTableStaticDecls := by
  rw [collectFnStatics_eq_fast]; rfl

private theorem collectFnStatics_inflateBack :
    collectFnStatics Zlib.Infback.infbackTU_fn_inflateBack.body = [orderStaticDecl] := by
  rw [collectFnStatics_eq_fast]; rfl

set_option maxRecDepth 4096 in
private theorem collectFnStatics_inflate :
    collectFnStatics Zlib.Inflate.inflateTU_fn_inflate.body = [orderStaticDecl] := by
  rw [collectFnStatics_eq_fast]; rfl

private theorem collectFnStatics_deflateInit2_ :
    collectFnStatics Zlib.Deflate.deflateTU_fn_deflateInit2_.body = [myVersionStaticDecl] := by
  rw [collectFnStatics_eq_fast]; rfl

private theorem mkU16StaticDecl_parse (vals : List Int) (h : vals.all (fun v => decide (0 ≤ v ∧ v < 2^31)) = true) :
    ((vals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).all (fun x => (parseIntInit? x).isSome) = true) ∧
    (vals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).filterMap parseIntInit? = vals := by
  induction vals with
  | nil => simp
  | cons v vs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hv := of_decide_eq_true h.1
    have hbv : (BitVec.ofInt 32 v).toInt = v := by
      rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)
    have hp : parseIntInit? (.expr (.lit v .i32 .none .dec none)) = some v := by
      simp [parseIntInit?, evalPureLit?, IntKind.signed, IntKind.bits, hbv]
    obtain ⟨ih1, ih2⟩ := ih h.2
    simp only [List.map_cons, List.all_cons, List.filterMap_cons, hp, Option.isSome_some,
      Bool.true_and, ih1, ih2, and_self]

private theorem lbase_all_ok : inflateTableLbaseVals.all (fun v => decide (0 ≤ v ∧ v < 2^31)) = true := by decide
private theorem lext_all_ok : inflateTableLextVals.all (fun v => decide (0 ≤ v ∧ v < 2^31)) = true := by decide
private theorem dbase_all_ok : inflateTableDbaseVals.all (fun v => decide (0 ≤ v ∧ v < 2^31)) = true := by decide
private theorem dext_all_ok : inflateTableDextVals.all (fun v => decide (0 ≤ v ∧ v < 2^31)) = true := by decide
private theorem order_all_ok : inflateOrderVals.all (fun v => decide (0 ≤ v ∧ v < 2^31)) = true := by decide
private theorem myVersion_str_ok : CStringLitOk "1.4.0.1-motley" = true := by decide

private theorem lbase_bounds_all : inflateTableLbaseVals.all (fun v => decide (0 ≤ v ∧ v ≤ 258)) = true := by decide
private theorem lext_bounds_all : inflateTableLextVals.all (fun v => decide (16 ≤ v ∧ v ≤ 199)) = true := by decide
private theorem dbase_bounds_all : inflateTableDbaseVals.all (fun v => decide (0 ≤ v ∧ v ≤ 24577)) = true := by decide
private theorem dext_bounds_all : inflateTableDextVals.all (fun v => decide (16 ≤ v ∧ v ≤ 64)) = true := by decide
private theorem order_bounds_all : inflateOrderVals.all (fun v => decide (0 ≤ v ∧ v < 19)) = true := by decide

private theorem lbase_bounds {i : Nat} (hi : i < 31) :
    0 ≤ inflateTableLbaseVals[i]! ∧ inflateTableLbaseVals[i]! ≤ 258 := by
  have hi' : i < inflateTableLbaseVals.length := hi
  have hm := List.all_eq_true.mp lbase_bounds_all _ (List.getElem_mem hi')
  simpa [getElem!_pos inflateTableLbaseVals i hi'] using of_decide_eq_true hm

private theorem lext_bounds {i : Nat} (hi : i < 31) :
    16 ≤ inflateTableLextVals[i]! ∧ inflateTableLextVals[i]! ≤ 199 := by
  have hi' : i < inflateTableLextVals.length := hi
  have hm := List.all_eq_true.mp lext_bounds_all _ (List.getElem_mem hi')
  simpa [getElem!_pos inflateTableLextVals i hi'] using of_decide_eq_true hm

private theorem dbase_bounds {i : Nat} (hi : i < 32) :
    0 ≤ inflateTableDbaseVals[i]! ∧ inflateTableDbaseVals[i]! ≤ 24577 := by
  have hi' : i < inflateTableDbaseVals.length := hi
  have hm := List.all_eq_true.mp dbase_bounds_all _ (List.getElem_mem hi')
  simpa [getElem!_pos inflateTableDbaseVals i hi'] using of_decide_eq_true hm

private theorem dext_bounds {i : Nat} (hi : i < 32) :
    16 ≤ inflateTableDextVals[i]! ∧ inflateTableDextVals[i]! ≤ 64 := by
  have hi' : i < inflateTableDextVals.length := hi
  have hm := List.all_eq_true.mp dext_bounds_all _ (List.getElem_mem hi')
  simpa [getElem!_pos inflateTableDextVals i hi'] using of_decide_eq_true hm

private theorem order_bounds {i : Nat} (hi : i < 19) :
    0 ≤ inflateOrderVals[i]! ∧ inflateOrderVals[i]! < 19 := by
  have hi' : i < inflateOrderVals.length := hi
  have hm := List.all_eq_true.mp order_bounds_all _ (List.getElem_mem hi')
  simpa [getElem!_pos inflateOrderVals i hi'] using of_decide_eq_true hm

private theorem list_getElem_of_eq {α : Type _} {l1 l2 : List α} (heq : l1 = l2) {i : Nat}
    (h1 : i < l1.length) (h2 : i < l2.length) : l1[i] = l2[i] := by
  subst heq; rfl

private theorem initStatics_inflate_table_inv {staticBase strBase : Nat → UInt64}
    {prog0 : Prog} {gEnv : Env} {idx ns : Nat} {m m' : Mem} {fnAcc fnList : List (String × Env)}
    (hinit : initProg.initStatics staticBase strBase prog0 gEnv idx ns m fnAcc
      ((Zlib.allFiles.flatMap (·.items)).filterMap fun | .fnDef f => some f | _ => none) = some (fnList, m')) :
    MemPreservedBelow m.nextBlock m m' ∧
    ∃ b_lb blk_lb b_le blk_le b_db blk_db b_de blk_de,
      (fnList.lookup "inflate_table").getD [] = [
        ("dext", b_de, u16ArrTy 32),
        ("dbase", b_db, u16ArrTy 32),
        ("lext", b_le, u16ArrTy 31),
        ("lbase", b_lb, u16ArrTy 31)
      ] ∧
      (m'.blocks b_lb = some blk_lb ∧ blk_lb.perm = .ro ∧ blk_lb.kind = .global ∧
        blk_lb.size = 62 ∧ blk_lb.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_lb.bytes i = .byte u) ∧
        (∀ i < 31, ∃ bv : BitVec 16,
          Sem.readVal prog0.tags m' b_lb (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
          bv = BitVec.ofInt 16 inflateTableLbaseVals[i]! ∧ bv.toNat ≤ 258)) ∧
      (m'.blocks b_le = some blk_le ∧ blk_le.perm = .ro ∧ blk_le.kind = .global ∧
        blk_le.size = 62 ∧ blk_le.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_le.bytes i = .byte u) ∧
        (∀ i < 31, ∃ bv : BitVec 16,
          Sem.readVal prog0.tags m' b_le (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
          bv = BitVec.ofInt 16 inflateTableLextVals[i]! ∧ 16 ≤ bv.toNat ∧ bv.toNat ≤ 199)) ∧
      (m'.blocks b_db = some blk_db ∧ blk_db.perm = .ro ∧ blk_db.kind = .global ∧
        blk_db.size = 64 ∧ blk_db.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_db.bytes i = .byte u) ∧
        (∀ i < 32, ∃ bv : BitVec 16,
          Sem.readVal prog0.tags m' b_db (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
          bv = BitVec.ofInt 16 inflateTableDbaseVals[i]! ∧ bv.toNat ≤ 24577)) ∧
      (m'.blocks b_de = some blk_de ∧ blk_de.perm = .ro ∧ blk_de.kind = .global ∧
        blk_de.size = 64 ∧ blk_de.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_de.bytes i = .byte u) ∧
        (∀ i < 32, ∃ bv : BitVec 16,
          Sem.readVal prog0.tags m' b_de (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
          bv = BitVec.ofInt 16 inflateTableDextVals[i]! ∧ 16 ≤ bv.toNat ∧ bv.toNat ≤ 64)) := by
  have hfnSplit := fnDefs_split_of_tu allTUs_split_inftrees
    (preFns := []) (postFns := [("inflate_fixed", Zlib.Inftrees.inftreesTU_fn_inflate_fixed)])
    (nm := "inflate_table") (f := Zlib.Inftrees.inftreesTU_fn_inflate_table)
    (by rw [inftreesTU_fnEntries]; rfl)
  rcases hfnSplit with ⟨pre, post, hfd, hnodup⟩
  rw [hfd] at hinit
  obtain ⟨idx1, ns1, m1, sEnv, m2, idx2, ns2, hp1, hfold, hp2, hlu⟩ :=
    initStatics_split_mem hnodup hinit
  rw [collectFnStatics_inflate_table] at hfold
  obtain ⟨b_lb, t_lb, ma, nsa, b_le, t_le, mb, nsb, b_db, t_db, mc, nsc, b_de, t_de,
      hal_lb, hal_le, hal_db, hal_de, hsEnv⟩ := foldlM_four_allocVarInit hfold
  obtain ⟨hplb_all, hplb_fm⟩ := mkU16StaticDecl_parse inflateTableLbaseVals lbase_all_ok
  obtain ⟨hple_all, hple_fm⟩ := mkU16StaticDecl_parse inflateTableLextVals lext_all_ok
  obtain ⟨hpdb_all, hpdb_fm⟩ := mkU16StaticDecl_parse inflateTableDbaseVals dbase_all_ok
  obtain ⟨hpde_all, hpde_fm⟩ := mkU16StaticDecl_parse inflateTableDextVals dext_all_ok
  obtain ⟨rfl, rfl, rfl, hp_lb, blk_lb, hblk_lb, hsz_lb, hal_lb', hk_lb, hperm_lb, hconcr_lb, hread_lb⟩ :=
    allocVarInit_intList_inv (ek := .u16) (n := 31) rfl rfl u16_unqual (u16_sizeof _) (u16_alignof _)
      rfl rfl hplb_all hal_lb
  obtain ⟨rfl, rfl, rfl, hp_le, blk_le, hblk_le, hsz_le, hal_le', hk_le, hperm_le, hconcr_le, hread_le⟩ :=
    allocVarInit_intList_inv (ek := .u16) (n := 31) rfl rfl u16_unqual (u16_sizeof _) (u16_alignof _)
      rfl rfl hple_all hal_le
  obtain ⟨rfl, rfl, rfl, hp_db, blk_db, hblk_db, hsz_db, hal_db', hk_db, hperm_db, hconcr_db, hread_db⟩ :=
    allocVarInit_intList_inv (ek := .u16) (n := 32) rfl rfl u16_unqual (u16_sizeof _) (u16_alignof _)
      rfl rfl hpdb_all hal_db
  obtain ⟨rfl, rfl, rfl, hp_de, blk_de, hblk_de, hsz_de, hal_de', hk_de, hperm_de, hconcr_de, hread_de⟩ :=
    allocVarInit_intList_inv (ek := .u16) (n := 32) rfl rfl u16_unqual (u16_sizeof _) (u16_alignof _)
      rfl rfl hpde_all hal_de
  have hp_from_mc : MemPreservedBelow mc.nextBlock mc m' := hp_de.trans (hp2.mono hp_de.1)
  have hp_from_mb : MemPreservedBelow mb.nextBlock mb m' := hp_db.trans (hp_from_mc.mono hp_db.1)
  have hp_from_ma : MemPreservedBelow ma.nextBlock ma m' := hp_le.trans (hp_from_mb.mono hp_le.1)
  have hp_from_m1 : MemPreservedBelow m1.nextBlock m1 m' := hp_lb.trans (hp_from_ma.mono hp_lb.1)
  refine ⟨hp1.trans (hp_from_m1.mono hp1.1),
    m1.nextBlock, blk_lb, ma.nextBlock, blk_le, mb.nextBlock, blk_db, mc.nextBlock, blk_de, ?_⟩
  have hlt_lb : m1.nextBlock < ma.nextBlock := lt_nextBlock_of_some hblk_lb
  have hlt_le : ma.nextBlock < mb.nextBlock := lt_nextBlock_of_some hblk_le
  have hlt_db : mb.nextBlock < mc.nextBlock := lt_nextBlock_of_some hblk_db
  have hlt_de : mc.nextBlock < m2.nextBlock := lt_nextBlock_of_some hblk_de
  have hname_inf : Zlib.Inftrees.inftreesTU_fn_inflate_table.name = "inflate_table" := rfl
  rw [hname_inf] at hlu
  have hperm_lb' : blk_lb.perm = .ro := by rw [hperm_lb]; rfl
  have hperm_le' : blk_le.perm = .ro := by rw [hperm_le]; rfl
  have hperm_db' : blk_db.perm = .ro := by rw [hperm_db]; rfl
  have hperm_de' : blk_de.perm = .ro := by rw [hperm_de]; rfl
  refine ⟨by rw [hlu, hsEnv]; rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hp_from_ma.2 _ hlt_lb, hblk_lb], hperm_lb', hk_lb, by rw [hsz_lb]; rfl,
      by rw [hal_lb']; rfl, hconcr_lb, fun i hi => ?_⟩
    have hi' : i < ((inflateTableLbaseVals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).filterMap parseIntInit?).length := by
      rw [hplb_fm]; exact hi
    have hr := hread_lb i hi'
    have hget : ((inflateTableLbaseVals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).filterMap parseIntInit?)[i]'hi' =
        inflateTableLbaseVals[i]! :=
      (list_getElem_of_eq hplb_fm hi' hi).trans (by simp [getElem!_pos inflateTableLbaseVals i hi])
    refine ⟨BitVec.ofInt 16 inflateTableLbaseVals[i]!, ?_, rfl, ?_⟩
    · rw [hp_from_ma.readVal hlt_lb, ← hget]; exact hr
    · have hb := lbase_bounds hi
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
      omega
  · refine ⟨by rw [hp_from_mb.2 _ hlt_le, hblk_le], hperm_le', hk_le, by rw [hsz_le]; rfl,
      by rw [hal_le']; rfl, hconcr_le, fun i hi => ?_⟩
    have hi' : i < ((inflateTableLextVals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).filterMap parseIntInit?).length := by
      rw [hple_fm]; exact hi
    have hr := hread_le i hi'
    have hget : ((inflateTableLextVals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).filterMap parseIntInit?)[i]'hi' =
        inflateTableLextVals[i]! :=
      (list_getElem_of_eq hple_fm hi' hi).trans (by simp [getElem!_pos inflateTableLextVals i hi])
    refine ⟨BitVec.ofInt 16 inflateTableLextVals[i]!, ?_, rfl, ?_⟩
    · rw [hp_from_mb.readVal hlt_le, ← hget]; exact hr
    · have hb := lext_bounds hi
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
      omega
  · refine ⟨by rw [hp_from_mc.2 _ hlt_db, hblk_db], hperm_db', hk_db, by rw [hsz_db]; rfl,
      by rw [hal_db']; rfl, hconcr_db, fun i hi => ?_⟩
    have hi' : i < ((inflateTableDbaseVals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).filterMap parseIntInit?).length := by
      rw [hpdb_fm]; exact hi
    have hr := hread_db i hi'
    have hget : ((inflateTableDbaseVals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).filterMap parseIntInit?)[i]'hi' =
        inflateTableDbaseVals[i]! :=
      (list_getElem_of_eq hpdb_fm hi' hi).trans (by simp [getElem!_pos inflateTableDbaseVals i hi])
    refine ⟨BitVec.ofInt 16 inflateTableDbaseVals[i]!, ?_, rfl, ?_⟩
    · rw [hp_from_mc.readVal hlt_db, ← hget]; exact hr
    · have hb := dbase_bounds hi
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
      omega
  · refine ⟨by rw [hp2.2 _ hlt_de, hblk_de], hperm_de', hk_de, by rw [hsz_de]; rfl,
      by rw [hal_de']; rfl, hconcr_de, fun i hi => ?_⟩
    have hi' : i < ((inflateTableDextVals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).filterMap parseIntInit?).length := by
      rw [hpde_fm]; exact hi
    have hr := hread_de i hi'
    have hget : ((inflateTableDextVals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).filterMap parseIntInit?)[i]'hi' =
        inflateTableDextVals[i]! :=
      (list_getElem_of_eq hpde_fm hi' hi).trans (by simp [getElem!_pos inflateTableDextVals i hi])
    refine ⟨BitVec.ofInt 16 inflateTableDextVals[i]!, ?_, rfl, ?_⟩
    · rw [hp2.readVal hlt_de, ← hget]; exact hr
    · have hb := dext_bounds hi
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
      omega

private theorem initStatics_order_inv {staticBase strBase : Nat → UInt64}
    {prog0 : Prog} {gEnv : Env} {idx ns : Nat} {m m' : Mem} {fnAcc fnList : List (String × Env)}
    {preTUs postTUs : List TU} {tu : TU}
    {preFns postFns : List (String × FnDef)} {nm : String} {f : FnDef}
    (hsplitTU : Zlib.allTUs = preTUs ++ tu :: postTUs)
    (hsplitFn : tuFnEntries tu = preFns ++ (nm, f) :: postFns)
    (hcol : collectFnStatics f.body = [orderStaticDecl])
    (hfn : f.name = nm)
    (hinit : initProg.initStatics staticBase strBase prog0 gEnv idx ns m fnAcc
      ((Zlib.allFiles.flatMap (·.items)).filterMap fun | .fnDef g => some g | _ => none) = some (fnList, m')) :
    ∃ b_ord blk_ord,
      (fnList.lookup nm).getD [] = [("order", b_ord, u16ArrTy 19)] ∧
      m'.blocks b_ord = some blk_ord ∧ blk_ord.perm = .ro ∧ blk_ord.kind = .global ∧
        blk_ord.size = 38 ∧ blk_ord.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_ord.bytes i = .byte u) ∧
        (∀ i < 19, ∃ bv : BitVec 16,
          Sem.readVal prog0.tags m' b_ord (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
          bv = BitVec.ofInt 16 inflateOrderVals[i]! ∧ bv.toNat < 19) := by
  have hfnSplit := fnDefs_split_of_tu hsplitTU hsplitFn
  rcases hfnSplit with ⟨pre, post, hfd, hnodup⟩
  rw [hfd] at hinit
  obtain ⟨idx1, ns1, m1, sEnv, m2, idx2, ns2, _, hfold, hp2, hlu⟩ :=
    initStatics_split_mem hnodup hinit
  rw [hcol] at hfold
  obtain ⟨b_ord, t_ord, hal_ord, hsEnv⟩ := foldlM_one_allocVarInit hfold
  obtain ⟨hpord_all, hpord_fm⟩ := mkU16StaticDecl_parse inflateOrderVals order_all_ok
  obtain ⟨rfl, rfl, rfl, _, blk_ord, hblk_ord, hsz_ord, hal_ord', hk_ord, hperm_ord, hconcr_ord, hread_ord⟩ :=
    allocVarInit_intList_inv (ek := .u16) (n := 19) rfl rfl u16_unqual (u16_sizeof _) (u16_alignof _)
      rfl rfl hpord_all hal_ord
  have hlt_ord : m1.nextBlock < m2.nextBlock := lt_nextBlock_of_some hblk_ord
  have hperm_ord' : blk_ord.perm = .ro := by rw [hperm_ord]; rfl
  refine ⟨m1.nextBlock, blk_ord, ?_, by rw [hp2.2 _ hlt_ord, hblk_ord], hperm_ord', hk_ord,
    by rw [hsz_ord]; rfl, by rw [hal_ord']; rfl, hconcr_ord, fun i hi => ?_⟩
  · rw [← hfn, hlu, hsEnv]; rfl
  · have hi' : i < ((inflateOrderVals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).filterMap parseIntInit?).length := by
      rw [hpord_fm]; exact hi
    have hr := hread_ord i hi'
    have hget : ((inflateOrderVals.map fun v => InitVal.expr (.lit v .i32 .none .dec none)).filterMap parseIntInit?)[i]'hi' =
        inflateOrderVals[i]! :=
      (list_getElem_of_eq hpord_fm hi' hi).trans (by simp [getElem!_pos inflateOrderVals i hi])
    refine ⟨BitVec.ofInt 16 inflateOrderVals[i]!, ?_, rfl, ?_⟩
    · rw [hp2.readVal hlt_ord, ← hget]; exact hr
    · have hb := order_bounds hi
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
      omega

private theorem initStatics_inflateBack_inv {staticBase strBase : Nat → UInt64}
    {prog0 : Prog} {gEnv : Env} {idx ns : Nat} {m m' : Mem} {fnAcc fnList : List (String × Env)}
    (hinit : initProg.initStatics staticBase strBase prog0 gEnv idx ns m fnAcc
      ((Zlib.allFiles.flatMap (·.items)).filterMap fun | .fnDef f => some f | _ => none) = some (fnList, m')) :
    ∃ b_ord blk_ord,
      (fnList.lookup "inflateBack").getD [] = [("order", b_ord, u16ArrTy 19)] ∧
      m'.blocks b_ord = some blk_ord ∧ blk_ord.perm = .ro ∧ blk_ord.kind = .global ∧
        blk_ord.size = 38 ∧ blk_ord.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_ord.bytes i = .byte u) ∧
        (∀ i < 19, ∃ bv : BitVec 16,
          Sem.readVal prog0.tags m' b_ord (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
          bv = BitVec.ofInt 16 inflateOrderVals[i]! ∧ bv.toNat < 19) :=
  initStatics_order_inv allTUs_split_infback
    (preFns := [("inflateBackInit_", Zlib.Infback.infbackTU_fn_inflateBackInit_)])
    (postFns := [("inflateBackEnd", Zlib.Infback.infbackTU_fn_inflateBackEnd)])
    (nm := "inflateBack") (f := Zlib.Infback.infbackTU_fn_inflateBack)
    (by rw [infbackTU_fnEntries]; rfl) collectFnStatics_inflateBack rfl hinit

private theorem initStatics_inflate_inv {staticBase strBase : Nat → UInt64}
    {prog0 : Prog} {gEnv : Env} {idx ns : Nat} {m m' : Mem} {fnAcc fnList : List (String × Env)}
    (hinit : initProg.initStatics staticBase strBase prog0 gEnv idx ns m fnAcc
      ((Zlib.allFiles.flatMap (·.items)).filterMap fun | .fnDef f => some f | _ => none) = some (fnList, m')) :
    ∃ b_ord blk_ord,
      (fnList.lookup "inflate").getD [] = [("order", b_ord, u16ArrTy 19)] ∧
      m'.blocks b_ord = some blk_ord ∧ blk_ord.perm = .ro ∧ blk_ord.kind = .global ∧
        blk_ord.size = 38 ∧ blk_ord.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_ord.bytes i = .byte u) ∧
        (∀ i < 19, ∃ bv : BitVec 16,
          Sem.readVal prog0.tags m' b_ord (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
          bv = BitVec.ofInt 16 inflateOrderVals[i]! ∧ bv.toNat < 19) := by
  have hsplitFn : tuFnEntries Zlib.Inflate.inflateTU =
      [("inflateStateCheck", Zlib.Inflate.inflateTU_fn_inflateStateCheck),
       ("inflateResetKeep", Zlib.Inflate.inflateTU_fn_inflateResetKeep),
       ("inflateReset", Zlib.Inflate.inflateTU_fn_inflateReset),
       ("inflateReset2", Zlib.Inflate.inflateTU_fn_inflateReset2),
       ("inflateInit2_", Zlib.Inflate.inflateTU_fn_inflateInit2_),
       ("inflateInit_", Zlib.Inflate.inflateTU_fn_inflateInit_),
       ("inflatePrime", Zlib.Inflate.inflateTU_fn_inflatePrime),
       ("updatewindow", Zlib.Inflate.inflateTU_fn_updatewindow)] ++
      ("inflate", Zlib.Inflate.inflateTU_fn_inflate) ::
      [("inflateEnd", Zlib.Inflate.inflateTU_fn_inflateEnd),
       ("inflateGetDictionary", Zlib.Inflate.inflateTU_fn_inflateGetDictionary),
       ("inflateSetDictionary", Zlib.Inflate.inflateTU_fn_inflateSetDictionary),
       ("inflateGetHeader", Zlib.Inflate.inflateTU_fn_inflateGetHeader),
       ("syncsearch", Zlib.Inflate.inflateTU_fn_syncsearch),
       ("inflateSync", Zlib.Inflate.inflateTU_fn_inflateSync),
       ("inflateSyncPoint", Zlib.Inflate.inflateTU_fn_inflateSyncPoint),
       ("inflateCopy", Zlib.Inflate.inflateTU_fn_inflateCopy),
       ("inflateUndermine", Zlib.Inflate.inflateTU_fn_inflateUndermine),
       ("inflateValidate", Zlib.Inflate.inflateTU_fn_inflateValidate),
       ("inflateMark", Zlib.Inflate.inflateTU_fn_inflateMark),
       ("inflateCodesUsed", Zlib.Inflate.inflateTU_fn_inflateCodesUsed)] := by
    rw [inflateTU_fnEntries]; rfl
  exact initStatics_order_inv allTUs_split_inflate hsplitFn collectFnStatics_inflate rfl hinit

private theorem initStatics_deflateInit2_inv {staticBase strBase : Nat → UInt64}
    {prog0 : Prog} {gEnv : Env} {idx ns : Nat} {m m' : Mem} {fnAcc fnList : List (String × Env)}
    (hinit : initProg.initStatics staticBase strBase prog0 gEnv idx ns m fnAcc
      ((Zlib.allFiles.flatMap (·.items)).filterMap fun | .fnDef f => some f | _ => none) = some (fnList, m')) :
    ∃ b_mv blk_mv,
      (fnList.lookup "deflateInit2_").getD [] =
        [("my_version", b_mv, .array (.const_ (.int .i8)) (some 15))] ∧
      m'.blocks b_mv = some blk_mv ∧ blk_mv.perm = .ro ∧ blk_mv.kind = .global ∧
        blk_mv.size = 15 ∧ blk_mv.align = 1 ∧ (∀ i, ∃ u : UInt8, blk_mv.bytes i = .byte u) ∧
        m'.strlenAt b_mv 0 = some 14 ∧
        Sem.readVal prog0.tags m' b_mv 0 (.int .i8) = some (.int .i8 (BitVec.ofNat 8 49)) := by
  have hsplitFn : tuFnEntries Zlib.Deflate.deflateTU =
      [("slide_hash", Zlib.Deflate.deflateTU_fn_slide_hash),
       ("read_buf", Zlib.Deflate.deflateTU_fn_read_buf),
       ("fill_window", Zlib.Deflate.deflateTU_fn_fill_window),
       ("deflateInit_", Zlib.Deflate.deflateTU_fn_deflateInit_)] ++
      ("deflateInit2_", Zlib.Deflate.deflateTU_fn_deflateInit2_) ::
      [("deflateStateCheck", Zlib.Deflate.deflateTU_fn_deflateStateCheck),
       ("deflateSetDictionary", Zlib.Deflate.deflateTU_fn_deflateSetDictionary),
       ("deflateGetDictionary", Zlib.Deflate.deflateTU_fn_deflateGetDictionary),
       ("deflateResetKeep", Zlib.Deflate.deflateTU_fn_deflateResetKeep),
       ("lm_init", Zlib.Deflate.deflateTU_fn_lm_init),
       ("deflateReset", Zlib.Deflate.deflateTU_fn_deflateReset),
       ("deflateSetHeader", Zlib.Deflate.deflateTU_fn_deflateSetHeader),
       ("deflatePending", Zlib.Deflate.deflateTU_fn_deflatePending),
       ("deflateUsed", Zlib.Deflate.deflateTU_fn_deflateUsed),
       ("deflatePrime", Zlib.Deflate.deflateTU_fn_deflatePrime),
       ("deflateParams", Zlib.Deflate.deflateTU_fn_deflateParams),
       ("deflateTune", Zlib.Deflate.deflateTU_fn_deflateTune),
       ("deflateBound_z", Zlib.Deflate.deflateTU_fn_deflateBound_z),
       ("deflateBound", Zlib.Deflate.deflateTU_fn_deflateBound),
       ("putShortMSB", Zlib.Deflate.deflateTU_fn_putShortMSB),
       ("flush_pending", Zlib.Deflate.deflateTU_fn_flush_pending),
       ("deflate", Zlib.Deflate.deflateTU_fn_deflate),
       ("deflateEnd", Zlib.Deflate.deflateTU_fn_deflateEnd),
       ("deflateCopy", Zlib.Deflate.deflateTU_fn_deflateCopy),
       ("longest_match", Zlib.Deflate.deflateTU_fn_longest_match),
       ("deflate_stored", Zlib.Deflate.deflateTU_fn_deflate_stored),
       ("deflate_fast", Zlib.Deflate.deflateTU_fn_deflate_fast),
       ("deflate_slow", Zlib.Deflate.deflateTU_fn_deflate_slow),
       ("deflate_rle", Zlib.Deflate.deflateTU_fn_deflate_rle),
       ("deflate_huff", Zlib.Deflate.deflateTU_fn_deflate_huff)] := by
    rw [deflateTU_fnEntries]; rfl
  have hfnSplit := fnDefs_split_of_tu allTUs_split_deflate hsplitFn
  rcases hfnSplit with ⟨pre, post, hfd, hnodup⟩
  rw [hfd] at hinit
  obtain ⟨idx1, ns1, m1, sEnv, m2, idx2, ns2, _, hfold, hp2, hlu⟩ :=
    initStatics_split_mem hnodup hinit
  rw [collectFnStatics_deflateInit2_] at hfold
  obtain ⟨b_mv, t_mv, hal_mv, hsEnv⟩ := foldlM_one_allocVarInit hfold
  obtain ⟨rfl, rfl, rfl, _, blk_mv, hblk_mv, hsz_mv, hal_mv', hk_mv, hperm_mv, hconcr_mv, hstr_mv, hread_mv⟩ :=
    allocVarInit_strLit_inv rfl rfl myVersion_str_ok hal_mv
  have hlt_mv : m1.nextBlock < m2.nextBlock := lt_nextBlock_of_some hblk_mv
  have hbyte0 : (("1.4.0.1-motley".toUTF8[0]?).getD 0).toNat = 49 := rfl
  have hlen14 : "1.4.0.1-motley".utf8ByteSize = 14 := rfl
  have hname_def : Zlib.Deflate.deflateTU_fn_deflateInit2_.name = "deflateInit2_" := rfl
  rw [hname_def] at hlu
  refine ⟨m1.nextBlock, blk_mv, ?_, by rw [hp2.2 _ hlt_mv, hblk_mv], hperm_mv, hk_mv,
    by rw [hsz_mv, hlen14], hal_mv', hconcr_mv,
    by rw [hp2.strlenAt hlt_mv, hstr_mv, hlen14], ?_⟩
  · rw [hlu, hsEnv, hlen14]; rfl
  · rw [hp2.readVal hlt_mv]
    have hr0 := hread_mv 0 (by rw [hlen14]; decide)
    rw [hbyte0] at hr0
    exact hr0

end ProgFnStaticsSection

/-! ## 4. Complete `InitLibzAllProps` and `initLibz_allProps` -/

section LibzAllPropsSection

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

/-! ### Memory & Initializer Step Helpers -/

private theorem int64_ofNat_toNat_eq {n : Nat} (hn : n < ptrDiffLimit) :
    (Int64.ofNat n).toInt.toNat = n := by
  change (Int64.ofInt (n : Nat)).toInt.toNat = n
  rw [ptrDiffLimit_val] at hn
  rw [int64_ofInt_toInt (by omega) (by omega)]
  exact Int.toNat_natCast n

private theorem isAligned_of_dvd {blk : Block} {off a : Nat}
    (ha : 0 < a) (hdvd : a ∣ blk.align) (hoff : a ∣ off) (hoff_lim : off < ptrDiffLimit) :
    Mem.isAligned blk (Int64.ofNat off) a = true := by
  rw [isAligned_iff]
  have hoff_int : (Int64.ofNat off).toInt = (off : Int) := int64_ofNat_toInt hoff_lim
  refine ⟨by rw [hoff_int]; exact Int.natCast_nonneg off, ha, ?_⟩
  rw [hoff_int, Int.toNat_natCast]
  have hba : a ∣ blk.baseAddr.toNat := Nat.dvd_trans hdvd (Nat.dvd_of_mod_eq_zero blk.baseAligned)
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add hba hoff)

private theorem writeBytes_preserve_and_write {m m' : Mem} {b : BlockId} {blk : Block}
    {off : Nat} {bs : List MemByte}
    (hb : m.blocks b = some blk)
    (hwb : m.writeBytes b (Int64.ofNat off) bs = some m')
    (hoff_lim : off < ptrDiffLimit) :
    m'.nextBlock = m.nextBlock ∧
    (∀ y, y ≠ b → m'.blocks y = m.blocks y) ∧
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.perm = blk.perm ∧
      blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr ∧
      (∀ j, j < off → blk'.bytes j = blk.bytes j) ∧
      (∀ j, off + bs.length ≤ j → blk'.bytes j = blk.bytes j) ∧
      (∀ j (hj : j < bs.length), blk'.bytes (off + j) = bs[j]) := by
  have hblk' := writeBytes_blocks_eq hb hwb
  have hoff_nat : (Int64.ofNat off).toInt.toNat = off := int64_ofNat_toNat_eq hoff_lim
  refine ⟨writeBytes_nextBlock hwb, fun y hy => writeBytes_blocks_ne hwb hy, _, hblk',
    rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro j hj; dsimp only; rw [hoff_nat]
    have hnot : ¬ (off ≤ j ∧ j < off + bs.length) := by omega
    simp only [hnot, ↓reduceIte]
  · intro j hj; dsimp only; rw [hoff_nat]
    have hnot : ¬ (off ≤ j ∧ j < off + bs.length) := by omega
    simp only [hnot, ↓reduceIte]
  · intro j hj; dsimp only; rw [hoff_nat]
    have hcond : off ≤ off + j ∧ off + j < off + bs.length := by omega
    rw [ite_eq_left hcond, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

private theorem readBytes_of_exact {m : Mem} {b : BlockId} {blk : Block} {off : Nat} {bs : List MemByte}
    (hb : m.blocks b = some blk) (hoff : off < ptrDiffLimit)
    (hin : Mem.inBounds blk (Int64.ofNat off) bs.length = true)
    (hbytes : ∀ j (hj : j < bs.length), blk.bytes (off + j) = bs[j]) :
    m.readBytes b (Int64.ofNat off) bs.length = some bs := by
  rw [readBytes_of_bounds hb hin]
  congr 1
  rw [int64_ofNat_toNat_eq hoff]
  apply List.ext_getElem
  · simp
  · intro j _ hj2
    rw [List.getElem_map, List.getElem_range]
    exact hbytes j hj2

private theorem readVal_int_of_exact {tags : TypeEnv} {m : Mem} {b : BlockId} {blk : Block} {off : Nat}
    {ty : CTy} {k : IntKind} {bv : BitVec k.bits}
    (htyu : ty.unqual = .int k)
    (hb : m.blocks b = some blk) (hoff : off < ptrDiffLimit)
    (hin : Mem.inBounds blk (Int64.ofNat off) k.bytes = true)
    (hal : Mem.isAligned blk (Int64.ofNat off) k.align = true)
    (hbytes : ∀ j (hj : j < (Mem.encodeInt k bv).length), blk.bytes (off + j) = (Mem.encodeInt k bv)[j]) :
    Sem.readVal tags m b (Int64.ofNat off) ty = some (.int k bv) := by
  have hin' : Mem.inBounds blk (Int64.ofNat off) (Mem.encodeInt k bv).length = true := by
    rw [encodeInt_length]; exact hin
  have hrb := readBytes_of_exact hb hoff hin' hbytes
  rw [encodeInt_length] at hrb
  unfold Sem.readVal
  dsimp only
  rw [htyu]
  simp only [CTy.unqual, CTy.intKind?, hb, hal, guard_true, bind, Option.bind]
  rw [hrb]
  dsimp [pure]
  rw [decodeInt_encodeInt]

private theorem readVal_ptr_of_exact {tags : TypeEnv} {m : Mem} {b : BlockId} {blk : Block} {off : Nat}
    {ty to : CTy} {pb : BlockId} {poff : Int64}
    (htyu : ty.unqual = .ptr to)
    (hb : m.blocks b = some blk) (hoff : off < ptrDiffLimit)
    (hin : Mem.inBounds blk (Int64.ofNat off) 8 = true)
    (hal : Mem.isAligned blk (Int64.ofNat off) 8 = true)
    (hbytes : ∀ j (hj : j < (Mem.encodePtr pb poff).length), blk.bytes (off + j) = (Mem.encodePtr pb poff)[j]) :
    Sem.readVal tags m b (Int64.ofNat off) ty = some (.ptr pb poff) := by
  have hin' : Mem.inBounds blk (Int64.ofNat off) (Mem.encodePtr pb poff).length = true := by
    rw [encodePtr_length]; exact hin
  have hrb := readBytes_of_exact hb hoff hin' hbytes
  rw [encodePtr_length] at hrb
  unfold Sem.readVal
  dsimp only
  rw [htyu]
  simp only [hb, hal, guard_true, bind, Option.bind]
  rw [hrb]
  dsimp [pure]
  rw [decodePtr_encodePtr]

private theorem readVal_null_of_exact {tags : TypeEnv} {m : Mem} {b : BlockId} {blk : Block} {off : Nat}
    {ty to : CTy}
    (htyu : ty.unqual = .ptr to)
    (hb : m.blocks b = some blk) (hoff : off < ptrDiffLimit)
    (hin : Mem.inBounds blk (Int64.ofNat off) 8 = true)
    (hal : Mem.isAligned blk (Int64.ofNat off) 8 = true)
    (hbytes : ∀ j (hj : j < Mem.encodeNull.length), blk.bytes (off + j) = Mem.encodeNull[j]) :
    Sem.readVal tags m b (Int64.ofNat off) ty = some .null := by
  have hin' : Mem.inBounds blk (Int64.ofNat off) Mem.encodeNull.length = true := by
    rw [encodeNull_length]; exact hin
  have hrb := readBytes_of_exact hb hoff hin' hbytes
  rw [encodeNull_length] at hrb
  unfold Sem.readVal
  dsimp only
  rw [htyu]
  simp only [hb, hal, guard_true, bind, Option.bind]
  rw [hrb]
  dsimp [pure]
  rw [decodePtr_encodeNull]

private theorem readVal_fnPtr_of_exact {tags : TypeEnv} {m : Mem} {b : BlockId} {blk : Block} {off : Nat}
    {ty ret : CTy} {ps : List CTy} {variadic : Bool} {fnm : String}
    (htyu : ty.unqual = .fnPtr ret ps variadic)
    (hb : m.blocks b = some blk) (hoff : off < ptrDiffLimit)
    (hin : Mem.inBounds blk (Int64.ofNat off) 8 = true)
    (hal : Mem.isAligned blk (Int64.ofNat off) 8 = true)
    (hbytes : ∀ j (hj : j < (Mem.encodeFnPtr fnm).length), blk.bytes (off + j) = (Mem.encodeFnPtr fnm)[j]) :
    Sem.readVal tags m b (Int64.ofNat off) ty = some (.fnPtr fnm) := by
  have hin' : Mem.inBounds blk (Int64.ofNat off) (Mem.encodeFnPtr fnm).length = true := by
    rw [encodeFnPtr_length]; exact hin
  have hrb := readBytes_of_exact hb hoff hin' hbytes
  rw [encodeFnPtr_length] at hrb
  unfold Sem.readVal
  dsimp only
  rw [htyu]
  simp only [hb, hal, guard_true, bind, Option.bind]
  rw [hrb]
  dsimp [pure]
  rw [decodePtr_encodeFnPtr]

private theorem writeInitVal_anonStruct {prog : Prog} {env : Env} {m : Mem}
    {strBase : Nat → UInt64} {b : BlockId} {off : Int64} {ty : CTy}
    {flds : List (String × CTy)} {xs : List InitVal} {ns : Nat}
    (htyu : ty.unqual = .anonStruct flds) :
    writeInitVal prog env m strBase b off ty (.list xs) ns =
      writeInitFields prog env m strBase b off.toInt.toNat 0 flds xs ns := by
  rw [writeInitVal.eq_def]; simp only [htyu]

private theorem writeInitVal_structTy {prog : Prog} {env : Env} {m : Mem}
    {strBase : Nat → UInt64} {b : BlockId} {off : Int64} {ty : CTy}
    {tag : String} {flds : List (String × CTy)} {xs : List InitVal} {ns : Nat}
    (htyu : ty.unqual = .structTy tag)
    (hlook : prog.tags.lookup tag = some (.structDef flds)) :
    writeInitVal prog env m strBase b off ty (.list xs) ns =
      writeInitFields prog env m strBase b off.toInt.toNat 0 flds xs ns := by
  rw [writeInitVal.eq_def]; simp only [htyu, hlook]

private theorem writeInitVal_anonUnion {prog : Prog} {env : Env} {m : Mem}
    {strBase : Nat → UInt64} {b : BlockId} {off : Int64} {ty : CTy}
    {fnm : String} {fty : CTy} {frest : List (String × CTy)}
    {x : InitVal} {tail : List InitVal} {ns : Nat}
    (htyu : ty.unqual = .anonUnion ((fnm, fty) :: frest)) :
    writeInitVal prog env m strBase b off ty (.list (x :: tail)) ns =
      writeInitVal prog env m strBase b off fty x ns := by
  rw [writeInitVal.eq_def]; simp only [htyu]

private theorem writeInitVal_list {prog : Prog} {env : Env} {m : Mem}
    {strBase : Nat → UInt64} {b : BlockId} {off : Int64} {ty : CTy}
    {el : CTy} {len? : Option Nat} {xs : List InitVal} {ns : Nat}
    (htyu : ty.unqual = .array el len?) :
    writeInitVal prog env m strBase b off ty (.list xs) ns =
      writeInitList prog env m strBase b off el 0 xs ns := by
  rw [writeInitVal.eq_def]; simp only [htyu]

private theorem writeInitFields_cons {prog : Prog} {env : Env} {m : Mem} {strBase : Nat → UInt64}
    {b : BlockId} {baseOff offAcc : Nat} {fnm : String} {fty : CTy} {frest : List (String × CTy)}
    {iv : InitVal} {irest : List InitVal} {ns : Nat} :
    writeInitFields prog env m strBase b baseOff offAcc ((fnm, fty) :: frest) (iv :: irest) ns =
      (let foff := alignUp offAcc (max 1 (alignofTy prog.tags fty))
       do let (m1, ns1) ← writeInitVal prog env m strBase b (Int64.ofNat (baseOff + foff)) fty iv ns
          writeInitFields prog env m1 strBase b baseOff (foff + sizeofTy prog.tags fty) frest irest ns1) := by
  rw [writeInitFields.eq_def]

private theorem writeInitFields_nil {prog : Prog} {env : Env} {m : Mem} {strBase : Nat → UInt64}
    {b : BlockId} {baseOff offAcc : Nat} {ns : Nat} :
    writeInitFields prog env m strBase b baseOff offAcc [] [] ns = some (m, ns) := by
  rw [writeInitFields.eq_def]

private theorem writeVal_int_step_mem {m m' : Mem} {b : BlockId} {blk : Block} {off : Nat}
    {ty : CTy} {k k1 : IntKind} {bv1 : BitVec k1.bits} {iv : Int}
    (hnc : ty.isConst = false) (htyu : ty.unqual = .int k)
    (hb : m.blocks b = some blk) (hoff_lim : off < ptrDiffLimit)
    (hval : valAsInt? (.int k1 bv1) = some (k1, iv))
    (hw : writeVal m b (Int64.ofNat off) ty (.int k1 bv1) = some m') :
    m'.nextBlock = m.nextBlock ∧
    (∀ y, y ≠ b → m'.blocks y = m.blocks y) ∧
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.perm = blk.perm ∧
      blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr ∧
      (∀ j, j < off → blk'.bytes j = blk.bytes j) ∧
      (∀ j, off + k.bytes ≤ j → blk'.bytes j = blk.bytes j) ∧
      (∀ j (hj : j < k.bytes),
        blk'.bytes (off + j) = (Mem.encodeInt k (BitVec.ofInt k.bits iv))[j]'(by rw [encodeInt_length]; exact hj)) := by
  unfold writeVal at hw
  simp only [hnc, Bool.not_false, guard_true, hb, htyu, hval, bind, Option.bind] at hw
  dsimp only [CTy.unqual, CTy.intKind?, guard, Pure.pure] at hw
  cases hal : Mem.isAligned blk (Int64.ofNat off) k.align
  · rw [hal] at hw; cases hw
  · rw [hal] at hw
    obtain ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      writeBytes_preserve_and_write hb hw hoff_lim
    rw [encodeInt_length] at h9
    exact ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7, h8, h9, fun j hj => h10 j (by rw [encodeInt_length]; exact hj)⟩

private theorem writeVal_ptr_step_mem {m m' : Mem} {b : BlockId} {blk : Block} {off : Nat}
    {ty to : CTy} {pb : BlockId} {poff : Int64}
    (hnc : ty.isConst = false) (htyu : ty.unqual = .ptr to)
    (hb : m.blocks b = some blk) (hoff_lim : off < ptrDiffLimit)
    (hw : writeVal m b (Int64.ofNat off) ty (.ptr pb poff) = some m') :
    m'.nextBlock = m.nextBlock ∧
    (∀ y, y ≠ b → m'.blocks y = m.blocks y) ∧
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.perm = blk.perm ∧
      blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr ∧
      (∀ j, j < off → blk'.bytes j = blk.bytes j) ∧
      (∀ j, off + 8 ≤ j → blk'.bytes j = blk.bytes j) ∧
      (∀ j (hj : j < 8),
        blk'.bytes (off + j) = (Mem.encodePtr pb poff)[j]'(by rw [encodePtr_length]; exact hj)) := by
  unfold writeVal at hw
  simp only [hnc, Bool.not_false, guard_true, hb, htyu, bind, Option.bind] at hw
  dsimp only [guard, Pure.pure] at hw
  cases hal : Mem.isAligned blk (Int64.ofNat off) 8
  · rw [hal] at hw; cases hw
  · rw [hal] at hw
    obtain ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      writeBytes_preserve_and_write hb hw hoff_lim
    rw [encodePtr_length] at h9
    exact ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7, h8, h9, fun j hj => h10 j (by rw [encodePtr_length]; exact hj)⟩

private theorem writeVal_null_step_mem {m m' : Mem} {b : BlockId} {blk : Block} {off : Nat}
    {ty to : CTy}
    (hnc : ty.isConst = false) (htyu : ty.unqual = .ptr to)
    (hb : m.blocks b = some blk) (hoff_lim : off < ptrDiffLimit)
    (hw : writeVal m b (Int64.ofNat off) ty .null = some m') :
    m'.nextBlock = m.nextBlock ∧
    (∀ y, y ≠ b → m'.blocks y = m.blocks y) ∧
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.perm = blk.perm ∧
      blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr ∧
      (∀ j, j < off → blk'.bytes j = blk.bytes j) ∧
      (∀ j, off + 8 ≤ j → blk'.bytes j = blk.bytes j) ∧
      (∀ j (hj : j < 8),
        blk'.bytes (off + j) = Mem.encodeNull[j]'(by rw [encodeNull_length]; exact hj)) := by
  unfold writeVal at hw
  simp only [hnc, Bool.not_false, guard_true, hb, htyu, bind, Option.bind] at hw
  dsimp only [guard, Pure.pure] at hw
  cases hal : Mem.isAligned blk (Int64.ofNat off) 8
  · rw [hal] at hw; cases hw
  · rw [hal] at hw
    obtain ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      writeBytes_preserve_and_write hb hw hoff_lim
    rw [encodeNull_length] at h9
    exact ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7, h8, h9, fun j hj => h10 j (by rw [encodeNull_length]; exact hj)⟩

private theorem writeVal_fnPtr_step_mem {m m' : Mem} {b : BlockId} {blk : Block} {off : Nat}
    {ty ret : CTy} {ps : List CTy} {variadic : Bool} {fnm : String}
    (hnc : ty.isConst = false) (htyu : ty.unqual = .fnPtr ret ps variadic)
    (hb : m.blocks b = some blk) (hoff_lim : off < ptrDiffLimit)
    (hw : writeVal m b (Int64.ofNat off) ty (.fnPtr fnm) = some m') :
    m'.nextBlock = m.nextBlock ∧
    (∀ y, y ≠ b → m'.blocks y = m.blocks y) ∧
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.perm = blk.perm ∧
      blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr ∧
      (∀ j, j < off → blk'.bytes j = blk.bytes j) ∧
      (∀ j, off + 8 ≤ j → blk'.bytes j = blk.bytes j) ∧
      (∀ j (hj : j < 8),
        blk'.bytes (off + j) = (Mem.encodeFnPtr fnm)[j]'(by rw [encodeFnPtr_length]; exact hj)) := by
  unfold writeVal at hw
  simp only [hnc, Bool.not_false, guard_true, hb, htyu, bind, Option.bind] at hw
  dsimp only [guard, Pure.pure] at hw
  cases hal : Mem.isAligned blk (Int64.ofNat off) 8
  · rw [hal] at hw; cases hw
  · rw [hal] at hw
    obtain ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      writeBytes_preserve_and_write hb hw hoff_lim
    rw [encodeFnPtr_length] at h9
    exact ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7, h8, h9, fun j hj => h10 j (by rw [encodeFnPtr_length]; exact hj)⟩

private theorem writeInitVal_pureInt_step {prog : Prog} {env : Env} {m m1 : Mem}
    {strBase : Nat → UInt64} {b : BlockId} {blk : Block} {off ns ns1 : Nat}
    {ty : CTy} {k : IntKind} {e : CExpr} {iv : Int}
    (htyu : ty.unqual = .int k) (hev : evalPureLit? e = some iv)
    (hb : m.blocks b = some blk) (hoff_lim : off < ptrDiffLimit)
    (hwr : writeInitVal prog env m strBase b (Int64.ofNat off) ty (.expr e) ns = some (m1, ns1)) :
    ns1 = ns ∧ m1.nextBlock = m.nextBlock ∧ (∀ y, y ≠ b → m1.blocks y = m.blocks y) ∧
    ∃ blk1, m1.blocks b = some blk1 ∧
      blk1.size = blk.size ∧ blk1.align = blk.align ∧ blk1.perm = blk.perm ∧
      blk1.kind = blk.kind ∧ blk1.baseAddr = blk.baseAddr ∧
      (∀ j, j < off → blk1.bytes j = blk.bytes j) ∧
      (∀ j, off + k.bytes ≤ j → blk1.bytes j = blk.bytes j) ∧
      (∀ j (hj : j < k.bytes),
        blk1.bytes (off + j) = (Mem.encodeInt k (BitVec.ofInt k.bits iv))[j]'(by rw [encodeInt_length]; exact hj)) := by
  have hnostr : ∀ s, e ≠ .strLit s := by
    intro s hs; subst hs; cases hev
  rw [writeInitVal_expr_not_strLit hnostr] at hwr
  obtain ⟨k0, bv0, heval0, hval0⟩ := evalConstExpr_of_evalPureLit (prog := prog) (env := env) (m := m) (strBase := strBase) (ns := ns) hev
  rw [heval0] at hwr
  simp only [bind, Option.bind] at hwr
  cases hw : writeVal m b (Int64.ofNat off) ty.stripConst (.int k0 bv0) with
  | none => rw [hw] at hwr; cases hwr
  | some mw =>
    rw [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwr
    rcases hwr with ⟨rfl, rfl⟩
    have htyu' : ty.stripConst.unqual = .int k := by rw [stripConst_unqual, htyu]
    obtain ⟨h1, h2, blk1, hb1, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      writeVal_int_step_mem (stripConst_isConst ty) htyu' hb hoff_lim hval0 hw
    exact ⟨rfl, h1, h2, blk1, hb1, h3, h4, h5, h6, h7, h8, h9, h10⟩

private theorem evalConstExpr_cast_null_ptr {prog : Prog} {env : Env} {m : Mem}
    {strBase : Nat → UInt64} {ns : Nat} {pty to : CTy}
    (hpty : pty.unqual = .ptr to) :
    evalConstExpr prog env m strBase ns (.cast pty (.lit 0 .i32 .none .dec none)) =
      some (.null, pty, m, ns) := by
  rw [evalConstExpr.eq_def]
  change (do
    let (v, _, m', ns') ← evalConstExpr prog env m strBase ns (.lit 0 .i32 .none .dec none)
    let cv ← castVal m' pty v
    pure (cv, pty, m', ns')) = some (.null, pty, m, ns)
  have h0 : evalConstExpr prog env m strBase ns (.lit 0 .i32 .none .dec none) =
      some (.int .i32 0, .int .i32, m, ns) := rfl
  rw [h0]
  dsimp only [bind, Option.bind, pure, Pure.pure]
  have hcast : castVal m pty (.int .i32 0) = some .null := by
    unfold castVal
    simp only [hpty]
    rfl
  rw [hcast]

private theorem evalConstExpr_var_array {prog : Prog} {env : Env} {m : Mem}
    {strBase : Nat → UInt64} {ns : Nat} {x : String} {b : BlockId} {el : CTy} {len? : Option Nat}
    (hlook : env.lookup x = some (b, .array el len?)) :
    evalConstExpr prog env m strBase ns (.var x) = some (.ptr b 0, .ptr el, m, ns) := by
  rw [evalConstExpr.eq_def]
  dsimp only
  rw [hlook]
  rfl

private theorem evalConstExpr_var_fnPtr {prog : Prog} {env : Env} {m : Mem}
    {strBase : Nat → UInt64} {ns : Nat} {x : String} {ret : CTy} {ps : List CTy} {variadic : Bool}
    (hlook : env.lookup x = none)
    (henum : enumConst? prog.tags x = none)
    (hproto : prog.fnProtos x = some (ret, ps, variadic)) :
    evalConstExpr prog env m strBase ns (.var x) =
      some (.fnPtr x, ret.fnPtr ps variadic, m, ns) := by
  rw [evalConstExpr.eq_def]
  dsimp only
  rw [hlook, henum, hproto]
  rfl

private theorem evalConstExpr_256_add_1 (prog : Prog) (env : Env) (m : Mem)
    (strBase : Nat → UInt64) (ns : Nat) :
    evalConstExpr prog env m strBase ns
      (.binary .add (.lit 256 .i32 .none .dec none) (.lit 1 .i32 .none .dec none)) =
      some (.int .i32 (BitVec.ofInt 32 257), .int .i32, m, ns) := by
  rw [evalConstExpr.eq_def]
  change (do
    let (v1, t1, m1, ns1) ← some (Val.int .i32 (BitVec.ofInt 32 256), CTy.int .i32, m, ns)
    let (v2, t2, m2, ns2) ← some (Val.int .i32 (BitVec.ofInt 32 1), CTy.int .i32, m1, ns1)
    let (rv, rt) ← applyBinary {} prog.tags m2 .add v1 t1 v2 t2
    pure (rv, rt, m2, ns2)) = _
  dsimp only [bind, Option.bind, pure, Pure.pure]
  have happ : applyBinary {} prog.tags m .add
      (.int .i32 (BitVec.ofInt 32 256)) (.int .i32)
      (.int .i32 (BitVec.ofInt 32 1)) (.int .i32) =
      some (.int .i32 (BitVec.ofInt 32 257), .int .i32) := rfl
  rw [happ]

private theorem evalConstExpr_257_add_29 (prog : Prog) (env : Env) (m : Mem)
    (strBase : Nat → UInt64) (ns : Nat) :
    evalConstExpr prog env m strBase ns
      (.paren (.binary .add (.binary .add (.lit 256 .i32 .none .dec none) (.lit 1 .i32 .none .dec none))
        (.lit 29 .i32 .none .dec none))) =
      some (.int .i32 (BitVec.ofInt 32 286), .int .i32, m, ns) := by
  rw [evalConstExpr.eq_def]; dsimp only
  rw [evalConstExpr.eq_def]; dsimp only [bind, Option.bind]
  rw [evalConstExpr_256_add_1]; dsimp only
  have h29 : evalConstExpr prog env m strBase ns (.lit 29 .i32 .none .dec none) =
      some (.int .i32 (BitVec.ofInt 32 29), .int .i32, m, ns) := rfl
  rw [h29]; dsimp only
  have happ : applyBinary {} prog.tags m .add
      (.int .i32 (BitVec.ofInt 32 257)) (.int .i32)
      (.int .i32 (BitVec.ofInt 32 29)) (.int .i32) =
      some (.int .i32 (BitVec.ofInt 32 286), .int .i32) := rfl
  rw [happ]; rfl

private theorem bytes_concat_step {blk0 blk1 blk2 : Block} {off : Nat} {bs1 bs2 : List MemByte}
    (h1_lt : ∀ j, j < off → blk1.bytes j = blk0.bytes j)
    (h1_ge : ∀ j, off + bs1.length ≤ j → blk1.bytes j = blk0.bytes j)
    (h1_cur : ∀ j (hj : j < bs1.length), blk1.bytes (off + j) = bs1[j])
    (h2_lt : ∀ j, j < off + bs1.length → blk2.bytes j = blk1.bytes j)
    (h2_ge : ∀ j, off + bs1.length + bs2.length ≤ j → blk2.bytes j = blk1.bytes j)
    (h2_cur : ∀ j (hj : j < bs2.length), blk2.bytes (off + bs1.length + j) = bs2[j]) :
    (∀ j, j < off → blk2.bytes j = blk0.bytes j) ∧
    (∀ j, off + (bs1 ++ bs2).length ≤ j → blk2.bytes j = blk0.bytes j) ∧
    (∀ j (hj : j < (bs1 ++ bs2).length), blk2.bytes (off + j) = (bs1 ++ bs2)[j]) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [h2_lt j (by omega), h1_lt j hj]
  · rw [List.length_append] at hj
    rw [h2_ge j (by omega), h1_ge j (by omega)]
  · rw [List.length_append] at hj
    by_cases hlt1 : j < bs1.length
    · rw [List.getElem_append_left hlt1, h2_lt (off + j) (by omega), h1_cur j hlt1]
    · have hge1 : bs1.length ≤ j := Nat.le_of_not_lt hlt1
      rw [List.getElem_append_right hge1]
      have hj_eq : off + j = off + bs1.length + (j - bs1.length) := by omega
      rw [hj_eq]
      exact h2_cur (j - bs1.length) (by omega)

private theorem bytes_slice_of_concat {blk : Block} {off : Nat} {bs1 bs2 : List MemByte}
    (h : ∀ j (hj : j < (bs1 ++ bs2).length), blk.bytes (off + j) = (bs1 ++ bs2)[j]) :
    (∀ j (hj : j < bs1.length), blk.bytes (off + j) = bs1[j]) ∧
    (∀ j (hj : j < bs2.length), blk.bytes (off + bs1.length + j) = bs2[j]) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have hj' : j < (bs1 ++ bs2).length := by rw [List.length_append]; omega
    have hr := h j hj'
    rw [List.getElem_append_left hj] at hr
    exact hr
  · have hj' : bs1.length + j < (bs1 ++ bs2).length := by rw [List.length_append]; omega
    have hr := h (bs1.length + j) hj'
    rw [List.getElem_append_right (Nat.le_add_right bs1.length j)] at hr
    simp only [Nat.add_sub_cancel_left] at hr
    have heq : off + (bs1.length + j) = off + bs1.length + j := by omega
    rw [← heq]
    exact hr

private theorem writeInitList_stride_inv {α : Type _} {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {b : BlockId} {elemTy : CTy} {esz eal_req : Nat}
    (hsz_el : sizeofTy prog.tags elemTy = esz)
    (parse? : InitVal → Option α)
    (elemBytes : α → List MemByte)
    (hblen : ∀ a, (elemBytes a).length = esz)
    (hstep : ∀ {m m1 : Mem} {blk : Block} {idx ns ns1 : Nat} {iv : InitVal} {a : α},
      parse? iv = some a → m.blocks b = some blk → eal_req ∣ blk.align → esz * (idx + 1) ≤ blk.size →
      writeInitVal prog env m strBase b (Int64.ofNat (esz * idx)) elemTy iv ns = some (m1, ns1) →
      ns1 = ns ∧ m1.nextBlock = m.nextBlock ∧ (∀ y, y ≠ b → m1.blocks y = m.blocks y) ∧
      ∃ blk1, m1.blocks b = some blk1 ∧
        blk1.size = blk.size ∧ blk1.align = blk.align ∧ blk1.perm = blk.perm ∧
        blk1.kind = blk.kind ∧ blk1.baseAddr = blk.baseAddr ∧
        (∀ j, j < esz * idx → blk1.bytes j = blk.bytes j) ∧
        (∀ j, esz * (idx + 1) ≤ j → blk1.bytes j = blk.bytes j) ∧
        (∀ j (hj : j < esz), blk1.bytes (esz * idx + j) = (elemBytes a)[j]'(by rw [hblen]; exact hj)))
    {m m' : Mem} {blk : Block} {idx ns ns' : Nat} {xs : List InitVal}
    (hb : m.blocks b = some blk)
    (hal_req : eal_req ∣ blk.align)
    (hsz_blk : esz * (idx + xs.length) ≤ blk.size)
    (hall : xs.all (fun x => (parse? x).isSome) = true)
    (hwr : writeInitList prog env m strBase b 0 elemTy idx xs ns = some (m', ns')) :
    ns' = ns ∧ m'.nextBlock = m.nextBlock ∧ (∀ y, y ≠ b → m'.blocks y = m.blocks y) ∧
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.perm = blk.perm ∧
      blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr ∧
      (∀ j, j < esz * idx → blk'.bytes j = blk.bytes j) ∧
      (∀ j, esz * (idx + xs.length) ≤ j → blk'.bytes j = blk.bytes j) ∧
      (∀ (i : Nat) (hi : i < (xs.filterMap parse?).length),
        ∀ j (hj : j < esz),
          blk'.bytes (esz * (idx + i) + j) =
            (elemBytes (xs.filterMap parse?)[i])[j]'(by rw [hblen]; exact hj)) := by
  induction xs generalizing idx m ns blk with
  | nil =>
    rw [writeInitList.eq_def] at hwr
    cases hwr
    refine ⟨rfl, rfl, fun _ _ => rfl, blk, hb, rfl, rfl, rfl, rfl, rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ hi => by cases hi⟩
  | cons iv rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rcases hall with ⟨hiv_some, hrest_all⟩
    cases hp : parse? iv with
    | none => rw [hp] at hiv_some; cases hiv_some
    | some a =>
      rw [writeInitList.eq_def] at hwr
      dsimp only at hwr
      rw [hsz_el] at hwr
      simp only [bind, Option.bind] at hwr
      have hoff_eq : Int64.ofInt ((0 : Int64).toInt + (idx : Int) * (esz : Int)) = Int64.ofNat (esz * idx) := by
        have h0 : (0 : Int64).toInt = 0 := rfl
        rw [h0, Int.zero_add, Int.mul_comm]
        rfl
      rw [hoff_eq] at hwr
      cases hs : writeInitVal prog env m strBase b (Int64.ofNat (esz * idx)) elemTy iv ns with
      | none => rw [hs] at hwr; cases hwr
      | some p1 =>
        rcases p1 with ⟨m1, ns1⟩
        rw [hs] at hwr
        dsimp only at hwr
        have hidx1_le : esz * (idx + 1) ≤ blk.size := by
          simp only [List.length_cons] at hsz_blk
          exact Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) hsz_blk
        obtain ⟨hns1, hm1_next, hm1_ne, blk1, hb1, hsz1, hal1, hperm1, hk1, hba1, hlt1, hge1, hcur1⟩ :=
          hstep hp hb hal_req hidx1_le hs
        have hsz_rest : esz * (idx + 1 + rest.length) ≤ blk1.size := by
          rw [hsz1]; simp only [List.length_cons] at hsz_blk
          have : idx + 1 + rest.length = idx + (rest.length + 1) := by omega
          rw [this]; exact hsz_blk
        obtain ⟨hns_eq, hm_next, hm_ne, blk', hb', hsz', hal', hperm', hk', hba', hlt_bytes, hge_bytes, hread_rest⟩ :=
          ih hb1 (by rw [hal1]; exact hal_req) hsz_rest hrest_all hwr
        refine ⟨hns_eq.trans hns1, hm_next.trans hm1_next, fun y hy => ?_,
          blk', hb', hsz'.trans hsz1, hal'.trans hal1, hperm'.trans hperm1, hk'.trans hk1, hba'.trans hba1,
          fun j hj => ?_, fun j hj => ?_, ?_⟩
        · rw [hm_ne y hy, hm1_ne y hy]
        · rw [hlt_bytes j (Nat.lt_of_lt_of_le hj (Nat.mul_le_mul_left _ (Nat.le_succ _))), hlt1 j hj]
        · simp only [List.length_cons] at hj
          have hj1 : esz * (idx + 1 + rest.length) ≤ j := by
            have : idx + 1 + rest.length = idx + (rest.length + 1) := by omega
            rw [this]; exact hj
          have hj2 : esz * (idx + 1) ≤ j :=
            Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) hj
          rw [hge_bytes j hj1, hge1 j hj2]
        · intro i hi j hj
          have hfm : (iv :: rest).filterMap parse? = a :: rest.filterMap parse? := by
            simp only [List.filterMap_cons, hp]
          cases i with
          | zero =>
            simp only [Nat.add_zero]
            have hget0 : ((iv :: rest).filterMap parse?)[0] = a := by simp only [hfm, List.getElem_cons_zero]
            rw [hget0]
            rw [hlt_bytes (esz * idx + j) (by rw [Nat.mul_add, Nat.mul_one]; omega)]
            exact hcur1 j hj
          | succ i' =>
            have hi' : i' < (rest.filterMap parse?).length := by
              rw [hfm, List.length_cons] at hi; exact Nat.lt_of_succ_lt_succ hi
            have hidx_eq : idx + (i' + 1) = idx + 1 + i' := by omega
            have hget_eq : ((iv :: rest).filterMap parse?)[i' + 1] = (rest.filterMap parse?)[i'] := by
              simp only [hfm, List.getElem_cons_succ]
            rw [hidx_eq, hget_eq]
            exact hread_rest i' hi' j hj

private theorem allocVarInit_strideArray_inv {α : Type _} {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {el : CTy} {n esz eal eal_req : Nat} {xs : List InitVal}
    (hty : d.ty = .array el (some n))
    (hxlen : xs.length = n)
    (hsz_el : sizeofTy prog.tags el = esz)
    (hal_el : alignofTy prog.tags el = eal)
    (hdvd_req : eal_req ∣ max 1 eal)
    (hinit : d.init? = some (.list xs))
    (parse? : InitVal → Option α)
    (hall : xs.all (fun x => (parse? x).isSome) = true)
    (elemBytes : α → List MemByte)
    (hblen : ∀ a, (elemBytes a).length = esz)
    (hstep : ∀ {m0 m1 : Mem} {blk : Block} {i ns0 ns1 : Nat} {iv : InitVal} {a : α},
      parse? iv = some a → m0.blocks m.nextBlock = some blk → eal_req ∣ blk.align → esz * (i + 1) ≤ blk.size →
      writeInitVal prog env m0 strBase m.nextBlock (Int64.ofNat (esz * i)) el iv ns0 = some (m1, ns1) →
      ns1 = ns0 ∧ m1.nextBlock = m0.nextBlock ∧ (∀ y, y ≠ m.nextBlock → m1.blocks y = m0.blocks y) ∧
      ∃ blk1, m1.blocks m.nextBlock = some blk1 ∧
        blk1.size = blk.size ∧ blk1.align = blk.align ∧ blk1.perm = blk.perm ∧
        blk1.kind = blk.kind ∧ blk1.baseAddr = blk.baseAddr ∧
        (∀ j, j < esz * i → blk1.bytes j = blk.bytes j) ∧
        (∀ j, esz * (i + 1) ≤ j → blk1.bytes j = blk.bytes j) ∧
        (∀ j (hj : j < esz), blk1.bytes (esz * i + j) = (elemBytes a)[j]'(by rw [hblen]; exact hj)))
    {bid : BlockId} {ty : CTy}
    (h : allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns')) :
    bid = m.nextBlock ∧ ty = .array el (some n) ∧ ns' = ns ∧
    MemPreservedBelow m.nextBlock m m' ∧
    ∃ blk, m'.blocks bid = some blk ∧
      blk.size = max 1 (n * esz) ∧ blk.align = max 1 eal ∧
      blk.kind = .global ∧ blk.perm = (if ty.isReadOnly then .ro else .rw) ∧
      (∀ (i : Nat) (hi : i < (xs.filterMap parse?).length),
        ∀ j (hj : j < esz),
          blk.bytes (esz * i + j) = (elemBytes (xs.filterMap parse?)[i])[j]'(by rw [hblen]; exact hj)) ∧
      (∀ j, esz * n ≤ j → blk.bytes j = .byte 0) := by
  have hres : resolveDeclTy d.ty d.init? = .array el (some n) := by rw [hty]; rfl
  have hsz_ty : max 1 (sizeofTy prog.tags (resolveDeclTy d.ty d.init?)) = max 1 (n * esz) := by
    rw [hres, sizeofTy_array_some, hsz_el]
  have hal_ty : max 1 (alignofTy prog.tags (resolveDeclTy d.ty d.init?)) = max 1 eal := by
    rw [hres, alignofTy_array, hal_el]
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
          blk1.size = max 1 (n * esz) ∧ blk1.align = max 1 eal ∧
          blk1.perm = .rw ∧ blk1.kind = .global ∧ (∀ i, blk1.bytes i = .byte 0) := by
      split at halloc
      · split at halloc
        · split at halloc
          · cases halloc
            refine ⟨rfl, rfl, fun x hx => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hx),
              _, alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, hsz_ty, hal_ty, rfl, rfl, fun _ => rfl⟩
          · cases halloc
        · cases halloc
      · cases halloc
    rcases ha with ⟨rfl, hm1next, hm1lt, blk1, hblk1, hsz1, hal1, hperm1, hk1, hbytes1⟩
    rw [hinit] at h
    dsimp only at h
    split at h
    · cases h
    · next p hwr =>
      rcases p with ⟨m2, ns2⟩
      dsimp only at h
      have hres' := hres
      rw [hinit] at hres'
      rw [writeInitVal_list (by rw [hres']; rfl)] at hwr
      have hsz_le : esz * (0 + xs.length) ≤ blk1.size := by
        rw [hsz1, hxlen, Nat.zero_add, Nat.mul_comm]
        exact Nat.le_max_right _ _
      obtain ⟨rfl, hm2next, hm2ne, blk2, hblk2, hsz2, hal2, hperm2, hk2, _, _, hge2, hcur2⟩ :=
        writeInitList_stride_inv hsz_el parse? elemBytes hblen hstep hblk1
          (by rw [hal1]; exact hdvd_req) hsz_le hall hwr
      have hge_zero : ∀ j, esz * n ≤ j → blk2.bytes j = .byte 0 := by
        intro j hj
        rw [hge2 j (by rw [Nat.zero_add, hxlen]; exact hj), hbytes1 j]
      rw [hres'] at h
      split at h <;> rename_i hro <;> cases h
      · refine ⟨rfl, rfl, rfl, ⟨by simp [hm2next, hm1next], fun x hx => ?_⟩, ?_⟩
        · have hne : x ≠ m.nextBlock := Nat.ne_of_lt hx
          simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
          rw [hm2ne x hne, hm1lt x hx]
        · refine ⟨{ blk2 with perm := .ro }, by simp [hblk2], by rw [hsz2, hsz1], by rw [hal2, hal1],
            by rw [hk2, hk1], ?_, fun i hi j hj => ?_, hge_zero⟩
          · rw [ite_eq_left hro]
          · simpa only [Nat.zero_add] using hcur2 i hi j hj
      · refine ⟨rfl, rfl, rfl, ⟨by rw [hm2next, hm1next]; exact Nat.le_succ _, fun x hx => ?_⟩, ?_⟩
        · rw [hm2ne x (Nat.ne_of_lt hx), hm1lt x hx]
        · refine ⟨blk2, hblk2, by rw [hsz2, hsz1], by rw [hal2, hal1], by rw [hk2, hk1], ?_,
            fun i hi j hj => ?_, hge_zero⟩
          · rw [ite_eq_right hro, hperm2, hperm1]
          · simpa only [Nat.zero_add] using hcur2 i hi j hj

private theorem allBytes_concrete_of_stride {α : Type _} {xs : List InitVal} {parse? : InitVal → Option α}
    {elemBytes : α → List MemByte} {esz n : Nat} {blk : Block}
    (hfmlen : (xs.filterMap parse?).length = n)
    (hesz : 0 < esz)
    (hblen : ∀ a, (elemBytes a).length = esz)
    (hconcr : ∀ a, ∀ x ∈ elemBytes a, ∃ u : UInt8, x = .byte u)
    (hcur : ∀ (i : Nat) (hi : i < (xs.filterMap parse?).length),
      ∀ j (hj : j < esz), blk.bytes (esz * i + j) = (elemBytes (xs.filterMap parse?)[i])[j]'(by rw [hblen]; exact hj))
    (hge : ∀ j, esz * n ≤ j → blk.bytes j = .byte 0) :
    ∀ k, ∃ u : UInt8, blk.bytes k = .byte u := by
  intro k
  by_cases hlt : k < esz * n
  · have hi_lt : k / esz < (xs.filterMap parse?).length := by
      rw [hfmlen]; exact Nat.div_lt_of_lt_mul hlt
    have hr_lt : k % esz < esz := Nat.mod_lt k hesz
    have hdiv_mod : esz * (k / esz) + k % esz = k := Nat.div_add_mod k esz
    have hk_eq := hcur (k / esz) hi_lt (k % esz) hr_lt
    rw [hdiv_mod] at hk_eq
    rw [hk_eq]
    exact hconcr _ _ (List.getElem_mem _)
  · exact ⟨0, hge k (Nat.le_of_not_lt hlt)⟩

/-! ### Parsed Table Definitions and Kernel-Verified Bounds -/

def parseCodeInit? : InitVal → Option (Nat × Nat × Nat)
  | .list [.expr opE, .expr bitsE, .expr valE] => do
    let op ← evalPureLit? opE
    let bits ← evalPureLit? bitsE
    let val ← evalPureLit? valE
    if 0 ≤ op ∧ op ≤ 255 ∧ 0 ≤ bits ∧ bits ≤ 255 ∧ 0 ≤ val ∧ val < 65536 then
      pure (op.toNat, bits.toNat, val.toNat)
    else none
  | _ => none

def lenfixVals : List (Nat × Nat × Nat) :=
  match Zlib.Tables.inffixedH_global_lenfix.init? with
  | some (.list xs) => xs.filterMap parseCodeInit?
  | _ => []

def distfixVals : List (Nat × Nat × Nat) :=
  match Zlib.Tables.inffixedH_global_distfix.init? with
  | some (.list xs) => xs.filterMap parseCodeInit?
  | _ => []

def parseCtDataInit? : InitVal → Option (Nat × Nat)
  | .list [.list [.expr fcE], .list [.expr dlE]] => do
    let fc ← evalPureLit? fcE
    let dl ← evalPureLit? dlE
    if 0 ≤ fc ∧ fc < 65536 ∧ 0 ≤ dl ∧ dl < 65536 then
      pure (fc.toNat, dl.toNat)
    else none
  | _ => none

def staticLtreeVals : List (Nat × Nat) :=
  match Zlib.Tables.treesH_global_static_ltree.init? with
  | some (.list xs) => xs.filterMap parseCtDataInit?
  | _ => []

def staticDtreeVals : List (Nat × Nat) :=
  match Zlib.Tables.treesH_global_static_dtree.init? with
  | some (.list xs) => xs.filterMap parseCtDataInit?
  | _ => []

def parseConfigInit? : InitVal → Option (Nat × Nat × Nat × Nat × String)
  | .list [.expr glE, .expr mlE, .expr nlE, .expr mcE, .expr (.var fnm)] => do
    let gl ← evalPureLit? glE
    let ml ← evalPureLit? mlE
    let nl ← evalPureLit? nlE
    let mc ← evalPureLit? mcE
    if 0 ≤ gl ∧ gl < 65536 ∧ 0 ≤ ml ∧ ml < 65536 ∧ 0 ≤ nl ∧ nl < 65536 ∧ 0 ≤ mc ∧ mc < 65536 ∧
        (fnm = "deflate_stored" ∨ fnm = "deflate_fast" ∨ fnm = "deflate_slow") then
      pure (gl.toNat, ml.toNat, nl.toNat, mc.toNat, fnm)
    else none
  | _ => none

def configurationTableVals : List (Nat × Nat × Nat × Nat × String) :=
  match Zlib.Deflate.deflateTU_global_configuration_table.init? with
  | some (.list xs) => xs.filterMap parseConfigInit?
  | _ => []

def configFuncFieldTy : CTy :=
  .typedef "compress_func" (.fnPtr (.typedef "block_state" (.int .u32))
    [.ptr (.typedef "deflate_state" (.structTy "internal_state")), .int .i32] false)

def configCTy : CTy := .typedef "config" (.structTy "config_s")
def configConstTy : CTy := .const_ configCTy
def staticTreeDescCTy : CTy := .typedef "static_tree_desc" (.structTy "static_tree_desc_s")
def staticTreeDescConstTy : CTy := .const_ staticTreeDescCTy

private theorem lenfix_init_all_ok :
    (match Zlib.Tables.inffixedH_global_lenfix.init? with
     | some (.list xs) => xs.length == 512 && xs.all (fun x => (parseCodeInit? x).isSome)
     | _ => false) = true := by decide +kernel

private theorem lenfix_bounds_all :
    lenfixVals.all (fun t =>
      decide (7 ≤ t.2.1 ∧ t.2.1 ≤ 9 ∧
        ((t.1 = 0 ∧ t.2.2 ≤ 255) ∨ (t.1 = 64 ∧ t.2.2 = 0) ∨ (t.1 = 96 ∧ t.2.2 = 0) ∨
          (16 ≤ t.1 ∧ t.1 ≤ 21 ∧ 3 ≤ t.2.2 ∧ t.2.2 + (1 <<< (t.1 &&& 15)) - 1 ≤ 258)))) = true := by
  decide +kernel

private theorem distfix_init_all_ok :
    (match Zlib.Tables.inffixedH_global_distfix.init? with
     | some (.list xs) => xs.length == 32 && xs.all (fun x => (parseCodeInit? x).isSome)
     | _ => false) = true := by decide +kernel

private theorem distfix_bounds_all :
    distfixVals.all (fun t =>
      decide (t.2.1 = 5 ∧
        ((t.1 = 64 ∧ t.2.2 = 0) ∨
          (16 ≤ t.1 ∧ t.1 ≤ 29 ∧ 1 ≤ t.2.2 ∧ t.2.2 + (1 <<< (t.1 &&& 15)) - 1 ≤ 32768)))) = true := by
  decide

private theorem staticLtree_init_all_ok :
    (match Zlib.Tables.treesH_global_static_ltree.init? with
     | some (.list xs) => xs.length == 288 && xs.all (fun x => (parseCtDataInit? x).isSome)
     | _ => false) = true := by decide +kernel

private theorem staticLtree_bounds_all :
    staticLtreeVals.all (fun t => decide (7 ≤ t.2 ∧ t.2 ≤ 9)) = true := by decide +kernel

private theorem staticDtree_init_all_ok :
    (match Zlib.Tables.treesH_global_static_dtree.init? with
     | some (.list xs) => xs.length == 30 && xs.all (fun x => (parseCtDataInit? x).isSome)
     | _ => false) = true := by decide

private theorem staticDtree_bounds_all :
    staticDtreeVals.all (fun t => decide (t.2 = 5)) = true := by decide

private theorem configurationTable_init_all_ok :
    (match Zlib.Deflate.deflateTU_global_configuration_table.init? with
     | some (.list xs) => xs.length == 10 && xs.all (fun x => (parseConfigInit? x).isSome)
     | _ => false) = true := by decide

private theorem configurationTable_bounds_all :
    configurationTableVals.all (fun c =>
      decide (c.1 ≤ 32 ∧ c.2.1 ≤ 258 ∧ c.2.2.1 ≤ 258 ∧ c.2.2.2.1 ≤ 4096 ∧
        (c.2.2.2.2 = "deflate_stored" ∨ c.2.2.2.2 = "deflate_fast" ∨ c.2.2.2.2 = "deflate_slow"))) = true := by
  decide

private theorem extra_lbits_bounds_all :
    (Zlib.Trees.treesTU_vals_extra_lbits.size == 29 &&
    Zlib.Trees.treesTU_vals_extra_lbits.toList.all (fun v => decide (0 ≤ v ∧ v ≤ 5))) = true := by decide

private theorem extra_dbits_bounds_all :
    (Zlib.Trees.treesTU_vals_extra_dbits.size == 30 &&
    Zlib.Trees.treesTU_vals_extra_dbits.toList.all (fun v => decide (0 ≤ v ∧ v ≤ 13))) = true := by decide

private theorem extra_blbits_bounds_all :
    (Zlib.Trees.treesTU_vals_extra_blbits.size == 19 &&
    Zlib.Trees.treesTU_vals_extra_blbits.toList.all (fun v => decide (0 ≤ v ∧ v ≤ 7))) = true := by decide

private theorem bl_order_bounds_all :
    (Zlib.Trees.treesTU_vals_bl_order.size == 19 &&
    Zlib.Trees.treesTU_vals_bl_order.toList.all (fun v => decide (0 ≤ v ∧ v < 19))) = true := by decide

private theorem dist_code_bounds_all :
    (Zlib.Tables.treesH_vals__dist_code.size == 512 &&
    Zlib.Tables.treesH_vals__dist_code.toList.all (fun v => decide (0 ≤ v ∧ v < 30))) = true := by decide +kernel

private theorem length_code_bounds_all :
    (Zlib.Tables.treesH_vals__length_code.size == 256 &&
    Zlib.Tables.treesH_vals__length_code.toList.all (fun v => decide (0 ≤ v ∧ v < 29))) = true := by decide +kernel

private theorem base_length_bounds_all :
    (Zlib.Tables.treesH_vals_base_length.size == 29 &&
    Zlib.Tables.treesH_vals_base_length.toList.all (fun v => decide (0 ≤ v ∧ v ≤ 224))) = true := by decide

private theorem base_dist_bounds_all :
    (Zlib.Tables.treesH_vals_base_dist.size == 30 &&
    Zlib.Tables.treesH_vals_base_dist.toList.all (fun v => decide (0 ≤ v ∧ v ≤ 24576))) = true := by decide

private theorem inflate_copyright_str_ok :
    CStringLitOk " inflate 1.4.0.1 Copyright 1995-2026 Mark Adler " = true := by decide

private theorem deflate_copyright_str_ok :
    CStringLitOk " deflate 1.4.0.1 Copyright 1995-2026 Jean-loup Gailly and Mark Adler " = true := by decide

private theorem filterMap_all_isSome_length {α β : Type _} (f : α → Option β) (xs : List α)
    (h : xs.all (fun x => (f x).isSome) = true) :
    (xs.filterMap f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases hx : f x with
    | none => rw [hx] at h; cases h.1
    | some y => simp only [List.filterMap_cons, hx, List.length_cons, ih h.2]

private theorem list_all_at {α : Type _} [Inhabited α] {xs : List α} {p : α → Bool} (h : xs.all p = true)
    {i : Nat} (hi : i < xs.length) : p xs[i]! = true := by
  have hm := List.all_eq_true.mp h _ (List.getElem_mem hi)
  simpa [getElem!_pos xs i hi] using hm

private theorem array_all_at {a : Array Int} {n : Nat} {q : Int → Bool}
    (hall : (a.size == n && a.toList.all q) = true) {i : Nat} (hi : i < n) :
    q a[i]! = true := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hall
  have hi_lst : i < a.toList.length := by rw [Array.length_toList, hall.1]; exact hi
  have hat := list_all_at hall.2 hi_lst
  have hget : a.toList[i]! = a[i]! := by
    rw [getElem!_pos a.toList i hi_lst, getElem!_pos a i (by rw [hall.1]; exact hi)]
    rfl
  rw [← hget]; exact hat

/-! ### Global Array and Struct Inversion Helpers -/

private def codeElemBytes (t : Nat × Nat × Nat) : List MemByte :=
  Mem.encodeInt .u8 (BitVec.ofNat IntKind.u8.bits t.1) ++
  Mem.encodeInt .u8 (BitVec.ofNat IntKind.u8.bits t.2.1) ++
  Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits t.2.2)

private theorem codeElemBytes_len (t : Nat × Nat × Nat) : (codeElemBytes t).length = 4 := by
  unfold codeElemBytes
  rw [List.length_append, List.length_append, encodeInt_length, encodeInt_length, encodeInt_length]
  rfl

private theorem codeElemBytes_concr (t : Nat × Nat × Nat) :
    ∀ x ∈ codeElemBytes t, ∃ u : UInt8, x = .byte u := by
  intro x hx
  unfold codeElemBytes at hx
  rcases List.mem_append.mp hx with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · exact mem_encodeInt_isByte h1
    · exact mem_encodeInt_isByte h2
  · exact mem_encodeInt_isByte h3

private theorem allocVarInit_codeArray_inv {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {n : Nat} {xs : List InitVal}
    (hty : d.ty = .array codeConstTy (some n))
    (hxlen : xs.length = n)
    (hinit : d.init? = some (.list xs))
    (hall : xs.all (fun x => (parseCodeInit? x).isSome) = true)
    {bid : BlockId} {ty : CTy}
    (h : allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns')) :
    bid = m.nextBlock ∧ ty = .array codeConstTy (some n) ∧ ns' = ns ∧
    MemPreservedBelow m.nextBlock m m' ∧
    ∃ blk, m'.blocks bid = some blk ∧
      blk.size = max 1 (n * 4) ∧ blk.align = 2 ∧ blk.kind = .global ∧ blk.perm = .ro ∧
      (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
      (∀ (i : Nat) (hi : i < (xs.filterMap parseCodeInit?).length),
        let t := (xs.filterMap parseCodeInit?)[i]
        Sem.readVal prog.tags m' bid (Int64.ofNat (4 * i)) (.int .u8) = some (.int .u8 (BitVec.ofNat 8 t.1)) ∧
        Sem.readVal prog.tags m' bid (Int64.ofNat (4 * i + 1)) (.int .u8) = some (.int .u8 (BitVec.ofNat 8 t.2.1)) ∧
        Sem.readVal prog.tags m' bid (Int64.ofNat (4 * i + 2)) (.int .u16) = some (.int .u16 (BitVec.ofNat 16 t.2.2))) := by
  have hsz_el : sizeofTy prog.tags codeConstTy = 4 := by simp [codeConstTy]
  have hal_el : alignofTy prog.tags codeConstTy = 2 := by simp [codeConstTy]
  have hstep : ∀ {m0 m1 : Mem} {blk : Block} {i ns0 ns1 : Nat} {iv : InitVal} {a : Nat × Nat × Nat},
      parseCodeInit? iv = some a → m0.blocks m.nextBlock = some blk → 2 ∣ blk.align → 4 * (i + 1) ≤ blk.size →
      writeInitVal prog env m0 strBase m.nextBlock (Int64.ofNat (4 * i)) codeConstTy iv ns0 = some (m1, ns1) →
      ns1 = ns0 ∧ m1.nextBlock = m0.nextBlock ∧ (∀ y, y ≠ m.nextBlock → m1.blocks y = m0.blocks y) ∧
      ∃ blk1, m1.blocks m.nextBlock = some blk1 ∧
        blk1.size = blk.size ∧ blk1.align = blk.align ∧ blk1.perm = blk.perm ∧
        blk1.kind = blk.kind ∧ blk1.baseAddr = blk.baseAddr ∧
        (∀ j, j < 4 * i → blk1.bytes j = blk.bytes j) ∧
        (∀ j, 4 * (i + 1) ≤ j → blk1.bytes j = blk.bytes j) ∧
        (∀ j (hj : j < 4), blk1.bytes (4 * i + j) = (codeElemBytes a)[j]'(by rw [codeElemBytes_len]; exact hj)) := by
    intro m0 m1 blk i ns0 ns1 iv a hp hb _ hsz_blk hwr
    rcases a with ⟨op, bits, val⟩
    cases iv with
    | list ys =>
      cases ys with
      | nil => simp [parseCodeInit?] at hp
      | cons e0 ys1 =>
        cases ys1 with
        | nil => simp [parseCodeInit?] at hp
        | cons e1 ys2 =>
          cases ys2 with
          | nil => simp [parseCodeInit?] at hp
          | cons e2 ys3 =>
            cases ys3 with
            | cons _ _ => simp [parseCodeInit?] at hp
            | nil =>
              cases e0 with
              | list _ | intSeq _ _ => simp [parseCodeInit?] at hp
              | expr opE =>
                cases e1 with
                | list _ | intSeq _ _ => simp [parseCodeInit?] at hp
                | expr bitsE =>
                  cases e2 with
                  | list _ | intSeq _ _ => simp [parseCodeInit?] at hp
                  | expr valE =>
                    simp only [parseCodeInit?, bind, Option.bind, pure, Pure.pure] at hp
                    cases hop : evalPureLit? opE with
                    | none => rw [hop] at hp; cases hp
                    | some opI =>
                      rw [hop] at hp; dsimp only at hp
                      cases hbi : evalPureLit? bitsE with
                      | none => rw [hbi] at hp; cases hp
                      | some biI =>
                        rw [hbi] at hp; dsimp only at hp
                        cases hva : evalPureLit? valE with
                        | none => rw [hva] at hp; cases hp
                        | some vaI =>
                          rw [hva] at hp; dsimp only at hp
                          split at hp
                          · next hbounds =>
                            simp only [Option.some.injEq, Prod.mk.injEq] at hp
                            rcases hp with ⟨hop_eq, hbi_eq, hva_eq⟩
                            have hlim4 : 4 * i < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
                            have htu : codeConstTy.unqual = .anonStruct codeFields := rfl
                            rw [writeInitVal_anonStruct htu, int64_ofNat_toNat_eq hlim4] at hwr
                            dsimp only [codeFields] at hwr
                            rw [writeInitFields_cons] at hwr
                            have hfoff0 : alignUp 0 (max 1 (alignofTy prog.tags (.int .u8))) = 0 := by simp; rfl
                            have hsz0 : sizeofTy prog.tags (.int .u8) = 1 := by simp; rfl
                            dsimp only at hwr
                            rw [hfoff0, hsz0, Nat.add_zero] at hwr
                            simp only [bind, Option.bind] at hwr
                            cases hs0 : writeInitVal prog env m0 strBase m.nextBlock (Int64.ofNat (4 * i)) (.int .u8) (.expr opE) ns0 with
                            | none => rw [hs0] at hwr; cases hwr
                            | some p0 =>
                              rcases p0 with ⟨ma, nsa⟩
                              rw [hs0] at hwr; dsimp only at hwr
                              obtain ⟨rfl, hma_next, hma_ne, blka, hblka, hsza, hala, hperma, hka, hbaa, hlt0, hge0, hcur0⟩ :=
                                writeInitVal_pureInt_step (k := .u8) rfl hop hb hlim4 hs0
                              rw [writeInitFields_cons] at hwr
                              have hfoff1 : alignUp (0 + 1) (max 1 (alignofTy prog.tags (.int .u8))) = 1 := by simp; rfl
                              have hsz1 : sizeofTy prog.tags (.int .u8) = 1 := by simp; rfl
                              dsimp only at hwr
                              rw [hfoff1, hsz1] at hwr
                              simp only [bind, Option.bind] at hwr
                              have hlim1 : 4 * i + 1 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
                              cases hs1 : writeInitVal prog env ma strBase m.nextBlock (Int64.ofNat (4 * i + 1)) (.int .u8) (.expr bitsE) nsa with
                              | none => rw [hs1] at hwr; cases hwr
                              | some p1 =>
                                rcases p1 with ⟨mb, nsb⟩
                                rw [hs1] at hwr; dsimp only at hwr
                                obtain ⟨rfl, hmb_next, hmb_ne, blkb, hblkb, hszb, halb, hpermb, hkb, hbab, hlt1, hge1, hcur1⟩ :=
                                  writeInitVal_pureInt_step (k := .u8) rfl hbi hblka hlim1 hs1
                                rw [writeInitFields_cons] at hwr
                                have hfoff2 : alignUp (1 + 1) (max 1 (alignofTy prog.tags (.int .u16))) = 2 := by simp; rfl
                                have hsz2 : sizeofTy prog.tags (.int .u16) = 2 := by simp; rfl
                                dsimp only at hwr
                                rw [hfoff2, hsz2] at hwr
                                simp only [bind, Option.bind] at hwr
                                have hlim2 : 4 * i + 2 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
                                cases hs2 : writeInitVal prog env mb strBase m.nextBlock (Int64.ofNat (4 * i + 2)) (.int .u16) (.expr valE) nsb with
                                | none => rw [hs2] at hwr; cases hwr
                                | some p2 =>
                                  rcases p2 with ⟨mc, nsc⟩
                                  rw [hs2] at hwr; dsimp only at hwr
                                  rw [writeInitFields_nil] at hwr
                                  simp only [Option.some.injEq, Prod.mk.injEq] at hwr
                                  rcases hwr with ⟨rfl, rfl⟩
                                  obtain ⟨rfl, hmc_next, hmc_ne, blkc, hblkc, hszc, halc, hpermc, hkc, hbac, hlt2, hge2, hcur2⟩ :=
                                    writeInitVal_pureInt_step (k := .u16) rfl hva hblkb hlim2 hs2
                                  have hbv0 : BitVec.ofInt IntKind.u8.bits opI = BitVec.ofNat IntKind.u8.bits op := by
                                    apply BitVec.eq_of_toNat_eq
                                    have hbv_nat : (BitVec.ofInt 8 opI).toNat = opI.toNat := by
                                      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
                                    have hbv_nat2 : (BitVec.ofNat 8 op).toNat = op := by
                                      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                                    change (BitVec.ofInt 8 opI).toNat = (BitVec.ofNat 8 op).toNat
                                    rw [hbv_nat, hbv_nat2, ← hop_eq]
                                  have hbv1 : BitVec.ofInt IntKind.u8.bits biI = BitVec.ofNat IntKind.u8.bits bits := by
                                    apply BitVec.eq_of_toNat_eq
                                    have hbv_nat : (BitVec.ofInt 8 biI).toNat = biI.toNat := by
                                      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
                                    have hbv_nat2 : (BitVec.ofNat 8 bits).toNat = bits := by
                                      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                                    change (BitVec.ofInt 8 biI).toNat = (BitVec.ofNat 8 bits).toNat
                                    rw [hbv_nat, hbv_nat2, ← hbi_eq]
                                  have hbv2 : BitVec.ofInt IntKind.u16.bits vaI = BitVec.ofNat IntKind.u16.bits val := by
                                    apply BitVec.eq_of_toNat_eq
                                    have hbv_nat : (BitVec.ofInt 16 vaI).toNat = vaI.toNat := by
                                      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
                                    have hbv_nat2 : (BitVec.ofNat 16 val).toNat = val := by
                                      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                                    change (BitVec.ofInt 16 vaI).toNat = (BitVec.ofNat 16 val).toNat
                                    rw [hbv_nat, hbv_nat2, ← hva_eq]
                                  rw [hbv0] at hcur0
                                  rw [hbv1] at hcur1
                                  rw [hbv2] at hcur2
                                  let bs0 := Mem.encodeInt .u8 (BitVec.ofNat IntKind.u8.bits op)
                                  let bs1 := Mem.encodeInt .u8 (BitVec.ofNat IntKind.u8.bits bits)
                                  let bs2 := Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits val)
                                  have hlen0 : bs0.length = 1 := encodeInt_length _ _
                                  have hlen1 : bs1.length = 1 := encodeInt_length _ _
                                  have hlen2 : bs2.length = 2 := encodeInt_length _ _
                                  have hbytes_u8 : IntKind.u8.bytes = 1 := rfl
                                  have hbytes_u16 : IntKind.u16.bytes = 2 := rfl
                                  obtain ⟨ha_lt, ha_ge, ha_cur⟩ := bytes_concat_step (bs1 := bs0) (bs2 := bs1) hlt0
                                    (fun j hj => hge0 j (by rw [hlen0] at hj; rw [hbytes_u8]; omega))
                                    (fun j hj => hcur0 j (by rw [hlen0] at hj; rw [hbytes_u8]; exact hj))
                                    (fun j hj => hlt1 j (by rw [hlen0] at hj; exact hj))
                                    (fun j hj => hge1 j (by rw [hlen0, hlen1] at hj; rw [hbytes_u8]; omega))
                                    (fun j hj => by rw [hlen0]; exact hcur1 j (by rw [hlen1] at hj; rw [hbytes_u8]; exact hj))
                                  have hlen01 : (bs0 ++ bs1).length = 2 := by
                                    rw [List.length_append, hlen0, hlen1]
                                  obtain ⟨hb_lt, hb_ge, hb_cur⟩ := bytes_concat_step (bs1 := bs0 ++ bs1) (bs2 := bs2) ha_lt ha_ge ha_cur
                                    (fun j hj => hlt2 j (by rw [hlen01] at hj; exact hj))
                                    (fun j hj => hge2 j (by rw [hlen01, hlen2] at hj; rw [hbytes_u16]; omega))
                                    (fun j hj => by rw [hlen01]; exact hcur2 j (by rw [hlen2] at hj; rw [hbytes_u16]; exact hj))
                                  refine ⟨rfl, hmc_next.trans (hmb_next.trans hma_next), fun y hy => ?_,
                                    blkc, hblkc, hszc.trans (hszb.trans hsza), halc.trans (halb.trans hala),
                                    hpermc.trans (hpermb.trans hperma), hkc.trans (hkb.trans hka),
                                    hbac.trans (hbab.trans hbaa), hb_lt, ?_, ?_⟩
                                  · rw [hmc_ne y hy, hmb_ne y hy, hma_ne y hy]
                                  · intro j hj
                                    apply hb_ge
                                    rw [List.length_append, hlen01, hlen2]
                                    omega
                                  · intro j hj
                                    exact hb_cur j (by rw [List.length_append, hlen01, hlen2]; exact hj)
                          · cases hp
    | expr _ | intSeq _ _ => simp [parseCodeInit?] at hp
  obtain ⟨rfl, rfl, rfl, hpres, blk, hblk, hsz, hal, hkind, hperm, hcur, hge⟩ :=
    allocVarInit_strideArray_inv hty hxlen hsz_el hal_el (eal_req := 2) (by decide)
      hinit parseCodeInit? hall codeElemBytes codeElemBytes_len hstep h
  have hal_eq : blk.align = 2 := hal
  have hperm_ro : blk.perm = .ro := hperm
  have hfmlen : (xs.filterMap parseCodeInit?).length = n := by
    rw [filterMap_all_isSome_length parseCodeInit? xs hall, hxlen]
  have hconcr : ∀ k, ∃ u : UInt8, blk.bytes k = .byte u :=
    allBytes_concrete_of_stride hfmlen (by decide) codeElemBytes_len codeElemBytes_concr hcur hge
  refine ⟨rfl, rfl, rfl, hpres, blk, hblk, hsz, hal_eq, hkind, hperm_ro, hconcr, fun i hi => ?_⟩
  have hsz_i : 4 * (i + 1) ≤ blk.size := by
    rw [hsz]; have hi_n : i < n := by rw [hfmlen] at hi; exact hi
    exact Nat.le_trans (Nat.mul_le_mul_left 4 (Nat.succ_le_of_lt hi_n))
      (by rw [Nat.mul_comm]; exact Nat.le_max_right 1 (n * 4))
  have hbytes_i := hcur i hi
  let t := (xs.filterMap parseCodeInit?)[i]
  have hbytes_len : ∀ j (hj : j < (codeElemBytes t).length),
      blk.bytes (4 * i + j) = (codeElemBytes t)[j] :=
    fun j hj => hbytes_i j (by rw [codeElemBytes_len] at hj; exact hj)
  dsimp only [codeElemBytes] at hbytes_len
  obtain ⟨hslice_01, hslice_2⟩ := bytes_slice_of_concat hbytes_len
  obtain ⟨hslice_0, hslice_1⟩ := bytes_slice_of_concat hslice_01
  have hlen0 : (Mem.encodeInt .u8 (BitVec.ofNat IntKind.u8.bits t.1)).length = 1 := encodeInt_length _ _
  have hlen1 : (Mem.encodeInt .u8 (BitVec.ofNat IntKind.u8.bits t.2.1)).length = 1 := encodeInt_length _ _
  have hlen01 : (Mem.encodeInt .u8 (BitVec.ofNat IntKind.u8.bits t.1) ++
      Mem.encodeInt .u8 (BitVec.ofNat IntKind.u8.bits t.2.1)).length = 2 := by
    rw [List.length_append, hlen0, hlen1]
  have hlim0 : 4 * i < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
  have hlim1 : 4 * i + 1 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
  have hlim2 : 4 * i + 2 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
  have hbu8 : IntKind.u8.bytes = 1 := rfl
  have hbu16 : IntKind.u16.bytes = 2 := rfl
  refine ⟨?_, ?_, ?_⟩
  · refine readVal_int_of_exact (k := .u8) rfl hblk hlim0
      (by rw [inBounds_iff, int64_ofNat_toInt hlim0, hbu8]; exact ⟨Int.natCast_nonneg _, by simp only [Int.toNat_natCast]; omega⟩)
      (isAligned_of_dvd (by decide) (by rw [hal_eq]; exact Nat.one_dvd 2) (Nat.one_dvd _) hlim0) ?_
    intro j hj; exact hslice_0 j hj
  · refine readVal_int_of_exact (k := .u8) rfl hblk hlim1
      (by rw [inBounds_iff, int64_ofNat_toInt hlim1, hbu8]; exact ⟨Int.natCast_nonneg _, by simp only [Int.toNat_natCast]; omega⟩)
      (isAligned_of_dvd (by decide) (by rw [hal_eq]; exact Nat.one_dvd 2) (Nat.one_dvd _) hlim1) ?_
    intro j hj; rw [← hlen0]; exact hslice_1 j hj
  · refine readVal_int_of_exact (k := .u16) rfl hblk hlim2
      (by rw [inBounds_iff, int64_ofNat_toInt hlim2, hbu16]; exact ⟨Int.natCast_nonneg _, by simp only [Int.toNat_natCast]; omega⟩)
      (isAligned_of_dvd (by decide) (by rw [hal_eq]; exact Nat.dvd_refl 2)
        (by rw [show IntKind.u16.align = 2 from rfl]; exact ⟨2 * i + 1, by omega⟩) hlim2) ?_
    intro j hj; rw [← hlen01]; exact hslice_2 j hj

private def ctDataElemBytes (t : Nat × Nat) : List MemByte :=
  Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits t.1) ++
  Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits t.2)

private theorem ctDataElemBytes_len (t : Nat × Nat) : (ctDataElemBytes t).length = 4 := by
  unfold ctDataElemBytes
  rw [List.length_append, encodeInt_length, encodeInt_length]
  rfl

private theorem ctDataElemBytes_concr (t : Nat × Nat) :
    ∀ x ∈ ctDataElemBytes t, ∃ u : UInt8, x = .byte u := by
  intro x hx
  unfold ctDataElemBytes at hx
  rcases List.mem_append.mp hx with h1 | h2
  · exact mem_encodeInt_isByte h1
  · exact mem_encodeInt_isByte h2

private theorem allocVarInit_ctDataArray_inv {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {n : Nat} {xs : List InitVal}
    (htags : prog.tags = (progOfTUs Zlib.allFiles).tags)
    (hty : d.ty = .array ctDataConstTy (some n))
    (hxlen : xs.length = n)
    (hinit : d.init? = some (.list xs))
    (hall : xs.all (fun x => (parseCtDataInit? x).isSome) = true)
    {bid : BlockId} {ty : CTy}
    (h : allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns')) :
    bid = m.nextBlock ∧ ty = .array ctDataConstTy (some n) ∧ ns' = ns ∧
    MemPreservedBelow m.nextBlock m m' ∧
    ∃ blk, m'.blocks bid = some blk ∧
      blk.size = max 1 (n * 4) ∧ blk.align = 2 ∧ blk.kind = .global ∧ blk.perm = .ro ∧
      (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
      (∀ (i : Nat) (hi : i < (xs.filterMap parseCtDataInit?).length),
        let t := (xs.filterMap parseCtDataInit?)[i]
        Sem.readVal prog.tags m' bid (Int64.ofNat (4 * i)) (.int .u16) = some (.int .u16 (BitVec.ofNat 16 t.1)) ∧
        Sem.readVal prog.tags m' bid (Int64.ofNat (4 * i + 2)) (.int .u16) = some (.int .u16 (BitVec.ofNat 16 t.2))) := by
  have hsz_el : sizeofTy prog.tags ctDataConstTy = 4 := by
    rw [ctDataConstTy, sizeofTy_const, ctDataCTy, sizeofTy_typedef, htags, sizeofTy_ct_data_s]
  have hal_el : alignofTy prog.tags ctDataConstTy = 2 := by
    rw [ctDataConstTy, alignofTy_const, ctDataCTy, alignofTy_typedef, htags, alignofTy_ct_data_s]
  have hstep : ∀ {m0 m1 : Mem} {blk : Block} {i ns0 ns1 : Nat} {iv : InitVal} {a : Nat × Nat},
      parseCtDataInit? iv = some a → m0.blocks m.nextBlock = some blk → 2 ∣ blk.align → 4 * (i + 1) ≤ blk.size →
      writeInitVal prog env m0 strBase m.nextBlock (Int64.ofNat (4 * i)) ctDataConstTy iv ns0 = some (m1, ns1) →
      ns1 = ns0 ∧ m1.nextBlock = m0.nextBlock ∧ (∀ y, y ≠ m.nextBlock → m1.blocks y = m0.blocks y) ∧
      ∃ blk1, m1.blocks m.nextBlock = some blk1 ∧
        blk1.size = blk.size ∧ blk1.align = blk.align ∧ blk1.perm = blk.perm ∧
        blk1.kind = blk.kind ∧ blk1.baseAddr = blk.baseAddr ∧
        (∀ j, j < 4 * i → blk1.bytes j = blk.bytes j) ∧
        (∀ j, 4 * (i + 1) ≤ j → blk1.bytes j = blk.bytes j) ∧
        (∀ j (hj : j < 4), blk1.bytes (4 * i + j) = (ctDataElemBytes a)[j]'(by rw [ctDataElemBytes_len]; exact hj)) := by
    intro m0 m1 blk i ns0 ns1 iv a hp hb _ hsz_blk hwr
    rcases a with ⟨fc, dl⟩
    cases iv with
    | list ys =>
      cases ys with
      | nil => simp [parseCtDataInit?] at hp
      | cons y0 ys1 =>
        cases ys1 with
        | nil => simp [parseCtDataInit?] at hp
        | cons y1 ys2 =>
          cases ys2 with
          | cons _ _ => simp [parseCtDataInit?] at hp
          | nil =>
            cases y0 with
            | expr _ | intSeq _ _ => simp [parseCtDataInit?] at hp
            | list z0 =>
              cases z0 with
              | nil => simp [parseCtDataInit?] at hp
              | cons efc z0r =>
                cases z0r with
                | cons _ _ => simp [parseCtDataInit?] at hp
                | nil =>
                  cases efc with
                  | list _ | intSeq _ _ => simp [parseCtDataInit?] at hp
                  | expr fcE =>
                    cases y1 with
                    | expr _ | intSeq _ _ => simp [parseCtDataInit?] at hp
                    | list z1 =>
                      cases z1 with
                      | nil => simp [parseCtDataInit?] at hp
                      | cons edl z1r =>
                        cases z1r with
                        | cons _ _ => simp [parseCtDataInit?] at hp
                        | nil =>
                          cases edl with
                          | list _ | intSeq _ _ => simp [parseCtDataInit?] at hp
                          | expr dlE =>
                            simp only [parseCtDataInit?, bind, Option.bind, pure, Pure.pure] at hp
                            cases hfc : evalPureLit? fcE with
                            | none => rw [hfc] at hp; cases hp
                            | some fcI =>
                              rw [hfc] at hp; dsimp only at hp
                              cases hdl : evalPureLit? dlE with
                              | none => rw [hdl] at hp; cases hp
                              | some dlI =>
                                rw [hdl] at hp; dsimp only at hp
                                split at hp
                                · next hbounds =>
                                  simp only [Option.some.injEq, Prod.mk.injEq] at hp
                                  rcases hp with ⟨hfc_eq, hdl_eq⟩
                                  have hlim4 : 4 * i < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
                                  have htu : ctDataConstTy.unqual = .structTy "ct_data_s" := rfl
                                  have hlook : prog.tags.lookup "ct_data_s" = some (.structDef ctDataFields) := by
                                    rw [htags]; exact prog_tags_lookup_ct_data_s
                                  rw [writeInitVal_structTy htu hlook, int64_ofNat_toNat_eq hlim4] at hwr
                                  dsimp only [ctDataFields] at hwr
                                  rw [writeInitFields_cons] at hwr
                                  have hfoff0 : alignUp 0 (max 1 (alignofTy prog.tags ctDataFcUnionTy)) = 0 := by simp; rfl
                                  have hsz0 : sizeofTy prog.tags ctDataFcUnionTy = 2 := by simp
                                  dsimp only at hwr
                                  rw [hfoff0, hsz0, Nat.add_zero] at hwr
                                  simp only [bind, Option.bind] at hwr
                                  have hfc_union : ctDataFcUnionTy.unqual =
                                      .anonUnion [("freq", .typedef "ush" (.int .u16)), ("code", .typedef "ush" (.int .u16))] := rfl
                                  cases hs0 : writeInitVal prog env m0 strBase m.nextBlock (Int64.ofNat (4 * i)) ctDataFcUnionTy (.list [.expr fcE]) ns0 with
                                  | none => rw [hs0] at hwr; cases hwr
                                  | some p0 =>
                                    rcases p0 with ⟨ma, nsa⟩
                                    rw [hs0] at hwr; dsimp only at hwr
                                    rw [writeInitVal_anonUnion hfc_union] at hs0
                                    obtain ⟨rfl, hma_next, hma_ne, blka, hblka, hsza, hala, hperma, hka, hbaa, hlt0, hge0, hcur0⟩ :=
                                      writeInitVal_pureInt_step (k := .u16) rfl hfc hb hlim4 hs0
                                    rw [writeInitFields_cons] at hwr
                                    have hfoff1 : alignUp 2 (max 1 (alignofTy prog.tags ctDataDlUnionTy)) = 2 := by simp; rfl
                                    have hsz1 : sizeofTy prog.tags ctDataDlUnionTy = 2 := by simp
                                    dsimp only at hwr
                                    rw [hfoff1, hsz1] at hwr
                                    simp only [bind, Option.bind] at hwr
                                    have hlim2 : 4 * i + 2 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
                                    have hdl_union : ctDataDlUnionTy.unqual =
                                        .anonUnion [("dad", .typedef "ush" (.int .u16)), ("len", .typedef "ush" (.int .u16))] := rfl
                                    cases hs1 : writeInitVal prog env ma strBase m.nextBlock (Int64.ofNat (4 * i + 2)) ctDataDlUnionTy (.list [.expr dlE]) nsa with
                                    | none => rw [hs1] at hwr; cases hwr
                                    | some p1 =>
                                      rcases p1 with ⟨mb, nsb⟩
                                      rw [hs1] at hwr; dsimp only at hwr
                                      rw [writeInitFields_nil] at hwr
                                      simp only [Option.some.injEq, Prod.mk.injEq] at hwr
                                      rcases hwr with ⟨rfl, rfl⟩
                                      rw [writeInitVal_anonUnion hdl_union] at hs1
                                      obtain ⟨rfl, hmb_next, hmb_ne, blkb, hblkb, hszb, halb, hpermb, hkb, hbab, hlt1, hge1, hcur1⟩ :=
                                        writeInitVal_pureInt_step (k := .u16) rfl hdl hblka hlim2 hs1
                                      have hbv0 : BitVec.ofInt IntKind.u16.bits fcI = BitVec.ofNat IntKind.u16.bits fc := by
                                        apply BitVec.eq_of_toNat_eq
                                        have hbv_nat : (BitVec.ofInt 16 fcI).toNat = fcI.toNat := by
                                          rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
                                        have hbv_nat2 : (BitVec.ofNat 16 fc).toNat = fc := by
                                          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                                        change (BitVec.ofInt 16 fcI).toNat = (BitVec.ofNat 16 fc).toNat
                                        rw [hbv_nat, hbv_nat2, ← hfc_eq]
                                      have hbv1 : BitVec.ofInt IntKind.u16.bits dlI = BitVec.ofNat IntKind.u16.bits dl := by
                                        apply BitVec.eq_of_toNat_eq
                                        have hbv_nat : (BitVec.ofInt 16 dlI).toNat = dlI.toNat := by
                                          rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
                                        have hbv_nat2 : (BitVec.ofNat 16 dl).toNat = dl := by
                                          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                                        change (BitVec.ofInt 16 dlI).toNat = (BitVec.ofNat 16 dl).toNat
                                        rw [hbv_nat, hbv_nat2, ← hdl_eq]
                                      rw [hbv0] at hcur0
                                      rw [hbv1] at hcur1
                                      let bs0 := Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits fc)
                                      let bs1 := Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits dl)
                                      have hlen0 : bs0.length = 2 := encodeInt_length _ _
                                      have hlen1 : bs1.length = 2 := encodeInt_length _ _
                                      have hbytes_u16 : IntKind.u16.bytes = 2 := rfl
                                      obtain ⟨ha_lt, ha_ge, ha_cur⟩ := bytes_concat_step (bs1 := bs0) (bs2 := bs1) hlt0
                                        (fun j hj => hge0 j (by rw [hlen0] at hj; rw [hbytes_u16]; omega))
                                        (fun j hj => hcur0 j (by rw [hlen0] at hj; rw [hbytes_u16]; exact hj))
                                        (fun j hj => hlt1 j (by rw [hlen0] at hj; exact hj))
                                        (fun j hj => hge1 j (by rw [hlen0, hlen1] at hj; rw [hbytes_u16]; omega))
                                        (fun j hj => by rw [hlen0]; exact hcur1 j (by rw [hlen1] at hj; rw [hbytes_u16]; exact hj))
                                      refine ⟨rfl, hmb_next.trans hma_next, fun y hy => ?_,
                                        blkb, hblkb, hszb.trans hsza, halb.trans hala, hpermb.trans hperma,
                                        hkb.trans hka, hbab.trans hbaa, ha_lt, ?_, ?_⟩
                                      · rw [hmb_ne y hy, hma_ne y hy]
                                      · intro j hj; apply ha_ge; rw [List.length_append, hlen0, hlen1]; omega
                                      · intro j hj; exact ha_cur j (by rw [List.length_append, hlen0, hlen1]; exact hj)
                                · cases hp
    | expr _ | intSeq _ _ => simp [parseCtDataInit?] at hp
  obtain ⟨rfl, rfl, rfl, hpres, blk, hblk, hsz, hal, hkind, hperm, hcur, hge⟩ :=
    allocVarInit_strideArray_inv hty hxlen hsz_el hal_el (eal_req := 2) (by decide)
      hinit parseCtDataInit? hall ctDataElemBytes ctDataElemBytes_len hstep h
  have hal_eq : blk.align = 2 := hal
  have hperm_ro : blk.perm = .ro := hperm
  have hfmlen : (xs.filterMap parseCtDataInit?).length = n := by
    rw [filterMap_all_isSome_length parseCtDataInit? xs hall, hxlen]
  have hconcr : ∀ k, ∃ u : UInt8, blk.bytes k = .byte u :=
    allBytes_concrete_of_stride hfmlen (by decide) ctDataElemBytes_len ctDataElemBytes_concr hcur hge
  refine ⟨rfl, rfl, rfl, hpres, blk, hblk, hsz, hal_eq, hkind, hperm_ro, hconcr, fun i hi => ?_⟩
  have hsz_i : 4 * (i + 1) ≤ blk.size := by
    rw [hsz]; have hi_n : i < n := by rw [hfmlen] at hi; exact hi
    exact Nat.le_trans (Nat.mul_le_mul_left 4 (Nat.succ_le_of_lt hi_n))
      (by rw [Nat.mul_comm]; exact Nat.le_max_right 1 (n * 4))
  have hbytes_i := hcur i hi
  let t := (xs.filterMap parseCtDataInit?)[i]
  have hbytes_len : ∀ j (hj : j < (ctDataElemBytes t).length),
      blk.bytes (4 * i + j) = (ctDataElemBytes t)[j] :=
    fun j hj => hbytes_i j (by rw [ctDataElemBytes_len] at hj; exact hj)
  dsimp only [ctDataElemBytes] at hbytes_len
  obtain ⟨hslice_0, hslice_1⟩ := bytes_slice_of_concat hbytes_len
  have hlen0 : (Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits t.1)).length = 2 := encodeInt_length _ _
  have hlim0 : 4 * i < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
  have hlim1 : 4 * i + 2 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
  have hbu16 : IntKind.u16.bytes = 2 := rfl
  refine ⟨?_, ?_⟩
  · refine readVal_int_of_exact (k := .u16) rfl hblk hlim0
      (by rw [inBounds_iff, int64_ofNat_toInt hlim0, hbu16]; exact ⟨Int.natCast_nonneg _, by simp only [Int.toNat_natCast]; omega⟩)
      (isAligned_of_dvd (by decide) (by rw [hal_eq]; exact Nat.dvd_refl 2)
        (by rw [show IntKind.u16.align = 2 from rfl]; exact ⟨2 * i, by omega⟩) hlim0) ?_
    intro j hj; exact hslice_0 j hj
  · refine readVal_int_of_exact (k := .u16) rfl hblk hlim1
      (by rw [inBounds_iff, int64_ofNat_toInt hlim1, hbu16]; exact ⟨Int.natCast_nonneg _, by simp only [Int.toNat_natCast]; omega⟩)
      (isAligned_of_dvd (by decide) (by rw [hal_eq]; exact Nat.dvd_refl 2)
        (by rw [show IntKind.u16.align = 2 from rfl]; exact ⟨2 * i + 1, by omega⟩) hlim1) ?_
    intro j hj; rw [← hlen0]; exact hslice_1 j hj

private def configElemBytes (c : Nat × Nat × Nat × Nat × String) : List MemByte :=
  Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.1) ++
  Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.1) ++
  Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.2.1) ++
  Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.2.2.1) ++
  Mem.encodeFnPtr c.2.2.2.2

private theorem configElemBytes_len (c : Nat × Nat × Nat × Nat × String) :
    (configElemBytes c).length = 16 := by
  unfold configElemBytes
  rw [List.length_append, List.length_append, List.length_append, List.length_append,
    encodeInt_length, encodeInt_length, encodeInt_length, encodeInt_length, encodeFnPtr_length]
  rfl

private theorem allocVarInit_configArray_inv {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {n : Nat} {xs : List InitVal}
    (htags : prog.tags = (progOfTUs Zlib.allFiles).tags)
    (hty : d.ty = .array configConstTy (some n))
    (hxlen : xs.length = n)
    (hinit : d.init? = some (.list xs))
    (hall : xs.all (fun x => (parseConfigInit? x).isSome) = true)
    (hfn_ok : ∀ fnm,
      (fnm = "deflate_stored" ∨ fnm = "deflate_fast" ∨ fnm = "deflate_slow") →
      env.lookup fnm = none ∧ enumConst? prog.tags fnm = none ∧
      ∃ ret ps variadic, prog.fnProtos fnm = some (ret, ps, variadic))
    {bid : BlockId} {ty : CTy}
    (h : allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns')) :
    bid = m.nextBlock ∧ ty = .array configConstTy (some n) ∧ ns' = ns ∧
    MemPreservedBelow m.nextBlock m m' ∧
    ∃ blk, m'.blocks bid = some blk ∧
      blk.size = max 1 (n * 16) ∧ blk.align = 8 ∧ blk.kind = .global ∧ blk.perm = .ro ∧
      (∀ (i : Nat) (hi : i < (xs.filterMap parseConfigInit?).length),
        let c := (xs.filterMap parseConfigInit?)[i]
        Sem.readVal prog.tags m' bid (Int64.ofNat (16 * i)) (.int .u16) = some (.int .u16 (BitVec.ofNat 16 c.1)) ∧
        Sem.readVal prog.tags m' bid (Int64.ofNat (16 * i + 2)) (.int .u16) = some (.int .u16 (BitVec.ofNat 16 c.2.1)) ∧
        Sem.readVal prog.tags m' bid (Int64.ofNat (16 * i + 4)) (.int .u16) = some (.int .u16 (BitVec.ofNat 16 c.2.2.1)) ∧
        Sem.readVal prog.tags m' bid (Int64.ofNat (16 * i + 6)) (.int .u16) = some (.int .u16 (BitVec.ofNat 16 c.2.2.2.1)) ∧
        Sem.readVal prog.tags m' bid (Int64.ofNat (16 * i + 8)) configFuncFieldTy = some (.fnPtr c.2.2.2.2)) := by
  have hsz_el : sizeofTy prog.tags configConstTy = 16 := by
    rw [configConstTy, sizeofTy_const, configCTy, sizeofTy_typedef, htags, sizeofTy_config_s]
  have hal_el : alignofTy prog.tags configConstTy = 8 := by
    rw [configConstTy, alignofTy_const, configCTy, alignofTy_typedef, htags, alignofTy_config_s]
  have hstep : ∀ {m0 m1 : Mem} {blk : Block} {i ns0 ns1 : Nat} {iv : InitVal}
      {a : Nat × Nat × Nat × Nat × String},
      parseConfigInit? iv = some a → m0.blocks m.nextBlock = some blk → 8 ∣ blk.align → 16 * (i + 1) ≤ blk.size →
      writeInitVal prog env m0 strBase m.nextBlock (Int64.ofNat (16 * i)) configConstTy iv ns0 = some (m1, ns1) →
      ns1 = ns0 ∧ m1.nextBlock = m0.nextBlock ∧ (∀ y, y ≠ m.nextBlock → m1.blocks y = m0.blocks y) ∧
      ∃ blk1, m1.blocks m.nextBlock = some blk1 ∧
        blk1.size = blk.size ∧ blk1.align = blk.align ∧ blk1.perm = blk.perm ∧
        blk1.kind = blk.kind ∧ blk1.baseAddr = blk.baseAddr ∧
        (∀ j, j < 16 * i → blk1.bytes j = blk.bytes j) ∧
        (∀ j, 16 * (i + 1) ≤ j → blk1.bytes j = blk.bytes j) ∧
        (∀ j (hj : j < 16), blk1.bytes (16 * i + j) = (configElemBytes a)[j]'(by rw [configElemBytes_len]; exact hj)) := by
    intro m0 m1 blk i ns0 ns1 iv a hp hb _ hsz_blk hwr
    rcases a with ⟨glV, mlV, nlV, mcV, fnm⟩
    cases iv with
    | list ys =>
      cases ys with
      | nil => simp [parseConfigInit?] at hp
      | cons e0 ys1 =>
        cases ys1 with
        | nil => simp [parseConfigInit?] at hp
        | cons e1 ys2 =>
          cases ys2 with
          | nil => simp [parseConfigInit?] at hp
          | cons e2 ys3 =>
            cases ys3 with
            | nil => simp [parseConfigInit?] at hp
            | cons e3 ys4 =>
              cases ys4 with
              | nil => simp [parseConfigInit?] at hp
              | cons e4 ys5 =>
                cases ys5 with
                | cons _ _ => simp [parseConfigInit?] at hp
                | nil =>
                  cases e0 with
                  | list _ | intSeq _ _ => simp [parseConfigInit?] at hp
                  | expr glE =>
                    cases e1 with
                    | list _ | intSeq _ _ => simp [parseConfigInit?] at hp
                    | expr mlE =>
                      cases e2 with
                      | list _ | intSeq _ _ => simp [parseConfigInit?] at hp
                      | expr nlE =>
                        cases e3 with
                        | list _ | intSeq _ _ => simp [parseConfigInit?] at hp
                        | expr mcE =>
                          cases e4 with
                          | list _ | intSeq _ _ => simp [parseConfigInit?] at hp
                          | expr fnE =>
                            cases fnE with
                            | var fnm' =>
                              simp only [parseConfigInit?, bind, Option.bind, pure, Pure.pure] at hp
                              cases hgl : evalPureLit? glE with
                              | none => rw [hgl] at hp; cases hp
                              | some glI =>
                                rw [hgl] at hp; dsimp only at hp
                                cases hml : evalPureLit? mlE with
                                | none => rw [hml] at hp; cases hp
                                | some mlI =>
                                  rw [hml] at hp; dsimp only at hp
                                  cases hnl : evalPureLit? nlE with
                                  | none => rw [hnl] at hp; cases hp
                                  | some nlI =>
                                    rw [hnl] at hp; dsimp only at hp
                                    cases hmc : evalPureLit? mcE with
                                    | none => rw [hmc] at hp; cases hp
                                    | some mcI =>
                                      rw [hmc] at hp; dsimp only at hp
                                      split at hp
                                      · next hbounds =>
                                        simp only [Option.some.injEq, Prod.mk.injEq] at hp
                                        rcases hp with ⟨hgl_eq, hml_eq, hnl_eq, hmc_eq, rfl⟩
                                        have hlim16 : 16 * i < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
                                        have htu : configConstTy.unqual = .structTy "config_s" := rfl
                                        have hlook : prog.tags.lookup "config_s" = some (.structDef configFields) := by
                                          rw [htags]; exact prog_tags_lookup_config_s
                                        rw [writeInitVal_structTy htu hlook, int64_ofNat_toNat_eq hlim16] at hwr
                                        dsimp only [configFields] at hwr
                                        have hfoff_u16 : ∀ acc, alignUp acc (max 1 (alignofTy prog.tags (.typedef "ush" (.int .u16)))) = alignUp acc 2 := by
                                          intro acc; simp; rfl
                                        have hsz_u16 : sizeofTy prog.tags (.typedef "ush" (.int .u16)) = 2 := by simp; rfl
                                        rw [writeInitFields_cons] at hwr
                                        dsimp only at hwr
                                        rw [hfoff_u16 0, hsz_u16] at hwr
                                        have hal0 : alignUp 0 2 = 0 := rfl
                                        rw [hal0, Nat.add_zero] at hwr
                                        simp only [bind, Option.bind] at hwr
                                        cases hs0 : writeInitVal prog env m0 strBase m.nextBlock (Int64.ofNat (16 * i)) (.typedef "ush" (.int .u16)) (.expr glE) ns0 with
                                        | none => rw [hs0] at hwr; cases hwr
                                        | some p0 =>
                                          rcases p0 with ⟨ma, nsa⟩
                                          rw [hs0] at hwr; dsimp only at hwr
                                          obtain ⟨rfl, hma_next, hma_ne, blka, hblka, hsza, hala, hperma, hka, hbaa, hlt0, hge0, hcur0⟩ :=
                                            writeInitVal_pureInt_step (k := .u16) rfl hgl hb hlim16 hs0
                                          rw [writeInitFields_cons] at hwr
                                          dsimp only at hwr
                                          rw [hfoff_u16 2, hsz_u16] at hwr
                                          have hal2 : alignUp 2 2 = 2 := rfl
                                          rw [hal2] at hwr
                                          simp only [bind, Option.bind] at hwr
                                          have hlim2 : 16 * i + 2 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
                                          cases hs1 : writeInitVal prog env ma strBase m.nextBlock (Int64.ofNat (16 * i + 2)) (.typedef "ush" (.int .u16)) (.expr mlE) nsa with
                                          | none => rw [hs1] at hwr; cases hwr
                                          | some p1 =>
                                            rcases p1 with ⟨mb, nsb⟩
                                            rw [hs1] at hwr; dsimp only at hwr
                                            obtain ⟨rfl, hmb_next, hmb_ne, blkb, hblkb, hszb, halb, hpermb, hkb, hbab, hlt1, hge1, hcur1⟩ :=
                                              writeInitVal_pureInt_step (k := .u16) rfl hml hblka hlim2 hs1
                                            rw [writeInitFields_cons] at hwr
                                            dsimp only at hwr
                                            rw [hfoff_u16 4, hsz_u16] at hwr
                                            have hal4 : alignUp 4 2 = 4 := rfl
                                            rw [hal4] at hwr
                                            simp only [bind, Option.bind] at hwr
                                            have hlim4 : 16 * i + 4 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
                                            cases hs2 : writeInitVal prog env mb strBase m.nextBlock (Int64.ofNat (16 * i + 4)) (.typedef "ush" (.int .u16)) (.expr nlE) nsb with
                                            | none => rw [hs2] at hwr; cases hwr
                                            | some p2 =>
                                              rcases p2 with ⟨mc, nsc⟩
                                              rw [hs2] at hwr; dsimp only at hwr
                                              obtain ⟨rfl, hmc_next, hmc_ne, blkc, hblkc, hszc, halc, hpermc, hkc, hbac, hlt2, hge2, hcur2⟩ :=
                                                writeInitVal_pureInt_step (k := .u16) rfl hnl hblkb hlim4 hs2
                                              rw [writeInitFields_cons] at hwr
                                              dsimp only at hwr
                                              rw [hfoff_u16 6, hsz_u16] at hwr
                                              have hal6 : alignUp 6 2 = 6 := rfl
                                              rw [hal6] at hwr
                                              simp only [bind, Option.bind] at hwr
                                              have hlim6 : 16 * i + 6 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
                                              cases hs3 : writeInitVal prog env mc strBase m.nextBlock (Int64.ofNat (16 * i + 6)) (.typedef "ush" (.int .u16)) (.expr mcE) nsc with
                                              | none => rw [hs3] at hwr; cases hwr
                                              | some p3 =>
                                                rcases p3 with ⟨md, nsd⟩
                                                rw [hs3] at hwr; dsimp only at hwr
                                                obtain ⟨rfl, hmd_next, hmd_ne, blkd, hblkd, hszd, hald, hpermd, hkd, hbad, hlt3, hge3, hcur3⟩ :=
                                                  writeInitVal_pureInt_step (k := .u16) rfl hmc hblkc hlim6 hs3
                                                rw [writeInitFields_cons] at hwr
                                                dsimp only at hwr
                                                have hfoff_fn : alignUp (6 + 2) (max 1 (alignofTy prog.tags configFuncFieldTy)) = 8 := by
                                                  simp [configFuncFieldTy]; rfl
                                                change (do
                                                  let (m1, ns1) ← writeInitVal prog env md strBase m.nextBlock
                                                    (Int64.ofNat (16 * i + alignUp (6 + 2) (max 1 (alignofTy prog.tags configFuncFieldTy))))
                                                    configFuncFieldTy (.expr (.var fnm')) nsd
                                                  writeInitFields prog env m1 strBase m.nextBlock (16 * i) _ [] [] ns1) = _ at hwr
                                                rw [hfoff_fn] at hwr
                                                simp only [bind, Option.bind] at hwr
                                                have hlim8 : 16 * i + 8 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
                                                obtain ⟨hlook_fn, henum_fn, ret, ps, variadic, hproto_fn⟩ := hfn_ok fnm' hbounds.2.2.2.2.2.2.2.2
                                                have hwr4 : writeInitVal prog env md strBase m.nextBlock (Int64.ofNat (16 * i + 8))
                                                    configFuncFieldTy (.expr (.var fnm')) nsd =
                                                    (writeVal md m.nextBlock (Int64.ofNat (16 * i + 8)) configFuncFieldTy.stripConst (.fnPtr fnm')).map (·, nsd) := by
                                                  rw [writeInitVal_expr_not_strLit (by intro s hs; cases hs)]
                                                  rw [evalConstExpr_var_fnPtr hlook_fn henum_fn hproto_fn]
                                                  rfl
                                                rw [hwr4] at hwr
                                                cases hw4 : writeVal md m.nextBlock (Int64.ofNat (16 * i + 8)) configFuncFieldTy.stripConst (.fnPtr fnm') with
                                                | none => rw [hw4] at hwr; cases hwr
                                                | some me =>
                                                  rw [hw4, Option.map_some] at hwr
                                                  dsimp only at hwr
                                                  rw [writeInitFields_nil] at hwr
                                                  simp only [Option.some.injEq, Prod.mk.injEq] at hwr
                                                  rcases hwr with ⟨rfl, rfl⟩
                                                  have hfn_nc : configFuncFieldTy.stripConst.isConst = false := stripConst_isConst _
                                                  have hfn_u : configFuncFieldTy.stripConst.unqual =
                                                      .fnPtr (.typedef "block_state" (.int .u32))
                                                        [.ptr (.typedef "deflate_state" (.structTy "internal_state")), .int .i32] false := rfl
                                                  obtain ⟨hme_next, hme_ne, blke, hblke, hsze, hale, hperme, hke, hbae, hlt4, hge4, hcur4⟩ :=
                                                    writeVal_fnPtr_step_mem hfn_nc hfn_u hblkd hlim8 hw4
                                                  have hbv0 : BitVec.ofInt IntKind.u16.bits glI = BitVec.ofNat IntKind.u16.bits glV := by
                                                    apply BitVec.eq_of_toNat_eq
                                                    have hnat : (BitVec.ofInt 16 glI).toNat = glI.toNat := by
                                                      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
                                                    have hnat2 : (BitVec.ofNat 16 glV).toNat = glV := by
                                                      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                                                    change (BitVec.ofInt 16 glI).toNat = (BitVec.ofNat 16 glV).toNat
                                                    rw [hnat, hnat2, ← hgl_eq]
                                                  have hbv1 : BitVec.ofInt IntKind.u16.bits mlI = BitVec.ofNat IntKind.u16.bits mlV := by
                                                    apply BitVec.eq_of_toNat_eq
                                                    have hnat : (BitVec.ofInt 16 mlI).toNat = mlI.toNat := by
                                                      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
                                                    have hnat2 : (BitVec.ofNat 16 mlV).toNat = mlV := by
                                                      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                                                    change (BitVec.ofInt 16 mlI).toNat = (BitVec.ofNat 16 mlV).toNat
                                                    rw [hnat, hnat2, ← hml_eq]
                                                  have hbv2 : BitVec.ofInt IntKind.u16.bits nlI = BitVec.ofNat IntKind.u16.bits nlV := by
                                                    apply BitVec.eq_of_toNat_eq
                                                    have hnat : (BitVec.ofInt 16 nlI).toNat = nlI.toNat := by
                                                      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
                                                    have hnat2 : (BitVec.ofNat 16 nlV).toNat = nlV := by
                                                      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                                                    change (BitVec.ofInt 16 nlI).toNat = (BitVec.ofNat 16 nlV).toNat
                                                    rw [hnat, hnat2, ← hnl_eq]
                                                  have hbv3 : BitVec.ofInt IntKind.u16.bits mcI = BitVec.ofNat IntKind.u16.bits mcV := by
                                                    apply BitVec.eq_of_toNat_eq
                                                    have hnat : (BitVec.ofInt 16 mcI).toNat = mcI.toNat := by
                                                      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
                                                    have hnat2 : (BitVec.ofNat 16 mcV).toNat = mcV := by
                                                      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                                                    change (BitVec.ofInt 16 mcI).toNat = (BitVec.ofNat 16 mcV).toNat
                                                    rw [hnat, hnat2, ← hmc_eq]
                                                  rw [hbv0] at hcur0; rw [hbv1] at hcur1; rw [hbv2] at hcur2; rw [hbv3] at hcur3
                                                  let bs0 := Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits glV)
                                                  let bs1 := Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits mlV)
                                                  let bs2 := Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits nlV)
                                                  let bs3 := Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits mcV)
                                                  let bs4 := Mem.encodeFnPtr fnm'
                                                  have hlen0 : bs0.length = 2 := encodeInt_length _ _
                                                  have hlen1 : bs1.length = 2 := encodeInt_length _ _
                                                  have hlen2 : bs2.length = 2 := encodeInt_length _ _
                                                  have hlen3 : bs3.length = 2 := encodeInt_length _ _
                                                  have hlen4 : bs4.length = 8 := encodeFnPtr_length _
                                                  have hbu16 : IntKind.u16.bytes = 2 := rfl
                                                  obtain ⟨ha_lt, ha_ge, ha_cur⟩ := bytes_concat_step (bs1 := bs0) (bs2 := bs1) hlt0
                                                    (fun j hj => hge0 j (by rw [hlen0] at hj; rw [hbu16]; omega))
                                                    (fun j hj => hcur0 j (by rw [hlen0] at hj; rw [hbu16]; exact hj))
                                                    (fun j hj => hlt1 j (by rw [hlen0] at hj; exact hj))
                                                    (fun j hj => hge1 j (by rw [hlen0, hlen1] at hj; rw [hbu16]; omega))
                                                    (fun j hj => by rw [hlen0]; exact hcur1 j (by rw [hlen1] at hj; rw [hbu16]; exact hj))
                                                  have hlen01 : (bs0 ++ bs1).length = 4 := by
                                                    rw [List.length_append, hlen0, hlen1]
                                                  obtain ⟨hb_lt, hb_ge, hb_cur⟩ := bytes_concat_step (bs1 := bs0 ++ bs1) (bs2 := bs2) ha_lt ha_ge ha_cur
                                                    (fun j hj => hlt2 j (by rw [hlen01] at hj; exact hj))
                                                    (fun j hj => hge2 j (by rw [hlen01, hlen2] at hj; rw [hbu16]; omega))
                                                    (fun j hj => by rw [hlen01]; exact hcur2 j (by rw [hlen2] at hj; rw [hbu16]; exact hj))
                                                  have hlen02 : (bs0 ++ bs1 ++ bs2).length = 6 := by
                                                    rw [List.length_append, hlen01, hlen2]
                                                  obtain ⟨hc_lt, hc_ge, hc_cur⟩ := bytes_concat_step (bs1 := bs0 ++ bs1 ++ bs2) (bs2 := bs3) hb_lt hb_ge hb_cur
                                                    (fun j hj => hlt3 j (by rw [hlen02] at hj; exact hj))
                                                    (fun j hj => hge3 j (by rw [hlen02, hlen3] at hj; rw [hbu16]; omega))
                                                    (fun j hj => by rw [hlen02]; exact hcur3 j (by rw [hlen3] at hj; rw [hbu16]; exact hj))
                                                  have hlen03 : (bs0 ++ bs1 ++ bs2 ++ bs3).length = 8 := by
                                                    rw [List.length_append, hlen02, hlen3]
                                                  obtain ⟨hd_lt, hd_ge, hd_cur⟩ := bytes_concat_step (bs1 := bs0 ++ bs1 ++ bs2 ++ bs3) (bs2 := bs4) hc_lt hc_ge hc_cur
                                                    (fun j hj => hlt4 j (by rw [hlen03] at hj; exact hj))
                                                    (fun j hj => hge4 j (by rw [hlen03, hlen4] at hj; omega))
                                                    (fun j hj => by rw [hlen03]; exact hcur4 j (by rw [hlen4] at hj; exact hj))
                                                  refine ⟨rfl, hme_next.trans (hmd_next.trans (hmc_next.trans (hmb_next.trans hma_next))),
                                                    fun y hy => ?_, blke, hblke,
                                                    hsze.trans (hszd.trans (hszc.trans (hszb.trans hsza))),
                                                    hale.trans (hald.trans (halc.trans (halb.trans hala))),
                                                    hperme.trans (hpermd.trans (hpermc.trans (hpermb.trans hperma))),
                                                    hke.trans (hkd.trans (hkc.trans (hkb.trans hka))),
                                                    hbae.trans (hbad.trans (hbac.trans (hbab.trans hbaa))),
                                                    hd_lt, ?_, ?_⟩
                                                  · rw [hme_ne y hy, hmd_ne y hy, hmc_ne y hy, hmb_ne y hy, hma_ne y hy]
                                                  · intro j hj; apply hd_ge; rw [List.length_append, hlen03, hlen4]; omega
                                                  · intro j hj; exact hd_cur j (by rw [List.length_append, hlen03, hlen4]; exact hj)
                                      · cases hp
                            | _ => simp [parseConfigInit?] at hp
    | expr _ | intSeq _ _ => simp [parseConfigInit?] at hp
  obtain ⟨rfl, rfl, rfl, hpres, blk, hblk, hsz, hal, hkind, hperm, hcur, _⟩ :=
    allocVarInit_strideArray_inv hty hxlen hsz_el hal_el (eal_req := 8) (by decide)
      hinit parseConfigInit? hall configElemBytes configElemBytes_len hstep h
  have hal_eq : blk.align = 8 := hal
  have hperm_ro : blk.perm = .ro := hperm
  have hfmlen : (xs.filterMap parseConfigInit?).length = n := by
    rw [filterMap_all_isSome_length parseConfigInit? xs hall, hxlen]
  refine ⟨rfl, rfl, rfl, hpres, blk, hblk, hsz, hal_eq, hkind, hperm_ro, fun i hi => ?_⟩
  have hsz_i : 16 * (i + 1) ≤ blk.size := by
    rw [hsz]; have hi_n : i < n := by rw [hfmlen] at hi; exact hi
    exact Nat.le_trans (Nat.mul_le_mul_left 16 (Nat.succ_le_of_lt hi_n))
      (by rw [Nat.mul_comm]; exact Nat.le_max_right 1 (n * 16))
  have hbytes_i := hcur i hi
  let c := (xs.filterMap parseConfigInit?)[i]
  have hbytes_len : ∀ j (hj : j < (configElemBytes c).length),
      blk.bytes (16 * i + j) = (configElemBytes c)[j] :=
    fun j hj => hbytes_i j (by rw [configElemBytes_len] at hj; exact hj)
  dsimp only [configElemBytes] at hbytes_len
  obtain ⟨hs03, hs4⟩ := bytes_slice_of_concat hbytes_len
  obtain ⟨hs02, hs3⟩ := bytes_slice_of_concat hs03
  obtain ⟨hs01, hs2⟩ := bytes_slice_of_concat hs02
  obtain ⟨hs0, hs1⟩ := bytes_slice_of_concat hs01
  have hlen0 : (Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.1)).length = 2 := encodeInt_length _ _
  have hlen1 : (Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.1)).length = 2 := encodeInt_length _ _
  have hlen2 : (Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.2.1)).length = 2 := encodeInt_length _ _
  have hlen3 : (Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.2.2.1)).length = 2 := encodeInt_length _ _
  have hlen01 : (Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.1) ++
      Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.1)).length = 4 := by
    rw [List.length_append, hlen0, hlen1]
  have hlen02 : ((Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.1) ++
      Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.1)) ++
      Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.2.1)).length = 6 := by
    rw [List.length_append, hlen01, hlen2]
  have hlen03 : (((Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.1) ++
      Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.1)) ++
      Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.2.1)) ++
      Mem.encodeInt .u16 (BitVec.ofNat IntKind.u16.bits c.2.2.2.1)).length = 8 := by
    rw [List.length_append, hlen02, hlen3]
  have hlim0 : 16 * i < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
  have hlim2 : 16 * i + 2 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
  have hlim4 : 16 * i + 4 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
  have hlim6 : 16 * i + 6 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
  have hlim8 : 16 * i + 8 < ptrDiffLimit := Nat.lt_of_lt_of_le (by omega) blk.sizeLt
  have hbu16 : IntKind.u16.bytes = 2 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine readVal_int_of_exact (k := .u16) rfl hblk hlim0
      (by rw [inBounds_iff, int64_ofNat_toInt hlim0, hbu16]; exact ⟨Int.natCast_nonneg _, by simp only [Int.toNat_natCast]; omega⟩)
      (isAligned_of_dvd (by decide) (by rw [hal_eq]; exact ⟨4, rfl⟩)
        (by rw [show IntKind.u16.align = 2 from rfl]; exact ⟨8 * i, by omega⟩) hlim0) ?_
    intro j hj; exact hs0 j hj
  · refine readVal_int_of_exact (k := .u16) rfl hblk hlim2
      (by rw [inBounds_iff, int64_ofNat_toInt hlim2, hbu16]; exact ⟨Int.natCast_nonneg _, by simp only [Int.toNat_natCast]; omega⟩)
      (isAligned_of_dvd (by decide) (by rw [hal_eq]; exact ⟨4, rfl⟩)
        (by rw [show IntKind.u16.align = 2 from rfl]; exact ⟨8 * i + 1, by omega⟩) hlim2) ?_
    intro j hj; rw [← hlen0]; exact hs1 j hj
  · refine readVal_int_of_exact (k := .u16) rfl hblk hlim4
      (by rw [inBounds_iff, int64_ofNat_toInt hlim4, hbu16]; exact ⟨Int.natCast_nonneg _, by simp only [Int.toNat_natCast]; omega⟩)
      (isAligned_of_dvd (by decide) (by rw [hal_eq]; exact ⟨4, rfl⟩)
        (by rw [show IntKind.u16.align = 2 from rfl]; exact ⟨8 * i + 2, by omega⟩) hlim4) ?_
    intro j hj; rw [← hlen01]; exact hs2 j hj
  · refine readVal_int_of_exact (k := .u16) rfl hblk hlim6
      (by rw [inBounds_iff, int64_ofNat_toInt hlim6, hbu16]; exact ⟨Int.natCast_nonneg _, by simp only [Int.toNat_natCast]; omega⟩)
      (isAligned_of_dvd (by decide) (by rw [hal_eq]; exact ⟨4, rfl⟩)
        (by rw [show IntKind.u16.align = 2 from rfl]; exact ⟨8 * i + 3, by omega⟩) hlim6) ?_
    intro j hj; rw [← hlen02]; exact hs3 j hj
  · refine readVal_fnPtr_of_exact
      (ty := configFuncFieldTy)
      (ret := .typedef "block_state" (.int .u32))
      (ps := [.ptr (.typedef "deflate_state" (.structTy "internal_state")), .int .i32])
      (variadic := false) rfl hblk hlim8
      (by rw [inBounds_iff, int64_ofNat_toInt hlim8]; exact ⟨Int.natCast_nonneg _, by simp only [Int.toNat_natCast]; omega⟩)
      (isAligned_of_dvd (by decide) (by rw [hal_eq]; exact Nat.dvd_refl 8) ⟨2 * i + 1, by omega⟩ hlim8) ?_
    intro j hj; rw [← hlen03]; exact hs4 j hj

private theorem allocVarInit_staticTreeDesc_inv {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {e0 e1 e2 e3 e4 : CExpr}
    {v0 : Val} {t0 : CTy} {bs0 : List MemByte}
    {b_eb : BlockId} {el_eb : CTy} {len_eb? : Option Nat}
    {ebName : String} {base_val elems_val max_val : Int}
    {bid : BlockId} {ty : CTy}
    (htags : prog.tags = (progOfTUs Zlib.allFiles).tags)
    (hty : d.ty = staticTreeDescConstTy)
    (hinit : d.init? = some (.list [.expr e0, .expr e1, .expr e2, .expr e3, .expr e4]))
    (h : allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns'))
    (hbs0_len : bs0.length = 8)
    (heval0 : ∀ (mA : Mem), evalConstExpr prog env mA strBase ns e0 = some (v0, t0, mA, ns))
    (hwrite0 : ∀ {mA mB : Mem} {blkA : Block} {b : BlockId},
      mA.blocks b = some blkA → writeVal mA b 0 (.ptr ctDataConstTy) v0 = some mB →
      mB.nextBlock = mA.nextBlock ∧ (∀ y, y ≠ b → mB.blocks y = mA.blocks y) ∧
      ∃ blkB, mB.blocks b = some blkB ∧
        blkB.size = blkA.size ∧ blkB.align = blkA.align ∧ blkB.perm = blkA.perm ∧
        blkB.kind = blkA.kind ∧ blkB.baseAddr = blkA.baseAddr ∧
        (∀ j, 8 ≤ j → blkB.bytes j = blkA.bytes j) ∧
        (∀ j (hj : j < 8), blkB.bytes j = bs0[j]'(by rw [hbs0_len]; exact hj)))
    (he1 : e1 = .var ebName)
    (hlook1 : env.lookup ebName = some (b_eb, .array el_eb len_eb?))
    (h_extra_base : ∀ (mA : Mem), evalConstExpr prog env mA strBase ns e2 = some (.int .i32 (BitVec.ofInt 32 base_val), .int .i32, mA, ns))
    (hbase : -(2^31) ≤ base_val ∧ base_val < 2^31)
    (h_elems : ∀ (mA : Mem), evalConstExpr prog env mA strBase ns e3 = some (.int .i32 (BitVec.ofInt 32 elems_val), .int .i32, mA, ns))
    (helems : -(2^31) ≤ elems_val ∧ elems_val < 2^31)
    (h_max : ∀ (mA : Mem), evalConstExpr prog env mA strBase ns e4 = some (.int .i32 (BitVec.ofInt 32 max_val), .int .i32, mA, ns))
    (hmax : -(2^31) ≤ max_val ∧ max_val < 2^31)
    (hnostr : (∀ s, e0 ≠ .strLit s) ∧ (∀ s, e2 ≠ .strLit s) ∧ (∀ s, e3 ≠ .strLit s) ∧ (∀ s, e4 ≠ .strLit s)) :
    bid = m.nextBlock ∧ ty = staticTreeDescConstTy ∧ ns' = ns ∧
    MemPreservedBelow m.nextBlock m m' ∧
    ∃ blk, m'.blocks bid = some blk ∧
      blk.size = 32 ∧ blk.align = 8 ∧ blk.kind = .global ∧ blk.perm = .ro ∧
      (∀ j (hj : j < 8), blk.bytes j = bs0[j]'(by rw [hbs0_len]; exact hj)) ∧
      Sem.readVal prog.tags m' bid 8 (.ptr (.const_ (.typedef "intf" (.int .i32)))) = some (.ptr b_eb 0) ∧
      Sem.readVal prog.tags m' bid 16 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 base_val)) ∧
      Sem.readVal prog.tags m' bid 20 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 elems_val)) ∧
      Sem.readVal prog.tags m' bid 24 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 max_val)) := by
  have hres : resolveDeclTy d.ty d.init? = staticTreeDescConstTy := by rw [hty]; rfl
  have hsz_ty : max 1 (sizeofTy prog.tags (resolveDeclTy d.ty d.init?)) = 32 := by
    rw [hres, staticTreeDescConstTy, sizeofTy_const, staticTreeDescCTy, sizeofTy_typedef, htags, sizeofTy_static_tree_desc_s]; rfl
  have hal_ty : max 1 (alignofTy prog.tags (resolveDeclTy d.ty d.init?)) = 8 := by
    rw [hres, staticTreeDescConstTy, alignofTy_const, staticTreeDescCTy, alignofTy_typedef, htags, alignofTy_static_tree_desc_s]; rfl
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
          blk1.size = 32 ∧ blk1.align = 8 ∧
          blk1.perm = .rw ∧ blk1.kind = .global := by
      split at halloc
      · split at halloc
        · split at halloc
          · cases halloc
            refine ⟨rfl, rfl, fun x hx => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hx),
              _, alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, hsz_ty, hal_ty, rfl, rfl⟩
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
      have hres' := hres
      rw [hinit] at hres'
      have htu : (resolveDeclTy d.ty (some (.list [.expr e0, .expr e1, .expr e2, .expr e3, .expr e4]))).unqual =
          .structTy "static_tree_desc_s" := by rw [hres']; rfl
      have hlook : prog.tags.lookup "static_tree_desc_s" = some (.structDef staticTreeDescFields) := by
        rw [htags]; exact prog_tags_lookup_static_tree_desc_s
      rw [writeInitVal_structTy htu hlook] at hwr
      have h0_nat : (0 : Int64).toInt.toNat = 0 := rfl
      rw [h0_nat] at hwr
      dsimp only [staticTreeDescFields] at hwr
      rw [writeInitFields_cons] at hwr
      have hfoff0 : alignUp 0 (max 1 (alignofTy prog.tags (.ptr ctDataConstTy))) = 0 := by simp; rfl
      have hsz0 : sizeofTy prog.tags (.ptr ctDataConstTy) = 8 := by simp
      dsimp only at hwr
      rw [hfoff0, hsz0, Nat.add_zero] at hwr
      simp only [bind, Option.bind] at hwr
      rw [show Int64.ofNat 0 = (0 : Int64) from rfl] at hwr
      have hwr0 : writeInitVal prog env m1 strBase m.nextBlock 0 (.ptr ctDataConstTy) (.expr e0) ns =
          (writeVal m1 m.nextBlock 0 (.ptr ctDataConstTy) v0).map (·, ns) := by
        rw [writeInitVal_expr_not_strLit hnostr.1, heval0 m1]; rfl
      rw [hwr0] at hwr
      cases hw0 : writeVal m1 m.nextBlock 0 (.ptr ctDataConstTy) v0 with
      | none => rw [hw0] at hwr; cases hwr
      | some ma =>
        rw [hw0, Option.map_some] at hwr; dsimp only at hwr
        obtain ⟨hma_next, hma_ne, blka, hblka, hsza, hala, hperma, hka, hbaa, _, hcur0⟩ :=
          hwrite0 hblk1 hw0
        rw [writeInitFields_cons] at hwr
        have hfoff1 : alignUp (0 + 8) (max 1 (alignofTy prog.tags (.ptr (.const_ (.typedef "intf" (.int .i32)))))) = 8 := by simp; rfl
        have hsz1f : sizeofTy prog.tags (.ptr (.const_ (.typedef "intf" (.int .i32)))) = 8 := by simp
        dsimp only at hwr
        rw [hfoff1, hsz1f, Nat.zero_add] at hwr
        simp only [bind, Option.bind] at hwr
        have hwr1 : writeInitVal prog env ma strBase m.nextBlock (Int64.ofNat 8) (.ptr (.const_ (.typedef "intf" (.int .i32)))) (.expr e1) ns =
            (writeVal ma m.nextBlock (Int64.ofNat 8) (.ptr (.const_ (.typedef "intf" (.int .i32)))) (.ptr b_eb 0)).map (·, ns) := by
          subst he1
          rw [writeInitVal_expr_not_strLit (by intro s hs; cases hs), evalConstExpr_var_array hlook1]
          rfl
        rw [hwr1] at hwr
        cases hw1 : writeVal ma m.nextBlock (Int64.ofNat 8) (.ptr (.const_ (.typedef "intf" (.int .i32)))) (.ptr b_eb 0) with
        | none => rw [hw1] at hwr; cases hwr
        | some mb =>
          rw [hw1, Option.map_some] at hwr; dsimp only at hwr
          have hsz1_lt : 32 < ptrDiffLimit := by rw [← hsz1]; exact blk1.sizeLt
          have hlim8 : 8 < ptrDiffLimit := Nat.lt_trans (by decide) hsz1_lt
          obtain ⟨hmb_next, hmb_ne, blkb, hblkb, hszb, halb, hpermb, hkb, hbab, hlt1, _, hcur1⟩ :=
            writeVal_ptr_step_mem rfl rfl hblka hlim8 hw1
          rw [writeInitFields_cons] at hwr
          have hfoff2 : alignUp (8 + 8) (max 1 (alignofTy prog.tags (.int .i32))) = 16 := by simp; rfl
          have hsz2f : sizeofTy prog.tags (.int .i32) = 4 := by simp; rfl
          dsimp only at hwr
          rw [hfoff2, hsz2f, Nat.zero_add] at hwr
          simp only [bind, Option.bind] at hwr
          have hwr2 : writeInitVal prog env mb strBase m.nextBlock (Int64.ofNat 16) (.int .i32) (.expr e2) ns =
              (writeVal mb m.nextBlock (Int64.ofNat 16) (.int .i32) (.int .i32 (BitVec.ofInt 32 base_val))).map (·, ns) := by
            rw [writeInitVal_expr_not_strLit hnostr.2.1, h_extra_base mb]; rfl
          rw [hwr2] at hwr
          have hval2 : valAsInt? (.int .i32 (BitVec.ofInt 32 base_val)) = some (.i32, base_val) := by
            change valAsInt? (.int .i32 (BitVec.ofInt IntKind.i32.bits base_val)) = some (.i32, base_val)
            simp only [valAsInt?, IntKind.signed, ↓reduceIte]
            rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (Int.le_trans (by decide) hbase.1) (Int.lt_of_lt_of_le hbase.2 (by decide))]
          cases hw2 : writeVal mb m.nextBlock (Int64.ofNat 16) (.int .i32) (.int .i32 (BitVec.ofInt 32 base_val)) with
          | none => rw [hw2] at hwr; cases hwr
          | some mc =>
            rw [hw2, Option.map_some] at hwr; dsimp only at hwr
            have hlim16 : 16 < ptrDiffLimit := Nat.lt_trans (by decide) hsz1_lt
            obtain ⟨hmc_next, hmc_ne, blkc, hblkc, hszc, halc, hpermc, hkc, hbac, hlt2, _, hcur2⟩ :=
              writeVal_int_step_mem rfl rfl hblkb hlim16 hval2 hw2
            rw [writeInitFields_cons] at hwr
            have hfoff3 : alignUp (16 + 4) (max 1 (alignofTy prog.tags (.int .i32))) = 20 := by simp; rfl
            dsimp only at hwr
            rw [hfoff3, hsz2f, Nat.zero_add] at hwr
            simp only [bind, Option.bind] at hwr
            have hwr3 : writeInitVal prog env mc strBase m.nextBlock (Int64.ofNat 20) (.int .i32) (.expr e3) ns =
                (writeVal mc m.nextBlock (Int64.ofNat 20) (.int .i32) (.int .i32 (BitVec.ofInt 32 elems_val))).map (·, ns) := by
              rw [writeInitVal_expr_not_strLit hnostr.2.2.1, h_elems mc]; rfl
            rw [hwr3] at hwr
            have hval3 : valAsInt? (.int .i32 (BitVec.ofInt 32 elems_val)) = some (.i32, elems_val) := by
              change valAsInt? (.int .i32 (BitVec.ofInt IntKind.i32.bits elems_val)) = some (.i32, elems_val)
              simp only [valAsInt?, IntKind.signed, ↓reduceIte]
              rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (Int.le_trans (by decide) helems.1) (Int.lt_of_lt_of_le helems.2 (by decide))]
            cases hw3 : writeVal mc m.nextBlock (Int64.ofNat 20) (.int .i32) (.int .i32 (BitVec.ofInt 32 elems_val)) with
            | none => rw [hw3] at hwr; cases hwr
            | some md =>
              rw [hw3, Option.map_some] at hwr; dsimp only at hwr
              have hlim20 : 20 < ptrDiffLimit := Nat.lt_trans (by decide) hsz1_lt
              obtain ⟨hmd_next, hmd_ne, blkd, hblkd, hszd, hald, hpermd, hkd, hbad, hlt3, _, hcur3⟩ :=
                writeVal_int_step_mem rfl rfl hblkc hlim20 hval3 hw3
              rw [writeInitFields_cons] at hwr
              have hfoff4 : alignUp (20 + 4) (max 1 (alignofTy prog.tags (.int .i32))) = 24 := by simp; rfl
              dsimp only at hwr
              rw [hfoff4, hsz2f, Nat.zero_add] at hwr
              simp only [bind, Option.bind] at hwr
              have hwr4 : writeInitVal prog env md strBase m.nextBlock (Int64.ofNat 24) (.int .i32) (.expr e4) ns =
                  (writeVal md m.nextBlock (Int64.ofNat 24) (.int .i32) (.int .i32 (BitVec.ofInt 32 max_val))).map (·, ns) := by
                rw [writeInitVal_expr_not_strLit hnostr.2.2.2, h_max md]; rfl
              rw [hwr4] at hwr
              have hval4 : valAsInt? (.int .i32 (BitVec.ofInt 32 max_val)) = some (.i32, max_val) := by
                change valAsInt? (.int .i32 (BitVec.ofInt IntKind.i32.bits max_val)) = some (.i32, max_val)
                simp only [valAsInt?, IntKind.signed, ↓reduceIte]
                rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (Int.le_trans (by decide) hmax.1) (Int.lt_of_lt_of_le hmax.2 (by decide))]
              cases hw4 : writeVal md m.nextBlock (Int64.ofNat 24) (.int .i32) (.int .i32 (BitVec.ofInt 32 max_val)) with
              | none => rw [hw4] at hwr; cases hwr
              | some me =>
                rw [hw4, Option.map_some] at hwr; dsimp only at hwr
                rw [writeInitFields_nil] at hwr
                simp only [Option.some.injEq, Prod.mk.injEq] at hwr
                rcases hwr with ⟨rfl, rfl⟩
                have hlim24 : 24 < ptrDiffLimit := Nat.lt_trans (by decide) hsz1_lt
                obtain ⟨hme_next, hme_ne, blke, hblke, hsze, hale, hperme, hke, hbae, hlt4, _, hcur4⟩ :=
                  writeVal_int_step_mem rfl rfl hblkd hlim24 hval4 hw4
                have hro : (resolveDeclTy d.ty (some (.list [.expr e0, .expr e1, .expr e2, .expr e3, .expr e4]))).isReadOnly = true := by
                  rw [hres']; rfl
                rw [hro] at h; simp only [↓reduceIte] at h
                cases h
                have hsz_e : blke.size = 32 := hsze.trans (hszd.trans (hszc.trans (hszb.trans (hsza.trans hsz1))))
                have hal_e : blke.align = 8 := hale.trans (hald.trans (halc.trans (halb.trans (hala.trans hal1))))
                have hkind_e : blke.kind = .global := hke.trans (hkd.trans (hkc.trans (hkb.trans (hka.trans hk1))))
                have hlim0 : 0 < ptrDiffLimit := Nat.lt_trans (by decide) hsz1_lt
                have hbytes0 : ∀ j (hj : j < 8), blke.bytes j = bs0[j]'(by rw [hbs0_len]; exact hj) := fun j hj => by
                  rw [hlt4 j (by omega), hlt3 j (by omega), hlt2 j (by omega), hlt1 j hj, hcur0 j hj]
                have hbytes1 : ∀ j (hj : j < (Mem.encodePtr b_eb (0 : Int64)).length),
                    blke.bytes (8 + j) = (Mem.encodePtr b_eb (0 : Int64))[j] := fun j hj => by
                  rw [encodePtr_length] at hj
                  rw [hlt4 (8 + j) (by omega), hlt3 (8 + j) (by omega), hlt2 (8 + j) (by omega), hcur1 j hj]
                have hbytes2 : ∀ j (hj : j < (Mem.encodeInt .i32 (BitVec.ofInt IntKind.i32.bits base_val)).length),
                    blke.bytes (16 + j) = (Mem.encodeInt .i32 (BitVec.ofInt IntKind.i32.bits base_val))[j] := fun j hj => by
                  have hbi32 : IntKind.i32.bytes = 4 := rfl
                  rw [encodeInt_length, hbi32] at hj
                  rw [hlt4 (16 + j) (by omega), hlt3 (16 + j) (by omega), hcur2 j hj]
                have hbytes3 : ∀ j (hj : j < (Mem.encodeInt .i32 (BitVec.ofInt IntKind.i32.bits elems_val)).length),
                    blke.bytes (20 + j) = (Mem.encodeInt .i32 (BitVec.ofInt IntKind.i32.bits elems_val))[j] := fun j hj => by
                  have hbi32 : IntKind.i32.bytes = 4 := rfl
                  rw [encodeInt_length, hbi32] at hj
                  rw [hlt4 (20 + j) (by omega), hcur3 j hj]
                have hbytes4 : ∀ j (hj : j < (Mem.encodeInt .i32 (BitVec.ofInt IntKind.i32.bits max_val)).length),
                    blke.bytes (24 + j) = (Mem.encodeInt .i32 (BitVec.ofInt IntKind.i32.bits max_val))[j] := fun j hj => by
                  have hbi32 : IntKind.i32.bytes = 4 := rfl
                  rw [encodeInt_length, hbi32] at hj
                  exact hcur4 j hj
                refine ⟨rfl, hres', rfl, ⟨?_, fun x hx => ?_⟩, ?_⟩
                · simp only [hme_next, hmd_next, hmc_next, hmb_next, hma_next, hm1next]; exact Nat.le_succ _
                · have hne : x ≠ m.nextBlock := Nat.ne_of_lt hx
                  simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
                  rw [hme_ne x hne, hmd_ne x hne, hmc_ne x hne, hmb_ne x hne, hma_ne x hne, hm1lt x hx]
                · refine ⟨{ blke with perm := .ro }, by simp [hblke], hsz_e, hal_e, hkind_e, rfl, hbytes0, ?_, ?_, ?_, ?_⟩
                  · rw [show (8 : Int64) = Int64.ofNat 8 from rfl]
                    exact readVal_ptr_of_exact (blk := { blke with perm := .ro }) rfl (by simp [hblke]) hlim8
                      (by rw [inBounds_iff, int64_ofNat_toInt hlim8]; dsimp only; rw [hsz_e]; decide)
                      (isAligned_of_dvd (by decide) (by dsimp only; rw [hal_e]; exact Nat.dvd_refl 8) (Nat.dvd_refl 8) hlim8)
                      hbytes1
                  · rw [show (16 : Int64) = Int64.ofNat 16 from rfl]
                    exact readVal_int_of_exact (blk := { blke with perm := .ro }) (k := .i32) rfl (by simp [hblke]) hlim16
                      (by rw [inBounds_iff, int64_ofNat_toInt hlim16]; dsimp only; rw [hsz_e]; decide)
                      (isAligned_of_dvd (by decide) (by dsimp only; rw [hal_e]; exact ⟨2, rfl⟩) ⟨4, rfl⟩ hlim16)
                      hbytes2
                  · rw [show (20 : Int64) = Int64.ofNat 20 from rfl]
                    exact readVal_int_of_exact (blk := { blke with perm := .ro }) (k := .i32) rfl (by simp [hblke]) hlim20
                      (by rw [inBounds_iff, int64_ofNat_toInt hlim20]; dsimp only; rw [hsz_e]; decide)
                      (isAligned_of_dvd (by decide) (by dsimp only; rw [hal_e]; exact ⟨2, rfl⟩) ⟨5, rfl⟩ hlim20)
                      hbytes3
                  · rw [show (24 : Int64) = Int64.ofNat 24 from rfl]
                    exact readVal_int_of_exact (blk := { blke with perm := .ro }) (k := .i32) rfl (by simp [hblke]) hlim24
                      (by rw [inBounds_iff, int64_ofNat_toInt hlim24]; dsimp only; rw [hsz_e]; decide)
                      (isAligned_of_dvd (by decide) (by dsimp only; rw [hal_e]; exact ⟨2, rfl⟩) ⟨6, rfl⟩ hlim24)
                      hbytes4

private theorem allocVarInit_intSeq_array_inv {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {el : CTy} {n : Nat} {k : IntKind} {rad : LitRadix} {vals : Array Int}
    (hty : d.ty = .array el (some n))
    (_htyu : el.unqual = .int k)
    (hleaf : (CTy.array el (some n)).arrayLeafIntKind? = some k)
    (hinit : d.init? = some (.intSeq rad vals))
    (hsz_el : sizeofTy prog.tags el = k.bytes)
    (hal_el : alignofTy prog.tags el = k.align)
    (hal_dvd : k.align ∣ max 1 k.align)
    (hvsize : vals.size = n)
    (hro : (CTy.array el (some n)).isReadOnly = true)
    {bid : BlockId} {ty : CTy}
    (h : allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns')) :
    bid = m.nextBlock ∧ ty = .array el (some n) ∧ ns' = ns ∧
    MemPreservedBelow m.nextBlock m m' ∧
    ∃ blk, m'.blocks bid = some blk ∧
      blk.size = max 1 (n * k.bytes) ∧ blk.align = max 1 k.align ∧
      blk.kind = .global ∧ blk.perm = .ro ∧
      (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
      (∀ i < n,
        Sem.readVal prog.tags m' bid (Int64.ofNat (k.bytes * i)) (.int k) =
          some (.int k (BitVec.ofInt k.bits vals[i]!))) := by
  have hres : resolveDeclTy d.ty d.init? = .array el (some n) := by rw [hty]; rfl
  have hres_u : (resolveDeclTy d.ty d.init?).unqual = .array el (some n) := by rw [hres]; rfl
  have hleaf' : (resolveDeclTy d.ty d.init?).arrayLeafIntKind? = some k := by rw [hres]; exact hleaf
  obtain ⟨rfl, hty_eq, rfl, hm_next, hm_lt, blk, hblk, hsz, hal, hk, hperm, hconcr, hread⟩ :=
    allocVarInit_intSeq_inv hres_u hleaf' hinit h
  rw [hres] at hty_eq
  rw [hty_eq] at hsz hal hperm
  have hsz' : blk.size = max 1 (n * k.bytes) := by
    rw [hsz, sizeofTy_array_some, hsz_el]
  have hal' : blk.align = max 1 k.align := by
    rw [hal, alignofTy_array, hal_el]
  have hperm' : blk.perm = .ro := by rw [hperm, ite_eq_left hro]
  refine ⟨rfl, hty_eq, rfl, ⟨by rw [hm_next]; exact Nat.le_succ _, hm_lt⟩,
    blk, hblk, hsz', hal', hk, hperm', hconcr, fun i hi => ?_⟩
  have hi' : i < vals.size := by rw [hvsize]; exact hi
  have hr := hread (by rw [hal']; exact hal_dvd) i hi'
  have hget : vals[i] = vals[i]! := by simp [getElem!_pos vals i hi']
  rw [← hget]; exact hr

/-! ### `tuGlobals` Split and `initGlobs` Invocations Across All 15 TUs -/

private theorem tuGlobals_gzclose : tuGlobals Zlib.Gzclose.gzcloseTU = [] := rfl
private theorem tuGlobals_adler32 : tuGlobals Zlib.Adler32.adler32TU = [] := rfl
private theorem tuGlobals_compress : tuGlobals Zlib.Compress.compressTU = [] := rfl
private theorem tuGlobals_uncompr : tuGlobals Zlib.Uncompr.uncomprTU = [] := rfl
private theorem tuGlobals_inffast : tuGlobals Zlib.Inffast.inffastTU = [] := rfl
private theorem tuGlobals_infback : tuGlobals Zlib.Infback.infbackTU = [] := rfl
private theorem tuGlobals_inflate : tuGlobals Zlib.Inflate.inflateTU = [] := rfl
private theorem tuGlobals_gzlib : tuGlobals Zlib.Gzlib.gzlibTU = [] := rfl
private theorem tuGlobals_gzread : tuGlobals Zlib.Gzread.gzreadTU = [] := rfl
private theorem tuGlobals_gzwrite : tuGlobals Zlib.Gzwrite.gzwriteTU = [] := rfl

private theorem tuGlobals_zutil_names :
    (tuGlobals Zlib.Zutil.zutilTU).map (·.2.name) = ["z_errmsg"] := rfl

private theorem tuGlobals_crc32_names :
    (tuGlobals Zlib.Crc32.crc32TU).map (·.2.name) =
      ["crc_table", "crc_big_table", "crc_braid2_table", "crc_braid2_big_table",
       "crc_braid5_table", "crc_braid5_big_table", "x2n_table"] := rfl

private def inftreesGlobalsList : List (Linkage × VarDecl) := [
  (.export_, Zlib.Inftrees.inftreesTU_global_inflate_copyright),
  (.static_, Zlib.Tables.inffixedH_global_lenfix),
  (.static_, Zlib.Tables.inffixedH_global_distfix)
]
private theorem tuGlobals_inftrees : tuGlobals Zlib.Inftrees.inftreesTU = inftreesGlobalsList := rfl

private def treesGlobalsList : List (Linkage × VarDecl) := [
  (.static_, Zlib.Trees.treesTU_global_extra_lbits),
  (.static_, Zlib.Trees.treesTU_global_extra_dbits),
  (.static_, Zlib.Trees.treesTU_global_extra_blbits),
  (.static_, Zlib.Trees.treesTU_global_bl_order),
  (.static_, Zlib.Tables.treesH_global_static_ltree),
  (.static_, Zlib.Tables.treesH_global_static_dtree),
  (.hidden, Zlib.Tables.treesH_global__dist_code),
  (.hidden, Zlib.Tables.treesH_global__length_code),
  (.static_, Zlib.Tables.treesH_global_base_length),
  (.static_, Zlib.Tables.treesH_global_base_dist),
  (.static_, Zlib.Trees.treesTU_global_static_l_desc),
  (.static_, Zlib.Trees.treesTU_global_static_d_desc),
  (.static_, Zlib.Trees.treesTU_global_static_bl_desc)
]
private theorem tuGlobals_trees : tuGlobals Zlib.Trees.treesTU = treesGlobalsList := rfl
private theorem treesGlobalsList_names :
    treesGlobalsList.map (·.2.name) =
      ["extra_lbits", "extra_dbits", "extra_blbits", "bl_order",
       "static_ltree", "static_dtree", "_dist_code", "_length_code",
       "base_length", "base_dist", "static_l_desc", "static_d_desc", "static_bl_desc"] := rfl

private def deflateGlobalsList : List (Linkage × VarDecl) := [
  (.export_, Zlib.Deflate.deflateTU_global_deflate_copyright),
  (.static_, Zlib.Deflate.deflateTU_global_configuration_table)
]
private theorem tuGlobals_deflate : tuGlobals Zlib.Deflate.deflateTU = deflateGlobalsList := rfl

private theorem prog0_globals_eq :
    (progOfTUs Zlib.allFiles).globals =
      tuGlobals Zlib.Zutil.zutilTU ++ inftreesGlobalsList ++ tuGlobals Zlib.Crc32.crc32TU ++
      treesGlobalsList ++ deflateGlobalsList := by
  rw [progOfTUs_globals]
  change (Zlib.allTUs.flatMap tuGlobals) = _
  simp only [Zlib.allTUs, List.flatMap_cons, List.flatMap_nil,
    tuGlobals_gzclose, tuGlobals_adler32, tuGlobals_compress, tuGlobals_uncompr,
    tuGlobals_inftrees, tuGlobals_inffast, tuGlobals_trees, tuGlobals_infback,
    tuGlobals_inflate, tuGlobals_deflate, tuGlobals_gzlib, tuGlobals_gzread, tuGlobals_gzwrite,
    List.nil_append, List.append_nil, List.append_assoc]

private theorem initGlobs_append {globBase strBase : Nat → UInt64} {prog0 : Prog}
    {idx ns ns' : Nat} {env env' : Env} {m m' : Mem} {gs1 gs2 : List (Linkage × VarDecl)}
    (h : initProg.initGlobs globBase strBase prog0 idx ns env m (gs1 ++ gs2) = some (env', m', ns')) :
    ∃ env1 m1 ns1 idx1,
      initProg.initGlobs globBase strBase prog0 idx ns env m gs1 = some (env1, m1, ns1) ∧
      initProg.initGlobs globBase strBase prog0 idx1 ns1 env1 m1 gs2 = some (env', m', ns') := by
  induction gs1 generalizing idx ns env m with
  | nil => exact ⟨env, m, ns, idx, rfl, h⟩
  | cons g rest ih =>
    simp only [List.cons_append] at h
    unfold initProg.initGlobs at h
    dsimp only at h
    cases hsome : (env.lookup g.2.name).isSome
    · simp only [hsome, Bool.false_eq_true, ↓reduceIte, bind, Option.bind] at h
      cases hal : allocVarInit prog0 env m globBase strBase idx ns g.2 with
      | none => rw [hal] at h; cases h
      | some p =>
        rcases p with ⟨bid, ty, m1, ns1⟩
        rw [hal] at h; dsimp only at h
        obtain ⟨env2, m2, ns2, idx2, hg1, hg2⟩ := ih h
        refine ⟨env2, m2, ns2, idx2, ?_, hg2⟩
        unfold initProg.initGlobs
        simp only [hsome, Bool.false_eq_true, ↓reduceIte, bind, Option.bind, hal]
        exact hg1
    · simp only [hsome, ↓reduceIte] at h
      obtain ⟨env2, m2, ns2, idx2, hg1, hg2⟩ := ih h
      refine ⟨env2, m2, ns2, idx2, ?_, hg2⟩
      unfold initProg.initGlobs
      simp only [hsome, ↓reduceIte]
      exact hg1

private theorem env_none_cons {name : String} {bid : BlockId} {ty : CTy}
    {env : Env} {used : List String}
    (h : ∀ nm, nm ∉ used → env.lookup nm = none) :
    ∀ nm, nm ∉ name :: used → ((name, bid, ty) :: env).lookup nm = none := by
  intro nm hnm
  simp only [List.mem_cons, not_or] at hnm
  rw [lookup_cons_ne _ hnm.1]
  exact h nm hnm.2

private theorem env_none_cons_prepend {name : String} {bid : BlockId} {ty : CTy}
    {ins : List String} {env : Env} {used : List String}
    (h : ∀ nm, nm ∉ ins ++ used → env.lookup nm = none) :
    ∀ nm, nm ∉ (name :: ins) ++ used → ((name, bid, ty) :: env).lookup nm = none := by
  intro nm hnm
  simp only [List.cons_append, List.mem_cons, not_or] at hnm
  rw [lookup_cons_ne _ hnm.1]
  exact h nm hnm.2

private theorem not_mem_prepend_of_disj {ins xs used : List String} {x : String}
    (hx_not_ins : x ∉ ins) (hdisj : ∀ nm ∈ xs, nm ∉ used) (hx_in : x ∈ xs) :
    x ∉ ins ++ used := by
  simp only [List.mem_append, not_or]
  exact ⟨hx_not_ins, hdisj x hx_in⟩

private theorem env_none_initGlobs {globBase strBase : Nat → UInt64} {prog0 : Prog}
    {idx ns ns' : Nat} {env env' : Env} {m m' : Mem} {globs : List (Linkage × VarDecl)}
    {used : List String}
    (hg : initProg.initGlobs globBase strBase prog0 idx ns env m globs = some (env', m', ns'))
    (h : ∀ nm, nm ∉ used → env.lookup nm = none) :
    ∀ nm, nm ∉ globs.map (·.2.name) ++ used → env'.lookup nm = none := by
  intro nm hnm
  simp only [List.mem_append, List.mem_map, not_or, not_exists, not_and] at hnm
  apply initGlobs_preserves_none hg (h nm hnm.2)
  intro g hgmem hname
  exact hnm.1 g hgmem hname

/-! ### TU-Level Global Unpacking Helpers -/

private theorem initGlobs_inftrees_unpack {globBase strBase : Nat → UInt64} {prog0 : Prog}
    {idx ns ns' : Nat} {env env' : Env} {m m' : Mem} {rest : List (Linkage × VarDecl)}
    {used : List String}
    (hnone_all : ∀ nm, nm ∉ used → env.lookup nm = none)
    (hdisj : ∀ nm ∈ ["inflate_copyright", "lenfix", "distfix"], nm ∉ used)
    (hg : initProg.initGlobs globBase strBase prog0 idx ns env m (inftreesGlobalsList ++ rest) = some (env', m', ns')) :
    ∃ (env1 : Env) (m1 : Mem) (ns1 : Nat)
      (b_ic : BlockId) (blk_ic : Block)
      (b_lf : BlockId) (blk_lf : Block)
      (b_df : BlockId) (blk_df : Block),
      initProg.initGlobs globBase strBase prog0 (idx + 3) ns1 env1 m1 rest = some (env', m', ns') ∧
      (∀ nm, nm ∉ ["distfix", "lenfix", "inflate_copyright"] ++ used → env1.lookup nm = none) ∧
      (env1.lookup "inflate_copyright" = some (b_ic, .array (.const_ (.int .i8)) (some 49)) ∧
        b_ic < m1.nextBlock ∧ m1.blocks b_ic = some blk_ic ∧ blk_ic.perm = .ro ∧ blk_ic.kind = .global ∧
        blk_ic.size = 49 ∧ blk_ic.align = 1 ∧ (∀ i, ∃ u : UInt8, blk_ic.bytes i = .byte u) ∧
        m1.strlenAt b_ic 0 = some 48) ∧
      (env1.lookup "lenfix" = some (b_lf, codeConstTy.array (some 512)) ∧
        b_lf < m1.nextBlock ∧ m1.blocks b_lf = some blk_lf ∧ blk_lf.perm = .ro ∧ blk_lf.kind = .global ∧
        blk_lf.size = 2048 ∧ blk_lf.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_lf.bytes i = .byte u) ∧
        ∀ i < 512, ∃ (op bits val : Nat), let t := lenfixVals[i]!;
          op = t.1 ∧ bits = t.2.1 ∧ val = t.2.2 ∧
          Sem.readVal prog0.tags m1 b_lf (Int64.ofNat (4 * i)) (.int .u8) = some (.int .u8 (BitVec.ofNat 8 op)) ∧
          Sem.readVal prog0.tags m1 b_lf (Int64.ofNat (4 * i + 1)) (.int .u8) = some (.int .u8 (BitVec.ofNat 8 bits)) ∧
          Sem.readVal prog0.tags m1 b_lf (Int64.ofNat (4 * i + 2)) (.int .u16) = some (.int .u16 (BitVec.ofNat 16 val))) ∧
      (env1.lookup "distfix" = some (b_df, codeConstTy.array (some 32)) ∧
        b_df < m1.nextBlock ∧ m1.blocks b_df = some blk_df ∧ blk_df.perm = .ro ∧ blk_df.kind = .global ∧
        blk_df.size = 128 ∧ blk_df.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_df.bytes i = .byte u) ∧
        ∀ i < 32, ∃ (op bits val : Nat), let t := distfixVals[i]!;
          op = t.1 ∧ bits = t.2.1 ∧ val = t.2.2 ∧
          Sem.readVal prog0.tags m1 b_df (Int64.ofNat (4 * i)) (.int .u8) = some (.int .u8 (BitVec.ofNat 8 op)) ∧
          Sem.readVal prog0.tags m1 b_df (Int64.ofNat (4 * i + 1)) (.int .u8) = some (.int .u8 (BitVec.ofNat 8 bits)) ∧
          Sem.readVal prog0.tags m1 b_df (Int64.ofNat (4 * i + 2)) (.int .u16) = some (.int .u16 (BitVec.ofNat 16 val))) := by
  dsimp only [inftreesGlobalsList, List.cons_append, List.nil_append] at hg
  obtain ⟨b_ic, t_ic, ma, nsa, hal_ic, hg1⟩ :=
    initGlobs_step_fresh (hnone_all _ (hdisj _ (by decide))) hg
  obtain ⟨rfl, rfl, rfl, hp_ic, blk_ic, hblk_ic, hsz_ic, hal_ic', hk_ic, hperm_ic, hconcr_ic, hstr_ic, _⟩ :=
    allocVarInit_strLit_inv rfl rfl inflate_copyright_str_ok hal_ic
  have hn1 := env_none_cons_prepend (ins := []) (name := Zlib.Inftrees.inftreesTU_global_inflate_copyright.name)
    (bid := m.nextBlock) (ty := .array (.const_ (.int .i8)) (some (" inflate 1.4.0.1 Copyright 1995-2026 Mark Adler ".utf8ByteSize + 1))) hnone_all
  have hname_ic : Zlib.Inftrees.inftreesTU_global_inflate_copyright.name = "inflate_copyright" := rfl
  rw [hname_ic] at hn1 hg1
  have hn_lf : (("inflate_copyright", m.nextBlock, _) :: env).lookup Zlib.Tables.inffixedH_global_lenfix.name = none :=
    hn1 _ (not_mem_prepend_of_disj (x := "lenfix") (by decide) hdisj (by decide))
  obtain ⟨b_lf, t_lf, mb, nsb, hal_lf, hg2⟩ := initGlobs_step_fresh hn_lf hg1
  cases hlf_init : Zlib.Tables.inffixedH_global_lenfix.init? with
  | none =>
    exfalso
    have hok := lenfix_init_all_ok
    rw [hlf_init] at hok; cases hok
  | some iv_lf =>
    cases iv_lf with
    | expr _ | intSeq _ _ =>
      exfalso; have hok := lenfix_init_all_ok; rw [hlf_init] at hok; cases hok
    | list xs_lf =>
      have hok_lf := lenfix_init_all_ok
      rw [hlf_init] at hok_lf
      simp only [Bool.and_eq_true, beq_iff_eq] at hok_lf
      obtain ⟨rfl, rfl, rfl, hp_lf, blk_lf, hblk_lf, hsz_lf, hal_lf', hk_lf, hperm_lf, hconcr_lf, hread_lf⟩ :=
        allocVarInit_codeArray_inv rfl hok_lf.1 hlf_init hok_lf.2 hal_lf
      have hn2 := env_none_cons_prepend (name := Zlib.Tables.inffixedH_global_lenfix.name)
        (bid := ma.nextBlock) (ty := codeConstTy.array (some 512)) hn1
      have hname_lf : Zlib.Tables.inffixedH_global_lenfix.name = "lenfix" := rfl
      rw [hname_lf] at hn2 hg2
      have hn_df : (("lenfix", ma.nextBlock, _) :: ("inflate_copyright", m.nextBlock, _) :: env).lookup
          Zlib.Tables.inffixedH_global_distfix.name = none :=
        hn2 _ (not_mem_prepend_of_disj (x := "distfix") (by decide) hdisj (by decide))
      obtain ⟨b_df, t_df, mc, nsc, hal_df, hg3⟩ := initGlobs_step_fresh hn_df hg2
      cases hdf_init : Zlib.Tables.inffixedH_global_distfix.init? with
      | none =>
        exfalso; have hok := distfix_init_all_ok; rw [hdf_init] at hok; cases hok
      | some iv_df =>
        cases iv_df with
        | expr _ | intSeq _ _ =>
          exfalso; have hok := distfix_init_all_ok; rw [hdf_init] at hok; cases hok
        | list xs_df =>
          have hok_df := distfix_init_all_ok
          rw [hdf_init] at hok_df
          simp only [Bool.and_eq_true, beq_iff_eq] at hok_df
          obtain ⟨rfl, rfl, rfl, hp_df, blk_df, hblk_df, hsz_df, hal_df', hk_df, hperm_df, hconcr_df, hread_df⟩ :=
            allocVarInit_codeArray_inv rfl hok_df.1 hdf_init hok_df.2 hal_df
          have hn3 := env_none_cons_prepend (name := Zlib.Tables.inffixedH_global_distfix.name)
            (bid := mb.nextBlock) (ty := codeConstTy.array (some 32)) hn2
          have hname_df : Zlib.Tables.inffixedH_global_distfix.name = "distfix" := rfl
          rw [hname_df] at hn3 hg3
          have hlt_ic : m.nextBlock < ma.nextBlock := lt_nextBlock_of_some hblk_ic
          have hlt_lf : ma.nextBlock < mb.nextBlock := lt_nextBlock_of_some hblk_lf
          have hlt_df : mb.nextBlock < mc.nextBlock := lt_nextBlock_of_some hblk_df
          have hp_ic_mc : MemPreservedBelow ma.nextBlock ma mc := hp_lf.trans (hp_df.mono hp_lf.1)
          have hlt_ic_mc : m.nextBlock < mc.nextBlock := Nat.lt_of_lt_of_le hlt_ic hp_ic_mc.1
          have hlt_lf_mc : ma.nextBlock < mc.nextBlock := Nat.lt_of_lt_of_le hlt_lf hp_df.1
          have hlen_ic : " inflate 1.4.0.1 Copyright 1995-2026 Mark Adler ".utf8ByteSize = 48 := rfl
          have hidx3 : idx + 1 + 1 + 1 = idx + 3 := by omega
          rw [hidx3] at hg3
          refine ⟨_, mc, nsc, m.nextBlock, blk_ic, ma.nextBlock, blk_lf, mb.nextBlock, blk_df, hg3, ?_, ?_, ?_, ?_⟩
          · intro nm hnm; exact hn3 nm hnm
          · refine ⟨?_, hlt_ic_mc, by rw [hp_ic_mc.2 _ hlt_ic, hblk_ic], hperm_ic, hk_ic,
              by rw [hsz_ic, hlen_ic], hal_ic', hconcr_ic, by rw [hp_ic_mc.strlenAt hlt_ic, hstr_ic, hlen_ic]⟩
            rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_eq _, hlen_ic]
          · refine ⟨?_, hlt_lf_mc, by rw [hp_df.2 _ hlt_lf, hblk_lf], hperm_lf, hk_lf,
              by rw [hsz_lf]; rfl, hal_lf', hconcr_lf, fun i hi => ?_⟩
            · rw [lookup_cons_ne _ (by decide), lookup_cons_eq _]
            · have hfm_eq : xs_lf.filterMap parseCodeInit? = lenfixVals := by
                unfold lenfixVals; rw [hlf_init]
              have hi' : i < (xs_lf.filterMap parseCodeInit?).length := by
                rw [filterMap_all_isSome_length parseCodeInit? xs_lf hok_lf.2, hok_lf.1]; exact hi
              have hr := hread_lf i hi'
              dsimp only at hr ⊢
              rw [hp_df.readVal hlt_lf, hp_df.readVal hlt_lf, hp_df.readVal hlt_lf]
              have hget : (xs_lf.filterMap parseCodeInit?)[i] = lenfixVals[i]! := by
                have hlen_fm : i < lenfixVals.length := by rw [← hfm_eq]; exact hi'
                rw [getElem!_pos lenfixVals i hlen_fm]
                have := list_getElem_of_eq hfm_eq hi' hlen_fm
                exact this
              rw [hget] at hr
              exact ⟨_, _, _, rfl, rfl, rfl, hr⟩
          · refine ⟨?_, hlt_df, hblk_df, hperm_df, hk_df, by rw [hsz_df]; rfl, hal_df', hconcr_df, fun i hi => ?_⟩
            · rw [lookup_cons_eq _]
            · have hfm_eq : xs_df.filterMap parseCodeInit? = distfixVals := by
                unfold distfixVals; rw [hdf_init]
              have hi' : i < (xs_df.filterMap parseCodeInit?).length := by
                rw [filterMap_all_isSome_length parseCodeInit? xs_df hok_df.2, hok_df.1]; exact hi
              have hr := hread_df i hi'
              dsimp only at hr ⊢
              have hget : (xs_df.filterMap parseCodeInit?)[i] = distfixVals[i]! := by
                have hlen_fm : i < distfixVals.length := by rw [← hfm_eq]; exact hi'
                rw [getElem!_pos distfixVals i hlen_fm]
                exact list_getElem_of_eq hfm_eq hi' hlen_fm
              rw [hget] at hr
              exact ⟨_, _, _, rfl, rfl, rfl, hr⟩

/-! ### Complete `InitLibzAllProps` Structure and Verification -/

private theorem initGlobs_trees_unpack {globBase strBase : Nat → UInt64} {prog0 : Prog}
    {idx ns ns' : Nat} {env env' : Env} {m m' : Mem} {rest : List (Linkage × VarDecl)}
    {used : List String}
    (htags : prog0.tags = (progOfTUs Zlib.allFiles).tags)
    (hnone_all : ∀ nm, nm ∉ used → env.lookup nm = none)
    (hdisj : ∀ nm ∈ ["extra_lbits", "extra_dbits", "extra_blbits", "bl_order",
      "static_ltree", "static_dtree", "_dist_code", "_length_code",
      "base_length", "base_dist", "static_l_desc", "static_d_desc", "static_bl_desc"], nm ∉ used)
    (hg : initProg.initGlobs globBase strBase prog0 idx ns env m (treesGlobalsList ++ rest) = some (env', m', ns')) :
    ∃ (env1 : Env) (m1 : Mem) (ns1 idx1 : Nat)
      (b_el : BlockId) (blk_el : Block)
      (b_ed : BlockId) (blk_ed : Block)
      (b_ebl : BlockId) (blk_ebl : Block)
      (b_bo : BlockId) (blk_bo : Block)
      (b_lt : BlockId) (blk_lt : Block)
      (b_dt : BlockId) (blk_dt : Block)
      (b_dc : BlockId) (blk_dc : Block)
      (b_lc : BlockId) (blk_lc : Block)
      (b_bl : BlockId) (blk_bl : Block)
      (b_bd : BlockId) (blk_bd : Block)
      (b_sld : BlockId) (blk_sld : Block)
      (b_sdd : BlockId) (blk_sdd : Block)
      (b_sbd : BlockId) (blk_sbd : Block),
      initProg.initGlobs globBase strBase prog0 idx1 ns1 env1 m1 rest = some (env', m', ns') ∧
      (∀ nm, nm ∉ treesGlobalsList.map (·.2.name) ++ used → env1.lookup nm = none) ∧
      (env1.lookup "extra_lbits" = some (b_el, (CTy.const_ (.int .i32)).array (some 29)) ∧
        b_el < m1.nextBlock ∧ m1.blocks b_el = some blk_el ∧ blk_el.perm = .ro ∧ blk_el.kind = .global ∧
        blk_el.size = 116 ∧ blk_el.align = 4 ∧ (∀ i, ∃ u : UInt8, blk_el.bytes i = .byte u) ∧
        ∀ i < 29, ∃ bv : BitVec 32,
          Sem.readVal prog0.tags m1 b_el (Int64.ofNat (4 * i)) (.int .i32) = some (.int .i32 bv) ∧
          bv = BitVec.ofInt 32 Zlib.Trees.treesTU_vals_extra_lbits[i]! ∧ 0 ≤ bv.toInt ∧ bv.toInt ≤ 5) ∧
      (env1.lookup "extra_dbits" = some (b_ed, (CTy.const_ (.int .i32)).array (some 30)) ∧
        b_ed < m1.nextBlock ∧ m1.blocks b_ed = some blk_ed ∧ blk_ed.perm = .ro ∧ blk_ed.kind = .global ∧
        blk_ed.size = 120 ∧ blk_ed.align = 4 ∧ (∀ i, ∃ u : UInt8, blk_ed.bytes i = .byte u) ∧
        ∀ i < 30, ∃ bv : BitVec 32,
          Sem.readVal prog0.tags m1 b_ed (Int64.ofNat (4 * i)) (.int .i32) = some (.int .i32 bv) ∧
          bv = BitVec.ofInt 32 Zlib.Trees.treesTU_vals_extra_dbits[i]! ∧ 0 ≤ bv.toInt ∧ bv.toInt ≤ 13) ∧
      (env1.lookup "extra_blbits" = some (b_ebl, (CTy.const_ (.int .i32)).array (some 19)) ∧
        b_ebl < m1.nextBlock ∧ m1.blocks b_ebl = some blk_ebl ∧ blk_ebl.perm = .ro ∧ blk_ebl.kind = .global ∧
        blk_ebl.size = 76 ∧ blk_ebl.align = 4 ∧ (∀ i, ∃ u : UInt8, blk_ebl.bytes i = .byte u) ∧
        ∀ i < 19, ∃ bv : BitVec 32,
          Sem.readVal prog0.tags m1 b_ebl (Int64.ofNat (4 * i)) (.int .i32) = some (.int .i32 bv) ∧
          bv = BitVec.ofInt 32 Zlib.Trees.treesTU_vals_extra_blbits[i]! ∧ 0 ≤ bv.toInt ∧ bv.toInt ≤ 7) ∧
      (env1.lookup "bl_order" = some (b_bo, (CTy.const_ (.typedef "uch" (.int .u8))).array (some 19)) ∧
        b_bo < m1.nextBlock ∧ m1.blocks b_bo = some blk_bo ∧ blk_bo.perm = .ro ∧ blk_bo.kind = .global ∧
        blk_bo.size = 19 ∧ blk_bo.align = 1 ∧ (∀ i, ∃ u : UInt8, blk_bo.bytes i = .byte u) ∧
        ∀ i < 19, ∃ bv : BitVec 8,
          Sem.readVal prog0.tags m1 b_bo (Int64.ofNat i) (.int .u8) = some (.int .u8 bv) ∧
          bv = BitVec.ofInt 8 Zlib.Trees.treesTU_vals_bl_order[i]! ∧ bv.toNat < 19) ∧
      (env1.lookup "static_ltree" = some (b_lt, ctDataConstTy.array (some 288)) ∧
        b_lt < m1.nextBlock ∧ m1.blocks b_lt = some blk_lt ∧ blk_lt.perm = .ro ∧ blk_lt.kind = .global ∧
        blk_lt.size = 1152 ∧ blk_lt.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_lt.bytes i = .byte u) ∧
        ∀ i < 288, ∃ fc dl : BitVec 16,
          Sem.readVal prog0.tags m1 b_lt (Int64.ofNat (4 * i)) (.int .u16) = some (.int .u16 fc) ∧
          Sem.readVal prog0.tags m1 b_lt (Int64.ofNat (4 * i + 2)) (.int .u16) = some (.int .u16 dl) ∧
          fc = BitVec.ofNat 16 staticLtreeVals[i]!.1 ∧ dl = BitVec.ofNat 16 staticLtreeVals[i]!.2 ∧
          7 ≤ dl.toNat ∧ dl.toNat ≤ 9) ∧
      (env1.lookup "static_dtree" = some (b_dt, ctDataConstTy.array (some 30)) ∧
        b_dt < m1.nextBlock ∧ m1.blocks b_dt = some blk_dt ∧ blk_dt.perm = .ro ∧ blk_dt.kind = .global ∧
        blk_dt.size = 120 ∧ blk_dt.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_dt.bytes i = .byte u) ∧
        ∀ i < 30, ∃ fc dl : BitVec 16,
          Sem.readVal prog0.tags m1 b_dt (Int64.ofNat (4 * i)) (.int .u16) = some (.int .u16 fc) ∧
          Sem.readVal prog0.tags m1 b_dt (Int64.ofNat (4 * i + 2)) (.int .u16) = some (.int .u16 dl) ∧
          fc = BitVec.ofNat 16 staticDtreeVals[i]!.1 ∧ dl = BitVec.ofNat 16 staticDtreeVals[i]!.2 ∧
          dl.toNat = 5) ∧
      (env1.lookup "_dist_code" = some (b_dc, (CTy.const_ (.typedef "uch" (.int .u8))).array (some 512)) ∧
        b_dc < m1.nextBlock ∧ m1.blocks b_dc = some blk_dc ∧ blk_dc.perm = .ro ∧ blk_dc.kind = .global ∧
        blk_dc.size = 512 ∧ blk_dc.align = 1 ∧ (∀ i, ∃ u : UInt8, blk_dc.bytes i = .byte u) ∧
        ∀ i < 512, ∃ bv : BitVec 8,
          Sem.readVal prog0.tags m1 b_dc (Int64.ofNat i) (.int .u8) = some (.int .u8 bv) ∧
          bv = BitVec.ofInt 8 Zlib.Tables.treesH_vals__dist_code[i]! ∧ bv.toNat < 30) ∧
      (env1.lookup "_length_code" = some (b_lc, (CTy.const_ (.typedef "uch" (.int .u8))).array (some 256)) ∧
        b_lc < m1.nextBlock ∧ m1.blocks b_lc = some blk_lc ∧ blk_lc.perm = .ro ∧ blk_lc.kind = .global ∧
        blk_lc.size = 256 ∧ blk_lc.align = 1 ∧ (∀ i, ∃ u : UInt8, blk_lc.bytes i = .byte u) ∧
        ∀ i < 256, ∃ bv : BitVec 8,
          Sem.readVal prog0.tags m1 b_lc (Int64.ofNat i) (.int .u8) = some (.int .u8 bv) ∧
          bv = BitVec.ofInt 8 Zlib.Tables.treesH_vals__length_code[i]! ∧ bv.toNat < 29) ∧
      (env1.lookup "base_length" = some (b_bl, (CTy.const_ (.int .i32)).array (some 29)) ∧
        b_bl < m1.nextBlock ∧ m1.blocks b_bl = some blk_bl ∧ blk_bl.perm = .ro ∧ blk_bl.kind = .global ∧
        blk_bl.size = 116 ∧ blk_bl.align = 4 ∧ (∀ i, ∃ u : UInt8, blk_bl.bytes i = .byte u) ∧
        ∀ i < 29, ∃ bv : BitVec 32,
          Sem.readVal prog0.tags m1 b_bl (Int64.ofNat (4 * i)) (.int .i32) = some (.int .i32 bv) ∧
          bv = BitVec.ofInt 32 Zlib.Tables.treesH_vals_base_length[i]! ∧ 0 ≤ bv.toInt ∧ bv.toInt ≤ 224) ∧
      (env1.lookup "base_dist" = some (b_bd, (CTy.const_ (.int .i32)).array (some 30)) ∧
        b_bd < m1.nextBlock ∧ m1.blocks b_bd = some blk_bd ∧ blk_bd.perm = .ro ∧ blk_bd.kind = .global ∧
        blk_bd.size = 120 ∧ blk_bd.align = 4 ∧ (∀ i, ∃ u : UInt8, blk_bd.bytes i = .byte u) ∧
        ∀ i < 30, ∃ bv : BitVec 32,
          Sem.readVal prog0.tags m1 b_bd (Int64.ofNat (4 * i)) (.int .i32) = some (.int .i32 bv) ∧
          bv = BitVec.ofInt 32 Zlib.Tables.treesH_vals_base_dist[i]! ∧ 0 ≤ bv.toInt ∧ bv.toInt ≤ 24576) ∧
      (env1.lookup "static_l_desc" = some (b_sld, staticTreeDescConstTy) ∧
        b_sld < m1.nextBlock ∧ m1.blocks b_sld = some blk_sld ∧ blk_sld.perm = .ro ∧ blk_sld.kind = .global ∧
        blk_sld.size = 32 ∧ blk_sld.align = 8 ∧
        Sem.readVal prog0.tags m1 b_sld 0 (.ptr ctDataConstTy) = some (.ptr b_lt 0) ∧
        Sem.readVal prog0.tags m1 b_sld 8 (.ptr (.const_ (.typedef "intf" (.int .i32)))) = some (.ptr b_el 0) ∧
        Sem.readVal prog0.tags m1 b_sld 16 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 257)) ∧
        Sem.readVal prog0.tags m1 b_sld 20 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 286)) ∧
        Sem.readVal prog0.tags m1 b_sld 24 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 15))) ∧
      (env1.lookup "static_d_desc" = some (b_sdd, staticTreeDescConstTy) ∧
        b_sdd < m1.nextBlock ∧ m1.blocks b_sdd = some blk_sdd ∧ blk_sdd.perm = .ro ∧ blk_sdd.kind = .global ∧
        blk_sdd.size = 32 ∧ blk_sdd.align = 8 ∧
        Sem.readVal prog0.tags m1 b_sdd 0 (.ptr ctDataConstTy) = some (.ptr b_dt 0) ∧
        Sem.readVal prog0.tags m1 b_sdd 8 (.ptr (.const_ (.typedef "intf" (.int .i32)))) = some (.ptr b_ed 0) ∧
        Sem.readVal prog0.tags m1 b_sdd 16 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 0)) ∧
        Sem.readVal prog0.tags m1 b_sdd 20 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 30)) ∧
        Sem.readVal prog0.tags m1 b_sdd 24 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 15))) ∧
      (env1.lookup "static_bl_desc" = some (b_sbd, staticTreeDescConstTy) ∧
        b_sbd < m1.nextBlock ∧ m1.blocks b_sbd = some blk_sbd ∧ blk_sbd.perm = .ro ∧ blk_sbd.kind = .global ∧
        blk_sbd.size = 32 ∧ blk_sbd.align = 8 ∧
        Sem.readVal prog0.tags m1 b_sbd 0 (.ptr ctDataConstTy) = some .null ∧
        Sem.readVal prog0.tags m1 b_sbd 8 (.ptr (.const_ (.typedef "intf" (.int .i32)))) = some (.ptr b_ebl 0) ∧
        Sem.readVal prog0.tags m1 b_sbd 16 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 0)) ∧
        Sem.readVal prog0.tags m1 b_sbd 20 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 19)) ∧
        Sem.readVal prog0.tags m1 b_sbd 24 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 7))) := by
  obtain ⟨env1, m1, ns1, idx1, hg_tr, hg_rest⟩ := initGlobs_append hg
  have hnone1 := env_none_initGlobs hg_tr hnone_all
  dsimp only [treesGlobalsList] at hg_tr
  -- 1. extra_lbits
  obtain ⟨b_el, t_el, m_el, ns_el, hal_el, hg_t1⟩ :=
    initGlobs_step_fresh (hnone_all "extra_lbits" (hdisj "extra_lbits" (by decide))) hg_tr
  obtain ⟨rfl, rfl, rfl, _, blk_el, hblk_el, hsz_el, hal_el', hk_el, hperm_el, hconcr_el, hread_el⟩ :=
    allocVarInit_intSeq_array_inv (k := .i32) (n := 29) rfl rfl rfl rfl (by simp) (by simp) (Nat.dvd_refl 4)
      (by decide) rfl hal_el
  have hnm1 : Zlib.Trees.treesTU_global_extra_lbits.name = "extra_lbits" := rfl
  rw [hnm1] at hg_t1
  obtain ⟨hp_el, henv_el⟩ := initGlobs_preserves hg_t1
  have hlt_el : m.nextBlock < m_el.nextBlock := lt_nextBlock_of_some hblk_el
  have hn1 := env_none_cons_prepend (ins := []) (name := "extra_lbits")
    (bid := m.nextBlock) (ty := (CTy.const_ (.int .i32)).array (some 29)) hnone_all
  -- 2. extra_dbits
  obtain ⟨b_ed, t_ed, m_ed, ns_ed, hal_ed, hg_t2⟩ := initGlobs_step_fresh
    (hn1 "extra_dbits" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t1
  obtain ⟨rfl, rfl, rfl, _, blk_ed, hblk_ed, hsz_ed, hal_ed', hk_ed, hperm_ed, hconcr_ed, hread_ed⟩ :=
    allocVarInit_intSeq_array_inv (k := .i32) (n := 30) rfl rfl rfl rfl (by simp) (by simp) (Nat.dvd_refl 4)
      (by decide) rfl hal_ed
  have hnm2 : Zlib.Trees.treesTU_global_extra_dbits.name = "extra_dbits" := rfl
  rw [hnm2] at hg_t2
  obtain ⟨hp_ed, henv_ed⟩ := initGlobs_preserves hg_t2
  have hlt_ed : m_el.nextBlock < m_ed.nextBlock := lt_nextBlock_of_some hblk_ed
  have hn2 := env_none_cons_prepend (name := "extra_dbits")
    (bid := m_el.nextBlock) (ty := (CTy.const_ (.int .i32)).array (some 30)) hn1
  -- 3. extra_blbits
  obtain ⟨b_ebl, t_ebl, m_ebl, ns_ebl, hal_ebl, hg_t3⟩ := initGlobs_step_fresh
    (hn2 "extra_blbits" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t2
  obtain ⟨rfl, rfl, rfl, _, blk_ebl, hblk_ebl, hsz_ebl, hal_ebl', hk_ebl, hperm_ebl, hconcr_ebl, hread_ebl⟩ :=
    allocVarInit_intSeq_array_inv (k := .i32) (n := 19) rfl rfl rfl rfl (by simp) (by simp) (Nat.dvd_refl 4)
      (by decide) rfl hal_ebl
  have hnm3 : Zlib.Trees.treesTU_global_extra_blbits.name = "extra_blbits" := rfl
  rw [hnm3] at hg_t3
  obtain ⟨hp_ebl, henv_ebl⟩ := initGlobs_preserves hg_t3
  have hlt_ebl : m_ed.nextBlock < m_ebl.nextBlock := lt_nextBlock_of_some hblk_ebl
  have hn3 := env_none_cons_prepend (name := "extra_blbits")
    (bid := m_ed.nextBlock) (ty := (CTy.const_ (.int .i32)).array (some 19)) hn2
  -- 4. bl_order
  obtain ⟨b_bo, t_bo, m_bo, ns_bo, hal_bo, hg_t4⟩ := initGlobs_step_fresh
    (hn3 "bl_order" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t3
  obtain ⟨rfl, rfl, rfl, _, blk_bo, hblk_bo, hsz_bo, hal_bo', hk_bo, hperm_bo, hconcr_bo, hread_bo⟩ :=
    allocVarInit_intSeq_array_inv (k := .u8) (n := 19) rfl rfl rfl rfl (by simp) (by simp) (Nat.dvd_refl 1)
      (by decide) rfl hal_bo
  have hnm4 : Zlib.Trees.treesTU_global_bl_order.name = "bl_order" := rfl
  rw [hnm4] at hg_t4
  obtain ⟨hp_bo, henv_bo⟩ := initGlobs_preserves hg_t4
  have hlt_bo : m_ebl.nextBlock < m_bo.nextBlock := lt_nextBlock_of_some hblk_bo
  have hn4 := env_none_cons_prepend (name := "bl_order")
    (bid := m_ebl.nextBlock) (ty := (CTy.const_ (.typedef "uch" (.int .u8))).array (some 19)) hn3
  -- 5. static_ltree
  obtain ⟨b_lt, t_lt, m_lt, ns_lt, hal_lt, hg_t5⟩ := initGlobs_step_fresh
    (hn4 "static_ltree" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t4
  cases hlt_init : Zlib.Tables.treesH_global_static_ltree.init? with
  | none => exfalso; have hok := staticLtree_init_all_ok; rw [hlt_init] at hok; cases hok
  | some iv_lt =>
    cases iv_lt with
    | expr _ | intSeq _ _ => exfalso; have hok := staticLtree_init_all_ok; rw [hlt_init] at hok; cases hok
    | list xs_lt =>
      have hok_lt := staticLtree_init_all_ok; rw [hlt_init] at hok_lt
      simp only [Bool.and_eq_true, beq_iff_eq] at hok_lt
      obtain ⟨rfl, rfl, rfl, _, blk_lt, hblk_lt, hsz_lt, hal_lt', hk_lt, hperm_lt, hconcr_lt, hread_lt⟩ :=
        allocVarInit_ctDataArray_inv htags rfl hok_lt.1 hlt_init hok_lt.2 hal_lt
      have hnm5 : Zlib.Tables.treesH_global_static_ltree.name = "static_ltree" := rfl
      rw [hnm5] at hg_t5
      obtain ⟨hp_lt, henv_lt⟩ := initGlobs_preserves hg_t5
      have hlt_lt : m_bo.nextBlock < m_lt.nextBlock := lt_nextBlock_of_some hblk_lt
      have hn5 := env_none_cons_prepend (name := "static_ltree")
        (bid := m_bo.nextBlock) (ty := ctDataConstTy.array (some 288)) hn4
      -- 6. static_dtree
      obtain ⟨b_dt, t_dt, m_dt, ns_dt, hal_dt, hg_t6⟩ := initGlobs_step_fresh
        (hn5 "static_dtree" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t5
      cases hdt_init : Zlib.Tables.treesH_global_static_dtree.init? with
      | none => exfalso; have hok := staticDtree_init_all_ok; rw [hdt_init] at hok; cases hok
      | some iv_dt =>
        cases iv_dt with
        | expr _ | intSeq _ _ => exfalso; have hok := staticDtree_init_all_ok; rw [hdt_init] at hok; cases hok
        | list xs_dt =>
          have hok_dt := staticDtree_init_all_ok; rw [hdt_init] at hok_dt
          simp only [Bool.and_eq_true, beq_iff_eq] at hok_dt
          obtain ⟨rfl, rfl, rfl, _, blk_dt, hblk_dt, hsz_dt, hal_dt', hk_dt, hperm_dt, hconcr_dt, hread_dt⟩ :=
            allocVarInit_ctDataArray_inv htags rfl hok_dt.1 hdt_init hok_dt.2 hal_dt
          have hnm6 : Zlib.Tables.treesH_global_static_dtree.name = "static_dtree" := rfl
          rw [hnm6] at hg_t6
          obtain ⟨hp_dt, henv_dt⟩ := initGlobs_preserves hg_t6
          have hlt_dt : m_lt.nextBlock < m_dt.nextBlock := lt_nextBlock_of_some hblk_dt
          have hn6 := env_none_cons_prepend (name := "static_dtree")
            (bid := m_lt.nextBlock) (ty := ctDataConstTy.array (some 30)) hn5
          -- 7. _dist_code
          obtain ⟨b_dc, t_dc, m_dc, ns_dc, hal_dc, hg_t7⟩ := initGlobs_step_fresh
            (hn6 "_dist_code" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t6
          obtain ⟨rfl, rfl, rfl, _, blk_dc, hblk_dc, hsz_dc, hal_dc', hk_dc, hperm_dc, hconcr_dc, hread_dc⟩ :=
            allocVarInit_intSeq_array_inv (k := .u8) (n := 512) rfl rfl rfl rfl (by simp) (by simp) (Nat.dvd_refl 1)
              (beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp dist_code_bounds_all).1) rfl hal_dc
          have hnm7 : Zlib.Tables.treesH_global__dist_code.name = "_dist_code" := rfl
          rw [hnm7] at hg_t7
          obtain ⟨hp_dc, henv_dc⟩ := initGlobs_preserves hg_t7
          have hlt_dc : m_dt.nextBlock < m_dc.nextBlock := lt_nextBlock_of_some hblk_dc
          have hn7 := env_none_cons_prepend (name := "_dist_code")
            (bid := m_dt.nextBlock) (ty := (CTy.const_ (.typedef "uch" (.int .u8))).array (some 512)) hn6
          -- 8. _length_code
          obtain ⟨b_lc, t_lc, m_lc, ns_lc, hal_lc, hg_t8⟩ := initGlobs_step_fresh
            (hn7 "_length_code" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t7
          obtain ⟨rfl, rfl, rfl, _, blk_lc, hblk_lc, hsz_lc, hal_lc', hk_lc, hperm_lc, hconcr_lc, hread_lc⟩ :=
            allocVarInit_intSeq_array_inv (k := .u8) (n := 256) rfl rfl rfl rfl (by simp) (by simp) (Nat.dvd_refl 1)
              (beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp length_code_bounds_all).1) rfl hal_lc
          have hnm8 : Zlib.Tables.treesH_global__length_code.name = "_length_code" := rfl
          rw [hnm8] at hg_t8
          obtain ⟨hp_lc, henv_lc⟩ := initGlobs_preserves hg_t8
          have hlt_lc : m_dc.nextBlock < m_lc.nextBlock := lt_nextBlock_of_some hblk_lc
          have hn8 := env_none_cons_prepend (name := "_length_code")
            (bid := m_dc.nextBlock) (ty := (CTy.const_ (.typedef "uch" (.int .u8))).array (some 256)) hn7
          -- 9. base_length
          obtain ⟨b_bl, t_bl, m_bl, ns_bl, hal_bl, hg_t9⟩ := initGlobs_step_fresh
            (hn8 "base_length" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t8
          obtain ⟨rfl, rfl, rfl, _, blk_bl, hblk_bl, hsz_bl, hal_bl', hk_bl, hperm_bl, hconcr_bl, hread_bl⟩ :=
            allocVarInit_intSeq_array_inv (k := .i32) (n := 29) rfl rfl rfl rfl (by simp) (by simp) (Nat.dvd_refl 4)
              (by decide) rfl hal_bl
          have hnm9 : Zlib.Tables.treesH_global_base_length.name = "base_length" := rfl
          rw [hnm9] at hg_t9
          obtain ⟨hp_bl, henv_bl⟩ := initGlobs_preserves hg_t9
          have hlt_bl : m_lc.nextBlock < m_bl.nextBlock := lt_nextBlock_of_some hblk_bl
          have hn9 := env_none_cons_prepend (name := "base_length")
            (bid := m_lc.nextBlock) (ty := (CTy.const_ (.int .i32)).array (some 29)) hn8
          -- 10. base_dist
          obtain ⟨b_bd, t_bd, m_bd, ns_bd, hal_bd, hg_t10⟩ := initGlobs_step_fresh
            (hn9 "base_dist" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t9
          obtain ⟨rfl, rfl, rfl, _, blk_bd, hblk_bd, hsz_bd, hal_bd', hk_bd, hperm_bd, hconcr_bd, hread_bd⟩ :=
            allocVarInit_intSeq_array_inv (k := .i32) (n := 30) rfl rfl rfl rfl (by simp) (by simp) (Nat.dvd_refl 4)
              (by decide) rfl hal_bd
          have hnm10 : Zlib.Tables.treesH_global_base_dist.name = "base_dist" := rfl
          rw [hnm10] at hg_t10
          obtain ⟨hp_bd, henv_bd⟩ := initGlobs_preserves hg_t10
          have hlt_bd : m_bl.nextBlock < m_bd.nextBlock := lt_nextBlock_of_some hblk_bd
          have hn10 := env_none_cons_prepend (name := "base_dist")
            (bid := m_bl.nextBlock) (ty := (CTy.const_ (.int .i32)).array (some 30)) hn9
          -- 11. static_l_desc
          obtain ⟨b_sld, t_sld, m_sld, ns_sld, hal_sld, hg_t11⟩ := initGlobs_step_fresh
            (hn10 "static_l_desc" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t10
          have hlim0 : 0 < ptrDiffLimit := by rw [ptrDiffLimit_val]; decide
          obtain ⟨rfl, rfl, rfl, _, blk_sld, hblk_sld, hsz_sld, hal_sld', hk_sld, hperm_sld, hbytes0_sld, hread1_sld, hread2_sld, hread3_sld, hread4_sld⟩ :=
            allocVarInit_staticTreeDesc_inv htags rfl rfl hal_sld (encodePtr_length m_bo.nextBlock 0)
              (fun _ => evalConstExpr_var_array (by
                rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
                  lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_eq _]))
              (fun hb_step hw_step => by
                obtain ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7, _, h8, h9⟩ :=
                  writeVal_ptr_step_mem (off := 0) (pb := m_bo.nextBlock) (poff := 0) rfl rfl hb_step hlim0 hw_step
                exact ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7,
                  by simpa only [Nat.zero_add] using h8, by simpa only [Nat.zero_add] using h9⟩)
              rfl (by
                rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
                  lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
                  lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_eq _])
              (fun mA => evalConstExpr_256_add_1 prog0 _ mA strBase _) (by decide)
              (fun mA => evalConstExpr_257_add_29 prog0 _ mA strBase _) (by decide)
              (fun _ => rfl) (by decide) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
          have hnm11 : Zlib.Trees.treesTU_global_static_l_desc.name = "static_l_desc" := rfl
          rw [hnm11] at hg_t11
          obtain ⟨hp_sld, henv_sld⟩ := initGlobs_preserves hg_t11
          have hlt_sld : m_bd.nextBlock < m_sld.nextBlock := lt_nextBlock_of_some hblk_sld
          have hn11 := env_none_cons_prepend (name := "static_l_desc")
            (bid := m_bd.nextBlock) (ty := staticTreeDescConstTy) hn10
          -- 12. static_d_desc
          obtain ⟨b_sdd, t_sdd, m_sdd, ns_sdd, hal_sdd, hg_t12⟩ := initGlobs_step_fresh
            (hn11 "static_d_desc" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t11
          obtain ⟨rfl, rfl, rfl, _, blk_sdd, hblk_sdd, hsz_sdd, hal_sdd', hk_sdd, hperm_sdd, hbytes0_sdd, hread1_sdd, hread2_sdd, hread3_sdd, hread4_sdd⟩ :=
            allocVarInit_staticTreeDesc_inv htags rfl rfl hal_sdd (encodePtr_length m_lt.nextBlock 0)
              (fun _ => evalConstExpr_var_array (by
                rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
                  lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_eq _]))
              (fun hb_step hw_step => by
                obtain ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7, _, h8, h9⟩ :=
                  writeVal_ptr_step_mem (off := 0) (pb := m_lt.nextBlock) (poff := 0) rfl rfl hb_step hlim0 hw_step
                exact ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7,
                  by simpa only [Nat.zero_add] using h8, by simpa only [Nat.zero_add] using h9⟩)
              rfl (by
                rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
                  lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
                  lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_eq _])
              (fun _ => rfl) (by decide) (fun _ => rfl) (by decide)
              (fun _ => rfl) (by decide) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
          have hnm12 : Zlib.Trees.treesTU_global_static_d_desc.name = "static_d_desc" := rfl
          rw [hnm12] at hg_t12
          obtain ⟨hp_sdd, henv_sdd⟩ := initGlobs_preserves hg_t12
          have hlt_sdd : m_sld.nextBlock < m_sdd.nextBlock := lt_nextBlock_of_some hblk_sdd
          have hn12 := env_none_cons_prepend (name := "static_d_desc")
            (bid := m_sld.nextBlock) (ty := staticTreeDescConstTy) hn11
          -- 13. static_bl_desc
          obtain ⟨b_sbd, t_sbd, m_sbd, ns_sbd, hal_sbd, hg_t13⟩ := initGlobs_step_fresh
            (hn12 "static_bl_desc" (not_mem_prepend_of_disj (by decide) hdisj (by decide))) hg_t12
          obtain ⟨rfl, rfl, rfl, _, blk_sbd, hblk_sbd, hsz_sbd, hal_sbd', hk_sbd, hperm_sbd, hbytes0_sbd, hread1_sbd, hread2_sbd, hread3_sbd, hread4_sbd⟩ :=
            allocVarInit_staticTreeDesc_inv htags rfl rfl hal_sbd encodeNull_length
              (fun _ => evalConstExpr_cast_null_ptr rfl)
              (fun hb_step hw_step => by
                obtain ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7, _, h8, h9⟩ :=
                  writeVal_null_step_mem (off := 0) rfl rfl hb_step hlim0 hw_step
                exact ⟨h1, h2, blk', hb', h3, h4, h5, h6, h7,
                  by simpa only [Nat.zero_add] using h8, by simpa only [Nat.zero_add] using h9⟩)
              rfl (by
                rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
                  lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
                  lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
                  lookup_cons_eq _])
              (fun _ => rfl) (by decide) (fun _ => rfl) (by decide)
              (fun _ => rfl) (by decide) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
          have hnm13 : Zlib.Trees.treesTU_global_static_bl_desc.name = "static_bl_desc" := rfl
          rw [hnm13] at hg_t13
          unfold initProg.initGlobs at hg_t13
          simp only [Option.some.injEq, Prod.mk.injEq] at hg_t13
          rcases hg_t13 with ⟨henv_fin, hm_fin, _⟩
          rw [hm_fin] at hblk_sbd hread1_sbd hread2_sbd hread3_sbd hread4_sbd
          have hlt_sbd : m_sdd.nextBlock < m1.nextBlock := lt_nextBlock_of_some hblk_sbd
          have hblk1_sld : m1.blocks m_bd.nextBlock = some blk_sld := by rw [hp_sld.2 _ hlt_sld, hblk_sld]
          have hblk1_sdd : m1.blocks m_sld.nextBlock = some blk_sdd := by rw [hp_sdd.2 _ hlt_sdd, hblk_sdd]
          have hblk1_sbd : m1.blocks m_sdd.nextBlock = some blk_sbd := hblk_sbd
          refine ⟨_, m1, ns1, idx1, m.nextBlock, blk_el, m_el.nextBlock, blk_ed, m_ed.nextBlock, blk_ebl,
            m_ebl.nextBlock, blk_bo, m_bo.nextBlock, blk_lt, m_lt.nextBlock, blk_dt,
            m_dt.nextBlock, blk_dc, m_dc.nextBlock, blk_lc, m_lc.nextBlock, blk_bl,
            m_bl.nextBlock, blk_bd, m_bd.nextBlock, blk_sld, m_sld.nextBlock, blk_sdd,
            m_sdd.nextBlock, blk_sbd, hg_rest, hnone1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · refine ⟨henv_el _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_el hp_el.1,
              by rw [hp_el.2 _ hlt_el, hblk_el], hperm_el, hk_el, by rw [hsz_el]; rfl, by rw [hal_el']; rfl,
              hconcr_el, fun i hi => ?_⟩
            have hb_el0 := array_all_at extra_lbits_bounds_all hi
            have hb_el := of_decide_eq_true hb_el0
            refine ⟨BitVec.ofInt 32 Zlib.Trees.treesTU_vals_extra_lbits[i]!, ?_, rfl, ?_⟩
            · rw [hp_el.readVal hlt_el]; exact hread_el i hi
            · rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]; exact hb_el
          · refine ⟨henv_ed _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_ed hp_ed.1,
              by rw [hp_ed.2 _ hlt_ed, hblk_ed], hperm_ed, hk_ed, by rw [hsz_ed]; rfl, by rw [hal_ed']; rfl,
              hconcr_ed, fun i hi => ?_⟩
            have hb_ed0 := array_all_at extra_dbits_bounds_all hi
            have hb_ed := of_decide_eq_true hb_ed0
            refine ⟨BitVec.ofInt 32 Zlib.Trees.treesTU_vals_extra_dbits[i]!, ?_, rfl, ?_⟩
            · rw [hp_ed.readVal hlt_ed]; exact hread_ed i hi
            · rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]; exact hb_ed
          · refine ⟨henv_ebl _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_ebl hp_ebl.1,
              by rw [hp_ebl.2 _ hlt_ebl, hblk_ebl], hperm_ebl, hk_ebl, by rw [hsz_ebl]; rfl, by rw [hal_ebl']; rfl,
              hconcr_ebl, fun i hi => ?_⟩
            have hb_ebl0 := array_all_at extra_blbits_bounds_all hi
            have hb_ebl := of_decide_eq_true hb_ebl0
            refine ⟨BitVec.ofInt 32 Zlib.Trees.treesTU_vals_extra_blbits[i]!, ?_, rfl, ?_⟩
            · rw [hp_ebl.readVal hlt_ebl]; exact hread_ebl i hi
            · rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]; exact hb_ebl
          · refine ⟨henv_bo _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_bo hp_bo.1,
              by rw [hp_bo.2 _ hlt_bo, hblk_bo], hperm_bo, hk_bo, by rw [hsz_bo]; rfl, by rw [hal_bo']; rfl,
              hconcr_bo, fun i hi => ?_⟩
            have hb_bo0 := array_all_at bl_order_bounds_all hi
            have hb_bo := of_decide_eq_true hb_bo0
            refine ⟨BitVec.ofInt 8 Zlib.Trees.treesTU_vals_bl_order[i]!, ?_, rfl, ?_⟩
            · rw [hp_bo.readVal hlt_bo]
              have hr := hread_bo i hi
              rw [show IntKind.u8.bytes = 1 from rfl, Nat.one_mul] at hr
              exact hr
            · rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]; omega
          · refine ⟨henv_lt _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_lt hp_lt.1,
              by rw [hp_lt.2 _ hlt_lt, hblk_lt], hperm_lt, hk_lt, by rw [hsz_lt]; rfl, hal_lt', hconcr_lt, fun i hi => ?_⟩
            have hfm_eq : xs_lt.filterMap parseCtDataInit? = staticLtreeVals := by unfold staticLtreeVals; rw [hlt_init]
            have hi' : i < (xs_lt.filterMap parseCtDataInit?).length := by
              rw [filterMap_all_isSome_length parseCtDataInit? xs_lt hok_lt.2, hok_lt.1]; exact hi
            have hr := hread_lt i hi'
            dsimp only at hr ⊢
            have hget : (xs_lt.filterMap parseCtDataInit?)[i] = staticLtreeVals[i]! := by
              have hlen_fm : i < staticLtreeVals.length := by rw [← hfm_eq]; exact hi'
              rw [getElem!_pos staticLtreeVals i hlen_fm]
              exact list_getElem_of_eq hfm_eq hi' hlen_fm
            rw [hget] at hr
            have hb_lt := of_decide_eq_true (list_all_at staticLtree_bounds_all (by rw [← hfm_eq]; exact hi'))
            refine ⟨BitVec.ofNat 16 staticLtreeVals[i]!.1, BitVec.ofNat 16 staticLtreeVals[i]!.2,
              ?_, ?_, rfl, rfl, ?_⟩
            · rw [hp_lt.readVal hlt_lt]; exact hr.1
            · rw [hp_lt.readVal hlt_lt]; exact hr.2
            · simp only [BitVec.toNat_ofNat]; omega
          · refine ⟨henv_dt _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_dt hp_dt.1,
              by rw [hp_dt.2 _ hlt_dt, hblk_dt], hperm_dt, hk_dt, by rw [hsz_dt]; rfl, hal_dt', hconcr_dt, fun i hi => ?_⟩
            have hfm_eq : xs_dt.filterMap parseCtDataInit? = staticDtreeVals := by unfold staticDtreeVals; rw [hdt_init]
            have hi' : i < (xs_dt.filterMap parseCtDataInit?).length := by
              rw [filterMap_all_isSome_length parseCtDataInit? xs_dt hok_dt.2, hok_dt.1]; exact hi
            have hr := hread_dt i hi'
            dsimp only at hr ⊢
            have hget : (xs_dt.filterMap parseCtDataInit?)[i] = staticDtreeVals[i]! := by
              have hlen_fm : i < staticDtreeVals.length := by rw [← hfm_eq]; exact hi'
              rw [getElem!_pos staticDtreeVals i hlen_fm]
              exact list_getElem_of_eq hfm_eq hi' hlen_fm
            rw [hget] at hr
            have hb_dt := of_decide_eq_true (list_all_at staticDtree_bounds_all (by rw [← hfm_eq]; exact hi'))
            refine ⟨BitVec.ofNat 16 staticDtreeVals[i]!.1, BitVec.ofNat 16 staticDtreeVals[i]!.2,
              ?_, ?_, rfl, rfl, ?_⟩
            · rw [hp_dt.readVal hlt_dt]; exact hr.1
            · rw [hp_dt.readVal hlt_dt]; exact hr.2
            · simp only [BitVec.toNat_ofNat]; omega
          · refine ⟨henv_dc _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_dc hp_dc.1,
              by rw [hp_dc.2 _ hlt_dc, hblk_dc], hperm_dc, hk_dc, by rw [hsz_dc]; rfl, by rw [hal_dc']; rfl,
              hconcr_dc, fun i hi => ?_⟩
            have hb_dc0 := array_all_at dist_code_bounds_all hi
            have hb_dc := of_decide_eq_true hb_dc0
            refine ⟨BitVec.ofInt 8 Zlib.Tables.treesH_vals__dist_code[i]!, ?_, rfl, ?_⟩
            · rw [hp_dc.readVal hlt_dc]
              have hr := hread_dc i hi
              rw [show IntKind.u8.bytes = 1 from rfl, Nat.one_mul] at hr
              exact hr
            · rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]; omega
          · refine ⟨henv_lc _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_lc hp_lc.1,
              by rw [hp_lc.2 _ hlt_lc, hblk_lc], hperm_lc, hk_lc, by rw [hsz_lc]; rfl, by rw [hal_lc']; rfl,
              hconcr_lc, fun i hi => ?_⟩
            have hb_lc0 := array_all_at length_code_bounds_all hi
            have hb_lc := of_decide_eq_true hb_lc0
            refine ⟨BitVec.ofInt 8 Zlib.Tables.treesH_vals__length_code[i]!, ?_, rfl, ?_⟩
            · rw [hp_lc.readVal hlt_lc]
              have hr := hread_lc i hi
              rw [show IntKind.u8.bytes = 1 from rfl, Nat.one_mul] at hr
              exact hr
            · rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]; omega
          · refine ⟨henv_bl _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_bl hp_bl.1,
              by rw [hp_bl.2 _ hlt_bl, hblk_bl], hperm_bl, hk_bl, by rw [hsz_bl]; rfl, by rw [hal_bl']; rfl,
              hconcr_bl, fun i hi => ?_⟩
            have hb_bl0 := array_all_at base_length_bounds_all hi
            have hb_bl := of_decide_eq_true hb_bl0
            refine ⟨BitVec.ofInt 32 Zlib.Tables.treesH_vals_base_length[i]!, ?_, rfl, ?_⟩
            · rw [hp_bl.readVal hlt_bl]; exact hread_bl i hi
            · rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]; exact hb_bl
          · refine ⟨henv_bd _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_bd hp_bd.1,
              by rw [hp_bd.2 _ hlt_bd, hblk_bd], hperm_bd, hk_bd, by rw [hsz_bd]; rfl, by rw [hal_bd']; rfl,
              hconcr_bd, fun i hi => ?_⟩
            have hb_bd0 := array_all_at base_dist_bounds_all hi
            have hb_bd := of_decide_eq_true hb_bd0
            refine ⟨BitVec.ofInt 32 Zlib.Tables.treesH_vals_base_dist[i]!, ?_, rfl, ?_⟩
            · rw [hp_bd.readVal hlt_bd]; exact hread_bd i hi
            · rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]; exact hb_bd
          · refine ⟨henv_sld _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_sld hp_sld.1,
              hblk1_sld, hperm_sld, hk_sld, hsz_sld, hal_sld', ?_,
              by rw [hp_sld.readVal hlt_sld]; exact hread1_sld,
              by rw [hp_sld.readVal hlt_sld]; exact hread2_sld,
              by rw [hp_sld.readVal hlt_sld]; exact hread3_sld,
              by rw [hp_sld.readVal hlt_sld]; exact hread4_sld⟩
            exact readVal_ptr_of_exact rfl hblk1_sld hlim0
              (by rw [inBounds_iff, int64_ofNat_toInt hlim0, hsz_sld]; decide)
              (isAligned_of_dvd (by decide) (by rw [hal_sld']; exact Nat.dvd_refl 8) (Nat.dvd_zero 8) hlim0)
              (fun j hj => by rw [Nat.zero_add]; exact hbytes0_sld j (by rw [encodePtr_length] at hj; exact hj))
          · refine ⟨henv_sdd _ _ (lookup_cons_eq _), Nat.lt_of_lt_of_le hlt_sdd hp_sdd.1,
              hblk1_sdd, hperm_sdd, hk_sdd, hsz_sdd, hal_sdd', ?_,
              by rw [hp_sdd.readVal hlt_sdd]; exact hread1_sdd,
              by rw [hp_sdd.readVal hlt_sdd]; exact hread2_sdd,
              by rw [hp_sdd.readVal hlt_sdd]; exact hread3_sdd,
              by rw [hp_sdd.readVal hlt_sdd]; exact hread4_sdd⟩
            exact readVal_ptr_of_exact rfl hblk1_sdd hlim0
              (by rw [inBounds_iff, int64_ofNat_toInt hlim0, hsz_sdd]; decide)
              (isAligned_of_dvd (by decide) (by rw [hal_sdd']; exact Nat.dvd_refl 8) (Nat.dvd_zero 8) hlim0)
              (fun j hj => by rw [Nat.zero_add]; exact hbytes0_sdd j (by rw [encodePtr_length] at hj; exact hj))
          · refine ⟨by rw [← henv_fin]; exact lookup_cons_eq _, hlt_sbd,
              hblk1_sbd, hperm_sbd, hk_sbd, hsz_sbd, hal_sbd', ?_,
              hread1_sbd, hread2_sbd, hread3_sbd, hread4_sbd⟩
            exact readVal_null_of_exact rfl hblk1_sbd hlim0
              (by rw [inBounds_iff, int64_ofNat_toInt hlim0, hsz_sbd]; decide)
              (isAligned_of_dvd (by decide) (by rw [hal_sbd']; exact Nat.dvd_refl 8) (Nat.dvd_zero 8) hlim0)
              (fun j hj => by rw [Nat.zero_add]; exact hbytes0_sbd j (by rw [encodeNull_length] at hj; exact hj))

private theorem initGlobs_deflate_unpack {globBase strBase : Nat → UInt64} {prog0 : Prog}
    {idx ns ns' : Nat} {env env' : Env} {m m' : Mem}
    {used : List String}
    (htags : prog0.tags = (progOfTUs Zlib.allFiles).tags)
    (hprotos : prog0.fnProtos = (progOfTUs Zlib.allFiles).fnProtos)
    (hnone_all : ∀ nm, nm ∉ used → env.lookup nm = none)
    (hdisj : ∀ nm ∈ ["deflate_copyright", "configuration_table", "deflate_stored", "deflate_fast", "deflate_slow"], nm ∉ used)
    (hg : initProg.initGlobs globBase strBase prog0 idx ns env m deflateGlobalsList = some (env', m', ns')) :
    ∃ (b_dc : BlockId) (blk_dc : Block) (b_ct : BlockId) (blk_ct : Block),
      (env'.lookup "deflate_copyright" = some (b_dc, .array (.const_ (.int .i8)) (some 70)) ∧
        b_dc < m'.nextBlock ∧ m'.blocks b_dc = some blk_dc ∧ blk_dc.perm = .ro ∧ blk_dc.kind = .global ∧
        blk_dc.size = 70 ∧ blk_dc.align = 1 ∧ (∀ i, ∃ u : UInt8, blk_dc.bytes i = .byte u) ∧
        m'.strlenAt b_dc 0 = some 69) ∧
      (env'.lookup "configuration_table" = some (b_ct, configConstTy.array (some 10)) ∧
        b_ct < m'.nextBlock ∧ m'.blocks b_ct = some blk_ct ∧ blk_ct.perm = .ro ∧ blk_ct.kind = .global ∧
        blk_ct.size = 160 ∧ blk_ct.align = 8 ∧
        ∀ i < 10, ∃ (gl ml nl mc : BitVec 16) (fnm : String),
          let c := configurationTableVals[i]!
          Sem.readVal prog0.tags m' b_ct (Int64.ofNat (16 * i)) (.int .u16) = some (.int .u16 gl) ∧
          Sem.readVal prog0.tags m' b_ct (Int64.ofNat (16 * i + 2)) (.int .u16) = some (.int .u16 ml) ∧
          Sem.readVal prog0.tags m' b_ct (Int64.ofNat (16 * i + 4)) (.int .u16) = some (.int .u16 nl) ∧
          Sem.readVal prog0.tags m' b_ct (Int64.ofNat (16 * i + 6)) (.int .u16) = some (.int .u16 mc) ∧
          Sem.readVal prog0.tags m' b_ct (Int64.ofNat (16 * i + 8)) configFuncFieldTy = some (.fnPtr fnm) ∧
          gl = BitVec.ofNat 16 c.1 ∧ ml = BitVec.ofNat 16 c.2.1 ∧
          nl = BitVec.ofNat 16 c.2.2.1 ∧ mc = BitVec.ofNat 16 c.2.2.2.1 ∧ fnm = c.2.2.2.2) := by
  dsimp only [deflateGlobalsList] at hg
  obtain ⟨b_dc, t_dc, ma, nsa, hal_dc, hg1⟩ :=
    initGlobs_step_fresh (hnone_all "deflate_copyright" (hdisj "deflate_copyright" (by decide))) hg
  obtain ⟨rfl, rfl, rfl, hp_dc, blk_dc, hblk_dc, hsz_dc, hal_dc', hk_dc, hperm_dc, hconcr_dc, hstr_dc, _⟩ :=
    allocVarInit_strLit_inv rfl rfl deflate_copyright_str_ok hal_dc
  have hn1 := env_none_cons_prepend (ins := []) (name := Zlib.Deflate.deflateTU_global_deflate_copyright.name)
    (bid := m.nextBlock) (ty := .array (.const_ (.int .i8)) (some (" deflate 1.4.0.1 Copyright 1995-2026 Jean-loup Gailly and Mark Adler ".utf8ByteSize + 1))) hnone_all
  have hname_dc : Zlib.Deflate.deflateTU_global_deflate_copyright.name = "deflate_copyright" := rfl
  rw [hname_dc] at hn1 hg1
  have hn_ct : (("deflate_copyright", m.nextBlock, _) :: env).lookup Zlib.Deflate.deflateTU_global_configuration_table.name = none :=
    hn1 "configuration_table" (not_mem_prepend_of_disj (by decide) hdisj (by decide))
  obtain ⟨b_ct, t_ct, mb, nsb, hal_ct, hg_nil⟩ := initGlobs_step_fresh hn_ct hg1
  unfold initProg.initGlobs at hg_nil
  simp only [Option.some.injEq, Prod.mk.injEq] at hg_nil
  rcases hg_nil with ⟨henv_fin, hm_fin, _⟩
  cases hct_init : Zlib.Deflate.deflateTU_global_configuration_table.init? with
  | none =>
    exfalso; have hok := configurationTable_init_all_ok; rw [hct_init] at hok; cases hok
  | some iv_ct =>
    cases iv_ct with
    | expr _ | intSeq _ _ =>
      exfalso; have hok := configurationTable_init_all_ok; rw [hct_init] at hok; cases hok
    | list xs_ct =>
      have hok_ct := configurationTable_init_all_ok
      rw [hct_init] at hok_ct
      simp only [Bool.and_eq_true, beq_iff_eq] at hok_ct
      have hfn_ok : ∀ fnm,
          (fnm = "deflate_stored" ∨ fnm = "deflate_fast" ∨ fnm = "deflate_slow") →
          (("deflate_copyright", m.nextBlock, (CTy.const_ (.int .i8)).array
              (some (" deflate 1.4.0.1 Copyright 1995-2026 Jean-loup Gailly and Mark Adler ".utf8ByteSize + 1))) :: env).lookup fnm = none ∧
          enumConst? prog0.tags fnm = none ∧
          ∃ ret ps variadic, prog0.fnProtos fnm = some (ret, ps, variadic) := by
        intro fnm hmem
        rcases hmem with rfl | rfl | rfl
        · refine ⟨hn1 "deflate_stored" (not_mem_prepend_of_disj (by decide) hdisj (by decide)),
            ?_, ?_⟩
          · rw [htags]; exact enumConst_none_of_not_mem (by decide)
          · rw [hprotos]; exact ⟨_, _, _, prog0_fnProtos_deflate_stored⟩
        · refine ⟨hn1 "deflate_fast" (not_mem_prepend_of_disj (by decide) hdisj (by decide)),
            ?_, ?_⟩
          · rw [htags]; exact enumConst_none_of_not_mem (by decide)
          · rw [hprotos]; exact ⟨_, _, _, prog0_fnProtos_deflate_fast⟩
        · refine ⟨hn1 "deflate_slow" (not_mem_prepend_of_disj (by decide) hdisj (by decide)),
            ?_, ?_⟩
          · rw [htags]; exact enumConst_none_of_not_mem (by decide)
          · rw [hprotos]; exact ⟨_, _, _, prog0_fnProtos_deflate_slow⟩
      obtain ⟨rfl, rfl, rfl, hp_ct, blk_ct, hblk_ct, hsz_ct, hal_ct', hk_ct, hperm_ct, hread_ct⟩ :=
        allocVarInit_configArray_inv htags rfl hok_ct.1 hct_init hok_ct.2 hfn_ok hal_ct
      rw [hm_fin] at hp_ct hblk_ct hread_ct
      have hname_ct : Zlib.Deflate.deflateTU_global_configuration_table.name = "configuration_table" := rfl
      rw [hname_ct] at henv_fin
      have hlt_dc : m.nextBlock < ma.nextBlock := lt_nextBlock_of_some hblk_dc
      have hlt_ct : ma.nextBlock < m'.nextBlock := lt_nextBlock_of_some hblk_ct
      have hlt_dc_m' : m.nextBlock < m'.nextBlock := Nat.lt_of_lt_of_le hlt_dc hp_ct.1
      have hlen_dc : " deflate 1.4.0.1 Copyright 1995-2026 Jean-loup Gailly and Mark Adler ".utf8ByteSize = 69 := rfl
      refine ⟨m.nextBlock, blk_dc, ma.nextBlock, blk_ct, ?_, ?_⟩
      · refine ⟨?_, hlt_dc_m', by rw [hp_ct.2 _ hlt_dc, hblk_dc], hperm_dc, hk_dc,
          by rw [hsz_dc, hlen_dc], hal_dc', hconcr_dc, by rw [hp_ct.strlenAt hlt_dc, hstr_dc, hlen_dc]⟩
        rw [← henv_fin, lookup_cons_ne _ (by decide), lookup_cons_eq _, hlen_dc]
      · refine ⟨?_, hlt_ct, hblk_ct, hperm_ct, hk_ct, by rw [hsz_ct]; rfl, hal_ct', fun i hi => ?_⟩
        · rw [← henv_fin, lookup_cons_eq _]
        · have hfm_eq : xs_ct.filterMap parseConfigInit? = configurationTableVals := by
            unfold configurationTableVals; rw [hct_init]
          have hi' : i < (xs_ct.filterMap parseConfigInit?).length := by
            rw [filterMap_all_isSome_length parseConfigInit? xs_ct hok_ct.2, hok_ct.1]; exact hi
          have hr := hread_ct i hi'
          dsimp only at hr ⊢
          have hget : (xs_ct.filterMap parseConfigInit?)[i] = configurationTableVals[i]! := by
            have hlen_fm : i < configurationTableVals.length := by rw [← hfm_eq]; exact hi'
            rw [getElem!_pos configurationTableVals i hlen_fm]
            exact list_getElem_of_eq hfm_eq hi' hlen_fm
          rw [hget] at hr
          exact ⟨_, _, _, _, _, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, rfl, rfl, rfl, rfl, rfl⟩

structure InitLibzAllProps (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState) : Prop where
  base : InitLibzProps prog gEnv m0 os0
  inflate_copyright_prop : ∃ b blk,
    gEnv.lookup "inflate_copyright" = some (b, .array (.const_ (.int .i8)) (some 49)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 49 ∧ blk.align = 1 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    m0.strlenAt b 0 = some 48
  lenfix_prop : ∃ b blk,
    gEnv.lookup "lenfix" = some (b, codeConstTy.array (some 512)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 2048 ∧ blk.align = 2 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 512, ∃ (op bits val : Nat),
      let t := lenfixVals[i]!
      op = t.1 ∧ bits = t.2.1 ∧ val = t.2.2 ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i)) (.int .u8) = some (.int .u8 (BitVec.ofNat 8 op)) ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i + 1)) (.int .u8) = some (.int .u8 (BitVec.ofNat 8 bits)) ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i + 2)) (.int .u16) = some (.int .u16 (BitVec.ofNat 16 val)) ∧
      7 ≤ bits ∧ bits ≤ 9 ∧
      ((op = 0 ∧ val ≤ 255) ∨ (op = 64 ∧ val = 0) ∨ (op = 96 ∧ val = 0) ∨
        (16 ≤ op ∧ op ≤ 21 ∧ 3 ≤ val ∧ val + (1 <<< (op &&& 15)) - 1 ≤ 258))
  distfix_prop : ∃ b blk,
    gEnv.lookup "distfix" = some (b, codeConstTy.array (some 32)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 128 ∧ blk.align = 2 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 32, ∃ (op bits val : Nat),
      let t := distfixVals[i]!
      op = t.1 ∧ bits = t.2.1 ∧ val = t.2.2 ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i)) (.int .u8) = some (.int .u8 (BitVec.ofNat 8 op)) ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i + 1)) (.int .u8) = some (.int .u8 (BitVec.ofNat 8 bits)) ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i + 2)) (.int .u16) = some (.int .u16 (BitVec.ofNat 16 val)) ∧
      bits = 5 ∧
      ((op = 64 ∧ val = 0) ∨
        (16 ≤ op ∧ op ≤ 29 ∧ 1 ≤ val ∧ val + (1 <<< (op &&& 15)) - 1 ≤ 32768))
  extra_lbits_prop : ∃ b blk,
    gEnv.lookup "extra_lbits" = some (b, (CTy.const_ (.int .i32)).array (some 29)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 116 ∧ blk.align = 4 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 29, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i)) (.int .i32) = some (.int .i32 bv) ∧
      bv = BitVec.ofInt 32 Zlib.Trees.treesTU_vals_extra_lbits[i]! ∧ 0 ≤ bv.toInt ∧ bv.toInt ≤ 5
  extra_dbits_prop : ∃ b blk,
    gEnv.lookup "extra_dbits" = some (b, (CTy.const_ (.int .i32)).array (some 30)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 120 ∧ blk.align = 4 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 30, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i)) (.int .i32) = some (.int .i32 bv) ∧
      bv = BitVec.ofInt 32 Zlib.Trees.treesTU_vals_extra_dbits[i]! ∧ 0 ≤ bv.toInt ∧ bv.toInt ≤ 13
  extra_blbits_prop : ∃ b blk,
    gEnv.lookup "extra_blbits" = some (b, (CTy.const_ (.int .i32)).array (some 19)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 76 ∧ blk.align = 4 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 19, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i)) (.int .i32) = some (.int .i32 bv) ∧
      bv = BitVec.ofInt 32 Zlib.Trees.treesTU_vals_extra_blbits[i]! ∧ 0 ≤ bv.toInt ∧ bv.toInt ≤ 7
  bl_order_prop : ∃ b blk,
    gEnv.lookup "bl_order" = some (b, (CTy.const_ (.typedef "uch" (.int .u8))).array (some 19)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 19 ∧ blk.align = 1 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 19, ∃ bv : BitVec 8,
      Sem.readVal prog.tags m0 b (Int64.ofNat i) (.int .u8) = some (.int .u8 bv) ∧
      bv = BitVec.ofInt 8 Zlib.Trees.treesTU_vals_bl_order[i]! ∧ bv.toNat < 19
  static_ltree_prop : ∃ b blk,
    gEnv.lookup "static_ltree" = some (b, ctDataConstTy.array (some 288)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 1152 ∧ blk.align = 2 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 288, ∃ fc dl : BitVec 16,
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i)) (.int .u16) = some (.int .u16 fc) ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i + 2)) (.int .u16) = some (.int .u16 dl) ∧
      fc = BitVec.ofNat 16 staticLtreeVals[i]!.1 ∧ dl = BitVec.ofNat 16 staticLtreeVals[i]!.2 ∧
      7 ≤ dl.toNat ∧ dl.toNat ≤ 9
  static_dtree_prop : ∃ b blk,
    gEnv.lookup "static_dtree" = some (b, ctDataConstTy.array (some 30)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 120 ∧ blk.align = 2 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 30, ∃ fc dl : BitVec 16,
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i)) (.int .u16) = some (.int .u16 fc) ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i + 2)) (.int .u16) = some (.int .u16 dl) ∧
      fc = BitVec.ofNat 16 staticDtreeVals[i]!.1 ∧ dl = BitVec.ofNat 16 staticDtreeVals[i]!.2 ∧
      dl.toNat = 5
  _dist_code_prop : ∃ b blk,
    gEnv.lookup "_dist_code" = some (b, (CTy.const_ (.typedef "uch" (.int .u8))).array (some 512)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 512 ∧ blk.align = 1 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 512, ∃ bv : BitVec 8,
      Sem.readVal prog.tags m0 b (Int64.ofNat i) (.int .u8) = some (.int .u8 bv) ∧
      bv = BitVec.ofInt 8 Zlib.Tables.treesH_vals__dist_code[i]! ∧ bv.toNat < 30
  _length_code_prop : ∃ b blk,
    gEnv.lookup "_length_code" = some (b, (CTy.const_ (.typedef "uch" (.int .u8))).array (some 256)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 256 ∧ blk.align = 1 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 256, ∃ bv : BitVec 8,
      Sem.readVal prog.tags m0 b (Int64.ofNat i) (.int .u8) = some (.int .u8 bv) ∧
      bv = BitVec.ofInt 8 Zlib.Tables.treesH_vals__length_code[i]! ∧ bv.toNat < 29
  base_length_prop : ∃ b blk,
    gEnv.lookup "base_length" = some (b, (CTy.const_ (.int .i32)).array (some 29)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 116 ∧ blk.align = 4 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 29, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i)) (.int .i32) = some (.int .i32 bv) ∧
      bv = BitVec.ofInt 32 Zlib.Tables.treesH_vals_base_length[i]! ∧ 0 ≤ bv.toInt ∧ bv.toInt ≤ 224
  base_dist_prop : ∃ b blk,
    gEnv.lookup "base_dist" = some (b, (CTy.const_ (.int .i32)).array (some 30)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 120 ∧ blk.align = 4 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    ∀ i < 30, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m0 b (Int64.ofNat (4 * i)) (.int .i32) = some (.int .i32 bv) ∧
      bv = BitVec.ofInt 32 Zlib.Tables.treesH_vals_base_dist[i]! ∧ 0 ≤ bv.toInt ∧ bv.toInt ≤ 24576
  static_l_desc_prop : ∃ b blk b_lt b_el,
    gEnv.lookup "static_l_desc" = some (b, staticTreeDescConstTy) ∧
    gEnv.lookup "static_ltree" = some (b_lt, ctDataConstTy.array (some 288)) ∧
    gEnv.lookup "extra_lbits" = some (b_el, (CTy.const_ (.int .i32)).array (some 29)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧ blk.size = 32 ∧ blk.align = 8 ∧
    Sem.readVal prog.tags m0 b 0 (.ptr ctDataConstTy) = some (.ptr b_lt 0) ∧
    Sem.readVal prog.tags m0 b 8 (.ptr (.const_ (.typedef "intf" (.int .i32)))) = some (.ptr b_el 0) ∧
    Sem.readVal prog.tags m0 b 16 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 257)) ∧
    Sem.readVal prog.tags m0 b 20 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 286)) ∧
    Sem.readVal prog.tags m0 b 24 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 15))
  static_d_desc_prop : ∃ b blk b_dt b_ed,
    gEnv.lookup "static_d_desc" = some (b, staticTreeDescConstTy) ∧
    gEnv.lookup "static_dtree" = some (b_dt, ctDataConstTy.array (some 30)) ∧
    gEnv.lookup "extra_dbits" = some (b_ed, (CTy.const_ (.int .i32)).array (some 30)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧ blk.size = 32 ∧ blk.align = 8 ∧
    Sem.readVal prog.tags m0 b 0 (.ptr ctDataConstTy) = some (.ptr b_dt 0) ∧
    Sem.readVal prog.tags m0 b 8 (.ptr (.const_ (.typedef "intf" (.int .i32)))) = some (.ptr b_ed 0) ∧
    Sem.readVal prog.tags m0 b 16 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 0)) ∧
    Sem.readVal prog.tags m0 b 20 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 30)) ∧
    Sem.readVal prog.tags m0 b 24 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 15))
  static_bl_desc_prop : ∃ b blk b_ebl,
    gEnv.lookup "static_bl_desc" = some (b, staticTreeDescConstTy) ∧
    gEnv.lookup "extra_blbits" = some (b_ebl, (CTy.const_ (.int .i32)).array (some 19)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧ blk.size = 32 ∧ blk.align = 8 ∧
    Sem.readVal prog.tags m0 b 0 (.ptr ctDataConstTy) = some .null ∧
    Sem.readVal prog.tags m0 b 8 (.ptr (.const_ (.typedef "intf" (.int .i32)))) = some (.ptr b_ebl 0) ∧
    Sem.readVal prog.tags m0 b 16 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 0)) ∧
    Sem.readVal prog.tags m0 b 20 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 19)) ∧
    Sem.readVal prog.tags m0 b 24 (.int .i32) = some (.int .i32 (BitVec.ofInt 32 7))
  deflate_copyright_prop : ∃ b blk,
    gEnv.lookup "deflate_copyright" = some (b, .array (.const_ (.int .i8)) (some 70)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 70 ∧ blk.align = 1 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
    m0.strlenAt b 0 = some 69
  configuration_table_prop : ∃ b blk,
    gEnv.lookup "configuration_table" = some (b, configConstTy.array (some 10)) ∧
    m0.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 160 ∧ blk.align = 8 ∧
    ∀ i < 10, ∃ (gl ml nl mc : BitVec 16) (fnm : String),
      let c := configurationTableVals[i]!
      Sem.readVal prog.tags m0 b (Int64.ofNat (16 * i)) (.int .u16) = some (.int .u16 gl) ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (16 * i + 2)) (.int .u16) = some (.int .u16 ml) ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (16 * i + 4)) (.int .u16) = some (.int .u16 nl) ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (16 * i + 6)) (.int .u16) = some (.int .u16 mc) ∧
      Sem.readVal prog.tags m0 b (Int64.ofNat (16 * i + 8)) configFuncFieldTy = some (.fnPtr fnm) ∧
      gl = BitVec.ofNat 16 c.1 ∧ ml = BitVec.ofNat 16 c.2.1 ∧
      nl = BitVec.ofNat 16 c.2.2.1 ∧ mc = BitVec.ofNat 16 c.2.2.2.1 ∧ fnm = c.2.2.2.2 ∧
      gl.toNat ≤ 32 ∧ ml.toNat ≤ 258 ∧ nl.toNat ≤ 258 ∧ mc.toNat ≤ 4096 ∧
      (fnm = "deflate_stored" ∨ fnm = "deflate_fast" ∨ fnm = "deflate_slow")
  prog_fnStatics_empty_all : ∀ sym, sym ∉ staticFnNames → prog.fnStatics sym = []
  inflate_table_statics_prop : ∃ b_lb blk_lb b_le blk_le b_db blk_db b_de blk_de,
    prog.fnStatics "inflate_table" = [
      ("dext", b_de, u16ArrTy 32),
      ("dbase", b_db, u16ArrTy 32),
      ("lext", b_le, u16ArrTy 31),
      ("lbase", b_lb, u16ArrTy 31)
    ] ∧
    (m0.blocks b_lb = some blk_lb ∧ blk_lb.perm = .ro ∧ blk_lb.kind = .global ∧
      blk_lb.size = 62 ∧ blk_lb.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_lb.bytes i = .byte u) ∧
      (∀ i < 31, ∃ bv : BitVec 16,
        Sem.readVal prog.tags m0 b_lb (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
        bv = BitVec.ofInt 16 inflateTableLbaseVals[i]! ∧ bv.toNat ≤ 258)) ∧
    (m0.blocks b_le = some blk_le ∧ blk_le.perm = .ro ∧ blk_le.kind = .global ∧
      blk_le.size = 62 ∧ blk_le.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_le.bytes i = .byte u) ∧
      (∀ i < 31, ∃ bv : BitVec 16,
        Sem.readVal prog.tags m0 b_le (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
        bv = BitVec.ofInt 16 inflateTableLextVals[i]! ∧ 16 ≤ bv.toNat ∧ bv.toNat ≤ 199)) ∧
    (m0.blocks b_db = some blk_db ∧ blk_db.perm = .ro ∧ blk_db.kind = .global ∧
      blk_db.size = 64 ∧ blk_db.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_db.bytes i = .byte u) ∧
      (∀ i < 32, ∃ bv : BitVec 16,
        Sem.readVal prog.tags m0 b_db (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
        bv = BitVec.ofInt 16 inflateTableDbaseVals[i]! ∧ bv.toNat ≤ 24577)) ∧
    (m0.blocks b_de = some blk_de ∧ blk_de.perm = .ro ∧ blk_de.kind = .global ∧
      blk_de.size = 64 ∧ blk_de.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_de.bytes i = .byte u) ∧
      (∀ i < 32, ∃ bv : BitVec 16,
        Sem.readVal prog.tags m0 b_de (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
        bv = BitVec.ofInt 16 inflateTableDextVals[i]! ∧ 16 ≤ bv.toNat ∧ bv.toNat ≤ 64))
  inflate_statics_prop : ∃ b_ord blk_ord,
    prog.fnStatics "inflate" = [("order", b_ord, u16ArrTy 19)] ∧
    m0.blocks b_ord = some blk_ord ∧ blk_ord.perm = .ro ∧ blk_ord.kind = .global ∧
    blk_ord.size = 38 ∧ blk_ord.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_ord.bytes i = .byte u) ∧
    ∀ i < 19, ∃ bv : BitVec 16,
      Sem.readVal prog.tags m0 b_ord (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
      bv = BitVec.ofInt 16 inflateOrderVals[i]! ∧ bv.toNat < 19
  inflateBack_statics_prop : ∃ b_ord blk_ord,
    prog.fnStatics "inflateBack" = [("order", b_ord, u16ArrTy 19)] ∧
    m0.blocks b_ord = some blk_ord ∧ blk_ord.perm = .ro ∧ blk_ord.kind = .global ∧
    blk_ord.size = 38 ∧ blk_ord.align = 2 ∧ (∀ i, ∃ u : UInt8, blk_ord.bytes i = .byte u) ∧
    ∀ i < 19, ∃ bv : BitVec 16,
      Sem.readVal prog.tags m0 b_ord (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 bv) ∧
      bv = BitVec.ofInt 16 inflateOrderVals[i]! ∧ bv.toNat < 19
  deflateInit2_statics_prop : ∃ b_mv blk_mv,
    prog.fnStatics "deflateInit2_" =
      [("my_version", b_mv, .array (.const_ (.int .i8)) (some 15))] ∧
    m0.blocks b_mv = some blk_mv ∧ blk_mv.perm = .ro ∧ blk_mv.kind = .global ∧
    blk_mv.size = 15 ∧ blk_mv.align = 1 ∧ (∀ i, ∃ u : UInt8, blk_mv.bytes i = .byte u) ∧
    m0.strlenAt b_mv 0 = some 14 ∧
    Sem.readVal prog.tags m0 b_mv 0 (.int .i8) = some (.int .i8 (BitVec.ofNat 8 49))

theorem initLibz_allProps {globBase staticBase strBase : Nat → UInt64} {errnoBase : UInt64}
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (h : Zlib.Spec.initLibz globBase staticBase strBase errnoBase = some (prog, gEnv, m0, os0)) :
    InitLibzAllProps prog gEnv m0 os0 := by
  have hbase : InitLibzProps prog gEnv m0 os0 := initLibz_props h
  have h_raw := h
  unfold Zlib.Spec.initLibz at h_raw
  simp only [bind, Option.bind, pure, Pure.pure] at h_raw
  split at h_raw
  · cases h_raw
  · next a_init h_init =>
    rcases a_init with ⟨p_init, gEnv_init, mFinal_init, _⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at h_raw
    rcases h_raw with ⟨hp_outer, hg_outer, hm_outer, _⟩
    unfold initProg at h_init
    simp only [bind, Option.bind, pure, Pure.pure] at h_init
    split at h_init
    · cases h_init
    · next a_err _ =>
      rcases a_err with ⟨eBid, _⟩
      dsimp only at h_init
      split at h_init
      · cases h_init
      · next a_gl hgl =>
        rcases a_gl with ⟨gEnv', m1, ns1⟩
        dsimp only at h_init
        split at h_init
        · cases h_init
        · next a_st hst =>
          rcases a_st with ⟨fnStaticList, m2⟩
          dsimp only at h_init
          simp only [Option.some.injEq, Prod.mk.injEq] at h_init
          rcases h_init with ⟨hp_inner, hg_inner, hm_inner, _⟩
          have hg_eq : gEnv' = gEnv := hg_inner.trans hg_outer
          have hm2_eq : m2 = m0 := hm_inner.trans hm_outer
          have hfnst_eq : prog.fnStatics = fun s => (fnStaticList.lookup s).getD [] := by
            rw [← hp_outer]; dsimp only; rw [← hp_inner]
          rw [hg_eq] at hgl hst
          rw [hm2_eq] at hst
          rw [prog0_globals_eq] at hgl
          have hn0 : ∀ nm, nm ∉ ["errno"] →
              ([("errno", eBid, CTy.int IntKind.i32)]).lookup nm = none := by
            intro nm hnm
            simp only [List.mem_singleton] at hnm
            rw [lookup_cons_ne _ hnm]; rfl
          rw [List.append_assoc, List.append_assoc, List.append_assoc] at hgl
          obtain ⟨_, _, _, _, hg_z, hgl_rest_z⟩ := initGlobs_append hgl
          have hn_z := env_none_initGlobs hg_z hn0
          rw [tuGlobals_zutil_names] at hn_z
          obtain ⟨_, m_inf, _, b_ic, blk_ic, b_lf, blk_lf, b_df, blk_df,
              hgl_rest_inf, hn_inf, h_ic, h_lf, h_df⟩ :=
            initGlobs_inftrees_unpack hn_z (fun nm hm hmem => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
              rcases hm with rfl | rfl | rfl <;> exact absurd hmem (by decide)) hgl_rest_z
          obtain ⟨hp_after_inf, henv_after_inf⟩ := initGlobs_preserves hgl_rest_inf
          obtain ⟨_, _, _, _, hg_crc, hgl_rest_crc⟩ := initGlobs_append hgl_rest_inf
          have hn_crc := env_none_initGlobs hg_crc hn_inf
          rw [tuGlobals_crc32_names] at hn_crc
          obtain ⟨_, m_tr, _, _, b_el, blk_el, b_ed, blk_ed, b_ebl, blk_ebl,
              b_bo, blk_bo, b_lt, blk_lt, b_dt, blk_dt, b_dcode, blk_dcode,
              b_lcode, blk_lcode, b_bl, blk_bl, b_bd, blk_bd,
              b_sld, blk_sld, b_sdd, blk_sdd, b_sbd, blk_sbd,
              hgl_def, hn_tr, h_el, h_ed, h_ebl, h_bo, h_lt, h_dt, h_dcode, h_lcode,
              h_bl, h_bd, h_sld, h_sdd, h_sbd⟩ :=
            initGlobs_trees_unpack rfl hn_crc (fun nm hm hmem => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
              rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                exact absurd hmem (by decide)) hgl_rest_crc
          rw [treesGlobalsList_names] at hn_tr
          obtain ⟨hp_after_tr, henv_after_tr⟩ := initGlobs_preserves hgl_def
          obtain ⟨b_dc, blk_dc, b_ct, blk_ct, h_dc, h_ct⟩ :=
            initGlobs_deflate_unpack rfl rfl hn_tr (fun nm hm hmem => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
              rcases hm with rfl | rfl | rfl | rfl | rfl <;> exact absurd hmem (by decide)) hgl_def
          have hp_st := initStatics_preserves hst
          have hp_inf_m0 : MemPreservedBelow m_inf.nextBlock m_inf m0 :=
            hp_after_inf.trans (hp_st.mono hp_after_inf.1)
          have hp_tr_m0 : MemPreservedBelow m_tr.nextBlock m_tr m0 :=
            hp_after_tr.trans (hp_st.mono hp_after_tr.1)
          refine
            { base := hbase
              inflate_copyright_prop := ?_
              lenfix_prop := ?_
              distfix_prop := ?_
              extra_lbits_prop := ?_
              extra_dbits_prop := ?_
              extra_blbits_prop := ?_
              bl_order_prop := ?_
              static_ltree_prop := ?_
              static_dtree_prop := ?_
              _dist_code_prop := ?_
              _length_code_prop := ?_
              base_length_prop := ?_
              base_dist_prop := ?_
              static_l_desc_prop := ?_
              static_d_desc_prop := ?_
              static_bl_desc_prop := ?_
              deflate_copyright_prop := ?_
              configuration_table_prop := ?_
              prog_fnStatics_empty_all := ?_
              inflate_table_statics_prop := ?_
              inflate_statics_prop := ?_
              inflateBack_statics_prop := ?_
              deflateInit2_statics_prop := ?_ }
          · refine ⟨b_ic, blk_ic, henv_after_inf _ _ h_ic.1, ?_, h_ic.2.2.2.1, h_ic.2.2.2.2.1,
              h_ic.2.2.2.2.2.1, h_ic.2.2.2.2.2.2.1, h_ic.2.2.2.2.2.2.2.1, ?_⟩
            · rw [hp_inf_m0.2 _ h_ic.2.1, h_ic.2.2.1]
            · rw [hp_inf_m0.strlenAt h_ic.2.1, h_ic.2.2.2.2.2.2.2.2]
          · refine ⟨b_lf, blk_lf, henv_after_inf _ _ h_lf.1, by rw [hp_inf_m0.2 _ h_lf.2.1, h_lf.2.2.1],
              h_lf.2.2.2.1, h_lf.2.2.2.2.1, h_lf.2.2.2.2.2.1, h_lf.2.2.2.2.2.2.1, h_lf.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨op, bits, val, hop, hbits, hval, hr0, hr1, hr2⟩ := h_lf.2.2.2.2.2.2.2.2 i hi
            have hb_lf := of_decide_eq_true (list_all_at lenfix_bounds_all (by
              have hok := lenfix_init_all_ok
              cases hlf_i : Zlib.Tables.inffixedH_global_lenfix.init? with
              | none => rw [hlf_i] at hok; cases hok
              | some iv => cases iv with
                | expr _ | intSeq _ _ => rw [hlf_i] at hok; cases hok
                | list xs =>
                  rw [hlf_i] at hok
                  simp only [Bool.and_eq_true, beq_iff_eq] at hok
                  have hlen_fm : lenfixVals.length = 512 := by
                    unfold lenfixVals; rw [hlf_i, filterMap_all_isSome_length parseCodeInit? xs hok.2, hok.1]
                  rw [hlen_fm]; exact hi))
            rw [← hop, ← hbits, ← hval] at hb_lf
            refine ⟨op, bits, val, hop, hbits, hval, ?_, ?_, ?_, hb_lf⟩
            · rw [hbase.prog_tags_eq, hp_inf_m0.readVal h_lf.2.1]; exact hr0
            · rw [hbase.prog_tags_eq, hp_inf_m0.readVal h_lf.2.1]; exact hr1
            · rw [hbase.prog_tags_eq, hp_inf_m0.readVal h_lf.2.1]; exact hr2
          · refine ⟨b_df, blk_df, henv_after_inf _ _ h_df.1, by rw [hp_inf_m0.2 _ h_df.2.1, h_df.2.2.1],
              h_df.2.2.2.1, h_df.2.2.2.2.1, h_df.2.2.2.2.2.1, h_df.2.2.2.2.2.2.1, h_df.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨op, bits, val, hop, hbits, hval, hr0, hr1, hr2⟩ := h_df.2.2.2.2.2.2.2.2 i hi
            have hb_df := of_decide_eq_true (list_all_at distfix_bounds_all (by
              have hok := distfix_init_all_ok
              cases hdf_i : Zlib.Tables.inffixedH_global_distfix.init? with
              | none => rw [hdf_i] at hok; cases hok
              | some iv => cases iv with
                | expr _ | intSeq _ _ => rw [hdf_i] at hok; cases hok
                | list xs =>
                  rw [hdf_i] at hok
                  simp only [Bool.and_eq_true, beq_iff_eq] at hok
                  have hlen_fm : distfixVals.length = 32 := by
                    unfold distfixVals; rw [hdf_i, filterMap_all_isSome_length parseCodeInit? xs hok.2, hok.1]
                  rw [hlen_fm]; exact hi))
            rw [← hop, ← hbits, ← hval] at hb_df
            refine ⟨op, bits, val, hop, hbits, hval, ?_, ?_, ?_, hb_df⟩
            · rw [hbase.prog_tags_eq, hp_inf_m0.readVal h_df.2.1]; exact hr0
            · rw [hbase.prog_tags_eq, hp_inf_m0.readVal h_df.2.1]; exact hr1
            · rw [hbase.prog_tags_eq, hp_inf_m0.readVal h_df.2.1]; exact hr2
          · refine ⟨b_el, blk_el, henv_after_tr _ _ h_el.1, by rw [hp_tr_m0.2 _ h_el.2.1, h_el.2.2.1],
              h_el.2.2.2.1, h_el.2.2.2.2.1, h_el.2.2.2.2.2.1, h_el.2.2.2.2.2.2.1, h_el.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨bv, hrb, hbv_eq, hlo, hhi⟩ := h_el.2.2.2.2.2.2.2.2 i hi
            exact ⟨bv, by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_el.2.1]; exact hrb, hbv_eq, hlo, hhi⟩
          · refine ⟨b_ed, blk_ed, henv_after_tr _ _ h_ed.1, by rw [hp_tr_m0.2 _ h_ed.2.1, h_ed.2.2.1],
              h_ed.2.2.2.1, h_ed.2.2.2.2.1, h_ed.2.2.2.2.2.1, h_ed.2.2.2.2.2.2.1, h_ed.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨bv, hrb, hbv_eq, hlo, hhi⟩ := h_ed.2.2.2.2.2.2.2.2 i hi
            exact ⟨bv, by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_ed.2.1]; exact hrb, hbv_eq, hlo, hhi⟩
          · refine ⟨b_ebl, blk_ebl, henv_after_tr _ _ h_ebl.1, by rw [hp_tr_m0.2 _ h_ebl.2.1, h_ebl.2.2.1],
              h_ebl.2.2.2.1, h_ebl.2.2.2.2.1, h_ebl.2.2.2.2.2.1, h_ebl.2.2.2.2.2.2.1, h_ebl.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨bv, hrb, hbv_eq, hlo, hhi⟩ := h_ebl.2.2.2.2.2.2.2.2 i hi
            exact ⟨bv, by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_ebl.2.1]; exact hrb, hbv_eq, hlo, hhi⟩
          · refine ⟨b_bo, blk_bo, henv_after_tr _ _ h_bo.1, by rw [hp_tr_m0.2 _ h_bo.2.1, h_bo.2.2.1],
              h_bo.2.2.2.1, h_bo.2.2.2.2.1, h_bo.2.2.2.2.2.1, h_bo.2.2.2.2.2.2.1, h_bo.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨bv, hrb, hbv_eq, hlt⟩ := h_bo.2.2.2.2.2.2.2.2 i hi
            exact ⟨bv, by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_bo.2.1]; exact hrb, hbv_eq, hlt⟩
          · refine ⟨b_lt, blk_lt, henv_after_tr _ _ h_lt.1, by rw [hp_tr_m0.2 _ h_lt.2.1, h_lt.2.2.1],
              h_lt.2.2.2.1, h_lt.2.2.2.2.1, h_lt.2.2.2.2.2.1, h_lt.2.2.2.2.2.2.1, h_lt.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨fc, dl, hrf, hrd, hfc_eq, hdl_eq, hlo, hhi⟩ := h_lt.2.2.2.2.2.2.2.2 i hi
            exact ⟨fc, dl,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_lt.2.1]; exact hrf,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_lt.2.1]; exact hrd,
              hfc_eq, hdl_eq, hlo, hhi⟩
          · refine ⟨b_dt, blk_dt, henv_after_tr _ _ h_dt.1, by rw [hp_tr_m0.2 _ h_dt.2.1, h_dt.2.2.1],
              h_dt.2.2.2.1, h_dt.2.2.2.2.1, h_dt.2.2.2.2.2.1, h_dt.2.2.2.2.2.2.1, h_dt.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨fc, dl, hrf, hrd, hfc_eq, hdl_eq, heq5⟩ := h_dt.2.2.2.2.2.2.2.2 i hi
            exact ⟨fc, dl,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_dt.2.1]; exact hrf,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_dt.2.1]; exact hrd,
              hfc_eq, hdl_eq, heq5⟩
          · refine ⟨b_dcode, blk_dcode, henv_after_tr _ _ h_dcode.1, by rw [hp_tr_m0.2 _ h_dcode.2.1, h_dcode.2.2.1],
              h_dcode.2.2.2.1, h_dcode.2.2.2.2.1, h_dcode.2.2.2.2.2.1, h_dcode.2.2.2.2.2.2.1, h_dcode.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨bv, hrb, hbv_eq, hlt⟩ := h_dcode.2.2.2.2.2.2.2.2 i hi
            exact ⟨bv, by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_dcode.2.1]; exact hrb, hbv_eq, hlt⟩
          · refine ⟨b_lcode, blk_lcode, henv_after_tr _ _ h_lcode.1, by rw [hp_tr_m0.2 _ h_lcode.2.1, h_lcode.2.2.1],
              h_lcode.2.2.2.1, h_lcode.2.2.2.2.1, h_lcode.2.2.2.2.2.1, h_lcode.2.2.2.2.2.2.1, h_lcode.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨bv, hrb, hbv_eq, hlt⟩ := h_lcode.2.2.2.2.2.2.2.2 i hi
            exact ⟨bv, by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_lcode.2.1]; exact hrb, hbv_eq, hlt⟩
          · refine ⟨b_bl, blk_bl, henv_after_tr _ _ h_bl.1, by rw [hp_tr_m0.2 _ h_bl.2.1, h_bl.2.2.1],
              h_bl.2.2.2.1, h_bl.2.2.2.2.1, h_bl.2.2.2.2.2.1, h_bl.2.2.2.2.2.2.1, h_bl.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨bv, hrb, hbv_eq, hlo, hhi⟩ := h_bl.2.2.2.2.2.2.2.2 i hi
            exact ⟨bv, by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_bl.2.1]; exact hrb, hbv_eq, hlo, hhi⟩
          · refine ⟨b_bd, blk_bd, henv_after_tr _ _ h_bd.1, by rw [hp_tr_m0.2 _ h_bd.2.1, h_bd.2.2.1],
              h_bd.2.2.2.1, h_bd.2.2.2.2.1, h_bd.2.2.2.2.2.1, h_bd.2.2.2.2.2.2.1, h_bd.2.2.2.2.2.2.2.1,
              fun i hi => ?_⟩
            obtain ⟨bv, hrb, hbv_eq, hlo, hhi⟩ := h_bd.2.2.2.2.2.2.2.2 i hi
            exact ⟨bv, by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_bd.2.1]; exact hrb, hbv_eq, hlo, hhi⟩
          · refine ⟨b_sld, blk_sld, b_lt, b_el, henv_after_tr _ _ h_sld.1, henv_after_tr _ _ h_lt.1,
              henv_after_tr _ _ h_el.1, by rw [hp_tr_m0.2 _ h_sld.2.1, h_sld.2.2.1],
              h_sld.2.2.2.1, h_sld.2.2.2.2.1, h_sld.2.2.2.2.2.1, h_sld.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sld.2.1]; exact h_sld.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sld.2.1]; exact h_sld.2.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sld.2.1]; exact h_sld.2.2.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sld.2.1]; exact h_sld.2.2.2.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sld.2.1]; exact h_sld.2.2.2.2.2.2.2.2.2.2.2⟩
          · refine ⟨b_sdd, blk_sdd, b_dt, b_ed, henv_after_tr _ _ h_sdd.1, henv_after_tr _ _ h_dt.1,
              henv_after_tr _ _ h_ed.1, by rw [hp_tr_m0.2 _ h_sdd.2.1, h_sdd.2.2.1],
              h_sdd.2.2.2.1, h_sdd.2.2.2.2.1, h_sdd.2.2.2.2.2.1, h_sdd.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sdd.2.1]; exact h_sdd.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sdd.2.1]; exact h_sdd.2.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sdd.2.1]; exact h_sdd.2.2.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sdd.2.1]; exact h_sdd.2.2.2.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sdd.2.1]; exact h_sdd.2.2.2.2.2.2.2.2.2.2.2⟩
          · refine ⟨b_sbd, blk_sbd, b_ebl, henv_after_tr _ _ h_sbd.1, henv_after_tr _ _ h_ebl.1,
              by rw [hp_tr_m0.2 _ h_sbd.2.1, h_sbd.2.2.1],
              h_sbd.2.2.2.1, h_sbd.2.2.2.2.1, h_sbd.2.2.2.2.2.1, h_sbd.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sbd.2.1]; exact h_sbd.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sbd.2.1]; exact h_sbd.2.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sbd.2.1]; exact h_sbd.2.2.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sbd.2.1]; exact h_sbd.2.2.2.2.2.2.2.2.2.2.1,
              by rw [hbase.prog_tags_eq, hp_tr_m0.readVal h_sbd.2.1]; exact h_sbd.2.2.2.2.2.2.2.2.2.2.2⟩
          · refine ⟨b_dc, blk_dc, h_dc.1, by rw [hp_st.2 _ h_dc.2.1, h_dc.2.2.1],
              h_dc.2.2.2.1, h_dc.2.2.2.2.1, h_dc.2.2.2.2.2.1, h_dc.2.2.2.2.2.2.1, h_dc.2.2.2.2.2.2.2.1,
              by rw [hp_st.strlenAt h_dc.2.1, h_dc.2.2.2.2.2.2.2.2]⟩
          · refine ⟨b_ct, blk_ct, h_ct.1, by rw [hp_st.2 _ h_ct.2.1, h_ct.2.2.1],
              h_ct.2.2.2.1, h_ct.2.2.2.2.1, h_ct.2.2.2.2.2.1, h_ct.2.2.2.2.2.2.1, fun i hi => ?_⟩
            obtain ⟨gl, ml, nl, mc, fnm, hr0, hr1, hr2, hr3, hr4, hgl_e, hml_e, hnl_e, hmc_e, hfn_e⟩ :=
              h_ct.2.2.2.2.2.2.2 i hi
            have hb_ct := of_decide_eq_true (list_all_at configurationTable_bounds_all (by
              have hok := configurationTable_init_all_ok
              cases hct_i : Zlib.Deflate.deflateTU_global_configuration_table.init? with
              | none => rw [hct_i] at hok; cases hok
              | some iv => cases iv with
                | expr _ | intSeq _ _ => rw [hct_i] at hok; cases hok
                | list xs =>
                  rw [hct_i] at hok
                  simp only [Bool.and_eq_true, beq_iff_eq] at hok
                  have hlen_fm : configurationTableVals.length = 10 := by
                    unfold configurationTableVals; rw [hct_i, filterMap_all_isSome_length parseConfigInit? xs hok.2, hok.1]
                  rw [hlen_fm]; exact hi))
            refine ⟨gl, ml, nl, mc, fnm,
              by rw [hbase.prog_tags_eq, hp_st.readVal h_ct.2.1]; exact hr0,
              by rw [hbase.prog_tags_eq, hp_st.readVal h_ct.2.1]; exact hr1,
              by rw [hbase.prog_tags_eq, hp_st.readVal h_ct.2.1]; exact hr2,
              by rw [hbase.prog_tags_eq, hp_st.readVal h_ct.2.1]; exact hr3,
              by rw [hbase.prog_tags_eq, hp_st.readVal h_ct.2.1]; exact hr4,
              hgl_e, hml_e, hnl_e, hmc_e, hfn_e, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hgl_e, BitVec.toNat_ofNat]; omega
            · rw [hml_e, BitVec.toNat_ofNat]; omega
            · rw [hnl_e, BitVec.toNat_ofNat]; omega
            · rw [hmc_e, BitVec.toNat_ofNat]; omega
            · rw [hfn_e]; exact hb_ct.2.2.2.2
          · intro sym hns
            rw [hfnst_eq]
            exact initStatics_fnStatics_empty hst (by rfl) (collectFnStatics_empty_of_nonStatic hns)
          · obtain ⟨_, b_lb, blk_lb, b_le, blk_le, b_db, blk_db, b_de, blk_de, hlu, hlb, hle, hdb, hde⟩ :=
              initStatics_inflate_table_inv hst
            refine ⟨b_lb, blk_lb, b_le, blk_le, b_db, blk_db, b_de, blk_de, by rw [hfnst_eq]; exact hlu, ?_, ?_, ?_, ?_⟩
            · obtain ⟨hb, hp, hk, hs, ha, hc, hr⟩ := hlb
              refine ⟨hb, hp, hk, hs, ha, hc, fun i hi => ?_⟩
              simpa only [hbase.prog_tags_eq] using hr i hi
            · obtain ⟨hb, hp, hk, hs, ha, hc, hr⟩ := hle
              refine ⟨hb, hp, hk, hs, ha, hc, fun i hi => ?_⟩
              simpa only [hbase.prog_tags_eq] using hr i hi
            · obtain ⟨hb, hp, hk, hs, ha, hc, hr⟩ := hdb
              refine ⟨hb, hp, hk, hs, ha, hc, fun i hi => ?_⟩
              simpa only [hbase.prog_tags_eq] using hr i hi
            · obtain ⟨hb, hp, hk, hs, ha, hc, hr⟩ := hde
              refine ⟨hb, hp, hk, hs, ha, hc, fun i hi => ?_⟩
              simpa only [hbase.prog_tags_eq] using hr i hi
          · obtain ⟨b_ord, blk_ord, hlu, hb, hp, hk, hs, ha, hc, hr⟩ := initStatics_inflate_inv hst
            refine ⟨b_ord, blk_ord, by rw [hfnst_eq]; exact hlu, hb, hp, hk, hs, ha, hc, fun i hi => ?_⟩
            simpa only [hbase.prog_tags_eq] using hr i hi
          · obtain ⟨b_ord, blk_ord, hlu, hb, hp, hk, hs, ha, hc, hr⟩ := initStatics_inflateBack_inv hst
            refine ⟨b_ord, blk_ord, by rw [hfnst_eq]; exact hlu, hb, hp, hk, hs, ha, hc, fun i hi => ?_⟩
            simpa only [hbase.prog_tags_eq] using hr i hi
          · obtain ⟨b_mv, blk_mv, hlu, hb, hp, hk, hs, ha, hc, hst_mv, hr0⟩ := initStatics_deflateInit2_inv hst
            refine ⟨b_mv, blk_mv, by rw [hfnst_eq]; exact hlu, hb, hp, hk, hs, ha, hc, hst_mv, ?_⟩
            simpa only [hbase.prog_tags_eq] using hr0

end LibzAllPropsSection

/-! ### Convenience `InitLibzAllProps` Dot-Notation Accessors -/

namespace InitLibzAllProps

section Accessors
variable {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState} (h : InitLibzAllProps prog gEnv m0 os0)
include h

theorem globalEnv_eq : prog.globalEnv = gEnv := h.base.globalEnv_eq
theorem prog_tags_eq : prog.tags = (progOfTUs Zlib.allFiles).tags := h.base.prog_tags_eq
theorem prog_fns_eq : prog.fns = (progOfTUs Zlib.allFiles).fns := h.base.prog_fns_eq
theorem prog_fnProtos_eq : prog.fnProtos = fun sym =>
    if sym == "LSEEK" then (progOfTUs Zlib.allFiles).fnProtos "lseek64"
    else (progOfTUs Zlib.allFiles).fnProtos sym :=
  h.base.prog_fnProtos_eq
theorem prog_fnStatics_eq_nil_all {sym : String} (hsym : sym ∉ staticFnNames) :
    prog.fnStatics sym = [] :=
  h.prog_fnStatics_empty_all sym hsym

-- Wave 1 forwarded `prog.fns` (33)
theorem prog_fns_zlibVersion : prog.fns "zlibVersion" = some Zlib.Zutil.zutilTU_fn_zlibVersion := Zlib.Proof.prog_fns_zlibVersion h.base
theorem prog_fns_zlibCompileFlags : prog.fns "zlibCompileFlags" = some Zlib.Zutil.zutilTU_fn_zlibCompileFlags := Zlib.Proof.prog_fns_zlibCompileFlags h.base
theorem prog_fns_zError : prog.fns "zError" = some Zlib.Zutil.zutilTU_fn_zError := Zlib.Proof.prog_fns_zError h.base
theorem prog_fns_zcalloc : prog.fns "zcalloc" = some Zlib.Zutil.zutilTU_fn_zcalloc := Zlib.Proof.prog_fns_zcalloc h.base
theorem prog_fns_zcfree : prog.fns "zcfree" = some Zlib.Zutil.zutilTU_fn_zcfree := Zlib.Proof.prog_fns_zcfree h.base
theorem prog_fns_compress2_z : prog.fns "compress2_z" = some Zlib.Compress.compressTU_fn_compress2_z := Zlib.Proof.prog_fns_compress2_z h.base
theorem prog_fns_compress2 : prog.fns "compress2" = some Zlib.Compress.compressTU_fn_compress2 := Zlib.Proof.prog_fns_compress2 h.base
theorem prog_fns_compress_z : prog.fns "compress_z" = some Zlib.Compress.compressTU_fn_compress_z := Zlib.Proof.prog_fns_compress_z h.base
theorem prog_fns_compress : prog.fns "compress" = some Zlib.Compress.compressTU_fn_compress := Zlib.Proof.prog_fns_compress h.base
theorem prog_fns_compressBound_z : prog.fns "compressBound_z" = some Zlib.Compress.compressTU_fn_compressBound_z := Zlib.Proof.prog_fns_compressBound_z h.base
theorem prog_fns_compressBound : prog.fns "compressBound" = some Zlib.Compress.compressTU_fn_compressBound := Zlib.Proof.prog_fns_compressBound h.base
theorem prog_fns_adler32_z : prog.fns "adler32_z" = some Zlib.Adler32.adler32TU_fn_adler32_z := Zlib.Proof.prog_fns_adler32_z h.base
theorem prog_fns_adler32 : prog.fns "adler32" = some Zlib.Adler32.adler32TU_fn_adler32 := Zlib.Proof.prog_fns_adler32 h.base
theorem prog_fns_adler32_combine_ : prog.fns "adler32_combine_" = some Zlib.Adler32.adler32TU_fn_adler32_combine_ := Zlib.Proof.prog_fns_adler32_combine_ h.base
theorem prog_fns_adler32_combine : prog.fns "adler32_combine" = some Zlib.Adler32.adler32TU_fn_adler32_combine := Zlib.Proof.prog_fns_adler32_combine h.base
theorem prog_fns_adler32_combine64 : prog.fns "adler32_combine64" = some Zlib.Adler32.adler32TU_fn_adler32_combine64 := Zlib.Proof.prog_fns_adler32_combine64 h.base
theorem prog_fns_byte_swap : prog.fns "byte_swap" = some Zlib.Crc32.crc32TU_fn_byte_swap := Zlib.Proof.prog_fns_byte_swap h.base
theorem prog_fns_multmodp : prog.fns "multmodp" = some Zlib.Crc32.crc32TU_fn_multmodp := Zlib.Proof.prog_fns_multmodp h.base
theorem prog_fns_x2nmodp : prog.fns "x2nmodp" = some Zlib.Crc32.crc32TU_fn_x2nmodp := Zlib.Proof.prog_fns_x2nmodp h.base
theorem prog_fns_get_crc_table : prog.fns "get_crc_table" = some Zlib.Crc32.crc32TU_fn_get_crc_table := Zlib.Proof.prog_fns_get_crc_table h.base
theorem prog_fns_crc_word : prog.fns "crc_word" = some Zlib.Crc32.crc32TU_fn_crc_word := Zlib.Proof.prog_fns_crc_word h.base
theorem prog_fns_crc_word_big : prog.fns "crc_word_big" = some Zlib.Crc32.crc32TU_fn_crc_word_big := Zlib.Proof.prog_fns_crc_word_big h.base
theorem prog_fns_crc32_braid : prog.fns "crc32_braid" = some Zlib.Crc32.crc32TU_fn_crc32_braid := Zlib.Proof.prog_fns_crc32_braid h.base
theorem prog_fns_crc32_z : prog.fns "crc32_z" = some Zlib.Crc32.crc32TU_fn_crc32_z := Zlib.Proof.prog_fns_crc32_z h.base
theorem prog_fns_crc32 : prog.fns "crc32" = some Zlib.Crc32.crc32TU_fn_crc32 := Zlib.Proof.prog_fns_crc32 h.base
theorem prog_fns_crc32_combine_gen64 : prog.fns "crc32_combine_gen64" = some Zlib.Crc32.crc32TU_fn_crc32_combine_gen64 := Zlib.Proof.prog_fns_crc32_combine_gen64 h.base
theorem prog_fns_crc32_combine_gen : prog.fns "crc32_combine_gen" = some Zlib.Crc32.crc32TU_fn_crc32_combine_gen := Zlib.Proof.prog_fns_crc32_combine_gen h.base
theorem prog_fns_crc32_combine_op : prog.fns "crc32_combine_op" = some Zlib.Crc32.crc32TU_fn_crc32_combine_op := Zlib.Proof.prog_fns_crc32_combine_op h.base
theorem prog_fns_crc32_combine64 : prog.fns "crc32_combine64" = some Zlib.Crc32.crc32TU_fn_crc32_combine64 := Zlib.Proof.prog_fns_crc32_combine64 h.base
theorem prog_fns_crc32_combine : prog.fns "crc32_combine" = some Zlib.Crc32.crc32TU_fn_crc32_combine := Zlib.Proof.prog_fns_crc32_combine h.base
theorem prog_fns_malloc : prog.fns "malloc" = none := Zlib.Proof.prog_fns_malloc h.base
theorem prog_fns_calloc : prog.fns "calloc" = none := Zlib.Proof.prog_fns_calloc h.base
theorem prog_fns_free : prog.fns "free" = none := Zlib.Proof.prog_fns_free h.base

-- Remaining `prog.fns` (134 defined + 17 extern/libc)
theorem prog_fns_gzclose : prog.fns "gzclose" = some Zlib.Gzclose.gzcloseTU_fn_gzclose :=
  h.base.prog_fns_eq ▸ prog0_fns_gzclose
theorem prog_fns_uncompress2_z : prog.fns "uncompress2_z" = some Zlib.Uncompr.uncomprTU_fn_uncompress2_z :=
  h.base.prog_fns_eq ▸ prog0_fns_uncompress2_z
theorem prog_fns_uncompress2 : prog.fns "uncompress2" = some Zlib.Uncompr.uncomprTU_fn_uncompress2 :=
  h.base.prog_fns_eq ▸ prog0_fns_uncompress2
theorem prog_fns_uncompress_z : prog.fns "uncompress_z" = some Zlib.Uncompr.uncomprTU_fn_uncompress_z :=
  h.base.prog_fns_eq ▸ prog0_fns_uncompress_z
theorem prog_fns_uncompress : prog.fns "uncompress" = some Zlib.Uncompr.uncomprTU_fn_uncompress :=
  h.base.prog_fns_eq ▸ prog0_fns_uncompress
theorem prog_fns_inflate_table : prog.fns "inflate_table" = some Zlib.Inftrees.inftreesTU_fn_inflate_table :=
  h.base.prog_fns_eq ▸ prog0_fns_inflate_table
theorem prog_fns_inflate_fixed : prog.fns "inflate_fixed" = some Zlib.Inftrees.inftreesTU_fn_inflate_fixed :=
  h.base.prog_fns_eq ▸ prog0_fns_inflate_fixed
theorem prog_fns_load64 : prog.fns "load64" = some Zlib.Inffast.inffastTU_fn_load64 :=
  h.base.prog_fns_eq ▸ prog0_fns_load64
theorem prog_fns_copy_back : prog.fns "copy_back" = some Zlib.Inffast.inffastTU_fn_copy_back :=
  h.base.prog_fns_eq ▸ prog0_fns_copy_back
theorem prog_fns_inflate_fast : prog.fns "inflate_fast" = some Zlib.Inffast.inffastTU_fn_inflate_fast :=
  h.base.prog_fns_eq ▸ prog0_fns_inflate_fast
theorem prog_fns_bi_reverse : prog.fns "bi_reverse" = some Zlib.Trees.treesTU_fn_bi_reverse :=
  h.base.prog_fns_eq ▸ prog0_fns_bi_reverse
theorem prog_fns_bi_flush : prog.fns "bi_flush" = some Zlib.Trees.treesTU_fn_bi_flush :=
  h.base.prog_fns_eq ▸ prog0_fns_bi_flush
theorem prog_fns_bi_windup : prog.fns "bi_windup" = some Zlib.Trees.treesTU_fn_bi_windup :=
  h.base.prog_fns_eq ▸ prog0_fns_bi_windup
theorem prog_fns_gen_codes : prog.fns "gen_codes" = some Zlib.Trees.treesTU_fn_gen_codes :=
  h.base.prog_fns_eq ▸ prog0_fns_gen_codes
theorem prog_fns_tr_static_init : prog.fns "tr_static_init" = some Zlib.Trees.treesTU_fn_tr_static_init :=
  h.base.prog_fns_eq ▸ prog0_fns_tr_static_init
theorem prog_fns_init_block : prog.fns "init_block" = some Zlib.Trees.treesTU_fn_init_block :=
  h.base.prog_fns_eq ▸ prog0_fns_init_block
theorem prog_fns__tr_init : prog.fns "_tr_init" = some Zlib.Trees.treesTU_fn__tr_init :=
  h.base.prog_fns_eq ▸ prog0_fns__tr_init
theorem prog_fns_pqdownheap : prog.fns "pqdownheap" = some Zlib.Trees.treesTU_fn_pqdownheap :=
  h.base.prog_fns_eq ▸ prog0_fns_pqdownheap
theorem prog_fns_gen_bitlen : prog.fns "gen_bitlen" = some Zlib.Trees.treesTU_fn_gen_bitlen :=
  h.base.prog_fns_eq ▸ prog0_fns_gen_bitlen
theorem prog_fns_build_tree : prog.fns "build_tree" = some Zlib.Trees.treesTU_fn_build_tree :=
  h.base.prog_fns_eq ▸ prog0_fns_build_tree
theorem prog_fns_scan_tree : prog.fns "scan_tree" = some Zlib.Trees.treesTU_fn_scan_tree :=
  h.base.prog_fns_eq ▸ prog0_fns_scan_tree
theorem prog_fns_send_tree : prog.fns "send_tree" = some Zlib.Trees.treesTU_fn_send_tree :=
  h.base.prog_fns_eq ▸ prog0_fns_send_tree
theorem prog_fns_build_bl_tree : prog.fns "build_bl_tree" = some Zlib.Trees.treesTU_fn_build_bl_tree :=
  h.base.prog_fns_eq ▸ prog0_fns_build_bl_tree
theorem prog_fns_send_all_trees : prog.fns "send_all_trees" = some Zlib.Trees.treesTU_fn_send_all_trees :=
  h.base.prog_fns_eq ▸ prog0_fns_send_all_trees
theorem prog_fns__tr_stored_block : prog.fns "_tr_stored_block" = some Zlib.Trees.treesTU_fn__tr_stored_block :=
  h.base.prog_fns_eq ▸ prog0_fns__tr_stored_block
theorem prog_fns__tr_flush_bits : prog.fns "_tr_flush_bits" = some Zlib.Trees.treesTU_fn__tr_flush_bits :=
  h.base.prog_fns_eq ▸ prog0_fns__tr_flush_bits
theorem prog_fns__tr_align : prog.fns "_tr_align" = some Zlib.Trees.treesTU_fn__tr_align :=
  h.base.prog_fns_eq ▸ prog0_fns__tr_align
theorem prog_fns_compress_block : prog.fns "compress_block" = some Zlib.Trees.treesTU_fn_compress_block :=
  h.base.prog_fns_eq ▸ prog0_fns_compress_block
theorem prog_fns_detect_data_type : prog.fns "detect_data_type" = some Zlib.Trees.treesTU_fn_detect_data_type :=
  h.base.prog_fns_eq ▸ prog0_fns_detect_data_type
theorem prog_fns__tr_flush_block : prog.fns "_tr_flush_block" = some Zlib.Trees.treesTU_fn__tr_flush_block :=
  h.base.prog_fns_eq ▸ prog0_fns__tr_flush_block
theorem prog_fns__tr_tally : prog.fns "_tr_tally" = some Zlib.Trees.treesTU_fn__tr_tally :=
  h.base.prog_fns_eq ▸ prog0_fns__tr_tally
theorem prog_fns_inflateBackInit_ : prog.fns "inflateBackInit_" = some Zlib.Infback.infbackTU_fn_inflateBackInit_ :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateBackInit_
theorem prog_fns_inflateBack : prog.fns "inflateBack" = some Zlib.Infback.infbackTU_fn_inflateBack :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateBack
theorem prog_fns_inflateBackEnd : prog.fns "inflateBackEnd" = some Zlib.Infback.infbackTU_fn_inflateBackEnd :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateBackEnd
theorem prog_fns_inflateStateCheck : prog.fns "inflateStateCheck" = some Zlib.Inflate.inflateTU_fn_inflateStateCheck :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateStateCheck
theorem prog_fns_inflateResetKeep : prog.fns "inflateResetKeep" = some Zlib.Inflate.inflateTU_fn_inflateResetKeep :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateResetKeep
theorem prog_fns_inflateReset : prog.fns "inflateReset" = some Zlib.Inflate.inflateTU_fn_inflateReset :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateReset
theorem prog_fns_inflateReset2 : prog.fns "inflateReset2" = some Zlib.Inflate.inflateTU_fn_inflateReset2 :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateReset2
theorem prog_fns_inflateInit2_ : prog.fns "inflateInit2_" = some Zlib.Inflate.inflateTU_fn_inflateInit2_ :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateInit2_
theorem prog_fns_inflateInit_ : prog.fns "inflateInit_" = some Zlib.Inflate.inflateTU_fn_inflateInit_ :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateInit_
theorem prog_fns_inflatePrime : prog.fns "inflatePrime" = some Zlib.Inflate.inflateTU_fn_inflatePrime :=
  h.base.prog_fns_eq ▸ prog0_fns_inflatePrime
theorem prog_fns_updatewindow : prog.fns "updatewindow" = some Zlib.Inflate.inflateTU_fn_updatewindow :=
  h.base.prog_fns_eq ▸ prog0_fns_updatewindow
theorem prog_fns_inflate : prog.fns "inflate" = some Zlib.Inflate.inflateTU_fn_inflate :=
  h.base.prog_fns_eq ▸ prog0_fns_inflate
theorem prog_fns_inflateEnd : prog.fns "inflateEnd" = some Zlib.Inflate.inflateTU_fn_inflateEnd :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateEnd
theorem prog_fns_inflateGetDictionary : prog.fns "inflateGetDictionary" = some Zlib.Inflate.inflateTU_fn_inflateGetDictionary :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateGetDictionary
theorem prog_fns_inflateSetDictionary : prog.fns "inflateSetDictionary" = some Zlib.Inflate.inflateTU_fn_inflateSetDictionary :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateSetDictionary
theorem prog_fns_inflateGetHeader : prog.fns "inflateGetHeader" = some Zlib.Inflate.inflateTU_fn_inflateGetHeader :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateGetHeader
theorem prog_fns_syncsearch : prog.fns "syncsearch" = some Zlib.Inflate.inflateTU_fn_syncsearch :=
  h.base.prog_fns_eq ▸ prog0_fns_syncsearch
theorem prog_fns_inflateSync : prog.fns "inflateSync" = some Zlib.Inflate.inflateTU_fn_inflateSync :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateSync
theorem prog_fns_inflateSyncPoint : prog.fns "inflateSyncPoint" = some Zlib.Inflate.inflateTU_fn_inflateSyncPoint :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateSyncPoint
theorem prog_fns_inflateCopy : prog.fns "inflateCopy" = some Zlib.Inflate.inflateTU_fn_inflateCopy :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateCopy
theorem prog_fns_inflateUndermine : prog.fns "inflateUndermine" = some Zlib.Inflate.inflateTU_fn_inflateUndermine :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateUndermine
theorem prog_fns_inflateValidate : prog.fns "inflateValidate" = some Zlib.Inflate.inflateTU_fn_inflateValidate :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateValidate
theorem prog_fns_inflateMark : prog.fns "inflateMark" = some Zlib.Inflate.inflateTU_fn_inflateMark :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateMark
theorem prog_fns_inflateCodesUsed : prog.fns "inflateCodesUsed" = some Zlib.Inflate.inflateTU_fn_inflateCodesUsed :=
  h.base.prog_fns_eq ▸ prog0_fns_inflateCodesUsed
theorem prog_fns_slide_hash : prog.fns "slide_hash" = some Zlib.Deflate.deflateTU_fn_slide_hash :=
  h.base.prog_fns_eq ▸ prog0_fns_slide_hash
theorem prog_fns_read_buf : prog.fns "read_buf" = some Zlib.Deflate.deflateTU_fn_read_buf :=
  h.base.prog_fns_eq ▸ prog0_fns_read_buf
theorem prog_fns_fill_window : prog.fns "fill_window" = some Zlib.Deflate.deflateTU_fn_fill_window :=
  h.base.prog_fns_eq ▸ prog0_fns_fill_window
theorem prog_fns_deflateInit_ : prog.fns "deflateInit_" = some Zlib.Deflate.deflateTU_fn_deflateInit_ :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateInit_
theorem prog_fns_deflateInit2_ : prog.fns "deflateInit2_" = some Zlib.Deflate.deflateTU_fn_deflateInit2_ :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateInit2_
theorem prog_fns_deflateStateCheck : prog.fns "deflateStateCheck" = some Zlib.Deflate.deflateTU_fn_deflateStateCheck :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateStateCheck
theorem prog_fns_deflateSetDictionary : prog.fns "deflateSetDictionary" = some Zlib.Deflate.deflateTU_fn_deflateSetDictionary :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateSetDictionary
theorem prog_fns_deflateGetDictionary : prog.fns "deflateGetDictionary" = some Zlib.Deflate.deflateTU_fn_deflateGetDictionary :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateGetDictionary
theorem prog_fns_deflateResetKeep : prog.fns "deflateResetKeep" = some Zlib.Deflate.deflateTU_fn_deflateResetKeep :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateResetKeep
theorem prog_fns_lm_init : prog.fns "lm_init" = some Zlib.Deflate.deflateTU_fn_lm_init :=
  h.base.prog_fns_eq ▸ prog0_fns_lm_init
theorem prog_fns_deflateReset : prog.fns "deflateReset" = some Zlib.Deflate.deflateTU_fn_deflateReset :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateReset
theorem prog_fns_deflateSetHeader : prog.fns "deflateSetHeader" = some Zlib.Deflate.deflateTU_fn_deflateSetHeader :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateSetHeader
theorem prog_fns_deflatePending : prog.fns "deflatePending" = some Zlib.Deflate.deflateTU_fn_deflatePending :=
  h.base.prog_fns_eq ▸ prog0_fns_deflatePending
theorem prog_fns_deflateUsed : prog.fns "deflateUsed" = some Zlib.Deflate.deflateTU_fn_deflateUsed :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateUsed
theorem prog_fns_deflatePrime : prog.fns "deflatePrime" = some Zlib.Deflate.deflateTU_fn_deflatePrime :=
  h.base.prog_fns_eq ▸ prog0_fns_deflatePrime
theorem prog_fns_deflateParams : prog.fns "deflateParams" = some Zlib.Deflate.deflateTU_fn_deflateParams :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateParams
theorem prog_fns_deflateTune : prog.fns "deflateTune" = some Zlib.Deflate.deflateTU_fn_deflateTune :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateTune
theorem prog_fns_deflateBound_z : prog.fns "deflateBound_z" = some Zlib.Deflate.deflateTU_fn_deflateBound_z :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateBound_z
theorem prog_fns_deflateBound : prog.fns "deflateBound" = some Zlib.Deflate.deflateTU_fn_deflateBound :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateBound
theorem prog_fns_putShortMSB : prog.fns "putShortMSB" = some Zlib.Deflate.deflateTU_fn_putShortMSB :=
  h.base.prog_fns_eq ▸ prog0_fns_putShortMSB
theorem prog_fns_flush_pending : prog.fns "flush_pending" = some Zlib.Deflate.deflateTU_fn_flush_pending :=
  h.base.prog_fns_eq ▸ prog0_fns_flush_pending
theorem prog_fns_deflate : prog.fns "deflate" = some Zlib.Deflate.deflateTU_fn_deflate :=
  h.base.prog_fns_eq ▸ prog0_fns_deflate
theorem prog_fns_deflateEnd : prog.fns "deflateEnd" = some Zlib.Deflate.deflateTU_fn_deflateEnd :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateEnd
theorem prog_fns_deflateCopy : prog.fns "deflateCopy" = some Zlib.Deflate.deflateTU_fn_deflateCopy :=
  h.base.prog_fns_eq ▸ prog0_fns_deflateCopy
theorem prog_fns_longest_match : prog.fns "longest_match" = some Zlib.Deflate.deflateTU_fn_longest_match :=
  h.base.prog_fns_eq ▸ prog0_fns_longest_match
theorem prog_fns_deflate_stored : prog.fns "deflate_stored" = some Zlib.Deflate.deflateTU_fn_deflate_stored :=
  h.base.prog_fns_eq ▸ prog0_fns_deflate_stored
theorem prog_fns_deflate_fast : prog.fns "deflate_fast" = some Zlib.Deflate.deflateTU_fn_deflate_fast :=
  h.base.prog_fns_eq ▸ prog0_fns_deflate_fast
theorem prog_fns_deflate_slow : prog.fns "deflate_slow" = some Zlib.Deflate.deflateTU_fn_deflate_slow :=
  h.base.prog_fns_eq ▸ prog0_fns_deflate_slow
theorem prog_fns_deflate_rle : prog.fns "deflate_rle" = some Zlib.Deflate.deflateTU_fn_deflate_rle :=
  h.base.prog_fns_eq ▸ prog0_fns_deflate_rle
theorem prog_fns_deflate_huff : prog.fns "deflate_huff" = some Zlib.Deflate.deflateTU_fn_deflate_huff :=
  h.base.prog_fns_eq ▸ prog0_fns_deflate_huff
theorem prog_fns_gz_reset : prog.fns "gz_reset" = some Zlib.Gzlib.gzlibTU_fn_gz_reset :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_reset
theorem prog_fns_gz_open : prog.fns "gz_open" = some Zlib.Gzlib.gzlibTU_fn_gz_open :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_open
theorem prog_fns_gzopen : prog.fns "gzopen" = some Zlib.Gzlib.gzlibTU_fn_gzopen :=
  h.base.prog_fns_eq ▸ prog0_fns_gzopen
theorem prog_fns_gzopen64 : prog.fns "gzopen64" = some Zlib.Gzlib.gzlibTU_fn_gzopen64 :=
  h.base.prog_fns_eq ▸ prog0_fns_gzopen64
theorem prog_fns_gzdopen : prog.fns "gzdopen" = some Zlib.Gzlib.gzlibTU_fn_gzdopen :=
  h.base.prog_fns_eq ▸ prog0_fns_gzdopen
theorem prog_fns_gzbuffer : prog.fns "gzbuffer" = some Zlib.Gzlib.gzlibTU_fn_gzbuffer :=
  h.base.prog_fns_eq ▸ prog0_fns_gzbuffer
theorem prog_fns_gzrewind : prog.fns "gzrewind" = some Zlib.Gzlib.gzlibTU_fn_gzrewind :=
  h.base.prog_fns_eq ▸ prog0_fns_gzrewind
theorem prog_fns_gzseek64 : prog.fns "gzseek64" = some Zlib.Gzlib.gzlibTU_fn_gzseek64 :=
  h.base.prog_fns_eq ▸ prog0_fns_gzseek64
theorem prog_fns_gzseek : prog.fns "gzseek" = some Zlib.Gzlib.gzlibTU_fn_gzseek :=
  h.base.prog_fns_eq ▸ prog0_fns_gzseek
theorem prog_fns_gztell64 : prog.fns "gztell64" = some Zlib.Gzlib.gzlibTU_fn_gztell64 :=
  h.base.prog_fns_eq ▸ prog0_fns_gztell64
theorem prog_fns_gztell : prog.fns "gztell" = some Zlib.Gzlib.gzlibTU_fn_gztell :=
  h.base.prog_fns_eq ▸ prog0_fns_gztell
theorem prog_fns_gzoffset64 : prog.fns "gzoffset64" = some Zlib.Gzlib.gzlibTU_fn_gzoffset64 :=
  h.base.prog_fns_eq ▸ prog0_fns_gzoffset64
theorem prog_fns_gzoffset : prog.fns "gzoffset" = some Zlib.Gzlib.gzlibTU_fn_gzoffset :=
  h.base.prog_fns_eq ▸ prog0_fns_gzoffset
theorem prog_fns_gzeof : prog.fns "gzeof" = some Zlib.Gzlib.gzlibTU_fn_gzeof :=
  h.base.prog_fns_eq ▸ prog0_fns_gzeof
theorem prog_fns_gzerror : prog.fns "gzerror" = some Zlib.Gzlib.gzlibTU_fn_gzerror :=
  h.base.prog_fns_eq ▸ prog0_fns_gzerror
theorem prog_fns_gzclearerr : prog.fns "gzclearerr" = some Zlib.Gzlib.gzlibTU_fn_gzclearerr :=
  h.base.prog_fns_eq ▸ prog0_fns_gzclearerr
theorem prog_fns_gz_error : prog.fns "gz_error" = some Zlib.Gzlib.gzlibTU_fn_gz_error :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_error
theorem prog_fns_gz_intmax : prog.fns "gz_intmax" = some Zlib.Gzlib.gzlibTU_fn_gz_intmax :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_intmax
theorem prog_fns_gz_load : prog.fns "gz_load" = some Zlib.Gzread.gzreadTU_fn_gz_load :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_load
theorem prog_fns_gz_avail : prog.fns "gz_avail" = some Zlib.Gzread.gzreadTU_fn_gz_avail :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_avail
theorem prog_fns_gz_room : prog.fns "gz_room" = some Zlib.Gzread.gzreadTU_fn_gz_room :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_room
theorem prog_fns_gz_look : prog.fns "gz_look" = some Zlib.Gzread.gzreadTU_fn_gz_look :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_look
theorem prog_fns_gz_decomp : prog.fns "gz_decomp" = some Zlib.Gzread.gzreadTU_fn_gz_decomp :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_decomp
theorem prog_fns_gz_fetch : prog.fns "gz_fetch" = some Zlib.Gzread.gzreadTU_fn_gz_fetch :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_fetch
theorem prog_fns_gz_skip_have : prog.fns "gz_skip_have" = some Zlib.Gzread.gzreadTU_fn_gz_skip_have :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_skip_have
theorem prog_fns_gz_skip : prog.fns "gz_skip" = some Zlib.Gzread.gzreadTU_fn_gz_skip :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_skip
theorem prog_fns_gz_read : prog.fns "gz_read" = some Zlib.Gzread.gzreadTU_fn_gz_read :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_read
theorem prog_fns_gzread : prog.fns "gzread" = some Zlib.Gzread.gzreadTU_fn_gzread :=
  h.base.prog_fns_eq ▸ prog0_fns_gzread
theorem prog_fns_gzfread : prog.fns "gzfread" = some Zlib.Gzread.gzreadTU_fn_gzfread :=
  h.base.prog_fns_eq ▸ prog0_fns_gzfread
theorem prog_fns_gzgetc : prog.fns "gzgetc" = some Zlib.Gzread.gzreadTU_fn_gzgetc :=
  h.base.prog_fns_eq ▸ prog0_fns_gzgetc
theorem prog_fns_gzgetc_ : prog.fns "gzgetc_" = some Zlib.Gzread.gzreadTU_fn_gzgetc_ :=
  h.base.prog_fns_eq ▸ prog0_fns_gzgetc_
theorem prog_fns_gzungetc : prog.fns "gzungetc" = some Zlib.Gzread.gzreadTU_fn_gzungetc :=
  h.base.prog_fns_eq ▸ prog0_fns_gzungetc
theorem prog_fns_gzgets : prog.fns "gzgets" = some Zlib.Gzread.gzreadTU_fn_gzgets :=
  h.base.prog_fns_eq ▸ prog0_fns_gzgets
theorem prog_fns_gzdirect : prog.fns "gzdirect" = some Zlib.Gzread.gzreadTU_fn_gzdirect :=
  h.base.prog_fns_eq ▸ prog0_fns_gzdirect
theorem prog_fns_gzclose_r : prog.fns "gzclose_r" = some Zlib.Gzread.gzreadTU_fn_gzclose_r :=
  h.base.prog_fns_eq ▸ prog0_fns_gzclose_r
theorem prog_fns_gz_init : prog.fns "gz_init" = some Zlib.Gzwrite.gzwriteTU_fn_gz_init :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_init
theorem prog_fns_gz_comp : prog.fns "gz_comp" = some Zlib.Gzwrite.gzwriteTU_fn_gz_comp :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_comp
theorem prog_fns_gz_zero : prog.fns "gz_zero" = some Zlib.Gzwrite.gzwriteTU_fn_gz_zero :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_zero
theorem prog_fns_gz_write : prog.fns "gz_write" = some Zlib.Gzwrite.gzwriteTU_fn_gz_write :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_write
theorem prog_fns_gzwrite : prog.fns "gzwrite" = some Zlib.Gzwrite.gzwriteTU_fn_gzwrite :=
  h.base.prog_fns_eq ▸ prog0_fns_gzwrite
theorem prog_fns_gzfwrite : prog.fns "gzfwrite" = some Zlib.Gzwrite.gzwriteTU_fn_gzfwrite :=
  h.base.prog_fns_eq ▸ prog0_fns_gzfwrite
theorem prog_fns_gzputc : prog.fns "gzputc" = some Zlib.Gzwrite.gzwriteTU_fn_gzputc :=
  h.base.prog_fns_eq ▸ prog0_fns_gzputc
theorem prog_fns_gzputs : prog.fns "gzputs" = some Zlib.Gzwrite.gzwriteTU_fn_gzputs :=
  h.base.prog_fns_eq ▸ prog0_fns_gzputs
theorem prog_fns_gz_vacate : prog.fns "gz_vacate" = some Zlib.Gzwrite.gzwriteTU_fn_gz_vacate :=
  h.base.prog_fns_eq ▸ prog0_fns_gz_vacate
theorem prog_fns_gzvprintf : prog.fns "gzvprintf" = some Zlib.Gzwrite.gzwriteTU_fn_gzvprintf :=
  h.base.prog_fns_eq ▸ prog0_fns_gzvprintf
theorem prog_fns_gzprintf : prog.fns "gzprintf" = some Zlib.Gzwrite.gzwriteTU_fn_gzprintf :=
  h.base.prog_fns_eq ▸ prog0_fns_gzprintf
theorem prog_fns_gzflush : prog.fns "gzflush" = some Zlib.Gzwrite.gzwriteTU_fn_gzflush :=
  h.base.prog_fns_eq ▸ prog0_fns_gzflush
theorem prog_fns_gzsetparams : prog.fns "gzsetparams" = some Zlib.Gzwrite.gzwriteTU_fn_gzsetparams :=
  h.base.prog_fns_eq ▸ prog0_fns_gzsetparams
theorem prog_fns_gzclose_w : prog.fns "gzclose_w" = some Zlib.Gzwrite.gzwriteTU_fn_gzclose_w :=
  h.base.prog_fns_eq ▸ prog0_fns_gzclose_w
theorem prog_fns_memcpy : prog.fns "memcpy" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_memcpy
theorem prog_fns_memmove : prog.fns "memmove" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_memmove
theorem prog_fns_memset : prog.fns "memset" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_memset
theorem prog_fns_memcmp : prog.fns "memcmp" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_memcmp
theorem prog_fns_strlen : prog.fns "strlen" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_strlen
theorem prog_fns_memchr : prog.fns "memchr" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_memchr
theorem prog_fns_open : prog.fns "open" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_open
theorem prog_fns_close : prog.fns "close" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_close
theorem prog_fns_fcntl : prog.fns "fcntl" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_fcntl
theorem prog_fns_lseek : prog.fns "lseek" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_lseek
theorem prog_fns_lseek64 : prog.fns "lseek64" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_lseek64
theorem prog_fns_LSEEK : prog.fns "LSEEK" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_LSEEK
theorem prog_fns_read : prog.fns "read" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_read
theorem prog_fns_write : prog.fns "write" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_write
theorem prog_fns_strerror : prog.fns "strerror" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_strerror
theorem prog_fns_snprintf : prog.fns "snprintf" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_snprintf
theorem prog_fns_vsnprintf : prog.fns "vsnprintf" = none :=
  h.base.prog_fns_eq ▸ prog0_fns_vsnprintf

-- Wave 1 forwarded `prog.fnProtos` (33)
theorem prog_fnProtos_zlibVersion : prog.fnProtos "zlibVersion" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zlibVersion) := Zlib.Proof.prog_fnProtos_zlibVersion h.base
theorem prog_fnProtos_zlibCompileFlags : prog.fnProtos "zlibCompileFlags" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zlibCompileFlags) := Zlib.Proof.prog_fnProtos_zlibCompileFlags h.base
theorem prog_fnProtos_zError : prog.fnProtos "zError" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zError) := Zlib.Proof.prog_fnProtos_zError h.base
theorem prog_fnProtos_zcalloc : prog.fnProtos "zcalloc" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zcalloc) := Zlib.Proof.prog_fnProtos_zcalloc h.base
theorem prog_fnProtos_zcfree : prog.fnProtos "zcfree" = some (fnDefSig Zlib.Zutil.zutilTU_fn_zcfree) := Zlib.Proof.prog_fnProtos_zcfree h.base
theorem prog_fnProtos_compress2_z : prog.fnProtos "compress2_z" = some (fnDefSig Zlib.Compress.compressTU_fn_compress2_z) := Zlib.Proof.prog_fnProtos_compress2_z h.base
theorem prog_fnProtos_compress2 : prog.fnProtos "compress2" = some (fnDefSig Zlib.Compress.compressTU_fn_compress2) := Zlib.Proof.prog_fnProtos_compress2 h.base
theorem prog_fnProtos_compress_z : prog.fnProtos "compress_z" = some (fnDefSig Zlib.Compress.compressTU_fn_compress_z) := Zlib.Proof.prog_fnProtos_compress_z h.base
theorem prog_fnProtos_compress : prog.fnProtos "compress" = some (fnDefSig Zlib.Compress.compressTU_fn_compress) := Zlib.Proof.prog_fnProtos_compress h.base
theorem prog_fnProtos_compressBound_z : prog.fnProtos "compressBound_z" = some (fnDefSig Zlib.Compress.compressTU_fn_compressBound_z) := Zlib.Proof.prog_fnProtos_compressBound_z h.base
theorem prog_fnProtos_compressBound : prog.fnProtos "compressBound" = some (fnDefSig Zlib.Compress.compressTU_fn_compressBound) := Zlib.Proof.prog_fnProtos_compressBound h.base
theorem prog_fnProtos_adler32_z : prog.fnProtos "adler32_z" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_z) := Zlib.Proof.prog_fnProtos_adler32_z h.base
theorem prog_fnProtos_adler32 : prog.fnProtos "adler32" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32) := Zlib.Proof.prog_fnProtos_adler32 h.base
theorem prog_fnProtos_adler32_combine_ : prog.fnProtos "adler32_combine_" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_combine_) := Zlib.Proof.prog_fnProtos_adler32_combine_ h.base
theorem prog_fnProtos_adler32_combine : prog.fnProtos "adler32_combine" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_combine) := Zlib.Proof.prog_fnProtos_adler32_combine h.base
theorem prog_fnProtos_adler32_combine64 : prog.fnProtos "adler32_combine64" = some (fnDefSig Zlib.Adler32.adler32TU_fn_adler32_combine64) := Zlib.Proof.prog_fnProtos_adler32_combine64 h.base
theorem prog_fnProtos_byte_swap : prog.fnProtos "byte_swap" = some (fnDefSig Zlib.Crc32.crc32TU_fn_byte_swap) := Zlib.Proof.prog_fnProtos_byte_swap h.base
theorem prog_fnProtos_multmodp : prog.fnProtos "multmodp" = some (fnDefSig Zlib.Crc32.crc32TU_fn_multmodp) := Zlib.Proof.prog_fnProtos_multmodp h.base
theorem prog_fnProtos_x2nmodp : prog.fnProtos "x2nmodp" = some (fnDefSig Zlib.Crc32.crc32TU_fn_x2nmodp) := Zlib.Proof.prog_fnProtos_x2nmodp h.base
theorem prog_fnProtos_get_crc_table : prog.fnProtos "get_crc_table" = some (fnDefSig Zlib.Crc32.crc32TU_fn_get_crc_table) := Zlib.Proof.prog_fnProtos_get_crc_table h.base
theorem prog_fnProtos_crc_word : prog.fnProtos "crc_word" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc_word) := Zlib.Proof.prog_fnProtos_crc_word h.base
theorem prog_fnProtos_crc_word_big : prog.fnProtos "crc_word_big" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc_word_big) := Zlib.Proof.prog_fnProtos_crc_word_big h.base
theorem prog_fnProtos_crc32_braid : prog.fnProtos "crc32_braid" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_braid) := Zlib.Proof.prog_fnProtos_crc32_braid h.base
theorem prog_fnProtos_crc32_z : prog.fnProtos "crc32_z" = some crc32_zProtoSig := Zlib.Proof.prog_fnProtos_crc32_z h.base
theorem prog_fnProtos_crc32 : prog.fnProtos "crc32" = some crc32ProtoSig := Zlib.Proof.prog_fnProtos_crc32 h.base
theorem prog_fnProtos_crc32_combine_gen64 : prog.fnProtos "crc32_combine_gen64" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine_gen64) := Zlib.Proof.prog_fnProtos_crc32_combine_gen64 h.base
theorem prog_fnProtos_crc32_combine_gen : prog.fnProtos "crc32_combine_gen" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine_gen) := Zlib.Proof.prog_fnProtos_crc32_combine_gen h.base
theorem prog_fnProtos_crc32_combine_op : prog.fnProtos "crc32_combine_op" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine_op) := Zlib.Proof.prog_fnProtos_crc32_combine_op h.base
theorem prog_fnProtos_crc32_combine64 : prog.fnProtos "crc32_combine64" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine64) := Zlib.Proof.prog_fnProtos_crc32_combine64 h.base
theorem prog_fnProtos_crc32_combine : prog.fnProtos "crc32_combine" = some (fnDefSig Zlib.Crc32.crc32TU_fn_crc32_combine) := Zlib.Proof.prog_fnProtos_crc32_combine h.base
theorem prog_fnProtos_malloc : prog.fnProtos "malloc" = some (.ptr .void, [.int .u64], false) := Zlib.Proof.prog_fnProtos_malloc h.base
theorem prog_fnProtos_calloc : prog.fnProtos "calloc" = some (.ptr .void, [.int .u64, .int .u64], false) := Zlib.Proof.prog_fnProtos_calloc h.base
theorem prog_fnProtos_free : prog.fnProtos "free" = some (.void, [.ptr .void], false) := Zlib.Proof.prog_fnProtos_free h.base

-- Remaining `prog.fnProtos` (134 defined + 16 stdLibc + LSEEK)
theorem prog_fnProtos_gzclose : prog.fnProtos "gzclose" = some (fnDefSig Zlib.Gzclose.gzcloseTU_fn_gzclose) :=
  (congrFun h.base.prog_fnProtos_eq "gzclose").trans prog0_fnProtos_gzclose
theorem prog_fnProtos_uncompress2_z : prog.fnProtos "uncompress2_z" = some (fnDefSig Zlib.Uncompr.uncomprTU_fn_uncompress2_z) :=
  (congrFun h.base.prog_fnProtos_eq "uncompress2_z").trans prog0_fnProtos_uncompress2_z
theorem prog_fnProtos_uncompress2 : prog.fnProtos "uncompress2" = some (fnDefSig Zlib.Uncompr.uncomprTU_fn_uncompress2) :=
  (congrFun h.base.prog_fnProtos_eq "uncompress2").trans prog0_fnProtos_uncompress2
theorem prog_fnProtos_uncompress_z : prog.fnProtos "uncompress_z" = some (fnDefSig Zlib.Uncompr.uncomprTU_fn_uncompress_z) :=
  (congrFun h.base.prog_fnProtos_eq "uncompress_z").trans prog0_fnProtos_uncompress_z
theorem prog_fnProtos_uncompress : prog.fnProtos "uncompress" = some (fnDefSig Zlib.Uncompr.uncomprTU_fn_uncompress) :=
  (congrFun h.base.prog_fnProtos_eq "uncompress").trans prog0_fnProtos_uncompress
theorem prog_fnProtos_inflate_table : prog.fnProtos "inflate_table" = some (fnDefSig Zlib.Inftrees.inftreesTU_fn_inflate_table) :=
  (congrFun h.base.prog_fnProtos_eq "inflate_table").trans prog0_fnProtos_inflate_table
theorem prog_fnProtos_inflate_fixed : prog.fnProtos "inflate_fixed" = some (fnDefSig Zlib.Inftrees.inftreesTU_fn_inflate_fixed) :=
  (congrFun h.base.prog_fnProtos_eq "inflate_fixed").trans prog0_fnProtos_inflate_fixed
theorem prog_fnProtos_load64 : prog.fnProtos "load64" = some (fnDefSig Zlib.Inffast.inffastTU_fn_load64) :=
  (congrFun h.base.prog_fnProtos_eq "load64").trans prog0_fnProtos_load64
theorem prog_fnProtos_copy_back : prog.fnProtos "copy_back" = some (fnDefSig Zlib.Inffast.inffastTU_fn_copy_back) :=
  (congrFun h.base.prog_fnProtos_eq "copy_back").trans prog0_fnProtos_copy_back
theorem prog_fnProtos_inflate_fast : prog.fnProtos "inflate_fast" = some (fnDefSig Zlib.Inffast.inffastTU_fn_inflate_fast) :=
  (congrFun h.base.prog_fnProtos_eq "inflate_fast").trans prog0_fnProtos_inflate_fast
theorem prog_fnProtos_bi_reverse : prog.fnProtos "bi_reverse" = some (fnDefSig Zlib.Trees.treesTU_fn_bi_reverse) :=
  (congrFun h.base.prog_fnProtos_eq "bi_reverse").trans prog0_fnProtos_bi_reverse
theorem prog_fnProtos_bi_flush : prog.fnProtos "bi_flush" = some (fnDefSig Zlib.Trees.treesTU_fn_bi_flush) :=
  (congrFun h.base.prog_fnProtos_eq "bi_flush").trans prog0_fnProtos_bi_flush
theorem prog_fnProtos_bi_windup : prog.fnProtos "bi_windup" = some (fnDefSig Zlib.Trees.treesTU_fn_bi_windup) :=
  (congrFun h.base.prog_fnProtos_eq "bi_windup").trans prog0_fnProtos_bi_windup
theorem prog_fnProtos_gen_codes : prog.fnProtos "gen_codes" = some (fnDefSig Zlib.Trees.treesTU_fn_gen_codes) :=
  (congrFun h.base.prog_fnProtos_eq "gen_codes").trans prog0_fnProtos_gen_codes
theorem prog_fnProtos_tr_static_init : prog.fnProtos "tr_static_init" = some (fnDefSig Zlib.Trees.treesTU_fn_tr_static_init) :=
  (congrFun h.base.prog_fnProtos_eq "tr_static_init").trans prog0_fnProtos_tr_static_init
theorem prog_fnProtos_init_block : prog.fnProtos "init_block" = some (fnDefSig Zlib.Trees.treesTU_fn_init_block) :=
  (congrFun h.base.prog_fnProtos_eq "init_block").trans prog0_fnProtos_init_block
theorem prog_fnProtos__tr_init : prog.fnProtos "_tr_init" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_init) :=
  (congrFun h.base.prog_fnProtos_eq "_tr_init").trans prog0_fnProtos__tr_init
theorem prog_fnProtos_pqdownheap : prog.fnProtos "pqdownheap" = some (fnDefSig Zlib.Trees.treesTU_fn_pqdownheap) :=
  (congrFun h.base.prog_fnProtos_eq "pqdownheap").trans prog0_fnProtos_pqdownheap
theorem prog_fnProtos_gen_bitlen : prog.fnProtos "gen_bitlen" = some (fnDefSig Zlib.Trees.treesTU_fn_gen_bitlen) :=
  (congrFun h.base.prog_fnProtos_eq "gen_bitlen").trans prog0_fnProtos_gen_bitlen
theorem prog_fnProtos_build_tree : prog.fnProtos "build_tree" = some (fnDefSig Zlib.Trees.treesTU_fn_build_tree) :=
  (congrFun h.base.prog_fnProtos_eq "build_tree").trans prog0_fnProtos_build_tree
theorem prog_fnProtos_scan_tree : prog.fnProtos "scan_tree" = some (fnDefSig Zlib.Trees.treesTU_fn_scan_tree) :=
  (congrFun h.base.prog_fnProtos_eq "scan_tree").trans prog0_fnProtos_scan_tree
theorem prog_fnProtos_send_tree : prog.fnProtos "send_tree" = some (fnDefSig Zlib.Trees.treesTU_fn_send_tree) :=
  (congrFun h.base.prog_fnProtos_eq "send_tree").trans prog0_fnProtos_send_tree
theorem prog_fnProtos_build_bl_tree : prog.fnProtos "build_bl_tree" = some (fnDefSig Zlib.Trees.treesTU_fn_build_bl_tree) :=
  (congrFun h.base.prog_fnProtos_eq "build_bl_tree").trans prog0_fnProtos_build_bl_tree
theorem prog_fnProtos_send_all_trees : prog.fnProtos "send_all_trees" = some (fnDefSig Zlib.Trees.treesTU_fn_send_all_trees) :=
  (congrFun h.base.prog_fnProtos_eq "send_all_trees").trans prog0_fnProtos_send_all_trees
theorem prog_fnProtos__tr_stored_block : prog.fnProtos "_tr_stored_block" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_stored_block) :=
  (congrFun h.base.prog_fnProtos_eq "_tr_stored_block").trans prog0_fnProtos__tr_stored_block
theorem prog_fnProtos__tr_flush_bits : prog.fnProtos "_tr_flush_bits" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_flush_bits) :=
  (congrFun h.base.prog_fnProtos_eq "_tr_flush_bits").trans prog0_fnProtos__tr_flush_bits
theorem prog_fnProtos__tr_align : prog.fnProtos "_tr_align" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_align) :=
  (congrFun h.base.prog_fnProtos_eq "_tr_align").trans prog0_fnProtos__tr_align
theorem prog_fnProtos_compress_block : prog.fnProtos "compress_block" = some (fnDefSig Zlib.Trees.treesTU_fn_compress_block) :=
  (congrFun h.base.prog_fnProtos_eq "compress_block").trans prog0_fnProtos_compress_block
theorem prog_fnProtos_detect_data_type : prog.fnProtos "detect_data_type" = some (fnDefSig Zlib.Trees.treesTU_fn_detect_data_type) :=
  (congrFun h.base.prog_fnProtos_eq "detect_data_type").trans prog0_fnProtos_detect_data_type
theorem prog_fnProtos__tr_flush_block : prog.fnProtos "_tr_flush_block" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_flush_block) :=
  (congrFun h.base.prog_fnProtos_eq "_tr_flush_block").trans prog0_fnProtos__tr_flush_block
theorem prog_fnProtos__tr_tally : prog.fnProtos "_tr_tally" = some (fnDefSig Zlib.Trees.treesTU_fn__tr_tally) :=
  (congrFun h.base.prog_fnProtos_eq "_tr_tally").trans prog0_fnProtos__tr_tally
theorem prog_fnProtos_inflateBackInit_ : prog.fnProtos "inflateBackInit_" = some (fnDefSig Zlib.Infback.infbackTU_fn_inflateBackInit_) :=
  (congrFun h.base.prog_fnProtos_eq "inflateBackInit_").trans prog0_fnProtos_inflateBackInit_
theorem prog_fnProtos_inflateBack : prog.fnProtos "inflateBack" = some (fnDefSig Zlib.Infback.infbackTU_fn_inflateBack) :=
  (congrFun h.base.prog_fnProtos_eq "inflateBack").trans prog0_fnProtos_inflateBack
theorem prog_fnProtos_inflateBackEnd : prog.fnProtos "inflateBackEnd" = some (fnDefSig Zlib.Infback.infbackTU_fn_inflateBackEnd) :=
  (congrFun h.base.prog_fnProtos_eq "inflateBackEnd").trans prog0_fnProtos_inflateBackEnd
theorem prog_fnProtos_inflateStateCheck : prog.fnProtos "inflateStateCheck" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateStateCheck) :=
  (congrFun h.base.prog_fnProtos_eq "inflateStateCheck").trans prog0_fnProtos_inflateStateCheck
theorem prog_fnProtos_inflateResetKeep : prog.fnProtos "inflateResetKeep" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateResetKeep) :=
  (congrFun h.base.prog_fnProtos_eq "inflateResetKeep").trans prog0_fnProtos_inflateResetKeep
theorem prog_fnProtos_inflateReset : prog.fnProtos "inflateReset" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateReset) :=
  (congrFun h.base.prog_fnProtos_eq "inflateReset").trans prog0_fnProtos_inflateReset
theorem prog_fnProtos_inflateReset2 : prog.fnProtos "inflateReset2" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateReset2) :=
  (congrFun h.base.prog_fnProtos_eq "inflateReset2").trans prog0_fnProtos_inflateReset2
theorem prog_fnProtos_inflateInit2_ : prog.fnProtos "inflateInit2_" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateInit2_) :=
  (congrFun h.base.prog_fnProtos_eq "inflateInit2_").trans prog0_fnProtos_inflateInit2_
theorem prog_fnProtos_inflateInit_ : prog.fnProtos "inflateInit_" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateInit_) :=
  (congrFun h.base.prog_fnProtos_eq "inflateInit_").trans prog0_fnProtos_inflateInit_
theorem prog_fnProtos_inflatePrime : prog.fnProtos "inflatePrime" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflatePrime) :=
  (congrFun h.base.prog_fnProtos_eq "inflatePrime").trans prog0_fnProtos_inflatePrime
theorem prog_fnProtos_updatewindow : prog.fnProtos "updatewindow" = some (fnDefSig Zlib.Inflate.inflateTU_fn_updatewindow) :=
  (congrFun h.base.prog_fnProtos_eq "updatewindow").trans prog0_fnProtos_updatewindow
theorem prog_fnProtos_inflate : prog.fnProtos "inflate" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflate) :=
  (congrFun h.base.prog_fnProtos_eq "inflate").trans prog0_fnProtos_inflate
theorem prog_fnProtos_inflateEnd : prog.fnProtos "inflateEnd" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateEnd) :=
  (congrFun h.base.prog_fnProtos_eq "inflateEnd").trans prog0_fnProtos_inflateEnd
theorem prog_fnProtos_inflateGetDictionary : prog.fnProtos "inflateGetDictionary" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateGetDictionary) :=
  (congrFun h.base.prog_fnProtos_eq "inflateGetDictionary").trans prog0_fnProtos_inflateGetDictionary
theorem prog_fnProtos_inflateSetDictionary : prog.fnProtos "inflateSetDictionary" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateSetDictionary) :=
  (congrFun h.base.prog_fnProtos_eq "inflateSetDictionary").trans prog0_fnProtos_inflateSetDictionary
theorem prog_fnProtos_inflateGetHeader : prog.fnProtos "inflateGetHeader" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateGetHeader) :=
  (congrFun h.base.prog_fnProtos_eq "inflateGetHeader").trans prog0_fnProtos_inflateGetHeader
theorem prog_fnProtos_syncsearch : prog.fnProtos "syncsearch" = some (fnDefSig Zlib.Inflate.inflateTU_fn_syncsearch) :=
  (congrFun h.base.prog_fnProtos_eq "syncsearch").trans prog0_fnProtos_syncsearch
theorem prog_fnProtos_inflateSync : prog.fnProtos "inflateSync" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateSync) :=
  (congrFun h.base.prog_fnProtos_eq "inflateSync").trans prog0_fnProtos_inflateSync
theorem prog_fnProtos_inflateSyncPoint : prog.fnProtos "inflateSyncPoint" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateSyncPoint) :=
  (congrFun h.base.prog_fnProtos_eq "inflateSyncPoint").trans prog0_fnProtos_inflateSyncPoint
theorem prog_fnProtos_inflateCopy : prog.fnProtos "inflateCopy" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateCopy) :=
  (congrFun h.base.prog_fnProtos_eq "inflateCopy").trans prog0_fnProtos_inflateCopy
theorem prog_fnProtos_inflateUndermine : prog.fnProtos "inflateUndermine" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateUndermine) :=
  (congrFun h.base.prog_fnProtos_eq "inflateUndermine").trans prog0_fnProtos_inflateUndermine
theorem prog_fnProtos_inflateValidate : prog.fnProtos "inflateValidate" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateValidate) :=
  (congrFun h.base.prog_fnProtos_eq "inflateValidate").trans prog0_fnProtos_inflateValidate
theorem prog_fnProtos_inflateMark : prog.fnProtos "inflateMark" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateMark) :=
  (congrFun h.base.prog_fnProtos_eq "inflateMark").trans prog0_fnProtos_inflateMark
theorem prog_fnProtos_inflateCodesUsed : prog.fnProtos "inflateCodesUsed" = some (fnDefSig Zlib.Inflate.inflateTU_fn_inflateCodesUsed) :=
  (congrFun h.base.prog_fnProtos_eq "inflateCodesUsed").trans prog0_fnProtos_inflateCodesUsed
theorem prog_fnProtos_slide_hash : prog.fnProtos "slide_hash" = some (fnDefSig Zlib.Deflate.deflateTU_fn_slide_hash) :=
  (congrFun h.base.prog_fnProtos_eq "slide_hash").trans prog0_fnProtos_slide_hash
theorem prog_fnProtos_read_buf : prog.fnProtos "read_buf" = some (fnDefSig Zlib.Deflate.deflateTU_fn_read_buf) :=
  (congrFun h.base.prog_fnProtos_eq "read_buf").trans prog0_fnProtos_read_buf
theorem prog_fnProtos_fill_window : prog.fnProtos "fill_window" = some (fnDefSig Zlib.Deflate.deflateTU_fn_fill_window) :=
  (congrFun h.base.prog_fnProtos_eq "fill_window").trans prog0_fnProtos_fill_window
theorem prog_fnProtos_deflateInit_ : prog.fnProtos "deflateInit_" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateInit_) :=
  (congrFun h.base.prog_fnProtos_eq "deflateInit_").trans prog0_fnProtos_deflateInit_
theorem prog_fnProtos_deflateInit2_ : prog.fnProtos "deflateInit2_" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateInit2_) :=
  (congrFun h.base.prog_fnProtos_eq "deflateInit2_").trans prog0_fnProtos_deflateInit2_
theorem prog_fnProtos_deflateStateCheck : prog.fnProtos "deflateStateCheck" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateStateCheck) :=
  (congrFun h.base.prog_fnProtos_eq "deflateStateCheck").trans prog0_fnProtos_deflateStateCheck
theorem prog_fnProtos_deflateSetDictionary : prog.fnProtos "deflateSetDictionary" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateSetDictionary) :=
  (congrFun h.base.prog_fnProtos_eq "deflateSetDictionary").trans prog0_fnProtos_deflateSetDictionary
theorem prog_fnProtos_deflateGetDictionary : prog.fnProtos "deflateGetDictionary" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateGetDictionary) :=
  (congrFun h.base.prog_fnProtos_eq "deflateGetDictionary").trans prog0_fnProtos_deflateGetDictionary
theorem prog_fnProtos_deflateResetKeep : prog.fnProtos "deflateResetKeep" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateResetKeep) :=
  (congrFun h.base.prog_fnProtos_eq "deflateResetKeep").trans prog0_fnProtos_deflateResetKeep
theorem prog_fnProtos_lm_init : prog.fnProtos "lm_init" = some (fnDefSig Zlib.Deflate.deflateTU_fn_lm_init) :=
  (congrFun h.base.prog_fnProtos_eq "lm_init").trans prog0_fnProtos_lm_init
theorem prog_fnProtos_deflateReset : prog.fnProtos "deflateReset" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateReset) :=
  (congrFun h.base.prog_fnProtos_eq "deflateReset").trans prog0_fnProtos_deflateReset
theorem prog_fnProtos_deflateSetHeader : prog.fnProtos "deflateSetHeader" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateSetHeader) :=
  (congrFun h.base.prog_fnProtos_eq "deflateSetHeader").trans prog0_fnProtos_deflateSetHeader
theorem prog_fnProtos_deflatePending : prog.fnProtos "deflatePending" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflatePending) :=
  (congrFun h.base.prog_fnProtos_eq "deflatePending").trans prog0_fnProtos_deflatePending
theorem prog_fnProtos_deflateUsed : prog.fnProtos "deflateUsed" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateUsed) :=
  (congrFun h.base.prog_fnProtos_eq "deflateUsed").trans prog0_fnProtos_deflateUsed
theorem prog_fnProtos_deflatePrime : prog.fnProtos "deflatePrime" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflatePrime) :=
  (congrFun h.base.prog_fnProtos_eq "deflatePrime").trans prog0_fnProtos_deflatePrime
theorem prog_fnProtos_deflateParams : prog.fnProtos "deflateParams" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateParams) :=
  (congrFun h.base.prog_fnProtos_eq "deflateParams").trans prog0_fnProtos_deflateParams
theorem prog_fnProtos_deflateTune : prog.fnProtos "deflateTune" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateTune) :=
  (congrFun h.base.prog_fnProtos_eq "deflateTune").trans prog0_fnProtos_deflateTune
theorem prog_fnProtos_deflateBound_z : prog.fnProtos "deflateBound_z" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateBound_z) :=
  (congrFun h.base.prog_fnProtos_eq "deflateBound_z").trans prog0_fnProtos_deflateBound_z
theorem prog_fnProtos_deflateBound : prog.fnProtos "deflateBound" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateBound) :=
  (congrFun h.base.prog_fnProtos_eq "deflateBound").trans prog0_fnProtos_deflateBound
theorem prog_fnProtos_putShortMSB : prog.fnProtos "putShortMSB" = some (fnDefSig Zlib.Deflate.deflateTU_fn_putShortMSB) :=
  (congrFun h.base.prog_fnProtos_eq "putShortMSB").trans prog0_fnProtos_putShortMSB
theorem prog_fnProtos_flush_pending : prog.fnProtos "flush_pending" = some (fnDefSig Zlib.Deflate.deflateTU_fn_flush_pending) :=
  (congrFun h.base.prog_fnProtos_eq "flush_pending").trans prog0_fnProtos_flush_pending
theorem prog_fnProtos_deflate : prog.fnProtos "deflate" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate) :=
  (congrFun h.base.prog_fnProtos_eq "deflate").trans prog0_fnProtos_deflate
theorem prog_fnProtos_deflateEnd : prog.fnProtos "deflateEnd" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateEnd) :=
  (congrFun h.base.prog_fnProtos_eq "deflateEnd").trans prog0_fnProtos_deflateEnd
theorem prog_fnProtos_deflateCopy : prog.fnProtos "deflateCopy" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflateCopy) :=
  (congrFun h.base.prog_fnProtos_eq "deflateCopy").trans prog0_fnProtos_deflateCopy
theorem prog_fnProtos_longest_match : prog.fnProtos "longest_match" = some (fnDefSig Zlib.Deflate.deflateTU_fn_longest_match) :=
  (congrFun h.base.prog_fnProtos_eq "longest_match").trans prog0_fnProtos_longest_match
theorem prog_fnProtos_deflate_stored : prog.fnProtos "deflate_stored" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate_stored) :=
  (congrFun h.base.prog_fnProtos_eq "deflate_stored").trans prog0_fnProtos_deflate_stored
theorem prog_fnProtos_deflate_fast : prog.fnProtos "deflate_fast" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate_fast) :=
  (congrFun h.base.prog_fnProtos_eq "deflate_fast").trans prog0_fnProtos_deflate_fast
theorem prog_fnProtos_deflate_slow : prog.fnProtos "deflate_slow" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate_slow) :=
  (congrFun h.base.prog_fnProtos_eq "deflate_slow").trans prog0_fnProtos_deflate_slow
theorem prog_fnProtos_deflate_rle : prog.fnProtos "deflate_rle" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate_rle) :=
  (congrFun h.base.prog_fnProtos_eq "deflate_rle").trans prog0_fnProtos_deflate_rle
theorem prog_fnProtos_deflate_huff : prog.fnProtos "deflate_huff" = some (fnDefSig Zlib.Deflate.deflateTU_fn_deflate_huff) :=
  (congrFun h.base.prog_fnProtos_eq "deflate_huff").trans prog0_fnProtos_deflate_huff
theorem prog_fnProtos_gz_reset : prog.fnProtos "gz_reset" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gz_reset) :=
  (congrFun h.base.prog_fnProtos_eq "gz_reset").trans prog0_fnProtos_gz_reset
theorem prog_fnProtos_gz_open : prog.fnProtos "gz_open" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gz_open) :=
  (congrFun h.base.prog_fnProtos_eq "gz_open").trans prog0_fnProtos_gz_open
theorem prog_fnProtos_gzopen : prog.fnProtos "gzopen" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzopen) :=
  (congrFun h.base.prog_fnProtos_eq "gzopen").trans prog0_fnProtos_gzopen
theorem prog_fnProtos_gzopen64 : prog.fnProtos "gzopen64" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzopen64) :=
  (congrFun h.base.prog_fnProtos_eq "gzopen64").trans prog0_fnProtos_gzopen64
theorem prog_fnProtos_gzdopen : prog.fnProtos "gzdopen" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzdopen) :=
  (congrFun h.base.prog_fnProtos_eq "gzdopen").trans prog0_fnProtos_gzdopen
theorem prog_fnProtos_gzbuffer : prog.fnProtos "gzbuffer" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzbuffer) :=
  (congrFun h.base.prog_fnProtos_eq "gzbuffer").trans prog0_fnProtos_gzbuffer
theorem prog_fnProtos_gzrewind : prog.fnProtos "gzrewind" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzrewind) :=
  (congrFun h.base.prog_fnProtos_eq "gzrewind").trans prog0_fnProtos_gzrewind
theorem prog_fnProtos_gzseek64 : prog.fnProtos "gzseek64" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzseek64) :=
  (congrFun h.base.prog_fnProtos_eq "gzseek64").trans prog0_fnProtos_gzseek64
theorem prog_fnProtos_gzseek : prog.fnProtos "gzseek" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzseek) :=
  (congrFun h.base.prog_fnProtos_eq "gzseek").trans prog0_fnProtos_gzseek
theorem prog_fnProtos_gztell64 : prog.fnProtos "gztell64" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gztell64) :=
  (congrFun h.base.prog_fnProtos_eq "gztell64").trans prog0_fnProtos_gztell64
theorem prog_fnProtos_gztell : prog.fnProtos "gztell" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gztell) :=
  (congrFun h.base.prog_fnProtos_eq "gztell").trans prog0_fnProtos_gztell
theorem prog_fnProtos_gzoffset64 : prog.fnProtos "gzoffset64" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzoffset64) :=
  (congrFun h.base.prog_fnProtos_eq "gzoffset64").trans prog0_fnProtos_gzoffset64
theorem prog_fnProtos_gzoffset : prog.fnProtos "gzoffset" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzoffset) :=
  (congrFun h.base.prog_fnProtos_eq "gzoffset").trans prog0_fnProtos_gzoffset
theorem prog_fnProtos_gzeof : prog.fnProtos "gzeof" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzeof) :=
  (congrFun h.base.prog_fnProtos_eq "gzeof").trans prog0_fnProtos_gzeof
theorem prog_fnProtos_gzerror : prog.fnProtos "gzerror" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzerror) :=
  (congrFun h.base.prog_fnProtos_eq "gzerror").trans prog0_fnProtos_gzerror
theorem prog_fnProtos_gzclearerr : prog.fnProtos "gzclearerr" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gzclearerr) :=
  (congrFun h.base.prog_fnProtos_eq "gzclearerr").trans prog0_fnProtos_gzclearerr
theorem prog_fnProtos_gz_error : prog.fnProtos "gz_error" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gz_error) :=
  (congrFun h.base.prog_fnProtos_eq "gz_error").trans prog0_fnProtos_gz_error
theorem prog_fnProtos_gz_intmax : prog.fnProtos "gz_intmax" = some (fnDefSig Zlib.Gzlib.gzlibTU_fn_gz_intmax) :=
  (congrFun h.base.prog_fnProtos_eq "gz_intmax").trans prog0_fnProtos_gz_intmax
theorem prog_fnProtos_gz_load : prog.fnProtos "gz_load" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_load) :=
  (congrFun h.base.prog_fnProtos_eq "gz_load").trans prog0_fnProtos_gz_load
theorem prog_fnProtos_gz_avail : prog.fnProtos "gz_avail" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_avail) :=
  (congrFun h.base.prog_fnProtos_eq "gz_avail").trans prog0_fnProtos_gz_avail
theorem prog_fnProtos_gz_room : prog.fnProtos "gz_room" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_room) :=
  (congrFun h.base.prog_fnProtos_eq "gz_room").trans prog0_fnProtos_gz_room
theorem prog_fnProtos_gz_look : prog.fnProtos "gz_look" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_look) :=
  (congrFun h.base.prog_fnProtos_eq "gz_look").trans prog0_fnProtos_gz_look
theorem prog_fnProtos_gz_decomp : prog.fnProtos "gz_decomp" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_decomp) :=
  (congrFun h.base.prog_fnProtos_eq "gz_decomp").trans prog0_fnProtos_gz_decomp
theorem prog_fnProtos_gz_fetch : prog.fnProtos "gz_fetch" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_fetch) :=
  (congrFun h.base.prog_fnProtos_eq "gz_fetch").trans prog0_fnProtos_gz_fetch
theorem prog_fnProtos_gz_skip_have : prog.fnProtos "gz_skip_have" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_skip_have) :=
  (congrFun h.base.prog_fnProtos_eq "gz_skip_have").trans prog0_fnProtos_gz_skip_have
theorem prog_fnProtos_gz_skip : prog.fnProtos "gz_skip" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_skip) :=
  (congrFun h.base.prog_fnProtos_eq "gz_skip").trans prog0_fnProtos_gz_skip
theorem prog_fnProtos_gz_read : prog.fnProtos "gz_read" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gz_read) :=
  (congrFun h.base.prog_fnProtos_eq "gz_read").trans prog0_fnProtos_gz_read
theorem prog_fnProtos_gzread : prog.fnProtos "gzread" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzread) :=
  (congrFun h.base.prog_fnProtos_eq "gzread").trans prog0_fnProtos_gzread
theorem prog_fnProtos_gzfread : prog.fnProtos "gzfread" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzfread) :=
  (congrFun h.base.prog_fnProtos_eq "gzfread").trans prog0_fnProtos_gzfread
theorem prog_fnProtos_gzgetc : prog.fnProtos "gzgetc" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzgetc) :=
  (congrFun h.base.prog_fnProtos_eq "gzgetc").trans prog0_fnProtos_gzgetc
theorem prog_fnProtos_gzgetc_ : prog.fnProtos "gzgetc_" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzgetc_) :=
  (congrFun h.base.prog_fnProtos_eq "gzgetc_").trans prog0_fnProtos_gzgetc_
theorem prog_fnProtos_gzungetc : prog.fnProtos "gzungetc" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzungetc) :=
  (congrFun h.base.prog_fnProtos_eq "gzungetc").trans prog0_fnProtos_gzungetc
theorem prog_fnProtos_gzgets : prog.fnProtos "gzgets" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzgets) :=
  (congrFun h.base.prog_fnProtos_eq "gzgets").trans prog0_fnProtos_gzgets
theorem prog_fnProtos_gzdirect : prog.fnProtos "gzdirect" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzdirect) :=
  (congrFun h.base.prog_fnProtos_eq "gzdirect").trans prog0_fnProtos_gzdirect
theorem prog_fnProtos_gzclose_r : prog.fnProtos "gzclose_r" = some (fnDefSig Zlib.Gzread.gzreadTU_fn_gzclose_r) :=
  (congrFun h.base.prog_fnProtos_eq "gzclose_r").trans prog0_fnProtos_gzclose_r
theorem prog_fnProtos_gz_init : prog.fnProtos "gz_init" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gz_init) :=
  (congrFun h.base.prog_fnProtos_eq "gz_init").trans prog0_fnProtos_gz_init
theorem prog_fnProtos_gz_comp : prog.fnProtos "gz_comp" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gz_comp) :=
  (congrFun h.base.prog_fnProtos_eq "gz_comp").trans prog0_fnProtos_gz_comp
theorem prog_fnProtos_gz_zero : prog.fnProtos "gz_zero" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gz_zero) :=
  (congrFun h.base.prog_fnProtos_eq "gz_zero").trans prog0_fnProtos_gz_zero
theorem prog_fnProtos_gz_write : prog.fnProtos "gz_write" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gz_write) :=
  (congrFun h.base.prog_fnProtos_eq "gz_write").trans prog0_fnProtos_gz_write
theorem prog_fnProtos_gzwrite : prog.fnProtos "gzwrite" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzwrite) :=
  (congrFun h.base.prog_fnProtos_eq "gzwrite").trans prog0_fnProtos_gzwrite
theorem prog_fnProtos_gzfwrite : prog.fnProtos "gzfwrite" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzfwrite) :=
  (congrFun h.base.prog_fnProtos_eq "gzfwrite").trans prog0_fnProtos_gzfwrite
theorem prog_fnProtos_gzputc : prog.fnProtos "gzputc" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzputc) :=
  (congrFun h.base.prog_fnProtos_eq "gzputc").trans prog0_fnProtos_gzputc
theorem prog_fnProtos_gzputs : prog.fnProtos "gzputs" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzputs) :=
  (congrFun h.base.prog_fnProtos_eq "gzputs").trans prog0_fnProtos_gzputs
theorem prog_fnProtos_gz_vacate : prog.fnProtos "gz_vacate" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gz_vacate) :=
  (congrFun h.base.prog_fnProtos_eq "gz_vacate").trans prog0_fnProtos_gz_vacate
theorem prog_fnProtos_gzvprintf : prog.fnProtos "gzvprintf" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzvprintf) :=
  (congrFun h.base.prog_fnProtos_eq "gzvprintf").trans prog0_fnProtos_gzvprintf
theorem prog_fnProtos_gzprintf : prog.fnProtos "gzprintf" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzprintf) :=
  (congrFun h.base.prog_fnProtos_eq "gzprintf").trans prog0_fnProtos_gzprintf
theorem prog_fnProtos_gzflush : prog.fnProtos "gzflush" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzflush) :=
  (congrFun h.base.prog_fnProtos_eq "gzflush").trans prog0_fnProtos_gzflush
theorem prog_fnProtos_gzsetparams : prog.fnProtos "gzsetparams" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzsetparams) :=
  (congrFun h.base.prog_fnProtos_eq "gzsetparams").trans prog0_fnProtos_gzsetparams
theorem prog_fnProtos_gzclose_w : prog.fnProtos "gzclose_w" = some (fnDefSig Zlib.Gzwrite.gzwriteTU_fn_gzclose_w) :=
  (congrFun h.base.prog_fnProtos_eq "gzclose_w").trans prog0_fnProtos_gzclose_w
theorem prog_fnProtos_memcpy : prog.fnProtos "memcpy" = some (.ptr .void, [.ptr .void, .ptr (.const_ .void), .int .u64], false) :=
  (congrFun h.base.prog_fnProtos_eq "memcpy").trans prog0_fnProtos_memcpy
theorem prog_fnProtos_memmove : prog.fnProtos "memmove" = some (.ptr .void, [.ptr .void, .ptr (.const_ .void), .int .u64], false) :=
  (congrFun h.base.prog_fnProtos_eq "memmove").trans prog0_fnProtos_memmove
theorem prog_fnProtos_memset : prog.fnProtos "memset" = some (.ptr .void, [.ptr .void, .int .i32, .int .u64], false) :=
  (congrFun h.base.prog_fnProtos_eq "memset").trans prog0_fnProtos_memset
theorem prog_fnProtos_memcmp : prog.fnProtos "memcmp" = some (.int .i32, [.ptr (.const_ .void), .ptr (.const_ .void), .int .u64], false) :=
  (congrFun h.base.prog_fnProtos_eq "memcmp").trans prog0_fnProtos_memcmp
theorem prog_fnProtos_strlen : prog.fnProtos "strlen" = some (.int .u64, [.ptr (.const_ (.int .i8))], false) :=
  (congrFun h.base.prog_fnProtos_eq "strlen").trans prog0_fnProtos_strlen
theorem prog_fnProtos_memchr : prog.fnProtos "memchr" = some (.ptr .void, [.ptr (.const_ .void), .int .i32, .int .u64], false) :=
  (congrFun h.base.prog_fnProtos_eq "memchr").trans prog0_fnProtos_memchr
theorem prog_fnProtos_open : prog.fnProtos "open" = some (.int .i32, [.ptr (.const_ (.int .i8)), .int .i32], true) :=
  (congrFun h.base.prog_fnProtos_eq "open").trans prog0_fnProtos_open
theorem prog_fnProtos_close : prog.fnProtos "close" = some (.int .i32, [.int .i32], false) :=
  (congrFun h.base.prog_fnProtos_eq "close").trans prog0_fnProtos_close
theorem prog_fnProtos_fcntl : prog.fnProtos "fcntl" = some (.int .i32, [.int .i32, .int .i32], true) :=
  (congrFun h.base.prog_fnProtos_eq "fcntl").trans prog0_fnProtos_fcntl
theorem prog_fnProtos_lseek : prog.fnProtos "lseek" = some (.int .i64, [.int .i32, .int .i64, .int .i32], false) :=
  (congrFun h.base.prog_fnProtos_eq "lseek").trans prog0_fnProtos_lseek
theorem prog_fnProtos_lseek64 : prog.fnProtos "lseek64" = some (.int .i64, [.int .i32, .int .i64, .int .i32], false) :=
  (congrFun h.base.prog_fnProtos_eq "lseek64").trans prog0_fnProtos_lseek64
theorem prog_fnProtos_read : prog.fnProtos "read" = some (.int .i64, [.int .i32, .ptr .void, .int .u64], false) :=
  (congrFun h.base.prog_fnProtos_eq "read").trans prog0_fnProtos_read
theorem prog_fnProtos_write : prog.fnProtos "write" = some (.int .i64, [.int .i32, .ptr (.const_ .void), .int .u64], false) :=
  (congrFun h.base.prog_fnProtos_eq "write").trans prog0_fnProtos_write
theorem prog_fnProtos_strerror : prog.fnProtos "strerror" = some (.ptr (.int .i8), [.int .i32], false) :=
  (congrFun h.base.prog_fnProtos_eq "strerror").trans prog0_fnProtos_strerror
theorem prog_fnProtos_snprintf : prog.fnProtos "snprintf" = some (.int .i32, [.ptr (.int .i8), .int .u64, .ptr (.const_ (.int .i8))], true) :=
  (congrFun h.base.prog_fnProtos_eq "snprintf").trans prog0_fnProtos_snprintf
theorem prog_fnProtos_vsnprintf : prog.fnProtos "vsnprintf" = some (.int .i32, [.ptr (.int .i8), .int .u64, .ptr (.const_ (.int .i8)), .vaList], false) :=
  (congrFun h.base.prog_fnProtos_eq "vsnprintf").trans prog0_fnProtos_vsnprintf
theorem prog_fnProtos_LSEEK : prog.fnProtos "LSEEK" = some (.int .i64, [.int .i32, .int .i64, .int .i32], false) :=
  (congrFun h.base.prog_fnProtos_eq "LSEEK").trans prog0_fnProtos_lseek64

-- Wave 1 forwarded `prog.fnStatics` (30)
theorem prog_fnStatics_zlibVersion : prog.fnStatics "zlibVersion" = [] := Zlib.Proof.prog_fnStatics_zlibVersion h.base
theorem prog_fnStatics_zlibCompileFlags : prog.fnStatics "zlibCompileFlags" = [] := Zlib.Proof.prog_fnStatics_zlibCompileFlags h.base
theorem prog_fnStatics_zError : prog.fnStatics "zError" = [] := Zlib.Proof.prog_fnStatics_zError h.base
theorem prog_fnStatics_zcalloc : prog.fnStatics "zcalloc" = [] := Zlib.Proof.prog_fnStatics_zcalloc h.base
theorem prog_fnStatics_zcfree : prog.fnStatics "zcfree" = [] := Zlib.Proof.prog_fnStatics_zcfree h.base
theorem prog_fnStatics_compress2_z : prog.fnStatics "compress2_z" = [] := Zlib.Proof.prog_fnStatics_compress2_z h.base
theorem prog_fnStatics_compress2 : prog.fnStatics "compress2" = [] := Zlib.Proof.prog_fnStatics_compress2 h.base
theorem prog_fnStatics_compress_z : prog.fnStatics "compress_z" = [] := Zlib.Proof.prog_fnStatics_compress_z h.base
theorem prog_fnStatics_compress : prog.fnStatics "compress" = [] := Zlib.Proof.prog_fnStatics_compress h.base
theorem prog_fnStatics_compressBound_z : prog.fnStatics "compressBound_z" = [] := Zlib.Proof.prog_fnStatics_compressBound_z h.base
theorem prog_fnStatics_compressBound : prog.fnStatics "compressBound" = [] := Zlib.Proof.prog_fnStatics_compressBound h.base
theorem prog_fnStatics_adler32_z : prog.fnStatics "adler32_z" = [] := Zlib.Proof.prog_fnStatics_adler32_z h.base
theorem prog_fnStatics_adler32 : prog.fnStatics "adler32" = [] := Zlib.Proof.prog_fnStatics_adler32 h.base
theorem prog_fnStatics_adler32_combine_ : prog.fnStatics "adler32_combine_" = [] := Zlib.Proof.prog_fnStatics_adler32_combine_ h.base
theorem prog_fnStatics_adler32_combine : prog.fnStatics "adler32_combine" = [] := Zlib.Proof.prog_fnStatics_adler32_combine h.base
theorem prog_fnStatics_adler32_combine64 : prog.fnStatics "adler32_combine64" = [] := Zlib.Proof.prog_fnStatics_adler32_combine64 h.base
theorem prog_fnStatics_byte_swap : prog.fnStatics "byte_swap" = [] := Zlib.Proof.prog_fnStatics_byte_swap h.base
theorem prog_fnStatics_multmodp : prog.fnStatics "multmodp" = [] := Zlib.Proof.prog_fnStatics_multmodp h.base
theorem prog_fnStatics_x2nmodp : prog.fnStatics "x2nmodp" = [] := Zlib.Proof.prog_fnStatics_x2nmodp h.base
theorem prog_fnStatics_get_crc_table : prog.fnStatics "get_crc_table" = [] := Zlib.Proof.prog_fnStatics_get_crc_table h.base
theorem prog_fnStatics_crc_word : prog.fnStatics "crc_word" = [] := Zlib.Proof.prog_fnStatics_crc_word h.base
theorem prog_fnStatics_crc_word_big : prog.fnStatics "crc_word_big" = [] := Zlib.Proof.prog_fnStatics_crc_word_big h.base
theorem prog_fnStatics_crc32_braid : prog.fnStatics "crc32_braid" = [] := Zlib.Proof.prog_fnStatics_crc32_braid h.base
theorem prog_fnStatics_crc32_z : prog.fnStatics "crc32_z" = [] := Zlib.Proof.prog_fnStatics_crc32_z h.base
theorem prog_fnStatics_crc32 : prog.fnStatics "crc32" = [] := Zlib.Proof.prog_fnStatics_crc32 h.base
theorem prog_fnStatics_crc32_combine_gen64 : prog.fnStatics "crc32_combine_gen64" = [] := Zlib.Proof.prog_fnStatics_crc32_combine_gen64 h.base
theorem prog_fnStatics_crc32_combine_gen : prog.fnStatics "crc32_combine_gen" = [] := Zlib.Proof.prog_fnStatics_crc32_combine_gen h.base
theorem prog_fnStatics_crc32_combine_op : prog.fnStatics "crc32_combine_op" = [] := Zlib.Proof.prog_fnStatics_crc32_combine_op h.base
theorem prog_fnStatics_crc32_combine64 : prog.fnStatics "crc32_combine64" = [] := Zlib.Proof.prog_fnStatics_crc32_combine64 h.base
theorem prog_fnStatics_crc32_combine : prog.fnStatics "crc32_combine" = [] := Zlib.Proof.prog_fnStatics_crc32_combine h.base

-- Remaining non-static `prog.fnStatics` (130)
theorem prog_fnStatics_gzclose : prog.fnStatics "gzclose" = [] := h.prog_fnStatics_empty_all "gzclose" (by decide)
theorem prog_fnStatics_uncompress2_z : prog.fnStatics "uncompress2_z" = [] := h.prog_fnStatics_empty_all "uncompress2_z" (by decide)
theorem prog_fnStatics_uncompress2 : prog.fnStatics "uncompress2" = [] := h.prog_fnStatics_empty_all "uncompress2" (by decide)
theorem prog_fnStatics_uncompress_z : prog.fnStatics "uncompress_z" = [] := h.prog_fnStatics_empty_all "uncompress_z" (by decide)
theorem prog_fnStatics_uncompress : prog.fnStatics "uncompress" = [] := h.prog_fnStatics_empty_all "uncompress" (by decide)
theorem prog_fnStatics_inflate_fixed : prog.fnStatics "inflate_fixed" = [] := h.prog_fnStatics_empty_all "inflate_fixed" (by decide)
theorem prog_fnStatics_load64 : prog.fnStatics "load64" = [] := h.prog_fnStatics_empty_all "load64" (by decide)
theorem prog_fnStatics_copy_back : prog.fnStatics "copy_back" = [] := h.prog_fnStatics_empty_all "copy_back" (by decide)
theorem prog_fnStatics_inflate_fast : prog.fnStatics "inflate_fast" = [] := h.prog_fnStatics_empty_all "inflate_fast" (by decide)
theorem prog_fnStatics_bi_reverse : prog.fnStatics "bi_reverse" = [] := h.prog_fnStatics_empty_all "bi_reverse" (by decide)
theorem prog_fnStatics_bi_flush : prog.fnStatics "bi_flush" = [] := h.prog_fnStatics_empty_all "bi_flush" (by decide)
theorem prog_fnStatics_bi_windup : prog.fnStatics "bi_windup" = [] := h.prog_fnStatics_empty_all "bi_windup" (by decide)
theorem prog_fnStatics_gen_codes : prog.fnStatics "gen_codes" = [] := h.prog_fnStatics_empty_all "gen_codes" (by decide)
theorem prog_fnStatics_tr_static_init : prog.fnStatics "tr_static_init" = [] := h.prog_fnStatics_empty_all "tr_static_init" (by decide)
theorem prog_fnStatics_init_block : prog.fnStatics "init_block" = [] := h.prog_fnStatics_empty_all "init_block" (by decide)
theorem prog_fnStatics__tr_init : prog.fnStatics "_tr_init" = [] := h.prog_fnStatics_empty_all "_tr_init" (by decide)
theorem prog_fnStatics_pqdownheap : prog.fnStatics "pqdownheap" = [] := h.prog_fnStatics_empty_all "pqdownheap" (by decide)
theorem prog_fnStatics_gen_bitlen : prog.fnStatics "gen_bitlen" = [] := h.prog_fnStatics_empty_all "gen_bitlen" (by decide)
theorem prog_fnStatics_build_tree : prog.fnStatics "build_tree" = [] := h.prog_fnStatics_empty_all "build_tree" (by decide)
theorem prog_fnStatics_scan_tree : prog.fnStatics "scan_tree" = [] := h.prog_fnStatics_empty_all "scan_tree" (by decide)
theorem prog_fnStatics_send_tree : prog.fnStatics "send_tree" = [] := h.prog_fnStatics_empty_all "send_tree" (by decide)
theorem prog_fnStatics_build_bl_tree : prog.fnStatics "build_bl_tree" = [] := h.prog_fnStatics_empty_all "build_bl_tree" (by decide)
theorem prog_fnStatics_send_all_trees : prog.fnStatics "send_all_trees" = [] := h.prog_fnStatics_empty_all "send_all_trees" (by decide)
theorem prog_fnStatics__tr_stored_block : prog.fnStatics "_tr_stored_block" = [] := h.prog_fnStatics_empty_all "_tr_stored_block" (by decide)
theorem prog_fnStatics__tr_flush_bits : prog.fnStatics "_tr_flush_bits" = [] := h.prog_fnStatics_empty_all "_tr_flush_bits" (by decide)
theorem prog_fnStatics__tr_align : prog.fnStatics "_tr_align" = [] := h.prog_fnStatics_empty_all "_tr_align" (by decide)
theorem prog_fnStatics_compress_block : prog.fnStatics "compress_block" = [] := h.prog_fnStatics_empty_all "compress_block" (by decide)
theorem prog_fnStatics_detect_data_type : prog.fnStatics "detect_data_type" = [] := h.prog_fnStatics_empty_all "detect_data_type" (by decide)
theorem prog_fnStatics__tr_flush_block : prog.fnStatics "_tr_flush_block" = [] := h.prog_fnStatics_empty_all "_tr_flush_block" (by decide)
theorem prog_fnStatics__tr_tally : prog.fnStatics "_tr_tally" = [] := h.prog_fnStatics_empty_all "_tr_tally" (by decide)
theorem prog_fnStatics_inflateBackInit_ : prog.fnStatics "inflateBackInit_" = [] := h.prog_fnStatics_empty_all "inflateBackInit_" (by decide)
theorem prog_fnStatics_inflateBackEnd : prog.fnStatics "inflateBackEnd" = [] := h.prog_fnStatics_empty_all "inflateBackEnd" (by decide)
theorem prog_fnStatics_inflateStateCheck : prog.fnStatics "inflateStateCheck" = [] := h.prog_fnStatics_empty_all "inflateStateCheck" (by decide)
theorem prog_fnStatics_inflateResetKeep : prog.fnStatics "inflateResetKeep" = [] := h.prog_fnStatics_empty_all "inflateResetKeep" (by decide)
theorem prog_fnStatics_inflateReset : prog.fnStatics "inflateReset" = [] := h.prog_fnStatics_empty_all "inflateReset" (by decide)
theorem prog_fnStatics_inflateReset2 : prog.fnStatics "inflateReset2" = [] := h.prog_fnStatics_empty_all "inflateReset2" (by decide)
theorem prog_fnStatics_inflateInit2_ : prog.fnStatics "inflateInit2_" = [] := h.prog_fnStatics_empty_all "inflateInit2_" (by decide)
theorem prog_fnStatics_inflateInit_ : prog.fnStatics "inflateInit_" = [] := h.prog_fnStatics_empty_all "inflateInit_" (by decide)
theorem prog_fnStatics_inflatePrime : prog.fnStatics "inflatePrime" = [] := h.prog_fnStatics_empty_all "inflatePrime" (by decide)
theorem prog_fnStatics_updatewindow : prog.fnStatics "updatewindow" = [] := h.prog_fnStatics_empty_all "updatewindow" (by decide)
theorem prog_fnStatics_inflateEnd : prog.fnStatics "inflateEnd" = [] := h.prog_fnStatics_empty_all "inflateEnd" (by decide)
theorem prog_fnStatics_inflateGetDictionary : prog.fnStatics "inflateGetDictionary" = [] := h.prog_fnStatics_empty_all "inflateGetDictionary" (by decide)
theorem prog_fnStatics_inflateSetDictionary : prog.fnStatics "inflateSetDictionary" = [] := h.prog_fnStatics_empty_all "inflateSetDictionary" (by decide)
theorem prog_fnStatics_inflateGetHeader : prog.fnStatics "inflateGetHeader" = [] := h.prog_fnStatics_empty_all "inflateGetHeader" (by decide)
theorem prog_fnStatics_syncsearch : prog.fnStatics "syncsearch" = [] := h.prog_fnStatics_empty_all "syncsearch" (by decide)
theorem prog_fnStatics_inflateSync : prog.fnStatics "inflateSync" = [] := h.prog_fnStatics_empty_all "inflateSync" (by decide)
theorem prog_fnStatics_inflateSyncPoint : prog.fnStatics "inflateSyncPoint" = [] := h.prog_fnStatics_empty_all "inflateSyncPoint" (by decide)
theorem prog_fnStatics_inflateCopy : prog.fnStatics "inflateCopy" = [] := h.prog_fnStatics_empty_all "inflateCopy" (by decide)
theorem prog_fnStatics_inflateUndermine : prog.fnStatics "inflateUndermine" = [] := h.prog_fnStatics_empty_all "inflateUndermine" (by decide)
theorem prog_fnStatics_inflateValidate : prog.fnStatics "inflateValidate" = [] := h.prog_fnStatics_empty_all "inflateValidate" (by decide)
theorem prog_fnStatics_inflateMark : prog.fnStatics "inflateMark" = [] := h.prog_fnStatics_empty_all "inflateMark" (by decide)
theorem prog_fnStatics_inflateCodesUsed : prog.fnStatics "inflateCodesUsed" = [] := h.prog_fnStatics_empty_all "inflateCodesUsed" (by decide)
theorem prog_fnStatics_slide_hash : prog.fnStatics "slide_hash" = [] := h.prog_fnStatics_empty_all "slide_hash" (by decide)
theorem prog_fnStatics_read_buf : prog.fnStatics "read_buf" = [] := h.prog_fnStatics_empty_all "read_buf" (by decide)
theorem prog_fnStatics_fill_window : prog.fnStatics "fill_window" = [] := h.prog_fnStatics_empty_all "fill_window" (by decide)
theorem prog_fnStatics_deflateInit_ : prog.fnStatics "deflateInit_" = [] := h.prog_fnStatics_empty_all "deflateInit_" (by decide)
theorem prog_fnStatics_deflateStateCheck : prog.fnStatics "deflateStateCheck" = [] := h.prog_fnStatics_empty_all "deflateStateCheck" (by decide)
theorem prog_fnStatics_deflateSetDictionary : prog.fnStatics "deflateSetDictionary" = [] := h.prog_fnStatics_empty_all "deflateSetDictionary" (by decide)
theorem prog_fnStatics_deflateGetDictionary : prog.fnStatics "deflateGetDictionary" = [] := h.prog_fnStatics_empty_all "deflateGetDictionary" (by decide)
theorem prog_fnStatics_deflateResetKeep : prog.fnStatics "deflateResetKeep" = [] := h.prog_fnStatics_empty_all "deflateResetKeep" (by decide)
theorem prog_fnStatics_lm_init : prog.fnStatics "lm_init" = [] := h.prog_fnStatics_empty_all "lm_init" (by decide)
theorem prog_fnStatics_deflateReset : prog.fnStatics "deflateReset" = [] := h.prog_fnStatics_empty_all "deflateReset" (by decide)
theorem prog_fnStatics_deflateSetHeader : prog.fnStatics "deflateSetHeader" = [] := h.prog_fnStatics_empty_all "deflateSetHeader" (by decide)
theorem prog_fnStatics_deflatePending : prog.fnStatics "deflatePending" = [] := h.prog_fnStatics_empty_all "deflatePending" (by decide)
theorem prog_fnStatics_deflateUsed : prog.fnStatics "deflateUsed" = [] := h.prog_fnStatics_empty_all "deflateUsed" (by decide)
theorem prog_fnStatics_deflatePrime : prog.fnStatics "deflatePrime" = [] := h.prog_fnStatics_empty_all "deflatePrime" (by decide)
theorem prog_fnStatics_deflateParams : prog.fnStatics "deflateParams" = [] := h.prog_fnStatics_empty_all "deflateParams" (by decide)
theorem prog_fnStatics_deflateTune : prog.fnStatics "deflateTune" = [] := h.prog_fnStatics_empty_all "deflateTune" (by decide)
theorem prog_fnStatics_deflateBound_z : prog.fnStatics "deflateBound_z" = [] := h.prog_fnStatics_empty_all "deflateBound_z" (by decide)
theorem prog_fnStatics_deflateBound : prog.fnStatics "deflateBound" = [] := h.prog_fnStatics_empty_all "deflateBound" (by decide)
theorem prog_fnStatics_putShortMSB : prog.fnStatics "putShortMSB" = [] := h.prog_fnStatics_empty_all "putShortMSB" (by decide)
theorem prog_fnStatics_flush_pending : prog.fnStatics "flush_pending" = [] := h.prog_fnStatics_empty_all "flush_pending" (by decide)
theorem prog_fnStatics_deflate : prog.fnStatics "deflate" = [] := h.prog_fnStatics_empty_all "deflate" (by decide)
theorem prog_fnStatics_deflateEnd : prog.fnStatics "deflateEnd" = [] := h.prog_fnStatics_empty_all "deflateEnd" (by decide)
theorem prog_fnStatics_deflateCopy : prog.fnStatics "deflateCopy" = [] := h.prog_fnStatics_empty_all "deflateCopy" (by decide)
theorem prog_fnStatics_longest_match : prog.fnStatics "longest_match" = [] := h.prog_fnStatics_empty_all "longest_match" (by decide)
theorem prog_fnStatics_deflate_stored : prog.fnStatics "deflate_stored" = [] := h.prog_fnStatics_empty_all "deflate_stored" (by decide)
theorem prog_fnStatics_deflate_fast : prog.fnStatics "deflate_fast" = [] := h.prog_fnStatics_empty_all "deflate_fast" (by decide)
theorem prog_fnStatics_deflate_slow : prog.fnStatics "deflate_slow" = [] := h.prog_fnStatics_empty_all "deflate_slow" (by decide)
theorem prog_fnStatics_deflate_rle : prog.fnStatics "deflate_rle" = [] := h.prog_fnStatics_empty_all "deflate_rle" (by decide)
theorem prog_fnStatics_deflate_huff : prog.fnStatics "deflate_huff" = [] := h.prog_fnStatics_empty_all "deflate_huff" (by decide)
theorem prog_fnStatics_gz_reset : prog.fnStatics "gz_reset" = [] := h.prog_fnStatics_empty_all "gz_reset" (by decide)
theorem prog_fnStatics_gz_open : prog.fnStatics "gz_open" = [] := h.prog_fnStatics_empty_all "gz_open" (by decide)
theorem prog_fnStatics_gzopen : prog.fnStatics "gzopen" = [] := h.prog_fnStatics_empty_all "gzopen" (by decide)
theorem prog_fnStatics_gzopen64 : prog.fnStatics "gzopen64" = [] := h.prog_fnStatics_empty_all "gzopen64" (by decide)
theorem prog_fnStatics_gzdopen : prog.fnStatics "gzdopen" = [] := h.prog_fnStatics_empty_all "gzdopen" (by decide)
theorem prog_fnStatics_gzbuffer : prog.fnStatics "gzbuffer" = [] := h.prog_fnStatics_empty_all "gzbuffer" (by decide)
theorem prog_fnStatics_gzrewind : prog.fnStatics "gzrewind" = [] := h.prog_fnStatics_empty_all "gzrewind" (by decide)
theorem prog_fnStatics_gzseek64 : prog.fnStatics "gzseek64" = [] := h.prog_fnStatics_empty_all "gzseek64" (by decide)
theorem prog_fnStatics_gzseek : prog.fnStatics "gzseek" = [] := h.prog_fnStatics_empty_all "gzseek" (by decide)
theorem prog_fnStatics_gztell64 : prog.fnStatics "gztell64" = [] := h.prog_fnStatics_empty_all "gztell64" (by decide)
theorem prog_fnStatics_gztell : prog.fnStatics "gztell" = [] := h.prog_fnStatics_empty_all "gztell" (by decide)
theorem prog_fnStatics_gzoffset64 : prog.fnStatics "gzoffset64" = [] := h.prog_fnStatics_empty_all "gzoffset64" (by decide)
theorem prog_fnStatics_gzoffset : prog.fnStatics "gzoffset" = [] := h.prog_fnStatics_empty_all "gzoffset" (by decide)
theorem prog_fnStatics_gzeof : prog.fnStatics "gzeof" = [] := h.prog_fnStatics_empty_all "gzeof" (by decide)
theorem prog_fnStatics_gzerror : prog.fnStatics "gzerror" = [] := h.prog_fnStatics_empty_all "gzerror" (by decide)
theorem prog_fnStatics_gzclearerr : prog.fnStatics "gzclearerr" = [] := h.prog_fnStatics_empty_all "gzclearerr" (by decide)
theorem prog_fnStatics_gz_error : prog.fnStatics "gz_error" = [] := h.prog_fnStatics_empty_all "gz_error" (by decide)
theorem prog_fnStatics_gz_intmax : prog.fnStatics "gz_intmax" = [] := h.prog_fnStatics_empty_all "gz_intmax" (by decide)
theorem prog_fnStatics_gz_load : prog.fnStatics "gz_load" = [] := h.prog_fnStatics_empty_all "gz_load" (by decide)
theorem prog_fnStatics_gz_avail : prog.fnStatics "gz_avail" = [] := h.prog_fnStatics_empty_all "gz_avail" (by decide)
theorem prog_fnStatics_gz_room : prog.fnStatics "gz_room" = [] := h.prog_fnStatics_empty_all "gz_room" (by decide)
theorem prog_fnStatics_gz_look : prog.fnStatics "gz_look" = [] := h.prog_fnStatics_empty_all "gz_look" (by decide)
theorem prog_fnStatics_gz_decomp : prog.fnStatics "gz_decomp" = [] := h.prog_fnStatics_empty_all "gz_decomp" (by decide)
theorem prog_fnStatics_gz_fetch : prog.fnStatics "gz_fetch" = [] := h.prog_fnStatics_empty_all "gz_fetch" (by decide)
theorem prog_fnStatics_gz_skip_have : prog.fnStatics "gz_skip_have" = [] := h.prog_fnStatics_empty_all "gz_skip_have" (by decide)
theorem prog_fnStatics_gz_skip : prog.fnStatics "gz_skip" = [] := h.prog_fnStatics_empty_all "gz_skip" (by decide)
theorem prog_fnStatics_gz_read : prog.fnStatics "gz_read" = [] := h.prog_fnStatics_empty_all "gz_read" (by decide)
theorem prog_fnStatics_gzread : prog.fnStatics "gzread" = [] := h.prog_fnStatics_empty_all "gzread" (by decide)
theorem prog_fnStatics_gzfread : prog.fnStatics "gzfread" = [] := h.prog_fnStatics_empty_all "gzfread" (by decide)
theorem prog_fnStatics_gzgetc : prog.fnStatics "gzgetc" = [] := h.prog_fnStatics_empty_all "gzgetc" (by decide)
theorem prog_fnStatics_gzgetc_ : prog.fnStatics "gzgetc_" = [] := h.prog_fnStatics_empty_all "gzgetc_" (by decide)
theorem prog_fnStatics_gzungetc : prog.fnStatics "gzungetc" = [] := h.prog_fnStatics_empty_all "gzungetc" (by decide)
theorem prog_fnStatics_gzgets : prog.fnStatics "gzgets" = [] := h.prog_fnStatics_empty_all "gzgets" (by decide)
theorem prog_fnStatics_gzdirect : prog.fnStatics "gzdirect" = [] := h.prog_fnStatics_empty_all "gzdirect" (by decide)
theorem prog_fnStatics_gzclose_r : prog.fnStatics "gzclose_r" = [] := h.prog_fnStatics_empty_all "gzclose_r" (by decide)
theorem prog_fnStatics_gz_init : prog.fnStatics "gz_init" = [] := h.prog_fnStatics_empty_all "gz_init" (by decide)
theorem prog_fnStatics_gz_comp : prog.fnStatics "gz_comp" = [] := h.prog_fnStatics_empty_all "gz_comp" (by decide)
theorem prog_fnStatics_gz_zero : prog.fnStatics "gz_zero" = [] := h.prog_fnStatics_empty_all "gz_zero" (by decide)
theorem prog_fnStatics_gz_write : prog.fnStatics "gz_write" = [] := h.prog_fnStatics_empty_all "gz_write" (by decide)
theorem prog_fnStatics_gzwrite : prog.fnStatics "gzwrite" = [] := h.prog_fnStatics_empty_all "gzwrite" (by decide)
theorem prog_fnStatics_gzfwrite : prog.fnStatics "gzfwrite" = [] := h.prog_fnStatics_empty_all "gzfwrite" (by decide)
theorem prog_fnStatics_gzputc : prog.fnStatics "gzputc" = [] := h.prog_fnStatics_empty_all "gzputc" (by decide)
theorem prog_fnStatics_gzputs : prog.fnStatics "gzputs" = [] := h.prog_fnStatics_empty_all "gzputs" (by decide)
theorem prog_fnStatics_gz_vacate : prog.fnStatics "gz_vacate" = [] := h.prog_fnStatics_empty_all "gz_vacate" (by decide)
theorem prog_fnStatics_gzvprintf : prog.fnStatics "gzvprintf" = [] := h.prog_fnStatics_empty_all "gzvprintf" (by decide)
theorem prog_fnStatics_gzprintf : prog.fnStatics "gzprintf" = [] := h.prog_fnStatics_empty_all "gzprintf" (by decide)
theorem prog_fnStatics_gzflush : prog.fnStatics "gzflush" = [] := h.prog_fnStatics_empty_all "gzflush" (by decide)
theorem prog_fnStatics_gzsetparams : prog.fnStatics "gzsetparams" = [] := h.prog_fnStatics_empty_all "gzsetparams" (by decide)
theorem prog_fnStatics_gzclose_w : prog.fnStatics "gzclose_w" = [] := h.prog_fnStatics_empty_all "gzclose_w" (by decide)

end Accessors

end InitLibzAllProps

end Zlib.Proof




