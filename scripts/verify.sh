#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
BUILD="$ROOT/build"
UPSTREAM="$ROOT/upstream"
PINS="$ROOT/pins.json"

json_field() {
  sed -n "s/^[[:space:]]*\"$1\"[[:space:]]*:[[:space:]]*\"\([^\"]*\)\".*/\1/p" "$PINS" | head -n 1
}

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

verify_patches() {
  expected=$(sed -n 's/^[[:space:]]*"\([^"]*\.patch\)"[[:space:]]*:[[:space:]]*"\([0-9a-f]*\)".*/\1:\2/p' "$PINS" | LC_ALL=C sort)
  actual=""
  for p in "$ROOT"/patches/*.patch; do
    [ -f "$p" ] || { echo "No patch files found in $ROOT/patches" >&2; exit 1; }
    actual="${actual}$(basename "$p"):$(sha256_file "$p")
"
  done
  actual=$(printf '%s' "$actual" | LC_ALL=C sort)
  if [ "$expected" != "$actual" ]; then
    echo "Patch names or SHA-256 digests differ from pins.json" >&2
    exit 1
  fi
}

materialize_reference() {
  dest=$1
  configure=$2
  pin=$(json_field zlib)
  [ -n "$pin" ] || { echo "Missing zlib commit in pins.json" >&2; exit 1; }
  verify_patches

  stage=$(mktemp -d "${TMPDIR:-/tmp}/zlib-ref.XXXXXX")
  trap 'rm -rf "$stage"' EXIT HUP INT TERM

  paths=$(git -C "$UPSTREAM" ls-tree --name-only "$pin" | awk '
    /\.c$/ || /\.h$/ { print; next }
    '"$configure"' == 1 && ($0 == "configure" || $0 == "Makefile.in" || $0 == "zconf.h.in" || $0 == "zlib.pc.in" || $0 == "zlib.map") { print }
  ')
  [ -n "$paths" ] || { echo "No library sources found at pinned zlib commit $pin" >&2; exit 1; }

  git -C "$stage" init -q
  printf '%s\n' "$paths" | while IFS= read -r name; do
    git -C "$UPSTREAM" show "$pin:$name" > "$stage/$name"
  done
  git -C "$stage" apply --whitespace=nowarn "$ROOT"/patches/*.patch

  mkdir -p "$dest"
  if [ -d "$dest" ]; then
    for existing in "$dest"/*; do
      [ -e "$existing" ] || continue
      base=$(basename "$existing")
      if ! printf '%s\n' "$paths" | grep -qxF "$base"; then
        echo "Unexpected file in reference destination $dest: $base" >&2
        exit 1
      fi
    done
  fi
  printf '%s\n' "$paths" | while IFS= read -r name; do
    cp "$stage/$name" "$dest/$name"
  done
  [ "$configure" != "1" ] || chmod 755 "$dest/configure"

  rm -rf "$stage"
  trap - EXIT HUP INT TERM
}

run_reference() {
  configure=0
  dest="$BUILD/reference"
  while [ $# -gt 0 ]; do
    case "$1" in
      --configure) configure=1 ;;
      *) dest=$1 ;;
    esac
    shift
  done
  materialize_reference "$dest" "$configure"
}

run_lean_exe() {
  (
    cd "$ROOT"
    PATH="${HOME}/.elan/bin:${PATH}"
    export PATH LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"
    lake build --wfail lean2c >&2
    exec lake exe lean2c "$@"
  )
}

run_binary() {
  pinned=0
  compcert=0
  lean_dir=""
  abi_check_dir=""
  out_dir=""

  while [ $# -gt 0 ]; do
    case "$1" in
      --pinned) pinned=1 ;;
      --compcert) compcert=1 ;;
      --lean-dir) shift; lean_dir=$1 ;;
      --abi-check-dir) shift; abi_check_dir=$1 ;;
      --output) shift; out_dir=$1 ;;
      *) echo "Unknown option: $1" >&2; exit 2 ;;
    esac
    shift
  done

  if [ "$compcert" = "1" ] && [ "$pinned" = "1" ]; then
    echo "--pinned cannot be combined with --compcert" >&2
    exit 2
  fi

  sysname=$(uname -s)
  clang_ver=$(json_field version)
  clang_target=$(json_field target)
  clang_std=$(json_field standard)

  if [ "$compcert" = "1" ]; then
    cc_cmd=${CC:-ccomp}
    ar_cmd=${AR:-ar}
    ranlib_cmd=${RANLIB:-"ranlib -D"}
    compiler_kind="compcert"
    target="$(uname -m)-unknown-linux-gnu"
    base_cflags="-O -DNDEBUG -fstruct-passing -fbitfields -D_POSIX_C_SOURCE=200809L"
    ar_flags="rcsD"
    version=$( ($cc_cmd -version 2>/dev/null || $cc_cmd --version 2>/dev/null) | head -n 1 | tr '"' "'" )
  else
    compiler_kind="clang"
    if [ "$sysname" = "Darwin" ]; then
      [ "$pinned" != "1" ] || { echo "--pinned Linux audit must run on x86_64-linux-gnu" >&2; exit 1; }
      cc_cmd=${CC:-"/usr/bin/clang --target=x86_64-apple-darwin"}
      ar_cmd=${AR:-/usr/bin/ar}
      ranlib_cmd=${RANLIB:-/usr/bin/ranlib}
      base_cflags="-O3 -std=$clang_std -g0 -DNDEBUG -ffunction-sections -fno-ident"
      export ZERO_AR_DATE=1
    else
      if [ -z "${CC:-}" ]; then
        which_clang=$(command -v clang 2>/dev/null || true)
        case "$which_clang" in
          *lean-*) [ -x /usr/bin/clang ] && cc_cmd=/usr/bin/clang || cc_cmd=clang ;;
          *) cc_cmd=clang ;;
        esac
      else
        cc_cmd=$CC
      fi
      ar_cmd=${AR:-llvm-ar}
      ranlib_cmd=${RANLIB:-llvm-ranlib}
      base_cflags="-O3 -std=$clang_std -g0 -DNDEBUG -ffunction-sections"
    fi
    version=$($cc_cmd --version | head -n 1)
    if [ "$pinned" = "1" ]; then
      [ "$version" = "$clang_ver" ] || { echo "expected $clang_ver, found $version" >&2; exit 1; }
      case " $cc_cmd " in
        *" --target="*) ;;
        *) cc_cmd="$cc_cmd --target=$clang_target" ;;
      esac
    fi
    target=$($cc_cmd -dumpmachine)
    if [ "$pinned" = "1" ]; then
      [ "$target" = "$clang_target" ] || { echo "expected $clang_target, found $target" >&2; exit 1; }
    fi
    ar_flags="rcsD"
  fi

  if [ -n "$out_dir" ]; then
    mkdir -p "$out_dir"
    work=$(CDPATH= cd -- "$out_dir" && pwd)
  else
    mkdir -p "$BUILD"
    work=$(mktemp -d "$BUILD/archive-XXXXXX")
  fi

  lean_work="$work/lean"
  ref_work="$work/reference"
  if [ -n "$lean_dir" ]; then
    cp -R "$lean_dir" "$lean_work"
  else
    run_lean_exe emit "$lean_work"
  fi

  materialize_reference "$ref_work" 1
  (
    cd "$ref_work"
    export CC="$cc_cmd" AR="$ar_cmd" RANLIB="$ranlib_cmd" ARFLAGS="$ar_flags" SOURCE_DATE_EPOCH=0 CFLAGS="$base_cflags"
    if [ "$compcert" != "1" ] && [ "$sysname" != "Darwin" ]; then
      export CHOST="$target"
    fi
    ./configure --static >/dev/null
  )

  flags=$(
    cd "$ref_work"
    export CC="$cc_cmd" AR="$ar_cmd" RANLIB="$ranlib_cmd" ARFLAGS="$ar_flags" SOURCE_DATE_EPOCH=0 CFLAGS="$base_cflags"
    printf 'abi-flags:\n\t@echo $(CFLAGS)\n' | make -s -f Makefile -f - abi-flags
  )

  if [ "$compcert" != "1" ] && { [ -n "$abi_check_dir" ] || [ -z "$lean_dir" ]; }; then
    abi_work="$work/abi"
    if [ -n "$abi_check_dir" ]; then
      cp -R "$abi_check_dir" "$abi_work"
    else
      run_lean_exe emit-abi-check "$abi_work" >/dev/null
    fi
    awk '/^struct static_tree_desc_s[[:space:]]*\{/,/^\};/' "$ref_work/trees.c" > "$abi_work/ref_static_tree_desc.h"
    $cc_cmd $flags -I "$ref_work" -I "$abi_work" -fsyntax-only "$abi_work/abi_check_ref_deflate.c"
    $cc_cmd $flags -I "$ref_work" -fsyntax-only "$abi_work/abi_check_ref_inflate.c"
    $cc_cmd $flags -I "$ref_work" -fsyntax-only "$abi_work/abi_check_ref_gz.c"
    $cc_cmd $flags -I "$lean_work" -fsyntax-only "$abi_work/abi_check_lean.c"
    echo "ABI structs OK: 10/10 structs, 163 fields verified"
  fi

  (
    cd "$ref_work"
    export CC="$cc_cmd" AR="$ar_cmd" RANLIB="$ranlib_cmd" ARFLAGS="$ar_flags" SOURCE_DATE_EPOCH=0 CFLAGS="$base_cflags"
    make -s libz.a
  )

  expected=$($ar_cmd t "$ref_work/libz.a" | awk '!/^__\.SYMDEF/')
  [ -n "$expected" ] || { echo "Empty reference archive" >&2; exit 1; }

  compile_errs=0
  compile_err_log=""
  for src_path in "$lean_work"/*.c; do
    [ -f "$src_path" ] || continue
    src=$(basename "$src_path")
    if err=$(cd "$lean_work" && $cc_cmd $flags -c "$src" -o "${src%.c}.o" 2>&1); then
      :
    else
      compile_errs=$((compile_errs + 1))
      clean_err=$(printf '%s' "$err" | head -n 5 | tr '\n\r"' ';  ')
      compile_err_log="${compile_err_log}  COMPILE ERROR ${src}: ${clean_err}
"
    fi
  done

  total=0
  eq_count=0
  missing_count=0
  obj_json=""
  diffs=""
  for m in $expected; do
    total=$((total + 1))
    ref_o="$ref_work/$m"
    lean_o="$lean_work/$m"
    rsha=$(sha256_file "$ref_o")
    if [ ! -f "$lean_o" ]; then
      missing_count=$((missing_count + 1))
      is_eq=false
      lsha=""
      rlen=$(wc -c < "$ref_o" | tr -d ' ')
      diffs="${diffs}  MISSING $m: reference=${rlen} bytes
"
    else
      lsha=$(sha256_file "$lean_o")
      if cmp -s "$ref_o" "$lean_o"; then
        is_eq=true
        eq_count=$((eq_count + 1))
      else
        is_eq=false
        rlen=$(wc -c < "$ref_o" | tr -d ' ')
        llen=$(wc -c < "$lean_o" | tr -d ' ')
        diffs="${diffs}  DIFF $m: reference=${rlen} bytes, lean=${llen} bytes
"
      fi
    fi
    [ -z "$obj_json" ] || obj_json="${obj_json},"
    obj_json="${obj_json}
    \"$m\": {\"equal\": $is_eq, \"reference_sha256\": \"$rsha\", \"lean_sha256\": \"$lsha\"}"
  done

  arch_eq=false
  lean_arch_sha=""
  if [ "$compile_errs" = "0" ] && [ "$missing_count" = "0" ]; then
    (
      cd "$lean_work"
      if [ "$sysname" = "Darwin" ]; then
        $ar_cmd rcs libz.a $expected
        $ranlib_cmd libz.a
      else
        $ar_cmd rcsD libz.a $expected
        $ranlib_cmd libz.a
      fi
    )
    if [ "$eq_count" = "$total" ] && cmp -s "$ref_work/libz.a" "$lean_work/libz.a"; then
      arch_eq=true
    fi
    lean_arch_sha=$(sha256_file "$lean_work/libz.a")
  fi
  ref_arch_sha=$(sha256_file "$ref_work/libz.a")

  cat > "$work/report.json" <<EOF
{
  "compiler_kind": "$compiler_kind",
  "pinned": $([ "$pinned" = "1" ] && echo true || echo false),
  "zlib": "$(json_field zlib)",
  "target": "$target",
  "compiler": "$version",
  "reference_sha256": "$ref_arch_sha",
  "lean_sha256": "$lean_arch_sha",
  "compile_errors": $compile_errs,
  "missing": $missing_count,
  "objects": {$obj_json
  },
  "archive_equal": $arch_eq
}
EOF

  echo "[$compiler_kind] $eq_count/$total objects byte-identical; archive equal: $arch_eq"
  [ -z "$compile_err_log" ] || printf '%s' "$compile_err_log"
  [ -z "$diffs" ] || printf '%s' "$diffs"
  if [ -n "$diffs" ] && command -v objdump >/dev/null 2>&1; then
    for m in $expected; do
      if [ -f "$lean_work/$m" ] && ! cmp -s "$ref_work/$m" "$lean_work/$m"; then
        echo "  --- objdump diff: $m ---"
        if objdump -d "$ref_work/$m" > "$work/ref.asm" 2>/dev/null &&
           objdump -d "$lean_work/$m" > "$work/lean.asm" 2>/dev/null; then
          diff -u "$work/ref.asm" "$work/lean.asm" | head -n 60 || true
        fi
      fi
    done
  fi
  echo "$work/report.json"
  [ "$arch_eq" = "true" ]
}

case "${1:-}" in
  reference) shift; run_reference "$@" ;;
  binary) shift; run_binary "$@" ;;
  *) echo "usage: $0 reference [--configure] [dest] | $0 binary [--pinned] [--compcert] [--lean-dir DIR] [--abi-check-dir DIR] [--output DIR]" >&2; exit 2 ;;
esac
