#!/usr/bin/env bash
# Rename src/ directories and *_intf.ml files to match new-style conventions.
#   - Lowercase dirs  → UpperCamelCase  (e.g. modes → Modes)
#   - *_intf.ml files → SCREAMING.ml   (e.g. Modecheck_intf.ml → MODECHECK.ml)
# Then patches (modules ...) stanzas in dune files and open/include in .ml files.
set -euo pipefail

ROOT="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
SRC="$ROOT/src"

# ── Phase 1: rename lowercase source directories ──────────────────────────────

declare -a DIR_RENAMES=(
  "compile:Compile"
  "compress:Compress"
  "cover:Cover"
  "debug:Debug"
  "domains:Domains"
  "flit:Flit"
  "formatter:Formatter"
  "frontend:Frontend"
  "global:Global"
  "heuristic:Heuristic"
  "index:Index"
  "intInf:IntInf"
  "inverse:Inverse"
  "m2:M2"
  "meta:Meta"
  "modes:Modes"
  "modules:Modules"
  "msg:Msg"
  "names:Names"
  "netserver:Netserver"
  "opsem:Opsem"
  "order:Order"
  "paths:Paths"
  "print:Print"
  "prover:Prover"
  "server:Server"
  "smlofnj:Smlofnj"
  "solvers:Solvers"
  "stream:Stream"
  "style:Style"
  "subordinate:Subordinate"
  "table:Table"
  "tabling:Tabling"
  "terminate:Terminate"
  "thm:Thm"
  "timing:Timing"
  "tomega:Tomega"
  "trail:Trail"
  "typecheck:Typecheck"
  "unique:Unique"
  "worldcheck:Worldcheck"
)

echo "=== Phase 1: directory renames ==="
for entry in "${DIR_RENAMES[@]}"; do
  old="${entry%%:*}"
  new="${entry##*:}"
  if [ -d "$SRC/$old" ]; then
    git -C "$ROOT" mv "src/$old" "src/$new"
    echo "  dir: $old → $new"
  elif [ -d "$SRC/$new" ]; then
    echo "  dir: $new already exists, skipping"
  else
    echo "  dir: $old not found, skipping"
  fi
done

# ── Phase 2: rename *_intf.ml files ───────────────────────────────────────────

echo ""
echo "=== Phase 2: *_intf.ml → SCREAMING.ml ==="

declare -A INTF_MAP  # old module name → new module name (e.g. Modecheck_intf → MODECHECK)

while IFS= read -r f; do
  dir=$(dirname "$f")
  old_base=$(basename "$f" .ml)              # e.g. Modecheck_intf
  stem="${old_base%_intf}"                   # e.g. Modecheck
  new_base=$(echo "$stem" | tr '[:lower:]' '[:upper:]')  # e.g. MODECHECK
  new_file="$dir/$new_base.ml"

  if [ "$f" = "$new_file" ]; then
    continue
  fi

  if [ -e "$new_file" ]; then
    echo "  WARNING: $new_file already exists, skipping $f"
    continue
  fi

  # Compute path relative to repo root for git mv
  rel_old="${f#$ROOT/}"
  rel_new="${new_file#$ROOT/}"
  git -C "$ROOT" mv "$rel_old" "$rel_new"
  echo "  file: $old_base.ml → $new_base.ml"

  INTF_MAP["$old_base"]="$new_base"
done < <(find "$SRC" -name "*_intf.ml" | sort)

# ── Phase 3 & 4: update text references in dune and .ml files ─────────────────

echo ""
echo "=== Phase 3+4: patching dune and .ml files ==="

if [ "${#INTF_MAP[@]}" -eq 0 ]; then
  echo "  No renames to patch."
  exit 0
fi

SED_SCRIPT=$(mktemp)
trap "rm -f $SED_SCRIPT" EXIT

for old_mod in $(echo "${!INTF_MAP[@]}" | tr ' ' '\n' | sort); do
  new_mod="${INTF_MAP[$old_mod]}"
  # GNU sed word-boundary replacement
  printf 's/\\b%s\\b/%s/g\n' "$old_mod" "$new_mod" >> "$SED_SCRIPT"
done

echo "  Generated ${#INTF_MAP[@]} substitution rules"

# Apply to dune files
find "$SRC" -name "dune" -print0 | xargs -0 sed -i -f "$SED_SCRIPT"
echo "  Patched dune files"

# Apply to .ml and .mli source files
find "$SRC" \( -name "*.ml" -o -name "*.mli" \) -print0 | xargs -0 sed -i -f "$SED_SCRIPT"
echo "  Patched .ml/.mli source files"

echo ""
echo "Done. Verify with: dune build @check"
