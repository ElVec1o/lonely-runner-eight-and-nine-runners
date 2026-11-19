#!/bin/bash
# regen_e8stage.sh [--install DIR] [P ...] : regenerate the staged Lean sources E8Stage/P<p>/*.lean of the 27 eight-runner certificates with the
# generator repro/eight/generator/l7v4.rs and compare every file with repro/eight/E8STAGE.tsv (prime, file, sha256, bytes, lines).
#   no option    generate into a scratch directory, compare, delete (one prime at a time; disk at most the largest prime, about 190 MB)
#   --install D  keep the sources of the selected primes in D/E8Stage/P<p>/ (the layout the staged builds use; all 27 primes need about 1.7 GB)
#   P ...        primes (default: all 27)
# Needs only rustc (std only, no crates) and shasum.  No Lean.  Exit 0 if every file of every selected prime matches, 1 otherwise.
# The shipped sources differ from the ones that were compiled in the original staged builds in line 1 only (the generated-by comment).
S=$(cd "$(dirname "$0")" && pwd); E=$(cd "$S/.." && pwd)
INSTALL=""; PR=""
while [ $# -gt 0 ]; do case "$1" in --install) INSTALL=$2; shift ;; *) PR="$PR $1" ;; esac; shift; done
[ -n "$PR" ] || PR="31 37 43 47 53 59 61 67 71 73 79 83 89 97 101 103 107 109 113 127 131 137 139 149 151 157 163"
GEN=${GEN:-$E/bin/l7v4s}
if [ ! -x "$GEN" ]; then mkdir -p "$(dirname "$GEN")"; rustc -O --edition 2021 -o "$GEN" "$E/generator/l7v4.rs" 2>/dev/null || { echo "rustc failed"; exit 2; }; echo "built $GEN"; fi
TMPD=$(mktemp -d); trap 'rm -rf "$TMPD"' EXIT
fail=0; nf=0
for p in $PR; do
  D=$TMPD/P$p; rm -rf "$D"
  "$GEN" "$p" stage "$D" 400000 16 bitkey > /dev/null 2>&1 || { echo "P$p GENERATOR FAILED"; fail=1; continue; }
  want=$(awk -F'\t' -v p="$p" '$1==p{n++} END{print n+0}' "$E/E8STAGE.tsv")
  got=$(ls "$D"/*.lean | wc -l | tr -d ' ')
  bad=0
  for f in $(cd "$D" && ls *.lean); do
    w=$(awk -F'\t' -v p="$p" -v f="$f" '$1==p && $2==f{print $3}' "$E/E8STAGE.tsv"); h=$(shasum -a 256 "$D/$f" | cut -d' ' -f1)
    [ "$w" = "$h" ] || { bad=$((bad+1)); echo "P$p $f DIFFERS"; }
  done
  nf=$((nf+got))
  if [ "$bad" = 0 ] && [ "$want" = "$got" ]; then echo "P$p OK: $got files identical to E8STAGE.tsv"; else echo "P$p FAIL: $bad differ, $got generated, $want in table"; fail=1; fi
  if [ -n "$INSTALL" ]; then mkdir -p "$INSTALL/E8Stage/P$p"; cp "$D"/*.lean "$INSTALL/E8Stage/P$p/"; fi
  rm -rf "$D"
done
[ $fail = 0 ] && echo "REGEN OK: $nf files identical" || echo "REGEN FAILED"
exit $fail
