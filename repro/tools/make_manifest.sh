#!/bin/bash
# make_manifest.sh : (re)generate MANIFEST.tsv, the build order of the nine-runner theorem.
#
# Root module: LRSpectrumFull.NineSound.Assemble9Final.  The manifest lists the PROJECT modules (LRSpectrumFull.*) of its import closure
# in DFS post-order (topological: every module appears after all of its project imports).  Mathlib/Batteries/... are not listed.
# Columns: idx module path sha256 bytes lines kind generator in_bundle project_imports
#   in_bundle  no for the two generated data families of every prime (D01.lean, D2.lean and TD*.lean: 633 MB of the 751 MB closure);
#              they are reproduced by regen_data.sh (and checked against the sha256 in this table)
#   kind       base      = top-level LRSpectrumFull/*.lean (older shared modules)
#              hand      = hand-written Lean (NineSound/*.lean, NineProbe/*.lean)
#              raw       = EightRunnersReal, Assemble9, Assemble9Final: elaborated with raw lean (assemble_final.sh --run), not by lake
#              generated = emitted by gen_prime12 / gen_prime13 (NineSound/G<p>/*) or by mkfinal.sh (Assemble9)
#   generator  gen_prime12, gen_prime13, mkfinal.sh, or -   (per prime: PARAMS.tsv)
# Usage: bash tools/make_manifest.sh LEAN_DIR [OUT]   LEAN_DIR must contain ALL closure sources, including the omitted families
#        (reads sources only; writes OUT through a temp file)
HERE=$(cd "$(dirname "$0")/.." && pwd)
LEAN_DIR=${1:?LEAN_DIR (a directory with all closure sources)}
OUT=${2:-$HERE/MANIFEST.tsv}
ROOT=LRSpectrumFull.NineSound.Assemble9Final
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
python3 -I "$HERE/tools/closure.py" "$ROOT" "$LEAN_DIR" > "$T/order.txt" || { echo "closure failed; manifest NOT written" >&2; exit 2; }
tr . / < "$T/order.txt" | sed 's/$/.lean/' > "$T/paths.txt"
( cd "$LEAN_DIR" && tr '\n' '\0' < "$T/paths.txt" | xargs -0 shasum -a 256 ) > "$T/sha.txt"
( cd "$LEAN_DIR" && tr '\n' '\0' < "$T/paths.txt" | xargs -0 wc -c ) | grep -v ' total$' > "$T/bytes.txt"
( cd "$LEAN_DIR" && tr '\n' '\0' < "$T/paths.txt" | xargs -0 wc -l ) | grep -v ' total$' > "$T/lines.txt"
[ "$(wc -l < "$T/sha.txt")" = "$(wc -l < "$T/paths.txt")" ] || { echo "sha count mismatch" >&2; exit 2; }
cd "$LEAN_DIR"
awk -v T="$T" -v params="$HERE/PARAMS.tsv" '
BEGIN {
  while ((getline l < (T "/sha.txt")) > 0) { split(l,a," "); sha[a[2]]=a[1] }
  while ((getline l < (T "/bytes.txt")) > 0) { split(l,a," "); by[a[2]]=a[1] }
  while ((getline l < (T "/lines.txt")) > 0) { split(l,a," "); li[a[2]]=a[1] }
  while ((getline l < params) > 0) { split(l,a,"\t"); if (a[1] ~ /^[0-9]+$/) gen[a[1]]=a[2] }
  print "idx\tmodule\tpath\tsha256\tbytes\tlines\tkind\tgenerator\tin_bundle\tproject_imports"
  i=0
  while ((getline p < (T "/paths.txt")) > 0) {
    i++; m=p; sub(/\.lean$/,"",m); gsub(/\//,".",m)
    imps=""
    while ((getline line < p) > 0) {
      if (line ~ /^import LRSpectrumFull\./) { x=line; sub(/^import /,"",x); sub(/\r$/,"",x); imps = imps (imps==""?"":",") x }
    }
    close(p)
    kind="hand"; g="-"; inb="yes"
    if (p ~ /^LRSpectrumFull\/[^\/]*\.lean$/) kind="base"
    if (p ~ /^LRSpectrumFull\/NineSound\/G[0-9]+\//) {
      kind="generated"; q=p; sub(/^LRSpectrumFull\/NineSound\/G/,"",q); sub(/\/.*/,"",q); g=gen[q]
      b=p; sub(/.*\//,"",b)
      if (b ~ /^(D01|D2|TD[0-9_]+)\.lean$/) inb="no"
    }
    if (p == "LRSpectrumFull/NineSound/Assemble9.lean") { kind="generated"; g="mkfinal.sh" }
    if (p == "LRSpectrumFull/EightRunnersReal.lean" || p == "LRSpectrumFull/NineSound/Assemble9.lean" || p == "LRSpectrumFull/NineSound/Assemble9Final.lean") raw=1; else raw=0
    if (raw) kind="raw"
    printf "%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n", i, m, p, sha[p], by[p], li[p], kind, g, inb, imps
  }
}' > "$T/m.tsv"
BAD=$(awk -F'\t' 'NR==FNR{if(FNR>1)idx[$2]=$1; next} FNR>1{n=split($10,a,","); for(j=1;j<=n;j++) if(a[j]!="" && !(a[j] in idx && idx[a[j]]<$1)) print $2" imports "a[j]}' "$T/m.tsv" "$T/m.tsv" | head -5)
[ -z "$BAD" ] || { echo "ORDER VIOLATIONS: $BAD" >&2; exit 2; }
cp "$T/m.tsv" "$OUT.tmp" && mv "$OUT.tmp" "$OUT"
echo "wrote $OUT: $(($(wc -l < "$OUT")-1)) modules"
