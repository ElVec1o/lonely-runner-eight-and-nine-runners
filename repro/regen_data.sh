#!/bin/bash
# regen_data.sh : regenerate the generated Lean sources (NineSound/G<p>/*, and Assemble9) with the Rust generators of generators/ and compare them,
# file by file, with the sha256 column of MANIFEST.tsv.  Runs NO Lean and NO lake; only rustc and the generators (about 1-3 s per prime, below 100 MB).
#
#   --all              all 36 primes of PARAMS.tsv
#   --primes "53 61"   the listed primes
#   --sample           primes 53 61 71 163 (generators gen_prime13, gen_prime12, gen_prime12, gen_prime13) and the Assemble9 step   [default]
#   --install          copy the regenerated files that are listed in MANIFEST.tsv with in_bundle=no (D01, D2, TD*) into LEAN_DIR (only when every
#                      file of that prime compared identical), so that build.sh --plan can validate them
#   --work DIR         scratch directory (default ./work); regenerated trees are deleted after the comparison unless --keep
#   --keep             keep the regenerated trees
# ENVIRONMENT  LEAN_DIR [../lean]   WRAPPER (a launcher `WRAPPER CEILING LOGDIR NAME cmd...`, e.g. a memory watchdog)   CEILING_MB [3000]   RUSTC_CEILING_MB [1500]   RUSTC [rustc]
# For every prime the generator named in PARAMS.tsv is run as
#     gen_prime1x P WORK/gen/G<P> LIM CHUNK 1 120 120 40 40 16 40 emit
# and every produced *.lean file that appears in MANIFEST.tsv is compared with its sha256; files not in the manifest (control modules such as
# Ctl9.lean, which are not in the import closure) are counted separately.  The Assemble9 step runs generators/mkfinal.sh with the 36 primes of S36.
# Output: a summary line per prime and logs/regen_summary.txt.  Exit 0 iff no compared file differs.
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN_DIR=${LEAN_DIR:-$HERE/../lean}
WORK=$HERE/work; CEILING_MB=${CEILING_MB:-3000}; RUSTC=${RUSTC:-rustc}
PRIMES=""; SAMPLE=1; INSTALL=0; KEEP=0
while [ $# -gt 0 ]; do
  case "$1" in
    --all) PRIMES=$(tail -n +2 "$HERE/PARAMS.tsv" | cut -f1 | tr '\n' ' '); SAMPLE=0 ;;
    --primes) PRIMES=$2; SAMPLE=0; shift ;;
    --sample) SAMPLE=1 ;;
    --install) INSTALL=1 ;;
    --work) WORK=$2; shift ;;
    --keep) KEEP=1 ;;
    -h|--help) sed -n '2,22p' "$0"; exit 0 ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
  shift
done
[ -n "$PRIMES" ] || PRIMES="53 61 71 163"
mkdir -p "$WORK/bin" "$WORK/gen" "$HERE/logs"
SUM=$HERE/logs/regen_summary.txt; : > "$SUM"
for g in gen_prime12 gen_prime13; do
  if [ ! -x "$WORK/bin/$g" ]; then
    echo "compiling $g"
    if [ -n "$WRAPPER" ]; then $WRAPPER "${RUSTC_CEILING_MB:-1500}" "$WORK" "rustc_$g" $RUSTC -O -o "$WORK/bin/$g" "$HERE/generators/$g.rs" || { echo "rustc failed"; exit 2; }
    else $RUSTC -O -o "$WORK/bin/$g" "$HERE/generators/$g.rs" 2> "$WORK/rustc_$g.err" || { echo "rustc failed (see $WORK/rustc_$g.err)"; exit 2; }; fi
  fi
done
# manifest: path -> sha256 (and in_bundle)
awk -F'\t' 'NR>1{print $3 "\t" $4 "\t" $9}' "$HERE/MANIFEST.tsv" > "$WORK/manifest_paths.tsv"
TOTI=0; TOTD=0; TOTN=0; FAILP=0
compare_dir() {   # DIR PREFIX(path prefix inside the Lean root)  -> prints "identical different notinmanifest"; lists differing files into $WORK/different.txt
  ( cd "$1" && ls | grep '\.lean$' | while IFS= read -r f; do printf '%s\0' "$f"; done | xargs -0 shasum -a 256 ) > "$WORK/have.sha"
  awk -v pre="$2" -v mf="$WORK/manifest_paths.tsv" 'BEGIN { while ((getline l < mf) > 0) { split(l, a, "\t"); sha[a[1]] = a[2] } }
    { f = $2; k = pre "/" f
      if (!(k in sha)) nm++; else if (sha[k] == $1) id++; else { df++; print k >> (ENVIRON["WORK"] "/different.txt") } }
    END { printf "%d %d %d\n", id + 0, df + 0, nm + 0 }' "$WORK/have.sha"
}
export WORK
for p in $PRIMES; do
  row=$(awk -F'\t' -v p=$p '$1==p' "$HERE/PARAMS.tsv"); [ -n "$row" ] || { echo "prime $p not in PARAMS.tsv"; continue; }
  g=$(echo "$row" | cut -f2); lim=$(echo "$row" | cut -f3); ch=$(echo "$row" | cut -f4)
  OUT=$WORK/gen/G$p; rm -rf "$OUT"; : > "$WORK/different.txt"
  T0=$(date +%s)
  if [ -n "$WRAPPER" ]; then $WRAPPER "$CEILING_MB" "$WORK" "gen_$p" "$WORK/bin/$g" $p "$OUT" $lim $ch 1 120 120 40 40 16 40 emit
  else "$WORK/bin/$g" $p "$OUT" $lim $ch 1 120 120 40 40 16 40 emit > "$WORK/gen_$p.out" 2>&1; fi
  RC=$?; T1=$(date +%s)
  if [ ! -f "$OUT/order.txt" ]; then echo "p=$p generator FAILED (rc $RC)" | tee -a "$SUM"; FAILP=$((FAILP+1)); continue; fi
  read -r I D N <<< "$(compare_dir "$OUT" "LRSpectrumFull/NineSound/G$p")"
  echo "p=$p $g LIM=$lim CHUNK=$ch: $((I+D+N)) files; identical to manifest $I, different $D, not in manifest (not in the import closure) $N; $((T1-T0)) s" | tee -a "$SUM"
  [ "$D" = 0 ] || { head -5 "$WORK/different.txt"; FAILP=$((FAILP+1)); }
  TOTI=$((TOTI+I)); TOTD=$((TOTD+D)); TOTN=$((TOTN+N))
  if [ $INSTALL = 1 ] && [ "$D" = 0 ]; then
    n=0; while IFS=$'\t' read -r path sha inb; do
      case "$path" in LRSpectrumFull/NineSound/G$p/*) [ "$inb" = no ] && [ -f "$OUT/$(basename "$path")" ] && { mkdir -p "$LEAN_DIR/$(dirname "$path")"; cp "$OUT/$(basename "$path")" "$LEAN_DIR/$path"; n=$((n+1)); } ;; esac
    done < "$WORK/manifest_paths.tsv"
    echo "     installed $n omitted-family files of G$p into $LEAN_DIR"
  fi
  [ $KEEP = 1 ] || rm -rf "$OUT"
done
# Assemble9 step
if [ $SAMPLE = 1 ] || [ "$PRIMES" = "$(tail -n +2 "$HERE/PARAMS.tsv" | cut -f1 | tr '\n' ' ')" ]; then
  AD=$WORK/gen/asm; rm -rf "$AD"; mkdir -p "$AD"
  OUTDIR="$AD" bash "$HERE/generators/mkfinal.sh" Assemble9 $(tail -n +2 "$HERE/PARAMS.tsv" | cut -f1 | tr '\n' ' ') > /dev/null
  want=$(awk -F'\t' '$3=="LRSpectrumFull/NineSound/Assemble9.lean"{print $4}' "$HERE/MANIFEST.tsv"); have=$(shasum -a 256 "$AD/Assemble9.lean" | cut -d' ' -f1)
  if [ "$want" = "$have" ]; then echo "Assemble9.lean: regenerated by mkfinal.sh, identical to manifest" | tee -a "$SUM"; TOTI=$((TOTI+1)); else echo "Assemble9.lean: DIFFERENT from manifest" | tee -a "$SUM"; TOTD=$((TOTD+1)); fi
  [ $KEEP = 1 ] || rm -rf "$AD"
fi
echo "TOTAL: identical $TOTI, different $TOTD, not in manifest $TOTN, generator failures $FAILP" | tee -a "$SUM"
[ "$TOTD" = 0 ] && [ "$FAILP" = 0 ]
