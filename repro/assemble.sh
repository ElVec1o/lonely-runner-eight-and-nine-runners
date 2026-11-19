#!/bin/bash
# assemble.sh : how the 36-prime assembly module Assemble9 (and with it the conditional theorem nine_runners_final) was elaborated, with raw `lean` and not with lake.
# This is the nine-runner step alone.  The UNCONDITIONAL theorem needs the three steps of assemble_final.sh (EightRunnersReal, Assemble9, Assemble9Final).
#
# BACKGROUND (measured once, 2026-11-19).  The 36 per-prime libraries were built one prime at a time over several days and archived after
# each prime (tar of the .olean/.ilean/.trace/.hash files of NineSound/G<p>, 36 archives, 641 MB; ARCHIVES.sha256 lists their sha256).
# The archives contain no ir/*.c files.  After restoring them, `lake build --no-build` reports the restored modules as out of date although
# every trace input agrees (with an empty placeholder .c file the same module became up to date), so lake could not be used for the last step.
# `import` does not need the .c files, so Assemble9.lean was elaborated with the plain `lean` binary and a LEAN_PATH whose first entry is a
# directory ("farm") built from symbolic links: every entry of the lake library directory LRSpectrumFull/, except that NineSound/G<p> comes
# from the restored archives.  (Lean resolves a package root to the first LEAN_PATH entry that contains it, so a second root cannot overlay the same
# package; hence the farm.)  One lean process, once.  Measured (macOS, `time -l`): 36 primes 76 s wall, 5.76 GB peak RSS (baseline import of
# Final9 alone: 14 s, 5.50 GB; 2 primes 28.5 s cold; 4 primes 5.8 s, 5.75 GB).  Output: expected_output/assemble_raw.txt.
# If every module was built by lake in the same tree (build.sh --run), this script is not needed: `lake env lean Assemble9.lean` or check_axioms.sh does the job.
#
#   --plan   no lean, no extraction: checks that the inputs exist (archives with the recorded sha256, the lake library directory with the shared
#            modules), prints the LEAN_PATH and the commands it would run.  Exit 0 if the inputs are complete, 2 otherwise.
#   --run    extract the archives into WORK/root, build the farm, run `lean` on lean/LRSpectrumFull/NineSound/Assemble9.lean, judge the output.
# ENVIRONMENT
#   LEAN_DIR        the lean/ directory of this repository                                [../lean]
#   BUILD_LIB       lake library directory holding LRSpectrumFull/ (shared modules built)   [$LEAN_DIR/.lake/build/lib/lean]
#   ARCHIVES        directory with G<p>_lib.tgz (36 files); if unset the G<p> directories of BUILD_LIB are used as they are
#   PKG_LEAN_PATH   LEAN_PATH entries of Mathlib and the other packages and the Lean library (colon separated)  [from `lake env printenv LEAN_PATH` in LEAN_DIR, minus BUILD_LIB]
#   LEAN_BIN        the lean binary                                                         [lean]
#   WRAPPER, CEILING_MB [12000]   optional memory-watchdog launcher as in build.sh
#   WORK            scratch directory                                                       [./work/assemble]
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN_DIR=${LEAN_DIR:-$HERE/../lean}
BUILD_LIB=${BUILD_LIB:-$LEAN_DIR/.lake/build/lib/lean}
WORK=${WORK:-$HERE/work/assemble}
LEAN_BIN=${LEAN_BIN:-lean}
CEILING_MB=${CEILING_MB:-12000}
MODE=${1:---plan}
case "$MODE" in --plan|--run) ;; *) echo "usage: assemble.sh --plan | --run" >&2; exit 2 ;; esac
PRIMES=$(tail -n +2 "$HERE/PARAMS.tsv" | cut -f1)
BAD=0
[ -f "$LEAN_DIR/LRSpectrumFull/NineSound/Assemble9.lean" ] && echo "ok   source Assemble9.lean present" || { echo "FAIL source Assemble9.lean missing in $LEAN_DIR"; BAD=1; }
[ -f "$BUILD_LIB/LRSpectrumFull/NineSound/Final9.olean" ] && echo "ok   shared modules built: $BUILD_LIB/LRSpectrumFull/NineSound/Final9.olean" || { echo "FAIL $BUILD_LIB/LRSpectrumFull/NineSound/Final9.olean missing (build the shared prefix first: build.sh --run --to 370)"; BAD=1; }
if [ -n "$ARCHIVES" ]; then
  NA=0; NB=0
  for p in $PRIMES; do
    f=$ARCHIVES/G${p}_lib.tgz
    if [ ! -f "$f" ]; then echo "FAIL archive missing: $f"; NB=$((NB+1)); continue; fi
    want=$(awk -v n="G${p}_lib.tgz" '$2==n{print $1}' "$HERE/ARCHIVES.sha256"); have=$(shasum -a 256 "$f" | cut -d' ' -f1)
    if [ "$want" = "$have" ]; then NA=$((NA+1)); else echo "FAIL archive sha256 differs: G${p}_lib.tgz (archives are not byte-reproducible across rebuilds; compare the PD.olean instead)"; NB=$((NB+1)); fi
  done
  echo "archives: $NA of 36 match ARCHIVES.sha256, $NB missing or different"
  [ "$NB" = 0 ] || BAD=1
else
  for p in $PRIMES; do [ -f "$BUILD_LIB/LRSpectrumFull/NineSound/G$p/PD.olean" ] || { echo "FAIL no PD.olean for G$p in BUILD_LIB and ARCHIVES not set"; BAD=1; }; done
fi
if [ -z "$PKG_LEAN_PATH" ] && [ "$MODE" = "--run" ]; then PKG_LEAN_PATH=$(cd "$LEAN_DIR" && lake env printenv LEAN_PATH | tr ':' '\n' | grep -vxF "$BUILD_LIB" | tr '\n' ':' | sed 's/:$//'); fi
[ -n "$PKG_LEAN_PATH" ] || PKG_LEAN_PATH="<entries of Mathlib, Batteries, ... and the Lean library, from: cd lean && lake env printenv LEAN_PATH>"
LP="$WORK/farm:$PKG_LEAN_PATH"
echo "LEAN_PATH would be: $LP"
echo "step 1: for each p: tar xzf ARCHIVES/G<p>_lib.tgz -C $WORK/root          (creates $WORK/root/LRSpectrumFull/NineSound/G<p>)"
echo "step 2: farm: $WORK/farm/LRSpectrumFull/<entry> -> $BUILD_LIB/LRSpectrumFull/<entry>   for every entry except NineSound;"
echo "        $WORK/farm/LRSpectrumFull/NineSound/<entry> -> same, except NineSound/G<p> -> $WORK/root/LRSpectrumFull/NineSound/G<p>"
echo "step 3: LEAN_PATH=<above> $LEAN_BIN $LEAN_DIR/LRSpectrumFull/NineSound/Assemble9.lean   (expect: two lines 'depends on axioms: [propext, Classical.choice, Quot.sound]' for pd36 and nine_runners_final, then the #check line)"
if [ $BAD != 0 ]; then echo "ASSEMBLE PLAN INCOMPLETE"; exit 2; fi
[ "$MODE" = "--plan" ] && { echo "ASSEMBLE PLAN VALID"; exit 0; }

# ---- run --------------------------------------------------------------------------------------------------------------------
rm -rf "$WORK/root" "$WORK/farm"; mkdir -p "$WORK/root" "$WORK/farm/LRSpectrumFull/NineSound"
if [ -n "$ARCHIVES" ]; then for p in $PRIMES; do tar xzf "$ARCHIVES/G${p}_lib.tgz" -C "$WORK/root" || { echo "tar failed for G$p"; exit 1; }; done; fi
for e in "$BUILD_LIB"/LRSpectrumFull/*; do b=$(basename "$e"); [ "$b" = NineSound ] || ln -s "$e" "$WORK/farm/LRSpectrumFull/$b"; done
for e in "$BUILD_LIB"/LRSpectrumFull/NineSound/*; do
  b=$(basename "$e")
  case "$b" in G[0-9]*) [ -z "$ARCHIVES" ] && ln -s "$e" "$WORK/farm/LRSpectrumFull/NineSound/$b" ;; *) ln -s "$e" "$WORK/farm/LRSpectrumFull/NineSound/$b" ;; esac
done
if [ -n "$ARCHIVES" ]; then for p in $PRIMES; do ln -s "$WORK/root/LRSpectrumFull/NineSound/G$p" "$WORK/farm/LRSpectrumFull/NineSound/G$p"; done; fi
export LEAN_PATH="$LP"
if [ -n "$WRAPPER" ]; then $WRAPPER "$CEILING_MB" "$WORK" assemble /usr/bin/time -l "$LEAN_BIN" "$LEAN_DIR/LRSpectrumFull/NineSound/Assemble9.lean"; cp "$WORK/assemble.out" "$WORK/assemble_raw.txt"; cp "$WORK/assemble.err" "$WORK/assemble_time.txt"
else /usr/bin/time -l "$LEAN_BIN" "$LEAN_DIR/LRSpectrumFull/NineSound/Assemble9.lean" > "$WORK/assemble_raw.txt" 2> "$WORK/assemble_time.txt"; fi
NSTD=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" "$WORK/assemble_raw.txt")
NERR=$(grep -c -i "error\|sorry" "$WORK/assemble_raw.txt")
if [ "$NSTD" = 2 ] && [ "$NERR" = 0 ]; then echo "ASSEMBLE PASS: pd36 and nine_runners_final depend on [propext, Classical.choice, Quot.sound] only"; grep -E "real|maximum resident" "$WORK/assemble_time.txt"; exit 0
else echo "ASSEMBLE FAIL (see $WORK/assemble_raw.txt)"; exit 1; fi
