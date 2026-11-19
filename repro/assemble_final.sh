#!/bin/bash
# assemble_final.sh : how the UNCONDITIONAL nine-runner theorem was assembled, with raw `lean` (one process per step) and not with lake.
#
#   Statement:  LRSpectrumFull.NineSound.Plan9.Assemble9Final.nine_runners_unconditional :
#               forall v : Fin 8 -> Z, (forall i, 0 < v i) -> 1/9 <= ML v      (axioms: propext, Classical.choice, Quot.sound)
#   Chain:      EightRunnersReal (LRC6 of Barajas and Serra, built by lake from the sources in lean/, plus the 27 per-prime kernel checks
#               lemma7Check 7 p = true, p in 31..163, staged modules E8Stage.P<p>, built OUTSIDE lake: repro/eight/stage)
#               -> Assemble9 (36 per-prime tables, restored archives; see assemble.sh)  -> Assemble9Final (bridge LRC7 from the eight-runner theorem).
#
# THREE RAW-LEAN STEPS (each one lean process; the three modules have kind `raw` in MANIFEST.tsv and are skipped by build.sh --run):
#     1. EightRunnersReal   -R lean -o farm/.../EightRunnersReal.olean   (measured: 127 s wall, 4.53 GB peak RSS)
#     2. Assemble9          -R lean -o farm/.../NineSound/Assemble9.olean (measured: 91 s, 5.57 GB)
#     3. Assemble9Final     -R lean -o farm/.../NineSound/Assemble9Final.olean (measured: 112 s, 5.91 GB); prints the axioms of
#                           lrc7_of_eight and nine_runners_unconditional.
#   (macOS, `time -l`, wrapper ceiling 9000 MB, one run each, 2026-11-19.)
#
# HONEST LIMITS
#   * Lake does not track these three modules: the 36 per-prime archives contain no ir/*.c files (so lake reports the restored modules out of date),
#     and the 27 staged eight-runner libraries live outside the lake package.  The assembly is therefore one raw-lean elaboration over RESTORED /
#     STAGED oleans, not a from-scratch build.
#   * The per-prime nine-runner oleans (archives, ARCHIVES.sha256) and the staged eight-runner oleans (E8STAGE_OLEANS.sha256, 949 files) were NOT
#     recompiled in the final run; they were produced earlier (the 36 archives by the per-prime builds of results.tsv; the 27 staged libraries
#     on 2026-09-24..30 with KEEP=1 builds), and their hashes / sizes are recorded.  The shipped staged sources differ from the compiled ones in line 1
#     only (README, repro/eight/README.md).
#   * The final oleans of the three steps were deleted after the run (about 3 GB scratch); this script regenerates them (about 10 minutes plus restore).
#
#   --plan   no lean, no extraction: checks that every input exists (the 36 archives with their recorded sha256, the 27 staged Asm.olean files,
#            the lake library directory with the shared modules incl. EightE5 and BarajasSerraLRC6Plan) and prints the commands.  Exit 0 / 2.
#   --run    extract the archives, build the symlink farm, run the three steps, judge the output of step 3.  Exit 0 PASS / 1 FAIL / 2 inputs missing.
# ENVIRONMENT (defaults in brackets)
#   LEAN_DIR       the lean/ directory of this repository                                       [../lean]
#   BUILD_LIB      lake library directory holding LRSpectrumFull/ (built shared modules)        [$LEAN_DIR/.lake/build/lib/lean]
#   ARCHIVES       directory with G<p>_lib.tgz (36 files); if unset the G<p> directories of BUILD_LIB are used  []
#   STAGE_OLEAN    directory holding E8Stage/P<p>/{Base,Tab,Top,S*,Asm}.olean of the 27 primes   [eight/stage/work/olean]
#   PKG_LEAN_PATH  LEAN_PATH entries of Mathlib, Batteries, ... and the Lean library (colon separated)  [from `lake env printenv LEAN_PATH` in LEAN_DIR, minus BUILD_LIB]
#   LEAN_BIN       the lean binary [lean];  WRAPPER, CEILING_MB [12000]: optional memory-watchdog launcher `WRAPPER CEILING LOGDIR NAME cmd...`
#   WORK           scratch directory [./work/assemble_final]
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN_DIR=${LEAN_DIR:-$HERE/../lean}
BUILD_LIB=${BUILD_LIB:-$LEAN_DIR/.lake/build/lib/lean}
STAGE_OLEAN=${STAGE_OLEAN:-$HERE/eight/stage/work/olean}
WORK=${WORK:-$HERE/work/assemble_final}
LEAN_BIN=${LEAN_BIN:-lean}
CEILING_MB=${CEILING_MB:-12000}
MODE=${1:---plan}
case "$MODE" in --plan|--run) ;; *) echo "usage: assemble_final.sh --plan | --run" >&2; exit 2 ;; esac
PRIMES=$(tail -n +2 "$HERE/PARAMS.tsv" | cut -f1)
PR27="31 37 43 47 53 59 61 67 71 73 79 83 89 97 101 103 107 109 113 127 131 137 139 149 151 157 163"
BAD=0
for m in EightRunnersReal NineSound/Assemble9 NineSound/Assemble9Final; do
  [ -f "$LEAN_DIR/LRSpectrumFull/$m.lean" ] && echo "ok   source $m.lean present" || { echo "FAIL source $m.lean missing in $LEAN_DIR"; BAD=1; }
done
for m in NineSound/Final9 EightE5 BarajasSerraLRC6Plan BarajasSerraLRC6; do
  [ -f "$BUILD_LIB/LRSpectrumFull/$m.olean" ] && echo "ok   shared module built: $m" || { echo "FAIL $BUILD_LIB/LRSpectrumFull/$m.olean missing (build the shared modules first: build.sh --run)"; BAD=1; }
done
NS=0; for p in $PR27; do [ -f "$STAGE_OLEAN/E8Stage/P$p/Asm.olean" ] && NS=$((NS+1)) || echo "FAIL staged olean missing: E8Stage/P$p/Asm.olean"; done
echo "staged eight-runner libraries: $NS of 27 Asm.olean present in $STAGE_OLEAN"; [ "$NS" = 27 ] || BAD=1
if [ -n "$ARCHIVES" ]; then
  NA=0; NB=0
  for p in $PRIMES; do
    f=$ARCHIVES/G${p}_lib.tgz
    if [ ! -f "$f" ]; then echo "FAIL archive missing: $f"; NB=$((NB+1)); continue; fi
    want=$(awk -v n="G${p}_lib.tgz" '$2==n{print $1}' "$HERE/ARCHIVES.sha256"); have=$(shasum -a 256 "$f" | cut -d' ' -f1)
    if [ "$want" = "$have" ]; then NA=$((NA+1)); else echo "FAIL archive sha256 differs: G${p}_lib.tgz"; NB=$((NB+1)); fi
  done
  echo "archives: $NA of 36 match ARCHIVES.sha256, $NB missing or different"; [ "$NB" = 0 ] || BAD=1
else
  for p in $PRIMES; do [ -f "$BUILD_LIB/LRSpectrumFull/NineSound/G$p/PD.olean" ] || { echo "FAIL no PD.olean for G$p in BUILD_LIB and ARCHIVES not set"; BAD=1; }; done
fi
if [ -z "$PKG_LEAN_PATH" ] && [ "$MODE" = "--run" ]; then PKG_LEAN_PATH=$(cd "$LEAN_DIR" && lake env printenv LEAN_PATH | tr ':' '\n' | grep -vxF "$BUILD_LIB" | tr '\n' ':' | sed 's/:$//'); fi
[ -n "$PKG_LEAN_PATH" ] || PKG_LEAN_PATH="<entries of Mathlib, Batteries, ... and the Lean library, from: cd lean && lake env printenv LEAN_PATH>"
LP="$WORK/farm:$PKG_LEAN_PATH:$STAGE_OLEAN"
echo "LEAN_PATH would be: $LP"
echo "farm: $WORK/farm/LRSpectrumFull/<entry> -> $BUILD_LIB/LRSpectrumFull/<entry> for every entry except NineSound; NineSound/<entry> likewise, except NineSound/G<p> -> $WORK/root (restored archives)"
echo "step 1: LEAN_PATH=<above> $LEAN_BIN -R $LEAN_DIR -o $WORK/farm/LRSpectrumFull/EightRunnersReal.olean $LEAN_DIR/LRSpectrumFull/EightRunnersReal.lean"
echo "step 2: same for NineSound/Assemble9   (expect 'depends on axioms: [propext, Classical.choice, Quot.sound]' for pd36 and nine_runners_final)"
echo "step 3: same for NineSound/Assemble9Final (expect the same line for lrc7_of_eight and nine_runners_unconditional, then the #check line)"
if [ $BAD != 0 ]; then echo "ASSEMBLE-FINAL PLAN INCOMPLETE"; exit 2; fi
[ "$MODE" = "--plan" ] && { echo "ASSEMBLE-FINAL PLAN VALID"; exit 0; }

# ---- run --------------------------------------------------------------------------------------------------------------------
rm -rf "$WORK/root" "$WORK/farm"; mkdir -p "$WORK/root" "$WORK/farm/LRSpectrumFull/NineSound"
if [ -n "$ARCHIVES" ]; then for p in $PRIMES; do tar xzf "$ARCHIVES/G${p}_lib.tgz" -C "$WORK/root" || { echo "tar failed for G$p"; exit 2; }; done; fi
for e in "$BUILD_LIB"/LRSpectrumFull/*; do b=$(basename "$e"); [ "$b" = NineSound ] || ln -s "$e" "$WORK/farm/LRSpectrumFull/$b"; done
for e in "$BUILD_LIB"/LRSpectrumFull/NineSound/*; do
  b=$(basename "$e")
  case "$b" in G[0-9]*) [ -z "$ARCHIVES" ] && ln -s "$e" "$WORK/farm/LRSpectrumFull/NineSound/$b" ;; *) ln -s "$e" "$WORK/farm/LRSpectrumFull/NineSound/$b" ;; esac
done
if [ -n "$ARCHIVES" ]; then for p in $PRIMES; do ln -s "$WORK/root/LRSpectrumFull/NineSound/G$p" "$WORK/farm/LRSpectrumFull/NineSound/G$p"; done; fi
export LEAN_PATH="$LP"
step() { # NAME MODULE-PATH (relative to LRSpectrumFull/, without .lean)
  local n=$1 m=$2
  local src="$LEAN_DIR/LRSpectrumFull/$m.lean" out="$WORK/farm/LRSpectrumFull/$m.olean"
  rm -f "$WORK/$n.out" "$WORK/$n.err"
  if [ -n "$WRAPPER" ]; then $WRAPPER "$CEILING_MB" "$WORK" "$n" /usr/bin/time -l "$LEAN_BIN" -R "$LEAN_DIR" -o "$out" "$src"
  else /usr/bin/time -l "$LEAN_BIN" -R "$LEAN_DIR" -o "$out" "$src" > "$WORK/$n.out" 2> "$WORK/$n.err"; fi
  echo "== step $n ($m)"; grep -E "error|maximum resident|real" "$WORK/$n.err" | head -5
}
step s1_real EightRunnersReal
step s2_a9 NineSound/Assemble9
step s3_a9f NineSound/Assemble9Final
cat "$WORK/s3_a9f.out"
NSTD=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" "$WORK/s3_a9f.out")
NERR=$(cat "$WORK"/s?_*.out "$WORK"/s?_*.err | grep -c -i "error\|sorry")
if [ "$NSTD" = 2 ] && [ "$NERR" = 0 ] && [ -f "$WORK/farm/LRSpectrumFull/NineSound/Assemble9Final.olean" ]; then
  echo "ASSEMBLE-FINAL PASS: lrc7_of_eight and nine_runners_unconditional depend on [propext, Classical.choice, Quot.sound] only"; exit 0
else echo "ASSEMBLE-FINAL FAIL (see $WORK/s*_*.out and .err)"; exit 1; fi
