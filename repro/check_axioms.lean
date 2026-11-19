/-
# check_axioms.lean : print the axioms of the unconditional nine-runner theorem, of the eight-runner chain and of the 36 per-prime constants.  Builds NOTHING.

Run through `check_axioms.sh`, which only READS the .olean files of the closure of `LRSpectrumFull.NineSound.Assemble9Final`
(25,988 project modules; they must exist: see build.sh, assemble.sh and assemble_final.sh; the three modules EightRunnersReal, Assemble9 and
Assemble9Final are elaborated with raw lean, so set CHECK_LEAN_PATH to the LEAN_PATH printed by `assemble_final.sh --plan`).

Every `#print axioms` below on a real theorem must print exactly [propext, Classical.choice, Quot.sound].  The two planted
controls at the end (a direct and a transitive `sorry`) must print `sorryAx`: they show that a `sorry` anywhere below a
theorem would be visible in this printout.  No `sorry`, no `native_decide`, no axiom is used by this file except in the controls.

The headline theorem `nine_runners_unconditional` has NO hypothesis: `lrc7_of_eight` derives the eight-runner statement `LRC7` from
`EightRunnersReal.eight_runners_unconditional_real`.  Read the `#check` and `#print` output below against the statement in README.md.
The library modules in the closure contain 27 axioms in `EightCert27` and some stubs with `sorry` that are not on the main path; the
`#print axioms` lines below show that none of them is used.
-/
import LRSpectrumFull.NineSound.Assemble9Final

/-! ## The statements, as Lean prints them (read these against the English statement in README.md) -/

#check @LRSpectrumFull.NineSound.Plan9.Assemble9Final.nine_runners_unconditional
#check @LRSpectrumFull.NineSound.Plan9.Assemble9Final.lrc7_of_eight
#check @LRSpectrumFull.EightRunnersReal.eight_runners_unconditional_real
#check @LRSpectrumFull.BarajasSerra.LRC6_barajasSerra
#check @LRSpectrumFull.NineSound.Plan9.Assemble9.nine_runners_final
#check @LRSpectrumFull.NineSound.Plan9.Assemble9.pd36
#print LRSpectrumFull.NineSound.LRC7
#print LRSpectrumFull.NineSound.Plan9.S36L
#print LRSpectrumFull.NineSound.Plan9.PrimeData
#print LRSpectrumFull.ML
#print LRSpectrumFull.gap
#print LRSpectrumFull.nearestIntDist

/-! ## Axioms: the headline theorem, the assembled prime data, and the 36 per-prime constants -/

#print axioms LRSpectrumFull.NineSound.Plan9.Assemble9Final.nine_runners_unconditional
#print axioms LRSpectrumFull.NineSound.Plan9.Assemble9Final.lrc7_of_eight
#print axioms LRSpectrumFull.EightRunnersReal.eight_runners_unconditional_real
#print axioms LRSpectrumFull.BarajasSerra.LRC6_barajasSerra
#print axioms LRSpectrumFull.NineSound.Plan9.Assemble9.nine_runners_final
#print axioms LRSpectrumFull.NineSound.Plan9.Assemble9.pd36
#print axioms LRSpectrumFull.NineSound.G53.PD.primeData_53
#print axioms LRSpectrumFull.NineSound.G61.PD.primeData_61
#print axioms LRSpectrumFull.NineSound.G67.PD.primeData_67
#print axioms LRSpectrumFull.NineSound.G71.PD.primeData_71
#print axioms LRSpectrumFull.NineSound.G79.PD.primeData_79
#print axioms LRSpectrumFull.NineSound.G83.PD.primeData_83
#print axioms LRSpectrumFull.NineSound.G89.PD.primeData_89
#print axioms LRSpectrumFull.NineSound.G97.PD.primeData_97
#print axioms LRSpectrumFull.NineSound.G101.PD.primeData_101
#print axioms LRSpectrumFull.NineSound.G103.PD.primeData_103
#print axioms LRSpectrumFull.NineSound.G107.PD.primeData_107
#print axioms LRSpectrumFull.NineSound.G109.PD.primeData_109
#print axioms LRSpectrumFull.NineSound.G113.PD.primeData_113
#print axioms LRSpectrumFull.NineSound.G127.PD.primeData_127
#print axioms LRSpectrumFull.NineSound.G131.PD.primeData_131
#print axioms LRSpectrumFull.NineSound.G137.PD.primeData_137
#print axioms LRSpectrumFull.NineSound.G139.PD.primeData_139
#print axioms LRSpectrumFull.NineSound.G149.PD.primeData_149
#print axioms LRSpectrumFull.NineSound.G151.PD.primeData_151
#print axioms LRSpectrumFull.NineSound.G157.PD.primeData_157
#print axioms LRSpectrumFull.NineSound.G163.PD.primeData_163
#print axioms LRSpectrumFull.NineSound.G167.PD.primeData_167
#print axioms LRSpectrumFull.NineSound.G173.PD.primeData_173
#print axioms LRSpectrumFull.NineSound.G179.PD.primeData_179
#print axioms LRSpectrumFull.NineSound.G181.PD.primeData_181
#print axioms LRSpectrumFull.NineSound.G191.PD.primeData_191
#print axioms LRSpectrumFull.NineSound.G193.PD.primeData_193
#print axioms LRSpectrumFull.NineSound.G197.PD.primeData_197
#print axioms LRSpectrumFull.NineSound.G199.PD.primeData_199
#print axioms LRSpectrumFull.NineSound.G211.PD.primeData_211
#print axioms LRSpectrumFull.NineSound.G223.PD.primeData_223
#print axioms LRSpectrumFull.NineSound.G227.PD.primeData_227
#print axioms LRSpectrumFull.NineSound.G229.PD.primeData_229
#print axioms LRSpectrumFull.NineSound.G233.PD.primeData_233
#print axioms LRSpectrumFull.NineSound.G239.PD.primeData_239
#print axioms LRSpectrumFull.NineSound.G241.PD.primeData_241

/-! ## NEGATIVE CONTROLS (must print sorryAx; check_axioms.sh requires both) -/

theorem check_axioms_planted_sorry : (1 : Nat) = 2 := by sorry
theorem check_axioms_planted_sorry_user : (2 : Nat) = 3 := by
  have := check_axioms_planted_sorry
  omega

#print axioms check_axioms_planted_sorry
#print axioms check_axioms_planted_sorry_user
