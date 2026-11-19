/-
# Nine runners, soundness part 4d: `hier_of_good` with `Sem` at levels 1 and 2 discharged

`hier_good9`: from a good class set `V` (`Good9 p V`) and the table statements, the hierarchical certificate
cannot be accepted: no semantic hypothesis is left except the existence of `V` (`lemma7Check_of_noGood`, part 5).
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Assembly3
import LRSpectrumFull.NineSound.Level2B

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe

theorem hier_good9 {X0 X1 X2 : Ctx} {p : ℕ} {V : Finset ℕ} (hp : 1 < p) (hp2 : p % 2 = 1)
    (hV : Good9 p V) (hT0 : TableOK9g X0 0 p) (hT1 : TableOK9g X1 1 p) (hT2 : TableOK9g X2 2 p)
    (hW0 : X0.W < 2 ^ 15) (hW1 : X1.W < 2 ^ 15) (hW2 : X2.W + 1 < 2 ^ 16) (hW2' : X2.W < 2 ^ 15)
    (C0 : ℕ → ℕ) (H : ℕ → St) (nx1 nx2 : ℕ → ℕ × ℕ × ℕ) (nT n1 n2 : ℕ) (Ct C1 C2 : ℕ → ℕ → ℕ)
    (a1 : checkTree0 X0 C0 H nx1 = true)
    (a2 : ∀ τ, τ < nT → checkTask X0 (Ct τ) nx1 (H τ) = true)
    (a3 : ∀ i, ∃ τ, τ < nT ∧ H i = H τ)
    (a4 : ∀ i, ∃ k, k < n1 ∧ nx1 i = nx1 k) (a5 : ∀ i, ∃ k, k < n2 ∧ nx2 i = nx2 k)
    (a6 : ∀ k, k < n1 → checkRootN X1 (C1 k) nx2 (nx1 k) = true)
    (a7 : ∀ k, k < n2 → checkRootN X2 (C2 k) (fun _ => (0, 0, 0)) (nx2 k) = true) : False :=
  hier_of_good hp hp2 hV hT0 hT1 hT2 hW0 hW2 (s1 hp2 hV hT1 hW1) (s2 hp2 hV hT2 hW2')
    C0 H nx1 nx2 nT n1 n2 Ct C1 C2 a1 a2 a3 a4 a5 a6 a7

end LRSpectrumFull.NineSound
