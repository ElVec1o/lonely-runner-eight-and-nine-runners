/-
# Nine runners, soundness part 3e: `hier_complete` with the semantic predicates instantiated

`hier_of_good` applies the assembly theorem `hier_complete` (Hier.lean) to `Cmp0 p V`, `Cmp1 p V`, `Cmp2 p V`
(Level0/1/2).  Discharged here from `Good9 p V` and the table statements `TableOK9g`: the level-0 `Sem`, the
delegation transfer `hdel`, the root `hroot`, `hr0`-`hr2`, the transfers `t01`, `t12` and the infeasible roots
`inf1`, `inf2`.  The ONLY semantic hypotheses left are `S1`, `S2`: `Sem X1 (Cmp1 ..)`, `Sem X2 (Cmp2 ..)`
(`bound`, `nocov` follow from `sem_bound_of`/`sem_nocov_of` once `Compl` is shown, `branch` is the level-1/2
role analysis); and the existence of `V` (`lemma7Check_of_noGood`, not in this part).
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Level2

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe

theorem hier_of_good {X0 X1 X2 : Ctx} {p : ℕ} {V : Finset ℕ} (hp : 1 < p) (hp2 : p % 2 = 1)
    (hV : Good9 p V) (hT0 : TableOK9g X0 0 p) (hT1 : TableOK9g X1 1 p) (hT2 : TableOK9g X2 2 p)
    (hW0 : X0.W < 2 ^ 15) (hW2 : X2.W + 1 < 2 ^ 16)
    (S1 : Sem X1 (Cmp1 X1 p V)) (S2 : Sem X2 (Cmp2 X2 p V))
    (C0 : ℕ → ℕ) (H : ℕ → St) (nx1 nx2 : ℕ → ℕ × ℕ × ℕ) (nT n1 n2 : ℕ) (Ct C1 C2 : ℕ → ℕ → ℕ)
    (a1 : checkTree0 X0 C0 H nx1 = true)
    (a2 : ∀ τ, τ < nT → checkTask X0 (Ct τ) nx1 (H τ) = true)
    (a3 : ∀ i, ∃ τ, τ < nT ∧ H i = H τ)
    (a4 : ∀ i, ∃ k, k < n1 ∧ nx1 i = nx1 k) (a5 : ∀ i, ∃ k, k < n2 ∧ nx2 i = nx2 k)
    (a6 : ∀ k, k < n1 → checkRootN X1 (C1 k) nx2 (nx1 k) = true)
    (a7 : ∀ k, k < n2 → checkRootN X2 (C2 k) (fun _ => (0, 0, 0)) (nx2 k) = true) : False :=
  hier_complete X0 X1 X2 (Cmp0 X0 p V) (Cmp1 X1 p V) (Cmp2 X2 p V)
    (sem0 (by omega) hV hT0 hW0) S1 S2 C0 H nx1 nx2 nT n1 n2 Ct C1 C2 a1 a2 a3 a4 a5 a6 a7 hT2.1
    (hroot0 hp hp2 hV hT0) (fun s h hs he => hdel0 hT0 s h hs he)
    (fun s hs i => hr0 s hs i) (fun s hs i => hr1 s hs i) (fun s hs i => hr2 s hs i)
    (fun s i hs hl => t01 hp hp2 hV hT0 hT1 nx1 s i hs hl)
    (fun s i hs hl => t12 hp hV hT1 hT2 hW2 nx2 s i hs hl)
    (fun d hd hl => inf1 (by omega) hV d hd hl) (fun d hd hl => inf2 d hd hl)

end LRSpectrumFull.NineSound
