/-
# Nine runners, part 14: delegated states as a logarithmic-depth table

Companion of `DrvFSound.lean` for the generator `gen_prime13`: the table of delegated states of the tasks is a function
`HT : ℕ → St` emitted as a balanced tree of definitions (`NineProbe/DrvF.lean`: `clampT`), not a list `HS`.
A list lookup `gtab HS i` costs about `i` kernel steps, cached per (suffix, remaining index), so the top tree, which looks up
every task state once, costs about `nT^2 / 2` steps of roughly 9.4 KB each (at p = 163 the `Top` module exceeds 8 GB).

* `primeData_of_partsG`   same conclusion `PrimeData p` as `primeData_of_partsF`; hypotheses: `HS : List St` with
  `hHS : HS.length = nT` is replaced by `HT : ℕ → St` with `NH`, `0 < NH`, `NH ≤ nT`, and the top tree and the tasks use
  `clampT HT NH` (clause a3: `clampT_surj`).
Nothing here is edited from `Drv*Sound.lean`; no `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.DrvFSound

namespace LRSpectrumFull.NineSound.Plan9

open LRSpectrumFull LRSpectrumFull.NineSound LRSpectrumFull.NineProbe

/-- **The assembly of one prime, table-valued form, delegated states as a function.**  Conclusion: `PrimeData p`. -/
theorem primeData_of_partsG (p : ℕ) (X0 X1 X2 : Ctx) (C0 : ℕ → ℕ) (CH : List (List (St × List ℕ))) (st : List ℕ) (nT : ℕ)
    (HT : ℕ → St) (NH : ℕ) (T1 T2 : ℕ → ℕ × ℕ × ℕ) (N1 N2 : ℕ) (S1 S2 : ℕ → List ℕ)
    (hTL : 0 < nT) (hNH : 0 < NH) (hNHle : NH ≤ nT) (hN1 : 0 < N1) (hN2 : 0 < N2)
    (h0 : TableOK9g X0 0 p) (h1 : TableOK9g X1 1 p) (h2 : TableOK9g X2 2 p)
    (htop : checkTree0 X0 C0 (clampT HT NH) (clampT T1 N1) = true)
    (ht : TasksUpTo X0 CH st nT (clampT HT NH) (clampT T1 N1) nT)
    (h6 : RootsUpToF X1 (ctT S1 N1) (clampT T2 N2) (clampT T1 N1) N1)
    (h7 : RootsUpToF X2 (ctT S2 N2) (fun _ => (0, 0, 0)) (clampT T2 N2) N2) : PrimeData p := by
  refine ⟨X0, X1, X2, C0, clampT HT NH, clampT T1 N1, clampT T2 N2, nT, N1, N2,
    tkC CH st nT, ctT S1 N1, ctT S2 N2, h0, h1, h2, htop, ht, ?_, ?_, ?_, h6, h7⟩
  · intro i
    obtain ⟨τ, hτ, h⟩ := clampT_surj HT NH hNH i
    exact ⟨τ, by omega, h⟩
  · intro i
    exact clampT_surj T1 N1 hN1 i
  · intro i
    exact clampT_surj T2 N2 hN2 i

end LRSpectrumFull.NineSound.Plan9
