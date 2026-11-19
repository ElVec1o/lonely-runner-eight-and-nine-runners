/-
# Nine runners, part 11: assembly of the 36 per-prime theorems (generic part)

The campaign proves `PrimeData p` for each prime `p` of `S36` in a generated module `G<p>.PD`, one prime at a time.
This file is the generic part of the last step; the modules that import the generated `G<p>.PD` are produced by
`repro/generators/mkfinal.sh` (`Final9Test` for a subset of primes, `Final36` for all of `S36`).

* `primeData_all_of_split`   `PrimeData` for the primes of a set `K` (closed by generated modules) and for the primes of
                             `S36` outside `K` (explicit hypothesis) gives `PrimeData` for all of `S36`;
* `nine_runners_of_closed`   the nine-runner theorem with exactly two kinds of hypothesis: `LRC7` and `PrimeData p` for the
                             primes of `S36` not in `K`.  With `K = S36` the second kind is empty.

The only hypotheses of the whole nine-runner chain are `LRC7` (LRC for seven speeds, eight runners; the statement of
`EightRunnersReal.eight_runners_unconditional_real`, label VERIFIED outside lake build) and the `PrimeData p`.
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Plan9Glue

namespace LRSpectrumFull.NineSound.Plan9

open LRSpectrumFull LRSpectrumFull.NineSound

theorem primeData_all_of_split (K : Finset ℕ) (hk : ∀ p ∈ K, PrimeData p)
    (hr : ∀ p ∈ S36, p ∉ K → PrimeData p) : ∀ p ∈ S36, PrimeData p := by
  intro p hp
  by_cases h : p ∈ K
  · exact hk p h
  · exact hr p hp h

theorem nine_runners_of_closed (h7 : LRC7) (K : Finset ℕ) (hk : ∀ p ∈ K, PrimeData p)
    (hr : ∀ p ∈ S36, p ∉ K → PrimeData p) (v : Fin 8 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 9 ≤ ML v :=
  nine_runners_of_data h7 (primeData_all_of_split K hk hr) v hv

end LRSpectrumFull.NineSound.Plan9
