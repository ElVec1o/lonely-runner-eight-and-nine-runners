def IsCE9 (v : Fin 8 → ℤ) : Prop :=
  (∀ i, 0 < v i) ∧ Finset.univ.gcd v = 1 ∧ ML v < 1 / 9
