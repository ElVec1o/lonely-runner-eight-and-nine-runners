def LRC6 : Prop :=
  ∀ u : Fin (5 + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((5 : ℝ) + 2) ≤ ML u
