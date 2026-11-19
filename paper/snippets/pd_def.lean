def PrimeData (p : ℕ) : Prop :=
  ∃ (X0 X1 X2 : Ctx) (C0 : ℕ → ℕ) (H : ℕ → St) (nx1 nx2 : ℕ → ℕ × ℕ × ℕ) (nT n1 n2 : ℕ)
    (Ct C1 C2 : ℕ → ℕ → ℕ),
    TableOK9g X0 0 p ∧ TableOK9g X1 1 p ∧ TableOK9g X2 2 p ∧
    checkTree0 X0 C0 H nx1 = true ∧
    (∀ τ, τ < nT → checkTask X0 (Ct τ) nx1 (H τ) = true) ∧
    (∀ i, ∃ τ, τ < nT ∧ H i = H τ) ∧
    (∀ i, ∃ k, k < n1 ∧ nx1 i = nx1 k) ∧
    (∀ i, ∃ k, k < n2 ∧ nx2 i = nx2 k) ∧
    (∀ k, k < n1 → checkRootN X1 (C1 k) nx2 (nx1 k) = true) ∧
    (∀ k, k < n2 → checkRootN X2 (C2 k) (fun _ => (0, 0, 0)) (nx2 k) = true)
