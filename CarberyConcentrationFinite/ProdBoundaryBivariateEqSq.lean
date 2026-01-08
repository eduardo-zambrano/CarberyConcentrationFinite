/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Product Boundary Bivariate Equals Squared (For Aristotle)

This file contains the `prod_boundary_bivariate_eq_sq` lemma to be proved by Aristotle.

The lemma shows that the boundary terms and bivariate products combine to give
each element appearing exactly twice (squared product form).
-/

import CarberyConcentrationFinite.Basic


open scoped ENNReal NNReal BigOperators

open Finset

noncomputable section

/-- Key algebraic lemma: Boundary terms and bivariate products combine to give
    each element appearing exactly twice (squared product form).

    This is the abstract form of the fact that in the Carbery functional,
    each marginal appears exactly twice under independence.

    Structure of the LHS:
    - f₀ : boundary term at front
    - ∏_{j=0}^{n-2} (f_j * f_{j+1}) : bivariate products
    - f_{n-1} : boundary term at end

    Each index i appears exactly twice:
    - i=0: once at front, once in bivariate product (j=0, first factor)
    - i=k for 1≤k≤n-2: once in bivariate product (j=k, first factor),
      once in bivariate product (j=k-1, second factor)
    - i=n-1: once in bivariate product (j=n-2, second factor), once at end

    Therefore LHS = ∏_i f_i² -/
theorem prod_boundary_bivariate_eq_sq' {n : ℕ} (hn : n ≥ 2) (f : Fin n → ℝ≥0∞) :
    f ⟨0, by omega⟩ *
    (∏ j : Fin (n - 1), f ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩ *
                        f ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) *
    f ⟨n - 1, by omega⟩ =
    ∏ i : Fin n, f i * f i := by
  sorry

end
