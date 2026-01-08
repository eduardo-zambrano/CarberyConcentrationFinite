/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Product Boundary Bivariate Equals Squared (Standalone for Aristotle)

Standalone file for Aristotle to prove the key Fin index algebra lemma.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ENNReal.Basic

open scoped ENNReal BigOperators

open Finset

noncomputable section

/-- Key algebraic lemma: Boundary terms and bivariate products combine to give
    each element appearing exactly twice (squared product form).

    Structure of the LHS:
    - f₀ : boundary term at front
    - ∏_{j=0}^{n-2} (f_j * f_{j+1}) : bivariate products
    - f_{n-1} : boundary term at end

    Each index i appears exactly twice on the LHS.
    Therefore LHS = ∏_i (f_i * f_i) -/
theorem prod_boundary_bivariate_eq_sq {n : ℕ} (hn : n ≥ 2) (f : Fin n → ℝ≥0∞) :
    f ⟨0, by omega⟩ *
    (∏ j : Fin (n - 1), f ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩ *
                        f ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) *
    f ⟨n - 1, by omega⟩ =
    ∏ i : Fin n, f i * f i := by
  sorry

end
