/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Term Equals Product Squared (For Aristotle)

This file contains the `term_eq_prod_sq` lemma to be proved by Aristotle.

The lemma shows that in the Carbery functional under independence, each marginal
appears exactly twice, giving a squared product structure.
-/

import CarberyConcentrationFinite.Basic

open scoped ENNReal NNReal BigOperators

open Finset

noncomputable section

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-- Key algebraic lemma: The boundary terms and bivariate products combine to give
    each marginal appearing exactly twice.

    Structure of the LHS:
    - p₀(s₀) : boundary term at front
    - ∏_{j=0}^{n-2} p_j(s_j) : first product (indices 0 to n-2)
    - ∏_{j=0}^{n-2} p_{j+1}(s_{j+1}) : second product (indices 1 to n-1)
    - p_{n-1}(s_{n-1}) : boundary term at end

    Each index i appears exactly twice:
    - i=0: once at front, once in first product (j=0)
    - i=k for 1≤k≤n-2: once in first product (j=k), once in second product (j=k-1)
    - i=n-1: once in second product (j=n-2), once at end

    Therefore LHS = ∏_i p_i(s_i)² = (∏_i p_i(s_i)) * (∏_i p_i(s_i)) -/
theorem term_eq_prod_sq (hn : n ≥ 2) (p : JointPMF Ω) (s : ∀ i, Ω i) :
    p.marginal ⟨0, by omega⟩ (s ⟨0, by omega⟩) *
    (∏ j : Fin (n - 1), p.marginal ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩
                         (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)) *
    (∏ j : Fin (n - 1), p.marginal ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩
                         (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩)) *
    p.marginal ⟨n - 1, by omega⟩ (s ⟨n - 1, by omega⟩) =
    (∏ i : Fin n, p.marginal i (s i)) * (∏ i : Fin n, p.marginal i (s i)) := by
  -- The key insight is that each marginal p_i(s_i) appears exactly twice on the LHS.
  -- We need to show this equals (∏_i p_i)².
  --
  -- Approach: Use Fin.prod_univ_castSucc and Fin.prod_univ_succ to decompose
  -- the RHS products and show they match the LHS structure.
  sorry

end
