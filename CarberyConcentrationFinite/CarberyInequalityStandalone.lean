/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Carbery's Inequality - Standalone for Aristotle

This file contains a standalone version of Carbery's inequality for Aristotle to prove.

**IMPORTANT**: This uses COUNTING MEASURE norms (unweighted sums), NOT marginal-weighted norms.
The previous version with marginal-weighted norms was DISPROVED by Aristotle.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.MeanInequalities

open scoped ENNReal BigOperators
open Finset

noncomputable section

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-- A joint probability mass function on finite spaces. -/
structure JointPMF (Ω : Fin n → Type*) [∀ i, Fintype (Ω i)] where
  prob : (∀ i, Ω i) → ℝ≥0∞
  prob_le_one : ∀ x, prob x ≤ 1
  sum_eq_one : ∑ x : ∀ i, Ω i, prob x = 1

/-- The marginal distribution on coordinate i. -/
def JointPMF.marginal (p : JointPMF Ω) (i : Fin n) (s : Ω i) : ℝ≥0∞ :=
  ∑ x : ∀ j, Ω j, if x i = s then p.prob x else 0

/-- Bivariate marginal for consecutive pairs. -/
def JointPMF.bivariateMarginai (p : JointPMF Ω) (i : Fin (n - 1))
    (s : Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
    (t : Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩) : ℝ≥0∞ :=
  ∑ x : ∀ j, Ω j,
    if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧
       x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t
    then p.prob x else 0

/-- The Carbery functional Q_n^{n+1}(p). -/
def carberyFunctionalPow (hn : n ≥ 1) (p : JointPMF Ω) : ℝ≥0∞ :=
  ∑ s : ∀ i, Ω i,
    p.marginal ⟨0, by omega⟩ (s ⟨0, by omega⟩) *
    (∏ j : Fin (n - 1), p.bivariateMarginai j
      (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)
      (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩)) *
    p.marginal ⟨n - 1, by omega⟩ (s ⟨n - 1, by omega⟩)

/-- The Carbery functional Q_n(p) = (Q_n^{n+1}(p))^{1/(n+1)}. -/
def carberyFunctional (hn : n ≥ 1) (p : JointPMF Ω) : ℝ≥0∞ :=
  (carberyFunctionalPow hn p) ^ (1 / (n + 1 : ℝ))

/-- The L^p norm with COUNTING MEASURE (unweighted sum over all states).
    This is the standard finite L^p norm: (∑_s f(s)^p)^{1/p}.
    This is NOT weighted by the marginal distribution. -/
def lpNormFinite (exp : ℝ) (f : α → ℝ≥0∞) [Fintype α] : ℝ≥0∞ :=
  (∑ s : α, f s ^ exp) ^ (1 / exp)

/-- **Carbery's Inequality** (Finite State Spaces) - Counting Measure Version

    For functions fᵢ : Ωᵢ → ℝ≥0∞,
    ∑_x K(x) ∏ᵢ fᵢ(xᵢ) ≤ Qₙ(K) · ∏ᵢ ‖fᵢ‖_{L^{n+1}(counting)}

    where ‖fᵢ‖_{L^{n+1}(counting)} = (∑_s fᵢ(s)^{n+1})^{1/(n+1)} is the
    standard finite L^{n+1} norm with counting measure (unweighted).

    The proof proceeds by induction on n, using Hölder's inequality
    and the Gibbs variational formula (see Terry Tao's blog post).

    Reference: Carbery, A. (2004). "A multilinear generalisation of the
    Cauchy-Schwarz inequality". Proc. Amer. Math. Soc. -/
theorem carberyInequality (hn : n ≥ 1) (K : JointPMF Ω)
    (f : ∀ i, Ω i → ℝ≥0∞) :
    ∑ x : ∀ i, Ω i, K.prob x * ∏ i, f i (x i) ≤
    carberyFunctional hn K * ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (f i) := by
  sorry

end
