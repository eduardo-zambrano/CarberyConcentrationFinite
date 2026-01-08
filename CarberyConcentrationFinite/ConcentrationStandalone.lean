/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Standalone Concentration Inequalities (For Aristotle)

This file is self-contained for automated proving. It includes all necessary
definitions and the theorems to prove.

## Main results (Paper Contributions - Zambrano 2025)

* `multivariate_markov`: Multivariate Markov inequality (Theorem 3.1)
* `multivariate_chebyshev`: Multivariate Chebyshev inequality (Theorem 3.2)
* `general_moment_bound`: General moment inequality (Theorem 3.4)

## References

* [Zambrano, E., Dependence-Aware Concentration Inequalities, 2025]
* [Carbery, A., A multilinear generalisation of the Cauchy-Schwarz inequality, 2004]
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

open scoped ENNReal NNReal BigOperators
open Finset

noncomputable section

variable {n : ℕ}

/-! ## Core Definitions -/

/-- The product of finite state spaces. -/
abbrev ProductSpace {n : ℕ} (Ω : Fin n → Type*) := ∀ i, Ω i

/-- A joint probability mass function on finite product spaces. -/
structure JointPMF {n : ℕ} (Ω : Fin n → Type*) [∀ i, Fintype (Ω i)] where
  prob : (∀ i, Ω i) → ℝ≥0∞
  sum_eq_one : ∑ x : ∀ i, Ω i, prob x = 1

variable {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-- The i-th univariate marginal PMF. -/
def JointPMF.marginal (p : JointPMF Ω) (i : Fin n) : Ω i → ℝ≥0∞ :=
  fun s => ∑ x : ∀ j, Ω j, if x i = s then p.prob x else 0

/-- The consecutive bivariate marginal PMF of (Xᵢ, Xᵢ₊₁). -/
def JointPMF.bivariateMarginai (p : JointPMF Ω) (i : Fin (n - 1)) :
    Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ →
    Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ → ℝ≥0∞ :=
  fun s t => ∑ x : ∀ j, Ω j,
    if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧
       x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t
    then p.prob x else 0

/-- The Carbery functional Q_n^{n+1}(p).

    Q_n^{n+1}(p) = ∑_s p₁(s₁) · p₁₂(s₁,s₂) · p₂₃(s₂,s₃) · ⋯ · p_{n-1,n}(s_{n-1},sₙ) · pₙ(sₙ)

    IMPORTANT: Only BOUNDARY marginals (p₁ and pₙ) appear, not interior marginals.
    This is the correct formula from Carbery (2004) / Tao (2023). -/
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

/-- The Lᵖ norm of a function on a finite type. -/
def lpNormFinite (p : ℝ) {α : Type*} [Fintype α] (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ x : α, f x ^ p) ^ (1 / p)

/-- The expectation of a real-valued function under the i-th marginal. -/
def JointPMF.expectation (p : JointPMF Ω) (i : Fin n) (f : Ω i → ℝ) : ℝ :=
  ∑ s : Ω i, (p.marginal i s).toReal * f s

/-! ## Carbery's Inequality (Assumed Foundation)

This is a published result [Carbery 2004] that we build upon. -/

/-- **Carbery's Inequality** [Carbery 2004] - Foundation for concentration bounds. -/
theorem carberyInequality (hn : n ≥ 1) (K : JointPMF Ω)
    (f : ∀ i, Ω i → ℝ≥0∞) :
    ∑ x : ∀ i, Ω i, K.prob x * ∏ i, f i (x i) ≤
    carberyFunctional hn K * ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (f i) := by
  sorry

/-! ## Concentration Inequalities (Paper Contributions) -/

/-- The joint tail probability P(h₁(X₁) ≥ c₁, ..., hₙ(Xₙ) ≥ cₙ). -/
def JointPMF.jointTailProb (p : JointPMF Ω) (h : ∀ i, Ω i → ℝ) (c : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ x : ∀ i, Ω i, if ∀ i, h i (x i) ≥ c i then p.prob x else 0

/-- Joint tail probability for centered deviations. -/
def JointPMF.centeredTailProb (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (a : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ x : ∀ i, Ω i,
    if ∀ i, |g i (x i) - p.expectation i (g i)| ≥ a i then p.prob x else 0

/-- Lower bound on expectation of product.
    E[h₁(X₁) ⋯ hₙ(Xₙ)] ≥ (c₁ ⋯ cₙ) · P(∩ᵢ {hᵢ(Xᵢ) ≥ cᵢ})

    **Paper contribution**: To be proved. -/
lemma expectation_prod_geq (p : JointPMF Ω) (h : ∀ i, Ω i → ℝ≥0∞) (c : Fin n → ℝ)
    (hc : ∀ i, c i > 0) (hh : ∀ i s, h i s ≥ 0) :
    ∑ x : ∀ i, Ω i, p.prob x * ∏ i, h i (x i) ≥
    (∏ i, ENNReal.ofReal (c i)) *
    ∑ x : ∀ i, Ω i, if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0 := by
  sorry

/-- **Multivariate Markov Inequality** (Theorem 3.1)

    P(h₁(X₁) ≥ c₁, ..., hₙ(Xₙ) ≥ cₙ) ≤ (Qₙ(p) / ∏ᵢ cᵢ) · ∏ᵢ E[hᵢ(Xᵢ)ⁿ⁺¹]^{1/(n+1)}

    **Paper contribution**: To be proved. -/
theorem multivariate_markov (hn : n ≥ 1) (p : JointPMF Ω)
    (h : ∀ i, Ω i → ℝ≥0∞) (c : Fin n → ℝ) (hc : ∀ i, c i > 0) :
    (∑ x : ∀ i, Ω i, if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0) ≤
    (carberyFunctional hn p / ∏ i, ENNReal.ofReal (c i)) *
    ∏ i : Fin n, (∑ s : Ω i, p.marginal i s * (h i s) ^ (n + 1 : ℝ)) ^ (1 / (n + 1 : ℝ)) := by
  sorry

/-- **Multivariate Chebyshev Inequality** (Theorem 3.2)

    P(|g₁(X₁) - μ₁| ≥ a₁, ..., |gₙ(Xₙ) - μₙ| ≥ aₙ) ≤
      (Qₙ(p) / ∏ᵢ aᵢ²) · ∏ᵢ E[|gᵢ(Xᵢ) - μᵢ|^{2(n+1)}]^{1/(n+1)}

    **Paper contribution**: To be proved. -/
theorem multivariate_chebyshev (hn : n ≥ 1) (p : JointPMF Ω)
    (g : ∀ i, Ω i → ℝ) (a : Fin n → ℝ) (ha : ∀ i, a i > 0) :
    p.centeredTailProb g a ≤
    (carberyFunctional hn p / ∏ i, ENNReal.ofReal (a i ^ 2)) *
    ∏ i : Fin n,
      (∑ s : Ω i, p.marginal i s *
        ENNReal.ofReal (|g i s - p.expectation i (g i)| ^ (2 * (n + 1)))) ^ (1 / (n + 1 : ℝ)) := by
  sorry

/-- **General Moment Inequality** (Theorem 3.4)

    P(∩ᵢ {hᵢ(Xᵢ) ≥ cᵢ}) ≤ (Qₙ(p) / ∏ᵢ cᵢ) · ∏ᵢ E[hᵢ(Xᵢ)^{n+1}]^{1/(n+1)}

    **Paper contribution**: To be proved. -/
theorem general_moment_bound (hn : n ≥ 1) (p : JointPMF Ω)
    (h : ∀ i, Ω i → ℝ≥0∞) (c : Fin n → ℝ) (hc : ∀ i, c i > 0) :
    (∑ x : ∀ i, Ω i, if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0) ≤
    (carberyFunctional hn p / ∏ i, ENNReal.ofReal (c i)) *
    ∏ i : Fin n, (∑ s : Ω i, p.marginal i s * (h i s) ^ (n + 1 : ℝ)) ^ (1 / (n + 1 : ℝ)) := by
  sorry

end
