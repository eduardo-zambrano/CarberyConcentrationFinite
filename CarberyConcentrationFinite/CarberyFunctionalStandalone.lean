/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Carbery Functional Independence Theorem (For Aristotle)

This file contains the carberyFunctional_of_independent theorem to be proved.
The key insight is that under independence, each marginal appears exactly twice
in the Carbery functional product.
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

/-- The marginal is well-defined: summing over all values gives 1. -/
theorem JointPMF.marginal_sum_eq_one (p : JointPMF Ω) (i : Fin n) :
    ∑ s : Ω i, p.marginal i s = 1 := by
  simp only [JointPMF.marginal]
  rw [Finset.sum_comm]
  have h : ∀ x : ∀ j, Ω j, ∑ s : Ω i, (if x i = s then p.prob x else 0) = p.prob x := by
    intro x
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp_rw [h]
  exact p.sum_eq_one

/-- The consecutive bivariate marginal PMF of (Xᵢ, Xᵢ₊₁). -/
def JointPMF.bivariateMarginai (p : JointPMF Ω) (i : Fin (n - 1)) :
    Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ →
    Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ → ℝ≥0∞ :=
  fun s t => ∑ x : ∀ j, Ω j,
    if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧
       x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t
    then p.prob x else 0

/-- A joint PMF represents independent random variables if it factorizes
    as a product of marginals. -/
def JointPMF.IsIndependent (p : JointPMF Ω) : Prop :=
  ∀ x, p.prob x = ∏ i : Fin n, p.marginal i (x i)

/-- The Lᵖ norm of a function on a finite type, using sums (counting measure). -/
def lpNormFinite (p : ℝ) {α : Type*} [Fintype α] (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ x : α, f x ^ p) ^ (1 / p)

/-- The Carbery functional Q_n^{n+1}(p) for a joint PMF on finite spaces.

    Q_n^{n+1}(p) = ∑_s p₁(s₁) · p₁₂(s₁,s₂) · p₂₃(s₂,s₃) · ⋯ · p_{n-1,n}(s_{n-1},sₙ) · pₙ(sₙ) -/
def carberyFunctionalPow (hn : n ≥ 1) (p : JointPMF Ω) : ℝ≥0∞ :=
  ∑ s : ∀ i, Ω i,
    p.marginal ⟨0, by omega⟩ (s ⟨0, by omega⟩) *
    (∏ j : Fin (n - 1), p.bivariateMarginai j
      (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)
      (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩)) *
    p.marginal ⟨n - 1, by omega⟩ (s ⟨n - 1, by omega⟩)

set_option maxHeartbeats 400000 in
/-- Under independence, the consecutive bivariate marginals factorize. -/
theorem bivariate_factorizes_of_independent (p : JointPMF Ω)
    (hp : p.IsIndependent) (i : Fin (n - 1)) (s : Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
    (t : Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩) :
    p.bivariateMarginai i s t =
    p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s *
    p.marginal ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ t := by
  have h_prod : ∑ x : ∀ j, Ω j, (if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧
      x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t then (∏ j, p.marginal j (x j)) else 0) =
      (∏ j ∈ Finset.univ \ {⟨i.val, Nat.lt_of_lt_pred i.isLt⟩,
        ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩}, ∑ x_j : Ω j, p.marginal j x_j) *
      (p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s) *
      (p.marginal ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ t) := by
    have h_sum_prod : ∑ x : ∀ j, Ω j, (if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧
        x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t then (∏ j, p.marginal j (x j)) else 0) =
        (∑ x : ∀ j, Ω j, if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧
          x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t then
          (∏ j ∈ Finset.univ \ {⟨i.val, Nat.lt_of_lt_pred i.isLt⟩,
            ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩}, p.marginal j (x j)) *
          (p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s) *
          (p.marginal ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ t) else 0) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp_all +decide [mul_assoc]
      rw [← Finset.prod_sdiff (Finset.subset_univ {⟨i.val, Nat.lt_of_lt_pred i.isLt⟩,
          ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩})]
      aesop
    rw [h_sum_prod]
    simp +decide only [prod_sum]
    simp +decide [Finset.sum_ite]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    refine congrArg₂ _ (congrArg₂ _ (Finset.sum_bij (fun x _ => fun j _ => x j) ?_ ?_ ?_ ?_) rfl) rfl
    · simp +contextual [Finset.mem_pi]
    · simp +contextual [funext_iff]
      grind
    · simp +decide [funext_iff, Finset.mem_pi]
      exact fun b => ⟨fun j => if hj : j = ⟨i, Nat.lt_of_lt_pred i.isLt⟩ then hj.symm ▸ s
        else if hj' : j = ⟨i + 1, Nat.add_lt_of_lt_sub i.isLt⟩ then hj'.symm ▸ t
        else b j (by aesop), by aesop⟩
    · exact fun x _ => by rw [← Finset.prod_attach]
  simp only [JointPMF.bivariateMarginai]
  have hp' : ∀ x, p.prob x = ∏ j, p.marginal j (x j) := hp
  simp_rw [hp']
  simp_all +decide [Finset.prod_eq_one, JointPMF.marginal_sum_eq_one]

/-- Under independence, Q_n^{n+1}(p) equals ∏_i ‖p_i‖₂².

    The key insight: under independence, p_{j,j+1}(s_j, s_{j+1}) = p_j(s_j) × p_{j+1}(s_{j+1}).
    So the full product in the Carbery functional becomes:
      p₀(s₀) × (∏_{j=0}^{n-2} p_j(s_j) × p_{j+1}(s_{j+1})) × p_{n-1}(s_{n-1})
    After factoring using prod_mul_distrib:
      = p₀(s₀) × (∏_{j=0}^{n-2} p_j(s_j)) × (∏_{j=0}^{n-2} p_{j+1}(s_{j+1})) × p_{n-1}(s_{n-1})
    The first product covers indices 0,...,n-2 and the second covers 1,...,n-1.
    Combined with boundary terms, each p_i(s_i) appears exactly twice:
      = ∏_{i=0}^{n-1} p_i(s_i)²
    Then by Fintype.prod_sum:
      ∑_s ∏_i p_i(s_i)² = ∏_i ∑_{s_i} p_i(s_i)² -/
theorem carberyFunctional_of_independent (hn : n ≥ 2) (p : JointPMF Ω)
    (hp : p.IsIndependent) :
    carberyFunctionalPow (Nat.one_le_of_lt hn) p =
    ∏ i : Fin n, (lpNormFinite 2 (p.marginal i)) ^ 2 := by
  sorry

end
