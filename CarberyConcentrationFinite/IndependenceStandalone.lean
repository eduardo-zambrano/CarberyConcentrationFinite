/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Independence Structure Lemmas (For Aristotle)

This file contains the independence structure lemmas to be proved.
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

/-- Under independence, the consecutive bivariate marginals factorize. -/
theorem bivariate_factorizes_of_independent (p : JointPMF Ω)
    (hp : p.IsIndependent) (i : Fin (n - 1)) (s : Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
    (t : Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩) :
    p.bivariateMarginai i s t =
    p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s *
    p.marginal ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ t := by
  sorry

/-- Expectation of a product factorizes under independence. -/
theorem expectation_prod_of_independent (p : JointPMF Ω) (hp : p.IsIndependent)
    (f : ∀ i, Ω i → ℝ≥0∞) :
    ∑ x : ∀ i, Ω i, p.prob x * ∏ i, f i (x i) =
    ∏ i : Fin n, ∑ s : Ω i, p.marginal i s * f i s := by
  have h1 : ∀ x, p.prob x * ∏ i, f i (x i) = ∏ i, (p.marginal i (x i) * f i (x i)) := by
    intro x
    rw [hp x, Finset.prod_mul_distrib]
  simp_rw [h1]
  exact (Fintype.prod_sum (fun i s => p.marginal i s * f i s)).symm

end
