/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Multivariate Concentration Inequalities (Finite State Spaces)

This file contains the main concentration inequalities derived from Carbery's
inequality for finite state spaces: multivariate Markov, Chebyshev, and
general moment bounds.

## Main results (Paper Contributions - Zambrano 2025)

* `multivariate_markov`: Multivariate Markov inequality (Theorem 3.1)
* `multivariate_chebyshev`: Multivariate Chebyshev inequality (Theorem 3.2)
* `general_moment_bound`: General moment inequality (Theorem 3.4)

These are the **core contributions** of the paper, deriving new concentration
bounds from the axiomatized Carbery inequality.

## Implementation notes

All expectations and probabilities are computed as finite sums, eliminating
the need for measure-theoretic machinery.

## References

* [Zambrano, E., Dependence-Aware Concentration Inequalities, 2025]
-/

import CarberyConcentrationFinite.Basic

open scoped ENNReal NNReal BigOperators
open Finset

noncomputable section

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-!
## Joint Tail Probability

For finite state spaces, the joint tail probability is a finite sum over
the event set.
-/

/-- The joint tail probability P(h₁(X₁) ≥ c₁, ..., hₙ(Xₙ) ≥ cₙ).
    In the finite case, this is a sum over the event set. -/
def JointPMF.jointTailProb (p : JointPMF Ω) (h : ∀ i, Ω i → ℝ) (c : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ x : ∀ i, Ω i, if ∀ i, h i (x i) ≥ c i then p.prob x else 0

/-- Equivalent formulation: sum over elements satisfying the condition. -/
theorem jointTailProb_eq_sum_filter (p : JointPMF Ω) (h : ∀ i, Ω i → ℝ) (c : Fin n → ℝ) :
    p.jointTailProb h c = ∑ x ∈ Finset.univ.filter (fun x => ∀ i, h i (x i) ≥ c i), p.prob x := by
  simp only [JointPMF.jointTailProb]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]

/-- The indicator function for the event {h(s) ≥ c}. -/
def indicatorGeq (c : ℝ) (h : α → ℝ) : α → ℝ≥0∞ :=
  fun s => if h s ≥ c then 1 else 0

/-!
## Multivariate Markov Inequality

**Theorem 3.1** (Zambrano 2025): For nonnegative random variables X = (X₁,...,Xₙ)
with joint PMF p and thresholds a₁,...,aₙ > 0,

  P(X₁ ≥ a₁, ..., Xₙ ≥ aₙ) ≤ (Qₙ(p) / (a₁ ⋯ aₙ)) · ∏ᵢ E[Xᵢⁿ⁺¹]^{1/(n+1)}

This is a **paper contribution** that extends classical Markov to the
multivariate dependent setting using Carbery's inequality.
-/

/-- Lower bound on expectation of product.
    E[h₁(X₁) ⋯ hₙ(Xₙ)] ≥ (c₁ ⋯ cₙ) · P(∩ᵢ {hᵢ(Xᵢ) ≥ cᵢ})

    In the finite case, this is an elementary inequality on sums.

    **Paper contribution**: To be proved. -/
lemma expectation_prod_geq (p : JointPMF Ω) (h : ∀ i, Ω i → ℝ≥0∞) (c : Fin n → ℝ)
    (hc : ∀ i, c i > 0) (hh : ∀ i s, h i s ≥ 0) :
    ∑ x : ∀ i, Ω i, p.prob x * ∏ i, h i (x i) ≥
    (∏ i, ENNReal.ofReal (c i)) *
    ∑ x : ∀ i, Ω i, if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0 := by
  rw [Finset.mul_sum _ _ _]
  refine' Finset.sum_le_sum fun x _ => _
  split_ifs <;> simp_all +decide [mul_comm]
  exact mul_le_mul_left' (Finset.prod_le_prod' fun i _ => by solve_by_elim) _

/-- **Multivariate Markov Inequality** (Theorem 3.1) for finite spaces.

    For nonnegative h = (h₁,...,hₙ) with hᵢ : Ωᵢ → ℝ≥0∞ and c₁,...,cₙ > 0:

    P(h₁(X₁) ≥ c₁, ..., hₙ(Xₙ) ≥ cₙ) ≤ (Qₙ(p) / ∏ᵢ cᵢ) · ∏ᵢ ‖hᵢ‖_{L^{n+1}(counting)}

    The proof applies Carbery's inequality (axiomatized) and the product lower bound.

    **Note**: Uses counting measure norms, not marginal-weighted norms.
    **Paper contribution**: To be proved. -/
theorem multivariate_markov (hn : n ≥ 1) (p : JointPMF Ω)
    (h : ∀ i, Ω i → ℝ≥0∞) (c : Fin n → ℝ) (hc : ∀ i, c i > 0) :
    (∑ x : ∀ i, Ω i, if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0) ≤
    (carberyFunctional hn p / ∏ i, ENNReal.ofReal (c i)) *
    ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (h i) := by
  -- Step 1: On the event {∀i, h_i ≥ c_i}, we have 1 ≤ ∏_i (h_i/c_i), so
  -- P(∀i, h_i ≥ c_i) ≤ (1/∏c_i) · E[∏h_i]
  have hc_pos : ∀ i, (0 : ℝ≥0∞) < ENNReal.ofReal (c i) := fun i =>
    ENNReal.ofReal_pos.mpr (hc i)
  have hc_ne_zero : ∀ i, ENNReal.ofReal (c i) ≠ 0 := fun i => ne_of_gt (hc_pos i)
  have hc_lt_top : ∀ i, ENNReal.ofReal (c i) < ⊤ := fun i => ENNReal.ofReal_lt_top
  have prod_c_ne_zero : ∏ i, ENNReal.ofReal (c i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hc_ne_zero i
  have prod_c_ne_top : ∏ i, ENNReal.ofReal (c i) ≠ ⊤ := by
    apply ne_of_lt
    apply ENNReal.prod_lt_top
    intro i _
    exact hc_lt_top i
  -- Bound: indicator ≤ product / ∏c_i
  have step1 : ∑ x, (if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0) ≤
      (∏ i, ENNReal.ofReal (c i))⁻¹ * ∑ x, p.prob x * ∏ i, h i (x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    split_ifs with hx
    · -- On the event, p.prob x ≤ (1/∏c_i) · p.prob x · ∏h_i
      have hprod : (∏ i, ENNReal.ofReal (c i)) ≤ ∏ i, h i (x i) :=
        Finset.prod_le_prod' fun i _ => hx i
      have inv_mul : (∏ i, ENNReal.ofReal (c i))⁻¹ * (∏ i, ENNReal.ofReal (c i)) = 1 :=
        ENNReal.inv_mul_cancel prod_c_ne_zero prod_c_ne_top
      calc p.prob x = 1 * p.prob x := by rw [one_mul]
           _ = ((∏ i, ENNReal.ofReal (c i))⁻¹ * (∏ i, ENNReal.ofReal (c i))) * p.prob x := by
               rw [inv_mul]
           _ ≤ (∏ i, ENNReal.ofReal (c i))⁻¹ * (∏ i, h i (x i)) * p.prob x := by
               have h1 : (∏ i, ENNReal.ofReal (c i))⁻¹ * (∏ i, ENNReal.ofReal (c i)) ≤
                         (∏ i, ENNReal.ofReal (c i))⁻¹ * (∏ i, h i (x i)) :=
                 mul_le_mul_left' hprod _
               exact mul_le_mul_right' h1 _
           _ = (∏ i, ENNReal.ofReal (c i))⁻¹ * (p.prob x * ∏ i, h i (x i)) := by ring
    · exact zero_le _
  -- Step 2: Apply Carbery's inequality (with counting measure norms)
  have step2 : ∑ x, p.prob x * ∏ i, h i (x i) ≤
      carberyFunctional hn p * ∏ i, lpNormFinite (n + 1 : ℝ) (h i) :=
    carberyInequality hn p h
  -- Step 3: Combine and simplify
  calc ∑ x, (if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0)
      ≤ (∏ i, ENNReal.ofReal (c i))⁻¹ * ∑ x, p.prob x * ∏ i, h i (x i) := step1
    _ ≤ (∏ i, ENNReal.ofReal (c i))⁻¹ * (carberyFunctional hn p *
          ∏ i, lpNormFinite (n + 1 : ℝ) (h i)) := mul_le_mul_left' step2 _
    _ = (carberyFunctional hn p / ∏ i, ENNReal.ofReal (c i)) *
          ∏ i, lpNormFinite (n + 1 : ℝ) (h i) := by
        rw [ENNReal.div_eq_inv_mul]
        ring

/-!
## Multivariate Chebyshev Inequality

**Theorem 3.2** (Zambrano 2025): For X = (X₁,...,Xₙ) with means μᵢ and a₁,...,aₙ > 0:

  P(|X₁ - μ₁| ≥ a₁, ..., |Xₙ - μₙ| ≥ aₙ) ≤
    (Qₙ(p̃) / ∏ᵢ aᵢ²) · ∏ᵢ E[|Xᵢ - μᵢ|^{2(n+1)}]^{1/(n+1)}

This is a **paper contribution** extending Chebyshev to joint deviations.
-/

/-- The centered version: deviation from mean. -/
def deviationFromMean (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (i : Fin n) : Ω i → ℝ :=
  fun s => g i s - p.expectation i (g i)

/-- Joint tail probability for centered deviations. -/
def JointPMF.centeredTailProb (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (a : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ x : ∀ i, Ω i,
    if ∀ i, |g i (x i) - p.expectation i (g i)| ≥ a i then p.prob x else 0

/-- **Multivariate Chebyshev Inequality** (Theorem 3.2) for finite spaces.

    For g = (g₁,...,gₙ) with gᵢ : Ωᵢ → ℝ, means μᵢ = E[gᵢ(Xᵢ)], and a₁,...,aₙ > 0:

    P(|g₁(X₁) - μ₁| ≥ a₁, ..., |gₙ(Xₙ) - μₙ| ≥ aₙ) ≤
      (Qₙ(p) / ∏ᵢ aᵢ²) · ∏ᵢ ‖|gᵢ - μᵢ|²‖_{L^{n+1}(counting)}

    The proof applies Carbery's inequality (axiomatized) with hᵢ(s) = (gᵢ(s) - μᵢ)².

    **Note**: Uses counting measure norms, not marginal-weighted norms.
    **Paper contribution**: To be proved. -/
theorem multivariate_chebyshev (hn : n ≥ 1) (p : JointPMF Ω)
    (g : ∀ i, Ω i → ℝ) (a : Fin n → ℝ) (ha : ∀ i, a i > 0) :
    p.centeredTailProb g a ≤
    (carberyFunctional hn p / ∏ i, ENNReal.ofReal (a i ^ 2)) *
    ∏ i : Fin n, lpNormFinite (n + 1 : ℝ)
      (fun s => ENNReal.ofReal (|g i s - p.expectation i (g i)| ^ 2)) := by
  -- Apply multivariate Markov with h_i(x) = |g_i(x) - μ_i|²
  convert multivariate_markov hn p
    (fun i s => ENNReal.ofReal (|g i s - p.expectation i (g i)| ^ 2))
    (fun i => (a i) ^ 2)
    (fun i => sq_pos_of_pos (ha i)) using 1
  -- Convert the condition
  refine' Finset.sum_congr rfl fun x _ => _
  simp +decide [ENNReal.ofReal_le_ofReal_iff (sq_nonneg _), ha]
  simp +decide only [sq_le_sq, abs_of_nonneg (le_of_lt (ha _))]

/-!
## General Moment Inequality

**Theorem 3.4** (Zambrano 2025) unifies Markov and Chebyshev by allowing
arbitrary test functions.
-/

/-- **General Moment Inequality** (Theorem 3.4) for finite spaces.

    For measurable hᵢ : Ωᵢ → ℝ≥0∞ and c₁,...,cₙ > 0:

    P(∩ᵢ {hᵢ(Xᵢ) ≥ cᵢ}) ≤ (Qₙ(p) / ∏ᵢ cᵢ) · ∏ᵢ ‖hᵢ‖_{L^{n+1}(counting)}

    This generalizes both Markov (hᵢ = id) and Chebyshev (hᵢ(x) = (x-μᵢ)²).

    **Note**: Uses counting measure norms, not marginal-weighted norms.
    **Paper contribution**: To be proved. -/
theorem general_moment_bound (hn : n ≥ 1) (p : JointPMF Ω)
    (h : ∀ i, Ω i → ℝ≥0∞) (c : Fin n → ℝ) (hc : ∀ i, c i > 0) :
    (∑ x : ∀ i, Ω i, if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0) ≤
    (carberyFunctional hn p / ∏ i, ENNReal.ofReal (c i)) *
    ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (h i) := by
  exact multivariate_markov hn p h c hc

/-!
## Bivariate Special Case

For n = 2, we get explicit formulas that are easier to verify.
-/

/-- Bivariate Chebyshev inequality (Remark after Theorem 3.2) for finite spaces.

    P(|X - μ_X| ≥ a, |Y - μ_Y| ≥ b) ≤
      (Q₂(p) / (a² b²)) · ‖|X-μ_X|²‖_{L³(counting)} · ‖|Y-μ_Y|²‖_{L³(counting)}

    **Note**: Uses counting measure norms, not marginal-weighted norms.
    **Paper contribution**: Proved as corollary of multivariate_chebyshev. -/
theorem bivariate_chebyshev {Ω : Fin 2 → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (a b : ℝ) (ha : a > 0) (hb : b > 0) :
    p.centeredTailProb g ![a, b] ≤
    (carberyFunctional (by norm_num : (2 : ℕ) ≥ 1) p /
      (ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (b ^ 2))) *
    (lpNormFinite (3 : ℝ) (fun s => ENNReal.ofReal (|g 0 s - p.expectation 0 (g 0)| ^ 2)) *
     lpNormFinite (3 : ℝ) (fun s => ENNReal.ofReal (|g 1 s - p.expectation 1 (g 1)| ^ 2))) := by
  -- Apply multivariate_chebyshev with n = 2
  have h := multivariate_chebyshev (by norm_num : (2 : ℕ) ≥ 1) p g ![a, b]
    (fun i => by fin_cases i <;> simp [ha, hb])
  -- Convert product over Fin 2 to explicit multiplication
  have prod_ab : ∏ i : Fin 2, ENNReal.ofReal (![a, b] i ^ 2) =
      ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (b ^ 2) := by
    rw [Fin.prod_univ_two]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have prod_norms : ∏ i : Fin 2, lpNormFinite ((2 : ℕ) + 1 : ℝ)
      (fun s => ENNReal.ofReal (|g i s - p.expectation i (g i)| ^ 2)) =
      lpNormFinite (3 : ℝ) (fun s => ENNReal.ofReal (|g 0 s - p.expectation 0 (g 0)| ^ 2)) *
      lpNormFinite (3 : ℝ) (fun s => ENNReal.ofReal (|g 1 s - p.expectation 1 (g 1)| ^ 2)) := by
    rw [Fin.prod_univ_two]
    norm_num
  rw [prod_ab, prod_norms] at h
  exact h

/-!
## Finite Sum Simplifications

Key lemmas showing that finite sums are easier to manipulate than integrals.
-/

/-- Marginal probabilities sum to 1. -/
theorem marginal_sum_one (p : JointPMF Ω) (i : Fin n) :
    ∑ s : Ω i, p.marginal i s = 1 := p.marginal_sum_eq_one i

/-- Marginal probabilities are nonnegative (automatic for ℝ≥0∞). -/
theorem marginal_nonneg (p : JointPMF Ω) (i : Fin n) (s : Ω i) :
    p.marginal i s ≥ 0 := zero_le _

end
