/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# MGF and Chernoff-Type Bounds (Finite State Spaces)

This file contains moment generating function (MGF) inequalities and
Chernoff-type concentration bounds derived from Carbery's inequality,
specialized to finite state spaces.

## IMPORTANT NOTE ON MEASURE CHOICE

**Carbery's inequality uses COUNTING MEASURE norms, not marginal-weighted norms.**

This has significant implications:
- The MGF bounds here use "counting measure MGF": `∑_s exp(t·g(s))` (unweighted)
- This is DIFFERENT from the standard probabilistic MGF: `E[exp(tX)] = ∑_s μ(s)·exp(t·g(s))`
- The paper (Zambrano 2025) needs revision to reflect this distinction

The original paper claimed bounds using marginal-weighted MGFs, but Aristotle
(theorem prover) found a counterexample showing that formulation is FALSE.

## Main results

* `mgf_inequality_counting`: MGF bound with counting measure norms
* `sum_concentration`: Chernoff-type bound for sums
* `subgaussian_concentration`: Sub-Gaussian concentration

## Implementation notes

In the finite case, MGFs are finite sums, eliminating convergence concerns.

## References

* [Zambrano, E., Dependence-Aware Concentration Inequalities, 2025]
* [Carbery, A., A multilinear generalisation of the Cauchy-Schwarz inequality, 2004]
-/

import CarberyConcentrationFinite.ConcentrationInequalities

open scoped ENNReal NNReal BigOperators
open Finset Real

noncomputable section

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-!
## Moment Generating Functions

For finite state spaces, MGFs are always well-defined finite sums.

We define TWO versions:
- `mgf`: The standard probabilistic MGF using marginal weights (for reference)
- `mgfCounting`: The counting measure MGF (used in Carbery bounds)
-/

/-- The moment generating function of the i-th marginal at parameter t.
    Mᵢ(t) = E[exp(t · g(Xᵢ))] for a real-valued function g.

    **Note**: This is the MARGINAL-WEIGHTED version (standard probabilistic MGF).
    Carbery's inequality does NOT directly provide bounds using this.
    See `mgfCounting` for the counting measure version. -/
def JointPMF.mgf (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (i : Fin n) (t : ℝ) : ℝ≥0∞ :=
  ∑ s : Ω i, p.marginal i s * ENNReal.ofReal (Real.exp (t * g i s))

/-- The COUNTING MEASURE MGF: sum over all states without marginal weights.
    This is what Carbery's inequality provides bounds for.

    mgfCounting(t) = ∑_s exp(t · g(s))

    **Important**: This is NOT the same as the probabilistic MGF E[exp(tX)]. -/
def mgfCounting (g : α → ℝ) (t : ℝ) [Fintype α] : ℝ≥0∞ :=
  ∑ s : α, ENNReal.ofReal (Real.exp (t * g s))

/-- The joint MGF: E[exp(∑ᵢ tᵢ · gᵢ(Xᵢ))]. -/
def JointPMF.jointMgf (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (t : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ x : ∀ i, Ω i, p.prob x * ENNReal.ofReal (Real.exp (∑ i, t i * g i (x i)))

/-- MGF of the sum S = ∑ᵢ gᵢ(Xᵢ) at uniform parameter t.
    M_S(t) = E[exp(t · S)] -/
def JointPMF.sumMgf (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∑ x : ∀ i, Ω i, p.prob x * ENNReal.ofReal (Real.exp (t * ∑ i, g i (x i)))

/-!
## MGF Inequality

**CORRECTED VERSION**: Carbery's inequality provides bounds using COUNTING MEASURE norms.

For t₁,...,tₙ ≥ 0:
  E[exp(∑ᵢ tᵢ gᵢ(Xᵢ))] ≤ Qₙ(p) · ∏ᵢ (∑_s exp((n+1)tᵢ gᵢ(s)))^{1/(n+1)}

Note: The RHS uses COUNTING MEASURE sums, not marginal-weighted MGFs.
-/

/-- **MGF Inequality with Counting Measure** for finite spaces.

    For t₁,...,tₙ ≥ 0 and real-valued functions gᵢ:
    E[exp(∑ᵢ tᵢ gᵢ(Xᵢ))] ≤ Qₙ(p) · ∏ᵢ (mgfCounting(gᵢ, (n+1)tᵢ))^{1/(n+1)}

    where mgfCounting(g,t) = ∑_s exp(t·g(s)) is the COUNTING MEASURE MGF.

    **Important**: This is NOT a bound using the probabilistic MGF E[exp(tX)].
    The original paper's claim using marginal-weighted MGFs was DISPROVED. -/
theorem mgf_inequality_counting (hn : n ≥ 1) (p : JointPMF Ω)
    (g : ∀ i, Ω i → ℝ) (t : Fin n → ℝ) (ht : ∀ i, t i ≥ 0) :
    p.jointMgf g t ≤
    carberyFunctional hn p *
    ∏ i : Fin n, (mgfCounting (g i) ((n + 1 : ℕ) * t i)) ^ (1 / (n + 1 : ℝ)) := by
  -- Step 1: Rewrite jointMgf in the form needed for Carbery's inequality
  simp only [JointPMF.jointMgf, mgfCounting]
  -- exp(∑ᵢ tᵢ gᵢ(xᵢ)) = ∏ᵢ exp(tᵢ gᵢ(xᵢ))
  have exp_sum : ∀ x : ∀ i, Ω i,
      Real.exp (∑ i, t i * g i (x i)) = ∏ i, Real.exp (t i * g i (x i)) := by
    intro x
    rw [Real.exp_sum]
  simp_rw [exp_sum]
  -- Convert ofReal of product to product of ofReal
  have ofReal_prod : ∀ x : ∀ i, Ω i,
      ENNReal.ofReal (∏ i, Real.exp (t i * g i (x i))) =
      ∏ i, ENNReal.ofReal (Real.exp (t i * g i (x i))) := by
    intro x
    rw [ENNReal.ofReal_prod_of_nonneg]
    intro i _
    exact le_of_lt (Real.exp_pos _)
  simp_rw [ofReal_prod]
  -- Step 2: Apply Carbery's inequality with f_i(s) = ofReal(exp(t_i g_i(s)))
  have carb := carberyInequality hn p (fun i s => ENNReal.ofReal (Real.exp (t i * g i s)))
  -- Step 3: Show the L^{n+1} counting measure norms equal mgfCounting
  have norm_eq : ∀ i : Fin n,
      lpNormFinite (n + 1 : ℝ) (fun s => ENNReal.ofReal (Real.exp (t i * g i s))) =
      (∑ s : Ω i, ENNReal.ofReal (Real.exp (↑(n + 1) * t i * g i s))) ^
      (1 / (n + 1 : ℝ)) := by
    intro i
    simp only [lpNormFinite]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    -- Need: ofReal(exp(t_i g_i s))^(n+1) = ofReal(exp((n+1) t_i g_i s))
    rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt (Real.exp_pos _)) (by linarith : (0 : ℝ) ≤ ↑n + 1)]
    congr 1
    rw [← Real.exp_mul]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  -- Step 4: Combine using Carbery's inequality
  calc ∑ x, p.prob x * ∏ i, ENNReal.ofReal (Real.exp (t i * g i (x i)))
      ≤ carberyFunctional hn p * ∏ i, lpNormFinite (n + 1 : ℝ)
          (fun s => ENNReal.ofReal (Real.exp (t i * g i s))) := carb
    _ = carberyFunctional hn p * ∏ i,
          (∑ s : Ω i, ENNReal.ofReal (Real.exp (↑(n + 1) * t i * g i s))) ^
          (1 / (n + 1 : ℝ)) := by
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        exact norm_eq i

/-! **Note**: A theorem `mgf_inequality` using marginal-weighted MGFs was previously here,
    but it CANNOT be proved from Carbery's inequality. The gap between counting measure
    and marginal-weighted norms is essential. Use `mgf_inequality_counting` instead. -/

/-- Corollary: When all tᵢ = t, we get a bound on the sum's MGF using counting measure.

    **IMPORTANT**: Uses counting measure MGF (mgfCounting), matching the paper's
    Theorem 3.4 where M_i(t) = ∑_s exp(t·s).

    **Paper contribution**: Proved. -/
theorem mgf_sum_uniform (hn : n ≥ 1) (p : JointPMF Ω)
    (g : ∀ i, Ω i → ℝ) (t : ℝ) (ht : t ≥ 0) :
    p.sumMgf g t ≤
    carberyFunctional hn p *
    ∏ i : Fin n, (mgfCounting (g i) ((n + 1 : ℕ) * t)) ^ (1 / (n + 1 : ℝ)) := by
  -- sumMgf equals jointMgf with all parameters equal
  have sumMgf_eq : p.sumMgf g t = p.jointMgf g (fun _ => t) := by
    simp only [JointPMF.sumMgf, JointPMF.jointMgf]
    congr 1
    ext x
    congr 2
    rw [mul_sum]
  rw [sumMgf_eq]
  exact mgf_inequality_counting hn p g (fun _ => t) (fun _ => ht)

/-!
## Sum Concentration (Chernoff-Type Bound)

**Corollary 3.6** (Zambrano 2025): For S = ∑ᵢ gᵢ(Xᵢ) and a > 0,

  P(S ≥ a) ≤ inf_{t ≥ 0} Qₙ(p) · ∏ᵢ Mᵢ((n+1)t)^{1/(n+1)} · exp(-ta)

This is a **paper contribution** giving Chernoff-type bounds for dependent sums.
-/

/-- The Chernoff bound for the sum S = ∑ᵢ gᵢ(Xᵢ) at threshold a with parameter t.
    This is the bound before optimization over t.

    **IMPORTANT**: Uses counting measure MGF (mgfCounting), matching the paper's
    Theorem 3.4 where M_i(t) = ∑_s exp(t·s). -/
def chernoffBound (hn : n ≥ 1) (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (a t : ℝ) : ℝ≥0∞ :=
  carberyFunctional hn p *
  (∏ i : Fin n, (mgfCounting (g i) ((n + 1 : ℕ) * t)) ^ (1 / (n + 1 : ℝ))) *
  ENNReal.ofReal (Real.exp (-t * a))

/-- **Sum Concentration** (Corollary 3.6) for finite spaces.

    For S = ∑ᵢ gᵢ(Xᵢ) and a > 0:
    P(S ≥ a) ≤ inf_{t ≥ 0} Qₙ(p) · ∏ᵢ Mᵢ((n+1)t)^{1/(n+1)} · exp(-ta)

    This follows from the MGF inequality and the standard Chernoff argument.

    **Paper contribution**: Proved. -/
theorem sum_concentration (hn : n ≥ 1) (p : JointPMF Ω)
    (g : ∀ i, Ω i → ℝ) (a : ℝ) (ha : a > 0) :
    (∑ x : ∀ i, Ω i, if ∑ i, g i (x i) ≥ a then p.prob x else 0) ≤
    ⨅ (t : ℝ) (_ : t ≥ 0), chernoffBound hn p g a t := by
  -- It suffices to show the bound holds for every t ≥ 0
  apply le_iInf₂
  intro t ht
  -- For any t ≥ 0, apply Chernoff argument: P(S ≥ a) ≤ E[exp(t*S)] * exp(-t*a)
  -- Step 1: P(S ≥ a) ≤ E[exp(t*S)] * exp(-t*a) by Markov for exp
  have markov_exp : ∀ x : ∀ i, Ω i, (∑ i, g i (x i)) ≥ a →
      p.prob x ≤ p.prob x * ENNReal.ofReal (Real.exp (t * ∑ i, g i (x i))) *
                 ENNReal.ofReal (Real.exp (-t * a)) := by
    intro x hx
    -- Key: t(S - a) ≥ 0 when S ≥ a and t ≥ 0
    have h1 : t * ∑ i, g i (x i) + (-t * a) ≥ 0 := by
      have : t * (∑ i, g i (x i) - a) ≥ 0 := mul_nonneg ht (by linarith)
      linarith
    have h2 : (1 : ℝ) ≤ Real.exp (t * ∑ i, g i (x i)) * Real.exp (-t * a) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp_of_le h1
    have h3 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (t * ∑ i, g i (x i))) *
                           ENNReal.ofReal (Real.exp (-t * a)) := by
      rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal h2
    calc p.prob x = p.prob x * 1 := by ring
      _ ≤ p.prob x * (ENNReal.ofReal (Real.exp (t * ∑ i, g i (x i))) *
                      ENNReal.ofReal (Real.exp (-t * a))) :=
          mul_le_mul_left' h3 _
      _ = p.prob x * ENNReal.ofReal (Real.exp (t * ∑ i, g i (x i))) *
          ENNReal.ofReal (Real.exp (-t * a)) := by ring
  -- Step 2: Sum over all x
  have step1 : (∑ x, if ∑ i, g i (x i) ≥ a then p.prob x else 0) ≤
      ∑ x, p.prob x * ENNReal.ofReal (Real.exp (t * ∑ i, g i (x i))) *
           ENNReal.ofReal (Real.exp (-t * a)) := by
    apply Finset.sum_le_sum
    intro x _
    split_ifs with hx
    · exact markov_exp x hx
    · exact zero_le _
  have step2 : (∑ x, p.prob x * ENNReal.ofReal (Real.exp (t * ∑ i, g i (x i))) *
                     ENNReal.ofReal (Real.exp (-t * a))) =
      (∑ x, p.prob x * ENNReal.ofReal (Real.exp (t * ∑ i, g i (x i)))) *
      ENNReal.ofReal (Real.exp (-t * a)) := (Finset.sum_mul _ _ _).symm
  have step3 : (∑ x, p.prob x * ENNReal.ofReal (Real.exp (t * ∑ i, g i (x i)))) =
      p.sumMgf g t := by simp only [JointPMF.sumMgf]
  have step4 : p.sumMgf g t * ENNReal.ofReal (Real.exp (-t * a)) ≤
      (carberyFunctional hn p * ∏ i, (mgfCounting (g i) ((n + 1 : ℕ) * t)) ^ (1 / (n + 1 : ℝ))) *
      ENNReal.ofReal (Real.exp (-t * a)) := by
    apply mul_le_mul_right'
    exact mgf_sum_uniform hn p g t ht
  calc (∑ x, if ∑ i, g i (x i) ≥ a then p.prob x else 0)
      ≤ (∑ x, p.prob x * ENNReal.ofReal (Real.exp (t * ∑ i, g i (x i)))) *
        ENNReal.ofReal (Real.exp (-t * a)) := by rw [← step2]; exact step1
    _ = p.sumMgf g t * ENNReal.ofReal (Real.exp (-t * a)) := by rw [step3]
    _ ≤ (carberyFunctional hn p * ∏ i, (mgfCounting (g i) ((n + 1 : ℕ) * t)) ^ (1 / (n + 1 : ℝ))) *
        ENNReal.ofReal (Real.exp (-t * a)) := step4
    _ = chernoffBound hn p g a t := by simp only [chernoffBound, mul_assoc]

/-!
## Sub-Gaussian Concentration

**Theorem 3.7** (Zambrano 2025): If each gᵢ(Xᵢ) is sub-Gaussian with parameter σᵢ², then

  P(S - E[S] ≥ a) ≤ Qₙ(p) · exp(-a² / (2(n+1) ∑ᵢ σᵢ²))

This is a **paper contribution** extending sub-Gaussian bounds to dependent variables.
-/

/-- A marginal is sub-Gaussian with parameter σ² if
    E[exp(t gᵢ(Xᵢ))] ≤ exp(σ² t² / 2) for all t.

    In the finite case, this is a condition on finite sums.

    **Note**: This is the marginal-weighted version. See `IsSubGaussianCounting` for
    the counting measure version that matches the paper's Theorem 3.7. -/
def JointPMF.IsSubGaussian (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (i : Fin n) (σsq : ℝ) : Prop :=
  σsq ≥ 0 ∧ ∀ t : ℝ, p.mgf g i t ≤ ENNReal.ofReal (Real.exp (σsq * t ^ 2 / 2))

/-- Centered sub-Gaussian: after mean subtraction (marginal-weighted version). -/
def JointPMF.IsSubGaussianCentered (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (i : Fin n) (σsq : ℝ) : Prop :=
  let μ := p.expectation i (g i)
  σsq ≥ 0 ∧ ∀ t : ℝ,
    ∑ s : Ω i, p.marginal i s * ENNReal.ofReal (Real.exp (t * (g i s - μ))) ≤
    ENNReal.ofReal (Real.exp (σsq * t ^ 2 / 2))

/-- **Counting measure sub-Gaussian** (matches paper's Theorem 3.7):
    ∑_s exp(t · (g(s) - μ)) ≤ |Ω_i| · exp(σ² t² / 2) for all t.

    This is the definition used in the paper, where M_i(t) = ∑_s exp(ts) is the
    counting measure MGF, and the bound includes a factor of |X_i| = |Ω_i|.

    **This is what Carbery's inequality can bound.** -/
def IsSubGaussianCounting (g : Ω i → ℝ) (μ : ℝ) (σsq : ℝ) : Prop :=
  σsq ≥ 0 ∧ ∀ t : ℝ,
    ∑ s : Ω i, ENNReal.ofReal (Real.exp (t * (g s - μ))) ≤
    (Fintype.card (Ω i) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (σsq * t ^ 2 / 2))

/-- The MGF of a centered function equals the centered MGF. -/
theorem mgf_centered (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (i : Fin n) (t : ℝ) :
    p.mgf (fun j s => g j s - p.expectation j (g j)) i t =
    ∑ s : Ω i, p.marginal i s * ENNReal.ofReal (Real.exp (t * (g i s - p.expectation i (g i)))) := by
  simp only [JointPMF.mgf]

/-- Under sub-Gaussian assumption, the MGF at (n+1)t raised to 1/(n+1) is bounded.
    This is the key bound that connects sub-Gaussian property to the Chernoff bound. -/
theorem mgf_subgaussian_bound (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (i : Fin n)
    (σsq : ℝ) (hσ : p.IsSubGaussianCentered g i σsq) (t : ℝ) :
    (p.mgf (fun j s => g j s - p.expectation j (g j)) i ((n + 1 : ℕ) * t)) ^ (1 / (n + 1 : ℝ)) ≤
    ENNReal.ofReal (Real.exp (σsq * (n + 1 : ℕ) * t ^ 2 / 2)) := by
  -- Step 1: Unfold mgf to sum form
  simp only [JointPMF.mgf]
  -- The sum becomes: ∑ s, p.marginal i s * ENNReal.ofReal (exp(((n+1)*t) * (g i s - μ)))
  -- Step 2: Use sub-Gaussian property at parameter (n+1)t
  let t' : ℝ := (n + 1 : ℕ) * t
  have hσ_bound := hσ.2 t'
  -- hσ_bound: ∑ s, p.marginal i s * ofReal(exp(t' * (g i s - μ))) ≤ ofReal(exp(σsq * t'^2 / 2))
  -- Step 3: The mgf sum matches the sub-Gaussian sum
  have sum_eq : ∀ s : Ω i,
      ENNReal.ofReal (Real.exp (t' * (g i s - p.expectation i (g i)))) =
      ENNReal.ofReal (Real.exp (t' * g i s + t' * (- p.expectation i (g i)))) := by
    intro s
    congr 1
    ring
  -- Step 4: Simplify exponents
  have exp_sq : σsq * t' ^ 2 / 2 = σsq * (n + 1 : ℕ) ^ 2 * t ^ 2 / 2 := by
    simp only [t']
    ring
  rw [exp_sq] at hσ_bound
  -- Step 5: Take (n+1)-th root of both sides
  have h_exp_nonneg : (1 : ℝ) / (n + 1) ≥ 0 := by positivity
  have step1 : (∑ s : Ω i, p.marginal i s *
        ENNReal.ofReal (Real.exp (t' * (g i s - p.expectation i (g i))))) ^ ((1 : ℝ) / (n + 1)) ≤
      (ENNReal.ofReal (Real.exp (σsq * (n + 1 : ℕ) ^ 2 * t ^ 2 / 2))) ^ ((1 : ℝ) / (n + 1)) :=
    ENNReal.rpow_le_rpow hσ_bound h_exp_nonneg
  have step2 : (ENNReal.ofReal (Real.exp (σsq * (n + 1 : ℕ) ^ 2 * t ^ 2 / 2))) ^ ((1 : ℝ) / (n + 1)) =
      ENNReal.ofReal ((Real.exp (σsq * (n + 1 : ℕ) ^ 2 * t ^ 2 / 2)) ^ ((1 : ℝ) / (n + 1))) :=
    ENNReal.ofReal_rpow_of_nonneg (le_of_lt (Real.exp_pos _)) h_exp_nonneg
  have step3 : (Real.exp (σsq * (n + 1 : ℕ) ^ 2 * t ^ 2 / 2)) ^ ((1 : ℝ) / (n + 1)) =
      Real.exp (σsq * (n + 1 : ℕ) ^ 2 * t ^ 2 / 2 * ((1 : ℝ) / (n + 1))) := by
    rw [← Real.exp_mul]
  have step4 : σsq * (n + 1 : ℕ) ^ 2 * t ^ 2 / 2 * ((1 : ℝ) / (n + 1)) = σsq * (n + 1 : ℕ) * t ^ 2 / 2 := by
    have hn1_ne : (n + 1 : ℝ) ≠ 0 := by positivity
    -- Normalize casts: ↑(n + 1) = ↑n + 1
    simp only [Nat.cast_add, Nat.cast_one]
    -- Now: σsq * (↑n + 1)^2 * t^2 / 2 * (1 / (↑n + 1)) = σsq * (↑n + 1) * t^2 / 2
    -- (n+1)² / (n+1) = n+1
    have h_sq_div : (n + 1 : ℝ) ^ 2 / (n + 1) = (n + 1 : ℝ) := by
      rw [sq, mul_div_assoc, div_self hn1_ne, mul_one]
    calc σsq * (n + 1 : ℝ) ^ 2 * t ^ 2 / 2 * ((1 : ℝ) / (n + 1))
        = σsq * t ^ 2 / 2 * ((n + 1 : ℝ) ^ 2 / (n + 1)) := by ring
      _ = σsq * t ^ 2 / 2 * (n + 1 : ℝ) := by rw [h_sq_div]
      _ = σsq * (n + 1 : ℝ) * t ^ 2 / 2 := by ring
  calc (∑ s : Ω i, p.marginal i s *
          ENNReal.ofReal (Real.exp (t' * (g i s - p.expectation i (g i))))) ^ ((1 : ℝ) / (n + 1))
      ≤ (ENNReal.ofReal (Real.exp (σsq * (n + 1 : ℕ) ^ 2 * t ^ 2 / 2))) ^ ((1 : ℝ) / (n + 1)) := step1
    _ = ENNReal.ofReal ((Real.exp (σsq * (n + 1 : ℕ) ^ 2 * t ^ 2 / 2)) ^ ((1 : ℝ) / (n + 1))) := step2
    _ = ENNReal.ofReal (Real.exp (σsq * (n + 1 : ℕ) ^ 2 * t ^ 2 / 2 * ((1 : ℝ) / (n + 1)))) := by
        rw [step3]
    _ = ENNReal.ofReal (Real.exp (σsq * (n + 1 : ℕ) * t ^ 2 / 2)) := by rw [step4]

/-- Helper: When σ² = 0, a sub-Gaussian centered variable must be identically 0.
    This is because the MGF bound exp(0) = 1 for all t forces the variable
    to be concentrated at its mean. -/
lemma subgaussian_zero_implies_deterministic (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (i : Fin n)
    (hσ : p.IsSubGaussianCentered g i 0) :
    ∀ s : Ω i, p.marginal i s ≠ 0 → g i s = p.expectation i (g i) := by
  -- The sub-Gaussian condition with σ² = 0 says E[exp(t·(g-μ))] ≤ 1 for all t
  -- For finite distributions, this forces g = μ on all states with positive probability
  intro s hs
  let μ := p.expectation i (g i)
  by_contra hne
  -- We have g(s) ≠ μ, so δ := g(s) - μ ≠ 0
  let δ := g i s - μ
  have hδ_ne : δ ≠ 0 := sub_ne_zero.mpr hne
  -- The sub-Gaussian bound with σ² = 0 says: ∑_s p(s) * exp(t * (g(s) - μ)) ≤ 1 for all t
  have bound := hσ.2
  -- Since σ² = 0: exp(0 * t² / 2) = exp(0) = 1
  simp only [zero_mul, zero_div, Real.exp_zero, ENNReal.ofReal_one] at bound
  -- Marginals are < ⊤ since they are bounded by 1
  have hmarg_lt_top : p.marginal i s < ⊤ := lt_of_le_of_lt (marginal_le_one p i s) ENNReal.one_lt_top
  have hs_toReal_pos : (p.marginal i s).toReal > 0 := ENNReal.toReal_pos hs hmarg_lt_top.ne
  -- Choose M large enough that p(s) * exp(M) > 1
  -- i.e., exp(M) > 1 / p(s).toReal, i.e., M > -log(p(s).toReal)
  let M := max 1 (-Real.log (p.marginal i s).toReal + 1)
  -- Choose t such that t * δ = M (this is always possible since δ ≠ 0)
  let t := M / δ
  have ht_mul : t * δ = M := by simp only [t]; field_simp
  -- The bound at this t gives: sum ≤ 1
  have hbound := bound t
  -- The sum includes p(s) * exp(t * δ) = p(s) * exp(M)
  have term_le_sum : p.marginal i s * ENNReal.ofReal (Real.exp (t * δ)) ≤
      ∑ s' : Ω i, p.marginal i s' * ENNReal.ofReal (Real.exp (t * (g i s' - μ))) := by
    have h_mem : s ∈ (Finset.univ : Finset (Ω i)) := Finset.mem_univ s
    have h_nonneg : ∀ s' ∈ Finset.univ, (0 : ℝ≥0∞) ≤
        p.marginal i s' * ENNReal.ofReal (Real.exp (t * (g i s' - μ))) := by
      intro s' _; exact zero_le _
    exact Finset.single_le_sum h_nonneg h_mem
  rw [ht_mul] at term_le_sum
  -- So p(s) * exp(M) ≤ sum ≤ 1
  have h1 : p.marginal i s * ENNReal.ofReal (Real.exp M) ≤ 1 := le_trans term_le_sum hbound
  -- But M ≥ -log(p(s).toReal) + 1, so exp(M) ≥ (1/p(s).toReal) * e
  have hM_ge : M ≥ -Real.log (p.marginal i s).toReal + 1 := le_max_right _ _
  have hexp_ge : Real.exp M ≥ (1 / (p.marginal i s).toReal) * Real.exp 1 := by
    calc Real.exp M ≥ Real.exp (-Real.log (p.marginal i s).toReal + 1) :=
           Real.exp_le_exp_of_le hM_ge
       _ = Real.exp (-Real.log (p.marginal i s).toReal) * Real.exp 1 := Real.exp_add _ _
       _ = (1 / (p.marginal i s).toReal) * Real.exp 1 := by
           rw [Real.exp_neg, Real.exp_log hs_toReal_pos, one_div]
  -- So p(s) * exp(M) ≥ p(s) * (1/p(s).toReal) * e = e > 1
  have h2 : p.marginal i s * ENNReal.ofReal (Real.exp M) ≥
      p.marginal i s * ENNReal.ofReal ((1 / (p.marginal i s).toReal) * Real.exp 1) := by
    apply mul_le_mul_left'
    exact ENNReal.ofReal_le_ofReal hexp_ge
  -- Simplify: p(s) * ofReal(1/p(s).toReal * e) = ofReal(e)
  have h_simp : p.marginal i s * ENNReal.ofReal ((1 / (p.marginal i s).toReal) * Real.exp 1) =
      ENNReal.ofReal (Real.exp 1) := by
    -- 1/toReal(p(s)) * e = toReal(p(s))⁻¹ * e
    have h_eq : (1 / (p.marginal i s).toReal) * Real.exp 1 =
        (p.marginal i s).toReal⁻¹ * Real.exp 1 := by rw [one_div]
    rw [h_eq]
    -- ofReal(x⁻¹ * e) = ofReal(x⁻¹) * ofReal(e) when x⁻¹ ≥ 0
    have h_inv_nonneg : (0 : ℝ) ≤ (p.marginal i s).toReal⁻¹ :=
      inv_nonneg.mpr (le_of_lt hs_toReal_pos)
    rw [ENNReal.ofReal_mul h_inv_nonneg]
    -- ofReal(toReal(p(s))⁻¹) = (ofReal(toReal(p(s))))⁻¹ = p(s)⁻¹
    rw [ENNReal.ofReal_inv_of_pos hs_toReal_pos]
    rw [ENNReal.ofReal_toReal hmarg_lt_top.ne]
    -- p(s) * (p(s)⁻¹ * ofReal(e)) = (p(s) * p(s)⁻¹) * ofReal(e) = 1 * ofReal(e) = ofReal(e)
    rw [← mul_assoc]
    rw [ENNReal.mul_inv_cancel hs hmarg_lt_top.ne, one_mul]
  rw [h_simp] at h2
  -- So p(s) * exp(M) ≥ e > 1, contradicting p(s) * exp(M) ≤ 1
  have he_gt_one : ENNReal.ofReal (Real.exp 1) > 1 := by
    rw [gt_iff_lt, ENNReal.one_lt_ofReal]
    exact Real.one_lt_exp_iff.mpr one_pos
  have contra : p.marginal i s * ENNReal.ofReal (Real.exp M) > 1 := lt_of_lt_of_le he_gt_one h2
  exact (not_lt.mpr h1) contra

/-! **Note**: An older version of `subgaussian_concentration` using marginal-weighted
    sub-Gaussian (IsSubGaussianCentered) was here but had an unprovable gap.
    Use `subgaussian_concentration_counting` below instead, which uses the counting
    measure sub-Gaussian definition matching the paper's Theorem 3.7. -/

/-- **Sub-Gaussian Concentration with Counting Measure** (Theorem 3.7 as stated in paper).

    This is the version that matches the paper exactly:
    - Uses counting measure sub-Gaussian: M_i(t) ≤ |X_i| exp(σ² t²/2)
    - Includes the cardinality factor (∏_i |X_i|)^{1/(n+1)}
    - Requires ∑σ² > 0 (excludes degenerate deterministic case)

    P(S - E[S] ≥ a) ≤ Q_n(p) · (∏_i |Ω_i|)^{1/(n+1)} · exp(-a²/(2(n+1)∑σ²))

    **Paper contribution**: This is Theorem 3.7. Fully proved. -/
theorem subgaussian_concentration_counting (hn : n ≥ 1) (p : JointPMF Ω)
    (g : ∀ i, Ω i → ℝ) (σsq : Fin n → ℝ)
    (hσ : ∀ i, IsSubGaussianCounting (fun s => g i s - p.expectation i (g i)) 0 (σsq i))
    (hσsum_pos : ∑ i, σsq i > 0)
    (a : ℝ) (ha : a > 0) :
    let μ := ∑ i, p.expectation i (g i)
    (∑ x : ∀ i, Ω i, if ∑ i, g i (x i) - μ ≥ a then p.prob x else 0) ≤
    carberyFunctional hn p *
    (∏ i : Fin n, (Fintype.card (Ω i) : ℝ≥0∞)) ^ (1 / (n + 1 : ℝ)) *
    ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * (n + 1 : ℕ) * ∑ i, σsq i))) := by
  intro μ
  -- Define centered functions
  let g' : ∀ i, Ω i → ℝ := fun i s => g i s - p.expectation i (g i)
  -- Key observation: ∑_i g_i(x_i) - μ = ∑_i g'_i(x_i)
  have sum_centered : ∀ x : ∀ i, Ω i, ∑ i, g i (x i) - μ = ∑ i, g' i (x i) := by
    intro x; simp only [g', μ]; rw [← Finset.sum_sub_distrib]
  have lhs_eq : (∑ x, if ∑ i, g i (x i) - μ ≥ a then p.prob x else 0) =
      (∑ x, if ∑ i, g' i (x i) ≥ a then p.prob x else 0) := by
    apply Finset.sum_congr rfl; intro x _; rw [sum_centered]
  rw [lhs_eq]
  -- Use optimal t* = a / ((n+1) ∑σ²)
  let t_opt := a / ((n + 1 : ℕ) * ∑ i, σsq i)
  have ht_opt_pos : t_opt > 0 := by simp only [t_opt]; positivity
  have ht_opt_nonneg : t_opt ≥ 0 := le_of_lt ht_opt_pos
  -- Use sum_concentration with counting measure MGF
  have sum_conc := sum_concentration hn p g' a ha
  -- Bound mgfCounting using counting-measure sub-Gaussian property
  have counting_bound : ∀ i : Fin n,
      (mgfCounting (g' i) ((n + 1 : ℕ) * t_opt)) ^ ((1 : ℝ) / (n + 1)) ≤
      (Fintype.card (Ω i) : ℝ≥0∞) ^ ((1 : ℝ) / (n + 1)) *
      ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2)) := by
      intro i
      have hσ_i := hσ i
      -- g'_i s - 0 = g'_i s since μ = 0 in counting-measure definition
      have g'_eq : ∀ s, g' i s - 0 = g' i s := fun s => sub_zero _
      -- mgfCounting(g', (n+1)t) = ∑_s exp((n+1)t · g'(s))
      simp only [mgfCounting]
      let t' := (n + 1 : ℕ) * t_opt
      have ht'_nonneg : t' ≥ 0 := by simp only [t']; positivity
      -- Apply counting-measure sub-Gaussian bound at t'
      have hbound := hσ_i.2 t'
      simp only [sub_zero] at hbound
      -- hbound: ∑_s exp(t' · g'(s)) ≤ |Ω_i| · exp(σ² t'²/2)
      have t'_sq : σsq i * t' ^ 2 / 2 = σsq i * (n + 1 : ℕ) ^ 2 * t_opt ^ 2 / 2 := by
        simp only [t']; ring
      rw [t'_sq] at hbound
      -- Take (n+1)th root
      have h_exp_nonneg : (1 : ℝ) / (n + 1) ≥ 0 := by positivity
      have step1 := ENNReal.rpow_le_rpow hbound h_exp_nonneg
      -- Distribute root over product
      have step2 : ((Fintype.card (Ω i) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) ^ 2 * t_opt ^ 2 / 2))) ^ ((1 : ℝ) / (n + 1)) =
          (Fintype.card (Ω i) : ℝ≥0∞) ^ ((1 : ℝ) / (n + 1)) *
          (ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) ^ 2 * t_opt ^ 2 / 2))) ^ ((1 : ℝ) / (n + 1)) :=
        ENNReal.mul_rpow_of_nonneg _ _ h_exp_nonneg
      rw [step2] at step1
      -- Simplify the exp root
      have step3 : (ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) ^ 2 * t_opt ^ 2 / 2))) ^ ((1 : ℝ) / (n + 1)) =
          ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt (Real.exp_pos _)) h_exp_nonneg]
        congr 1
        rw [← Real.exp_mul]
        congr 1
        have hn1_ne : (n + 1 : ℝ) ≠ 0 := by positivity
        simp only [Nat.cast_add, Nat.cast_one]
        have h_sq_div : (n + 1 : ℝ) ^ 2 / (n + 1) = (n + 1 : ℝ) := by
          rw [sq, mul_div_assoc, div_self hn1_ne, mul_one]
        calc σsq i * (n + 1 : ℝ) ^ 2 * t_opt ^ 2 / 2 * ((1 : ℝ) / (n + 1))
            = σsq i * t_opt ^ 2 / 2 * ((n + 1 : ℝ) ^ 2 / (n + 1)) := by ring
          _ = σsq i * t_opt ^ 2 / 2 * (n + 1 : ℝ) := by rw [h_sq_div]
          _ = σsq i * (n + 1 : ℝ) * t_opt ^ 2 / 2 := by ring
      rw [step3] at step1
      exact step1
  -- Bound the product
  have prod_bound : ∏ i : Fin n, (mgfCounting (g' i) ((n + 1 : ℕ) * t_opt)) ^ ((1 : ℝ) / (n + 1)) ≤
      (∏ i : Fin n, (Fintype.card (Ω i) : ℝ≥0∞) ^ ((1 : ℝ) / (n + 1))) *
      (∏ i : Fin n, ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2))) := by
    calc ∏ i : Fin n, (mgfCounting (g' i) ((n + 1 : ℕ) * t_opt)) ^ ((1 : ℝ) / (n + 1))
        ≤ ∏ i : Fin n, ((Fintype.card (Ω i) : ℝ≥0∞) ^ ((1 : ℝ) / (n + 1)) *
            ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2))) :=
          Finset.prod_le_prod (fun i _ => zero_le _) (fun i _ => counting_bound i)
      _ = (∏ i : Fin n, (Fintype.card (Ω i) : ℝ≥0∞) ^ ((1 : ℝ) / (n + 1))) *
          (∏ i : Fin n, ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2))) :=
          Finset.prod_mul_distrib
  -- Simplify the cardinality product
  have card_prod : ∏ i : Fin n, (Fintype.card (Ω i) : ℝ≥0∞) ^ ((1 : ℝ) / (n + 1)) =
      (∏ i : Fin n, (Fintype.card (Ω i) : ℝ≥0∞)) ^ ((1 : ℝ) / (n + 1)) := by
    rw [ENNReal.prod_rpow_of_nonneg (by positivity : (1 : ℝ) / (n + 1) ≥ 0)]
  -- Simplify the exp product
  have exp_prod : ∏ i : Fin n, ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2)) =
      ENNReal.ofReal (Real.exp (∑ i, σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2)) := by
    rw [← ENNReal.ofReal_prod_of_nonneg]; congr 1; rw [Real.exp_sum]
    intro i _; exact le_of_lt (Real.exp_pos _)
  -- The key arithmetic
  have exp_sum_simp : (∑ i, σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2) =
      (n + 1 : ℕ) * t_opt ^ 2 * (∑ i, σsq i) / 2 := by
    conv_lhs => arg 2; ext i
                rw [show σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2 = (n + 1 : ℕ) * t_opt ^ 2 / 2 * σsq i by ring]
    rw [← Finset.mul_sum]; ring
  have exp_arith : (n + 1 : ℕ) * t_opt ^ 2 * (∑ i, σsq i) / 2 + (-t_opt * a) =
      -a ^ 2 / (2 * (n + 1 : ℕ) * ∑ i, σsq i) := by
    simp only [t_opt]
    have h1 : ((n + 1 : ℕ) : ℝ) * (∑ i, σsq i) ≠ 0 := by positivity
    have h2 : (∑ i, σsq i) ≠ 0 := by linarith
    field_simp; ring
  -- Combine everything
  calc (∑ x, if ∑ i, g' i (x i) ≥ a then p.prob x else 0)
      ≤ ⨅ t ∈ Set.Ici (0 : ℝ), chernoffBound hn p g' a t := sum_conc
    _ ≤ chernoffBound hn p g' a t_opt := iInf₂_le t_opt ht_opt_nonneg
    _ = carberyFunctional hn p *
        (∏ i : Fin n, (mgfCounting (g' i) ((n + 1 : ℕ) * t_opt)) ^ (1 / (n + 1 : ℝ))) *
        ENNReal.ofReal (Real.exp (-t_opt * a)) := rfl
    _ ≤ carberyFunctional hn p *
        ((∏ i : Fin n, (Fintype.card (Ω i) : ℝ≥0∞) ^ ((1 : ℝ) / (n + 1))) *
         (∏ i : Fin n, ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2)))) *
        ENNReal.ofReal (Real.exp (-t_opt * a)) := by
        apply mul_le_mul_right'; apply mul_le_mul_left'; exact prod_bound
    _ = carberyFunctional hn p *
        (∏ i : Fin n, (Fintype.card (Ω i) : ℝ≥0∞)) ^ ((1 : ℝ) / (n + 1)) *
        (ENNReal.ofReal (Real.exp (∑ i, σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2)) *
         ENNReal.ofReal (Real.exp (-t_opt * a))) := by
        rw [card_prod, exp_prod]; ring
    _ = carberyFunctional hn p *
        (∏ i : Fin n, (Fintype.card (Ω i) : ℝ≥0∞)) ^ ((1 : ℝ) / (n + 1)) *
        ENNReal.ofReal (Real.exp ((∑ i, σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2) + (-t_opt * a))) := by
        rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)), ← Real.exp_add]
    _ = carberyFunctional hn p *
        (∏ i : Fin n, (Fintype.card (Ω i) : ℝ≥0∞)) ^ ((1 : ℝ) / (n + 1)) *
        ENNReal.ofReal (Real.exp ((n + 1 : ℕ) * t_opt ^ 2 * (∑ i, σsq i) / 2 + (-t_opt * a))) := by
        simp only [Nat.cast_add, Nat.cast_one] at exp_sum_simp ⊢; rw [exp_sum_simp]
    _ = carberyFunctional hn p *
        (∏ i : Fin n, (Fintype.card (Ω i) : ℝ≥0∞)) ^ ((1 : ℝ) / (n + 1)) *
        ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * (n + 1 : ℕ) * ∑ i, σsq i))) := by
        simp only [Nat.cast_add, Nat.cast_one] at exp_arith ⊢; rw [exp_arith]

/-- At t* = a / ((n+1) ∑ᵢ σᵢ²), the Chernoff-type bound for sub-Gaussian variables gives
    the claimed concentration inequality.

    **Note**: This uses the MARGINAL-WEIGHTED MGF (p.mgf), not the counting measure MGF.
    This is appropriate for sub-Gaussian bounds since the sub-Gaussian property is defined
    in terms of marginal-weighted expectations E[exp(tX)].

    **Paper contribution**: Proved. -/
theorem subgaussian_optimal_t (hn : n ≥ 1) (p : JointPMF Ω)
    (g : ∀ i, Ω i → ℝ) (σsq : Fin n → ℝ)
    (hσ : ∀ i, p.IsSubGaussianCentered g i (σsq i))
    (hpos : ∑ i, σsq i > 0) (a : ℝ) (ha : a > 0) :
    let g' := fun i s => g i s - p.expectation i (g i)
    let t_opt := a / ((n + 1 : ℕ) * ∑ i, σsq i)
    -- The marginal-weighted Chernoff bound at t_opt
    carberyFunctional hn p *
    (∏ i : Fin n, (p.mgf g' i ((n + 1 : ℕ) * t_opt)) ^ (1 / (n + 1 : ℝ))) *
    ENNReal.ofReal (Real.exp (-t_opt * a)) ≤
    carberyFunctional hn p *
    ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * (n + 1 : ℕ) * ∑ i, σsq i))) := by
  -- Define centered functions
  intro g' t_opt
  -- The Chernoff bound is: Q_n · ∏_i M_i((n+1)t)^{1/(n+1)} · exp(-t·a)
  -- Under sub-Gaussian assumption: M_i(t) ≤ exp(σᵢ² t² / 2)
  -- So M_i((n+1)t)^{1/(n+1)} ≤ exp(σᵢ² (n+1) t² / 2)
  -- Product gives: ∏_i exp(σᵢ² (n+1) t² / 2) = exp((n+1) t² ∑_i σᵢ² / 2)
  -- Multiplied by exp(-t·a) gives: exp((n+1) t² ∑_i σᵢ² / 2 - t·a)
  -- At t* = a / ((n+1) ∑_i σᵢ²):
  -- (n+1) t*² ∑_i σᵢ² / 2 - t*·a
  -- = (n+1) · (a² / ((n+1)² (∑σ)²)) · ∑σ / 2 - a² / ((n+1) ∑σ)
  -- = a² / (2(n+1) ∑σ) - a² / ((n+1) ∑σ)
  -- = -a² / (2(n+1) ∑σ)
  -- Step 1: Bound each MGF factor using mgf_subgaussian_bound
  -- Each (p.mgf g' i ((n+1)*t))^{1/(n+1)} ≤ exp(σᵢ² (n+1) t² / 2)
  have factor_bound : ∀ i : Fin n,
      (p.mgf g' i ((n + 1 : ℕ) * t_opt)) ^ ((1 : ℝ) / (n + 1)) ≤
      ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2)) := by
    intro i
    exact mgf_subgaussian_bound p g i (σsq i) (hσ i) t_opt
  -- Step 2: Bound the product
  have prod_bound : ∏ i : Fin n, (p.mgf g' i ((n + 1 : ℕ) * t_opt)) ^ ((1 : ℝ) / (n + 1)) ≤
      ∏ i : Fin n, ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2)) := by
    apply Finset.prod_le_prod
    · intro i _
      exact zero_le _
    · intro i _
      exact factor_bound i
  -- Step 3: Simplify product of exponentials
  have exp_prod : ∏ i : Fin n, ENNReal.ofReal (Real.exp (σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2)) =
      ENNReal.ofReal (Real.exp (∑ i, σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2)) := by
    rw [← ENNReal.ofReal_prod_of_nonneg]
    · congr 1
      rw [Real.exp_sum]
    · intro i _
      exact le_of_lt (Real.exp_pos _)
  -- Step 4: Simplify exponent sum
  have exp_sum_simp : (∑ i, σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2) =
      (n + 1 : ℕ) * t_opt ^ 2 * (∑ i, σsq i) / 2 := by
    -- Factor out common terms from the sum
    conv_lhs =>
      arg 2; ext i
      rw [show σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2 = (n + 1 : ℕ) * t_opt ^ 2 / 2 * σsq i by ring]
    rw [← Finset.mul_sum]
    ring
  -- Step 5: Compute the final exponent at t_opt
  -- At t* = a / ((n+1) ∑σ), the combined exponent is:
  -- (n+1) * t*² * ∑σ / 2 - t* * a = -a² / (2(n+1)∑σ)
  have exp_arith : (n + 1 : ℕ) * t_opt ^ 2 * (∑ i, σsq i) / 2 + (-t_opt * a) =
      -a ^ 2 / (2 * (n + 1 : ℕ) * ∑ i, σsq i) := by
    simp only [t_opt]
    have h1 : ((n + 1 : ℕ) : ℝ) * (∑ i, σsq i) ≠ 0 := by positivity
    have h2 : (∑ i, σsq i) ≠ 0 := by linarith
    field_simp
    ring
  -- Step 6: Combine bounds
  -- Q * prod * exp(-t*a)
  -- ≤ Q * exp(∑ σᵢ² (n+1) t² / 2) * exp(-t*a)
  -- = Q * exp((n+1) t² ∑σ / 2 - t*a)
  -- = Q * exp(-a²/(2(n+1)∑σ))
  calc carberyFunctional hn p *
        (∏ i : Fin n, (p.mgf g' i (↑(n + 1) * t_opt)) ^ ((1 : ℝ) / (↑n + 1))) *
        ENNReal.ofReal (Real.exp (-t_opt * a))
      ≤ carberyFunctional hn p *
        (∏ i : Fin n, ENNReal.ofReal (Real.exp (σsq i * ↑(n + 1) * t_opt ^ 2 / 2))) *
        ENNReal.ofReal (Real.exp (-t_opt * a)) := by
          apply mul_le_mul_right'
          apply mul_le_mul_left'
          exact prod_bound
    _ = carberyFunctional hn p *
        ENNReal.ofReal (Real.exp (∑ i, σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2)) *
        ENNReal.ofReal (Real.exp (-t_opt * a)) := by
          simp only [Nat.cast_add, Nat.cast_one] at exp_prod ⊢
          rw [exp_prod]
    _ = carberyFunctional hn p *
        ENNReal.ofReal (Real.exp (∑ i, σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2) *
                        Real.exp (-t_opt * a)) := by
          rw [mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    _ = carberyFunctional hn p *
        ENNReal.ofReal (Real.exp ((∑ i, σsq i * (n + 1 : ℕ) * t_opt ^ 2 / 2) + (-t_opt * a))) := by
          rw [← Real.exp_add]
    _ = carberyFunctional hn p *
        ENNReal.ofReal (Real.exp ((n + 1 : ℕ) * t_opt ^ 2 * (∑ i, σsq i) / 2 + (-t_opt * a))) := by
          simp only [Nat.cast_add, Nat.cast_one] at exp_sum_simp ⊢
          rw [exp_sum_simp]
    _ = carberyFunctional hn p *
        ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * (n + 1 : ℕ) * ∑ i, σsq i))) := by
          simp only [Nat.cast_add, Nat.cast_one] at exp_arith ⊢
          rw [exp_arith]

/-! **Note**: A theorem `subgaussian_independent` showing Q_n ≤ 1 under independence was here,
    but it used the marginal-weighted sub-Gaussian definition which is incompatible with
    Carbery's inequality. Use `subgaussian_concentration_counting` with `IsSubGaussianCounting`
    for results compatible with the paper's framework. -/

/-!
## Finite Sum Advantages

The finite case has several computational advantages.
-/

/-- MGF is always finite in the finite case.

    **Paper contribution**: Proved. -/
theorem mgf_finite (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (i : Fin n) (t : ℝ) :
    p.mgf g i t < ⊤ := by
  -- MGF is a finite sum of products of finite terms
  simp only [JointPMF.mgf]
  apply ENNReal.sum_lt_top.mpr
  intro s _
  apply ENNReal.mul_lt_top
  · exact lt_of_le_of_lt (marginal_le_one p i s) ENNReal.one_lt_top
  · exact ENNReal.ofReal_lt_top

/-- The sum MGF equals the product of marginal MGFs under independence.

    **Paper contribution**: Proved. -/
theorem sumMgf_of_independent (p : JointPMF Ω) (hp : p.IsIndependent)
    (g : ∀ i, Ω i → ℝ) (t : ℝ) :
    p.sumMgf g t = ∏ i : Fin n, p.mgf g i t := by
  -- Key insight: exp(t · ∑ᵢ gᵢ(xᵢ)) = ∏ᵢ exp(t · gᵢ(xᵢ))
  simp only [JointPMF.sumMgf, JointPMF.mgf]
  -- Rewrite exp of sum as product of exps
  have exp_sum : ∀ x : ∀ i, Ω i,
      Real.exp (t * ∑ i, g i (x i)) = ∏ i, Real.exp (t * g i (x i)) := by
    intro x
    rw [mul_sum, Real.exp_sum]
  simp_rw [exp_sum]
  -- Convert ENNReal.ofReal of product to product of ofReal (exp is positive)
  have ofReal_prod : ∀ x : ∀ i, Ω i,
      ENNReal.ofReal (∏ i, Real.exp (t * g i (x i))) =
      ∏ i, ENNReal.ofReal (Real.exp (t * g i (x i))) := by
    intro x
    rw [ENNReal.ofReal_prod_of_nonneg]
    intro i _
    exact le_of_lt (Real.exp_pos _)
  simp_rw [ofReal_prod]
  -- Apply independence factorization
  exact expectation_prod_of_independent p hp (fun i s => ENNReal.ofReal (Real.exp (t * g i s)))

/-!
## Weighted Sum Helper

For weighted sums S = ∑ᵢ wᵢ gᵢ(Xᵢ), if each gᵢ(Xᵢ) is sub-Gaussian with parameter σᵢ²,
then wᵢ gᵢ(Xᵢ) is sub-Gaussian with parameter wᵢ² σᵢ².

**Note**: The main weighted sum concentration theorem (Proposition 6.5 in the paper) is not
formalized here because it requires the counting measure sub-Gaussian definition.
The helper lemma below can be used to build such a result.
-/

/-- Scaling a sub-Gaussian variable by a constant w scales the parameter by w².
    If g is sub-Gaussian with parameter σ², then w·g is sub-Gaussian with parameter w²σ². -/
theorem isSubGaussianCentered_scale (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ)
    (i : Fin n) (σsq : ℝ) (w : ℝ)
    (hσ : p.IsSubGaussianCentered g i σsq) :
    p.IsSubGaussianCentered (fun j s => w * g j s) i (w ^ 2 * σsq) := by
  constructor
  · -- w² σ² ≥ 0
    apply mul_nonneg (sq_nonneg w) hσ.1
  · -- MGF bound for scaled variable
    intro t
    -- Mean of w·g is w·(mean of g)
    have mean_scale : p.expectation i (fun s => w * g i s) = w * p.expectation i (g i) := by
      simp only [JointPMF.expectation]
      simp_rw [mul_comm (p.marginal i _).toReal (w * _), mul_assoc w]
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    -- w·g(s) - w·μ = w·(g(s) - μ)
    have centered_scale : ∀ s, w * g i s - p.expectation i (fun s => w * g i s) =
        w * (g i s - p.expectation i (g i)) := by
      intro s
      rw [mean_scale]
      ring
    simp_rw [centered_scale]
    -- exp(t · w · (g - μ)) = exp((t·w) · (g - μ))
    have exp_factor : ∀ s, Real.exp (t * (w * (g i s - p.expectation i (g i)))) =
        Real.exp ((t * w) * (g i s - p.expectation i (g i))) := by
      intro s
      ring_nf
    simp_rw [exp_factor]
    -- Apply original sub-Gaussian bound at t' = t·w
    calc ∑ s, p.marginal i s * ENNReal.ofReal (Real.exp ((t * w) * (g i s - p.expectation i (g i))))
        ≤ ENNReal.ofReal (Real.exp (σsq * (t * w) ^ 2 / 2)) := hσ.2 (t * w)
      _ = ENNReal.ofReal (Real.exp (w ^ 2 * σsq * t ^ 2 / 2)) := by
          congr 1
          ring

/-! **Note**: Theorems `weighted_sum_concentration` and `weighted_sum_concentration_uniform`
    were here but used the marginal-weighted sub-Gaussian definition (`IsSubGaussianCentered`).
    This definition is incompatible with Carbery's inequality. For weighted sum bounds
    using the counting measure approach, adapt `subgaussian_concentration_counting`. -/

end
