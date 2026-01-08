/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Sub-Gaussian Concentration (For Aristotle)

This file contains the subgaussian_concentration theorem to be proved.
-/

import CarberyConcentrationFinite.ConcentrationInequalities

open scoped ENNReal NNReal BigOperators
open Finset Real

noncomputable section

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-- The moment generating function of the i-th marginal at parameter t.
    Mᵢ(t) = E[exp(t · g(Xᵢ))] for a real-valued function g. -/
def JointPMF.mgf (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (i : Fin n) (t : ℝ) : ℝ≥0∞ :=
  ∑ s : Ω i, p.marginal i s * ENNReal.ofReal (Real.exp (t * g i s))

/-- Centered sub-Gaussian: after mean subtraction. -/
def JointPMF.IsSubGaussianCentered (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (i : Fin n) (σsq : ℝ) : Prop :=
  let μ := p.expectation i (g i)
  σsq ≥ 0 ∧ ∀ t : ℝ,
    ∑ s : Ω i, p.marginal i s * ENNReal.ofReal (Real.exp (t * (g i s - μ))) ≤
    ENNReal.ofReal (Real.exp (σsq * t ^ 2 / 2))

/-- The Chernoff bound for the sum S = ∑ᵢ gᵢ(Xᵢ) at threshold a with parameter t. -/
def chernoffBound (hn : n ≥ 1) (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (a t : ℝ) : ℝ≥0∞ :=
  carberyFunctional hn p *
  (∏ i : Fin n, (p.mgf g i ((n + 1 : ℕ) * t)) ^ (1 / (n + 1 : ℝ))) *
  ENNReal.ofReal (Real.exp (-t * a))

/-- Sub-Gaussian Concentration (Theorem 3.7) for finite spaces.

    If each gᵢ(Xᵢ) is sub-Gaussian with parameter σᵢ², then for S = ∑ᵢ gᵢ(Xᵢ):

    P(S - E[S] ≥ a) ≤ Qₙ(p) · exp(-a² / (2(n+1) ∑ᵢ σᵢ²))

    The factor (n+1) arises from the MGF bound being evaluated at (n+1)t.

    Proof strategy:
    1. Apply sum_concentration with centered g'ᵢ = gᵢ - E[gᵢ]
    2. Use sub-Gaussian property to bound each MGF term
    3. Optimize over t at t* = a / ((n+1) ∑ᵢ σᵢ²)
    4. The exponential arithmetic gives the result -/
theorem subgaussian_concentration (hn : n ≥ 1) (p : JointPMF Ω)
    (g : ∀ i, Ω i → ℝ) (σsq : Fin n → ℝ)
    (hσ : ∀ i, p.IsSubGaussianCentered g i (σsq i))
    (a : ℝ) (ha : a > 0) :
    let μ := ∑ i, p.expectation i (g i)
    (∑ x : ∀ i, Ω i, if ∑ i, g i (x i) - μ ≥ a then p.prob x else 0) ≤
    carberyFunctional hn p *
    ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * (n + 1 : ℕ) * ∑ i, σsq i))) := by
  sorry

end
