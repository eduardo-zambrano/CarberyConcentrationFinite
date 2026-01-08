/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Carbery's Multilinear Inequality and Concentration (Finite State Spaces)

This file contains the core definitions for formalizing concentration inequalities
based on Carbery's multilinear generalization of the Cauchy-Schwarz inequality,
specialized to finite state spaces.

## Main definitions

* `JointPMF`: A joint probability mass function on a finite product space
* `CarberyFunctional`: The functional Q_n encoding dependence through consecutive marginals
* `carberyInequality`: Carbery's inequality (AXIOMATIZED - see note below)

## Axiomatization Strategy

This formalization adopts a pragmatic approach:

**Axiomatized (well-established results not contributed by this paper):**
- Carbery's inequality [Carbery, Proc. AMS 2004]
- Hölder's inequality and its generalizations (available in Mathlib)

**To be proved (contributions of Zambrano 2025):**
- Concentration inequalities (Markov, Chebyshev, Chernoff extensions)
- Structure of Q_n under independence
- Variable reordering optimization

This approach focuses formalization effort on verifying the paper's novel contributions
while treating established mathematical results as trusted foundations.

## References

* [Carbery, A., A multilinear generalisation of the Cauchy-Schwarz inequality, 2004]
  Proceedings of the AMS, 132(11), 3141-3152.
* [Zambrano, E., Dependence-Aware Concentration Inequalities, 2025]
* [Tao, T., Blog post on Cauchy-Schwarz in finite settings]
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

/-!
## Core Definitions

We work with finite state spaces Ω₁, ..., Ωₙ, each with a Fintype instance.
A joint distribution is a probability mass function on the product space.
-/

variable {n : ℕ}

/-- A finite state space for each coordinate. -/
abbrev FiniteStateSpace (n : ℕ) := Fin n → Type*

/-- The product of finite state spaces. -/
abbrev ProductSpace {n : ℕ} (Ω : Fin n → Type*) := ∀ i, Ω i

/-- A joint probability mass function on finite product spaces.
    This is a function p : (∀ i, Ω i) → ℝ≥0∞ that sums to 1. -/
structure JointPMF {n : ℕ} (Ω : Fin n → Type*) [∀ i, Fintype (Ω i)] where
  /-- The probability mass function -/
  prob : (∀ i, Ω i) → ℝ≥0∞
  /-- Probabilities sum to 1 -/
  sum_eq_one : ∑ x : ∀ i, Ω i, prob x = 1

variable {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-- The i-th univariate marginal PMF.
    pᵢ(s) = ∑_{x : x_i = s} p(x) -/
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

/-- The consecutive bivariate marginal PMF of (Xᵢ, Xᵢ₊₁).
    p_{i,i+1}(s, t) = ∑_{x : x_i = s, x_{i+1} = t} p(x) -/
def JointPMF.bivariateMarginai (p : JointPMF Ω) (i : Fin (n - 1)) :
    Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ →
    Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ → ℝ≥0∞ :=
  fun s t => ∑ x : ∀ j, Ω j,
    if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧
       x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t
    then p.prob x else 0

/-- The Carbery functional Q_n^{n+1}(p) for a joint PMF on finite spaces.

    Q_n^{n+1}(p) = ∑_s p₁(s₁) · p₁₂(s₁,s₂) · p₂₃(s₂,s₃) · ⋯ · p_{n-1,n}(s_{n-1},sₙ) · pₙ(sₙ)

    IMPORTANT: This is the CORRECT formula from Carbery (2004) and Tao's exposition.
    Only BOUNDARY marginals (p₁ and pₙ) appear, not interior marginals.
    The formula has n+1 factors: 2 boundary marginals + (n-1) bivariate marginals.

    Reference: Tao, T. "A generalized Cauchy-Schwarz inequality via the Gibbs
    variational formula" (2023), which derives this from Carbery's original. -/
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

/-- The Lᵖ norm of a function on a finite type, using sums (counting measure). -/
def lpNormFinite (p : ℝ) {α : Type*} [Fintype α] (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ x : α, f x ^ p) ^ (1 / p)

/-- The Lᵖ norm of a function weighted by the marginal distribution.
    Note: This is used for independence characterization, NOT for Carbery's inequality.
    Carbery's inequality uses counting measure (lpNormFinite). -/
def lpNormMarginal (p : JointPMF Ω) (exp : ℝ) (i : Fin n) (f : Ω i → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ s : Ω i, p.marginal i s * f s ^ exp) ^ (1 / exp)

/-!
## Axiomatized Foundations

The following results are axiomatized as they are well-established mathematical
facts that the paper builds upon, not contributions of the paper itself.

### Carbery's Inequality (2004)

Carbery's multilinear generalization of Cauchy-Schwarz was proved in:
  Carbery, A. "A multilinear generalisation of the Cauchy-Schwarz inequality."
  Proceedings of the AMS, 132(11), 3141-3152, 2004.

The finite-case version can be proved by elementary induction using Hölder's
inequality, but this is not a contribution of the current paper.
-/

/-- **Carbery's Inequality** (Finite State Spaces) - ASSUMED.

    For functions fᵢ : Ωᵢ → ℝ≥0∞,
    ∑_x K(x) ∏ᵢ fᵢ(xᵢ) ≤ Qₙ(K) · ∏ᵢ ‖fᵢ‖_{L^{n+1}}

    where the L^{n+1} norms are with respect to counting measure (not the marginal).
    For n=1, this reduces to Cauchy-Schwarz: ∑ K·f ≤ ‖K‖₂ · ‖f‖₂.

    This is a well-known result [Carbery 2004]. We assume it to focus
    the formalization on the paper's novel contributions.

    Reference: Carbery, A. Proc. AMS 132(11), 3141-3152, 2004.
    See also: Tao, T. "A generalized Cauchy-Schwarz inequality via Gibbs" (2023).

    Note: This is marked `sorry` rather than `axiom` for compatibility with
    automated provers. The result is a published theorem (2004) that the
    paper builds upon, not a novel contribution. -/
theorem carberyInequality {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (hn : n ≥ 1) (K : JointPMF Ω)
    (f : ∀ i, Ω i → ℝ≥0∞) :
    ∑ x : ∀ i, Ω i, K.prob x * ∏ i, f i (x i) ≤
    carberyFunctional hn K * ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (f i) := by
  sorry

/-!
## Independence Structure

Under independence, the joint PMF factorizes as a product of marginals.
These results characterize Q_n under independence and are contributions
of the paper to be proved.
-/

/-- A joint PMF represents independent random variables if it factorizes
    as a product of marginals. -/
def JointPMF.IsIndependent (p : JointPMF Ω) : Prop :=
  ∀ x, p.prob x = ∏ i : Fin n, p.marginal i (x i)

set_option maxHeartbeats 400000 in
/-- Under independence, the consecutive bivariate marginals factorize.

    **Paper contribution**: Proved (by Aristotle). -/
theorem bivariate_factorizes_of_independent (p : JointPMF Ω)
    (hp : p.IsIndependent) (i : Fin (n - 1)) (s : Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
    (t : Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩) :
    p.bivariateMarginai i s t =
    p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s *
    p.marginal ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ t := by
  have h_prod : ∑ x : ∀ j, Ω j, (if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧ x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t then (∏ j, p.marginal j (x j)) else 0) = (∏ j ∈ Finset.univ \ {⟨i.val, Nat.lt_of_lt_pred i.isLt⟩, ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩}, ∑ x_j : Ω j, p.marginal j x_j) * (p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s) * (p.marginal ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ t) := by
    have h_sum_prod : ∑ x : ∀ j, Ω j, (if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧ x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t then (∏ j, p.marginal j (x j)) else 0) = (∑ x : ∀ j, Ω j, if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧ x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t then (∏ j ∈ Finset.univ \ {⟨i.val, Nat.lt_of_lt_pred i.isLt⟩, ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩}, p.marginal j (x j)) * (p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s) * (p.marginal ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ t) else 0) := by
      refine' Finset.sum_congr rfl fun x hx => _
      split_ifs <;> simp_all +decide [mul_assoc, Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_univ _]
      rw [← Finset.prod_sdiff (Finset.subset_univ {⟨i.val, Nat.lt_of_lt_pred i.isLt⟩, ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩})]
      aesop
    rw [h_sum_prod]
    simp +decide only [prod_sum]
    simp +decide [Finset.sum_ite, Finset.prod_mul_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    refine' congrArg₂ _ (congrArg₂ _ (Finset.sum_bij (fun x hx => fun j hj => x j) _ _ _ _) rfl) rfl
    · simp +contextual [Finset.mem_pi]
    · simp +contextual [funext_iff]
      grind
    · simp +decide [funext_iff, Finset.mem_pi]
      exact fun b => ⟨fun j => if hj : j = ⟨i, Nat.lt_of_lt_pred i.isLt⟩ then hj.symm ▸ s else if hj' : j = ⟨i + 1, Nat.add_lt_of_lt_sub i.isLt⟩ then hj'.symm ▸ t else b j (by aesop), by aesop⟩
    · exact fun x hx => by rw [← Finset.prod_attach]
  simp only [JointPMF.bivariateMarginai]
  have hp' : ∀ x, p.prob x = ∏ j, p.marginal j (x j) := hp
  simp_rw [hp']
  simp_all +decide [mul_assoc, Finset.prod_eq_one, JointPMF.marginal_sum_eq_one]

/-- Key algebraic lemma: Boundary terms and bivariate products combine to give
    each element appearing exactly twice (squared product form).

    This is the abstract form of the fact that in the Carbery functional,
    each marginal appears exactly twice under independence.

    **Paper contribution**: Proved by Aristotle. -/
theorem prod_boundary_bivariate_eq_sq {n : ℕ} (hn : n ≥ 2) (f : Fin n → ℝ≥0∞) :
    f ⟨0, by omega⟩ *
    (∏ j : Fin (n - 1), f ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩ *
                        f ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) *
    f ⟨n - 1, by omega⟩ =
    ∏ i : Fin n, f i * f i := by
  -- Proof by Aristotle using Fin product decomposition lemmas
  rcases n with (_ | _ | n) <;> norm_num
  · contradiction
  · contradiction
  · rw [Fin.prod_univ_castSucc]
    norm_num [Finset.prod_mul_distrib, mul_assoc]
    erw [Fin.prod_univ_succ]
    erw [Fin.prod_univ_castSucc]; ring!

/-- Under independence, Q_n^{n+1}(p) has a specific factorized form.

    With the CORRECT Carbery formula, under independence ALL marginals appear
    with power 2 (not the boundary-2/interior-3 pattern from the incorrect formula).

    Derivation: Under independence, p_{j,j+1}(s_j, s_{j+1}) = p_j(s_j) × p_{j+1}(s_{j+1}).
    So each interior marginal p_i (for 2 ≤ i ≤ n-1) appears exactly twice:
    once from p_{i-1,i} and once from p_{i,i+1}.
    Boundary marginals p_1 and p_n each appear twice: once from the explicit
    boundary term and once from the adjacent bivariate marginal.

    **Paper contribution**: To be proved (complex - needs careful index tracking). -/
theorem carberyFunctional_of_independent (hn : n ≥ 2) (p : JointPMF Ω)
    (hp : p.IsIndependent) :
    carberyFunctionalPow (Nat.one_le_of_lt hn) p =
    ∏ i : Fin n, (lpNormFinite 2 (p.marginal i)) ^ 2 := by
  -- Step 1: Rewrite RHS using lpNormFinite definition
  simp only [lpNormFinite]
  -- (∑_s f(s)^2)^{1/2})^2 = ∑_s f(s)^2
  -- First convert the natural number exponent 2 to real exponent
  have rhs_simp : ∀ i : Fin n, ((∑ s : Ω i, p.marginal i s ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) =
      ∑ s : Ω i, p.marginal i s ^ (2 : ℝ) := by
    intro i
    rw [← ENNReal.rpow_natCast _ (2 : ℕ), ← ENNReal.rpow_mul]
    simp only [one_div, Nat.cast_ofNat, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
               not_false_eq_true, IsUnit.inv_mul_cancel, ENNReal.rpow_one]
  simp_rw [rhs_simp]
  -- Step 2: Expand carberyFunctionalPow and use independence
  simp only [carberyFunctionalPow]
  -- Use bivariate_factorizes_of_independent to factor bivariate marginals
  have biv_factor : ∀ (j : Fin (n - 1)) (s : ∀ i, Ω i),
      p.bivariateMarginai j (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)
                           (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) =
      p.marginal ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩ (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩) *
      p.marginal ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩ (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) := by
    intro j s
    exact bivariate_factorizes_of_independent p hp j _ _
  -- After factoring bivariate marginals, show each marginal appears twice
  -- The key insight: with bivariate factorization, the full product becomes:
  --   p₀(s₀) × (∏_{j} p_j(s_j) × p_{j+1}(s_{j+1})) × p_{n-1}(s_{n-1})
  -- = p₀(s₀) × (∏_{j=0}^{n-2} p_j(s_j)) × (∏_{j=0}^{n-2} p_{j+1}(s_{j+1})) × p_{n-1}(s_{n-1})
  -- = p₀² × p₁² × ... × p_{n-1}²  (each marginal appears exactly twice)
  --
  -- Step 1: Rewrite bivariate product using prod_mul_distrib
  have prod_factor : ∀ s : ∀ i, Ω i,
      ∏ j : Fin (n - 1), (p.marginal ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩
                           (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩) *
                         p.marginal ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩
                           (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩)) =
      (∏ j : Fin (n - 1), p.marginal ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩
                           (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)) *
      (∏ j : Fin (n - 1), p.marginal ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩
                           (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩)) := by
    intro s
    exact Finset.prod_mul_distrib
  -- The remaining algebra requires showing the index pattern gives ∏_i p_i(s_i)²
  -- This is complex due to Fin arithmetic. The proof structure is:
  -- 1. The first product over Fin (n-1) gives p₀ × p₁ × ... × p_{n-2}
  -- 2. The second product gives p₁ × p₂ × ... × p_{n-1}
  -- 3. Combined with boundary terms p₀ and p_{n-1}, each appears twice
  -- 4. Use Fintype.prod_sum to interchange sum and product
  --
  -- Key lemma: For each s, the term equals ∏_i p_i(s_i)²
  have term_eq_prod_sq : ∀ s : ∀ i, Ω i,
      p.marginal ⟨0, by omega⟩ (s ⟨0, by omega⟩) *
      (∏ j : Fin (n - 1), p.marginal ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩
                           (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩) *
                         p.marginal ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩
                           (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩)) *
      p.marginal ⟨n - 1, by omega⟩ (s ⟨n - 1, by omega⟩) =
      ∏ i : Fin n, p.marginal i (s i) ^ (2 : ℝ) := by
    intro s
    -- For x^(2:ℝ) in ENNReal, convert to x * x
    have rpow_two_eq : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x * x := by
      intro x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
    simp_rw [rpow_two_eq]
    -- Apply the abstract algebraic lemma directly
    exact prod_boundary_bivariate_eq_sq hn (fun i => p.marginal i (s i))
  -- Rewrite LHS using biv_factor and term_eq_prod_sq
  -- First, rewrite bivariate marginals using factorization
  conv_lhs =>
    arg 2; ext s
    rw [Finset.prod_congr rfl (fun j _ => biv_factor j s)]
  -- Now apply term_eq_prod_sq to each summand
  conv_lhs =>
    arg 2; ext s
    rw [term_eq_prod_sq s]
  -- Use Fubini: ∑_s ∏_i f_i(s_i) = ∏_i (∑_{s_i} f_i(s_i))
  exact (Fintype.prod_sum (fun i si => p.marginal i si ^ (2 : ℝ))).symm

/-!
## Moment Definitions

For concentration inequalities, we need moments of random variables.
In the finite case, moments are finite sums.
-/

/-- The expectation of a real-valued function under the i-th marginal. -/
def JointPMF.expectation (p : JointPMF Ω) (i : Fin n) (f : Ω i → ℝ) : ℝ :=
  ∑ s : Ω i, (p.marginal i s).toReal * f s

/-- The k-th moment of a real-valued function under the i-th marginal.
    E[|g(Xᵢ)|^k] -/
def JointPMF.moment (p : JointPMF Ω) (i : Fin n) (g : Ω i → ℝ) (k : ℝ) : ℝ≥0∞ :=
  ∑ s : Ω i, p.marginal i s * ENNReal.ofReal (|g s| ^ k)

/-!
## Key Simplification: Finite Sums

The main advantage of finite state spaces is that all expectations and
probabilities are finite sums, avoiding measure-theoretic complications.
-/

/-- Expectation of a product factorizes under independence.

    **Paper contribution**: Proved. -/
theorem expectation_prod_of_independent (p : JointPMF Ω) (hp : p.IsIndependent)
    (f : ∀ i, Ω i → ℝ≥0∞) :
    ∑ x : ∀ i, Ω i, p.prob x * ∏ i, f i (x i) =
    ∏ i : Fin n, ∑ s : Ω i, p.marginal i s * f i s := by
  -- Under independence, p.prob x = ∏ i, p.marginal i (x i)
  have h1 : ∀ x, p.prob x * ∏ i, f i (x i) = ∏ i, (p.marginal i (x i) * f i (x i)) := by
    intro x
    rw [hp x, Finset.prod_mul_distrib]
  simp_rw [h1]
  -- Use Fintype.prod_sum to interchange sum and product
  exact (Fintype.prod_sum (fun i s => p.marginal i s * f i s)).symm

/-- The sum of all probabilities equals 1 (sanity check). -/
theorem prob_sum_one (p : JointPMF Ω) : ∑ x : ∀ i, Ω i, p.prob x = 1 := p.sum_eq_one

/-!
## Utility Lemmas

Basic properties of probabilities in the finite setting.
-/

/-- In the finite case, probabilities are always in [0, 1]. -/
theorem prob_le_one (p : JointPMF Ω) (x : ∀ i, Ω i) : p.prob x ≤ 1 := by
  have h := p.sum_eq_one
  calc p.prob x ≤ ∑ y : ∀ i, Ω i, p.prob y := Finset.single_le_sum (fun _ _ => zero_le _)
                                               (Finset.mem_univ x)
       _ = 1 := h

/-- Marginal probabilities are bounded by 1. -/
theorem marginal_le_one (p : JointPMF Ω) (i : Fin n) (s : Ω i) :
    p.marginal i s ≤ 1 := by
  have h := p.marginal_sum_eq_one i
  calc p.marginal i s ≤ ∑ t : Ω i, p.marginal i t :=
         Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ s)
       _ = 1 := h

end
