/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Extension via Variable Reordering (Finite State Spaces)

The Carbery functional Q_n treats consecutive pairs (Xᵢ, Xᵢ₊₁) specially.
For general dependence structures, we can optimize over variable orderings
(permutations) to capture the strongest dependencies within the consecutive
structure.

## Main results (Paper Contributions - Zambrano 2025)

* `permutation_bound_uniform`: Optimized bound over all permutations
* `permutation_bound_attained_uniform`: The infimum is attained (finite set)

These are **paper contributions** showing how to optimize the Carbery bound
over variable orderings.

## Implementation notes

In the finite case, there are exactly n! permutations, so the infimum is a minimum.

Working with permuted state spaces in dependent type theory is subtle.
We restrict to uniform state spaces (all Ωᵢ = α) for simplicity.

## References

* [Zambrano, E., Dependence-Aware Concentration Inequalities, 2025]
-/

import CarberyConcentrationFinite.ConcentrationInequalities
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open scoped ENNReal NNReal BigOperators
open Finset Equiv.Perm

noncomputable section

/-!
## Permutation Bound for Uniform State Spaces

When all state spaces are the same type α, permutations are straightforward.
-/

variable {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

/-- A joint PMF on a uniform product space α^n. -/
abbrev UniformJointPMF (n : ℕ) (α : Type*) [Fintype α] := JointPMF (fun _ : Fin n => α)

/-- The permuted PMF when all state spaces are the same.
    p_σ(x) = p(x ∘ σ⁻¹)

    **Paper contribution**: sum_eq_one to be proved. -/
def UniformJointPMF.permute (p : UniformJointPMF n α) (σ : Equiv.Perm (Fin n)) :
    UniformJointPMF n α where
  prob := fun x => p.prob (x ∘ σ.symm)
  sum_eq_one := by
    have h : ∑ x : Fin n → α, p.prob (x ∘ σ.symm) = ∑ y : Fin n → α, p.prob y := by
      -- Direct reindexing using Fintype.sum_equiv
      let φ : (Fin n → α) ≃ (Fin n → α) :=
        { toFun := fun x => x ∘ σ
          invFun := fun x => x ∘ σ.symm
          left_inv := by intro x; ext i; simp [Function.comp]
          right_inv := by intro x; ext i; simp [Function.comp] }
      have : ∀ x, p.prob (x ∘ σ.symm) = p.prob (φ.symm x) := by
        intro x; rfl
      simp_rw [this]
      exact Equiv.sum_comp φ.symm (fun y => p.prob y)
    rw [h, p.sum_eq_one]

/-- Permuting twice with inverse gives the original.

    **Paper contribution**: Proved. -/
theorem UniformJointPMF.permute_symm (p : UniformJointPMF n α) (σ : Equiv.Perm (Fin n)) :
    (p.permute σ).permute σ.symm = p := by
  -- Two JointPMFs are equal if their prob functions are equal
  have h : ((p.permute σ).permute σ.symm).prob = p.prob := by
    ext x
    simp only [UniformJointPMF.permute, Function.comp]
    congr 1
    ext i
    simp [Equiv.symm_symm]
  cases p
  simp only [UniformJointPMF.permute] at h ⊢
  congr

/-- The marginal of the permuted PMF at index i equals the original marginal at σ(i).

    **Paper contribution**: Proved. -/
theorem UniformJointPMF.permute_marginal (p : UniformJointPMF n α)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) (s : α) :
    (p.permute σ).marginal i s = p.marginal (σ i) s := by
  simp only [JointPMF.marginal, UniformJointPMF.permute]
  -- Need to show: ∑ x, (if x i = s then p.prob(x ∘ σ⁻¹) else 0)
  --             = ∑ y, (if y (σ i) = s then p.prob y else 0)
  -- Use reindexing: let y = x ∘ σ⁻¹, so x = y ∘ σ
  -- Then x i = (y ∘ σ) i = y (σ i)
  let φ : (Fin n → α) ≃ (Fin n → α) :=
    { toFun := fun x => x ∘ σ.symm
      invFun := fun x => x ∘ σ
      left_inv := by intro x; ext j; simp [Function.comp]
      right_inv := by intro x; ext j; simp [Function.comp] }
  have hφ : ∀ x, p.prob (x ∘ σ.symm) = p.prob (φ x) := fun _ => rfl
  have hi : ∀ x, x i = (φ x) (σ i) := by
    intro x
    simp only [φ, Equiv.coe_fn_mk, Function.comp_apply, Equiv.symm_apply_apply]
  simp_rw [hφ, hi]
  exact Equiv.sum_comp φ fun y => if y (σ i) = s then p.prob y else 0

/-!
## Permutation Bound

The key insight is that the intersection event P(∩ᵢ {hᵢ(Xᵢ) ≥ cᵢ}) is invariant
under relabeling of variables, but different labelings yield different Q_n values.
This is a **paper contribution**.
-/

set_option maxHeartbeats 400000 in
/-- The permutation bound for uniform state spaces. -/
def permutationBoundUniform (hn : n ≥ 1) (p : UniformJointPMF n α)
    (h : Fin n → α → ℝ≥0∞) (c : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ≥0∞ :=
  (carberyFunctional hn (p.permute σ) / ∏ i, ENNReal.ofReal (c i)) *
  ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (h (σ i))

/-- **Permutation Bound** for uniform state spaces.

    P(∩ᵢ {hᵢ(Xᵢ) ≥ cᵢ}) ≤ inf_{σ ∈ Sₙ} bound(σ)

    Since Sₙ is finite, the infimum is a minimum.

    Proof strategy:
    1. For any σ, rewrite the probability via change of variables y = x ∘ σ
    2. Apply multivariate_markov to (p.permute σ) with functions h ∘ σ
    3. The resulting bound equals permutationBoundUniform(σ)
    4. Since this holds for all σ, the LHS ≤ inf_σ bound(σ)

    **Paper contribution**: To be proved. -/
theorem permutation_bound_uniform (hn : n ≥ 1) (p : UniformJointPMF n α)
    (h : Fin n → α → ℝ≥0∞) (c : Fin n → ℝ) (hc : ∀ i, c i > 0) :
    (∑ x : Fin n → α, if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0) ≤
    ⨅ σ : Equiv.Perm (Fin n), permutationBoundUniform hn p h c σ := by
  -- Use le_ciInf: to show LHS ≤ inf_σ f(σ), it suffices to show LHS ≤ f(σ) for all σ
  apply le_ciInf
  intro σ
  -- Step 1: Change of variables x → y where y = x ∘ σ.symm (so x = y ∘ σ)
  -- The original probability equals:
  -- ∑_y if ∀i, h i (y (σ i)) ≥ c i then (p.permute σ.symm).prob y else 0
  -- Reindex i → σ.symm i (so i = σ j):
  -- ∑_y if ∀j, h (σ j) (y j) ≥ c (σ j) then (p.permute σ.symm).prob y else 0
  --
  -- But we want to use (p.permute σ). Let's work with τ = σ directly.
  -- Change vars: Let y = x ∘ σ, then x = y ∘ σ.symm
  -- p.prob x = p.prob (y ∘ σ.symm) = (p.permute σ).prob y
  have change_vars : ∑ x : Fin n → α, (if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0) =
      ∑ y : Fin n → α, (if ∀ i, h i ((y ∘ σ.symm) i) ≥ ENNReal.ofReal (c i)
                        then (p.permute σ).prob y else 0) := by
    -- Use Equiv.sum_comp with the equivalence x ↦ x ∘ σ
    let φ : (Fin n → α) ≃ (Fin n → α) :=
      { toFun := fun x => x ∘ σ
        invFun := fun x => x ∘ σ.symm
        left_inv := by intro x; ext i; simp [Function.comp]
        right_inv := by intro x; ext i; simp [Function.comp] }
    have h1 : ∀ x, p.prob x = (p.permute σ).prob (φ x) := by
      intro x
      simp only [φ, UniformJointPMF.permute, Equiv.coe_fn_mk, Function.comp]
      congr 1
      ext i; simp
    have h2 : ∀ x, (∀ i, h i (x i) ≥ ENNReal.ofReal (c i)) ↔
                   (∀ i, h i ((φ x ∘ σ.symm) i) ≥ ENNReal.ofReal (c i)) := by
      intro x
      constructor <;> intro hx i
      · simp only [φ, Equiv.coe_fn_mk, Function.comp_apply, Equiv.apply_symm_apply]; exact hx i
      · have := hx i
        simp only [φ, Equiv.coe_fn_mk, Function.comp_apply, Equiv.apply_symm_apply] at this
        exact this
    calc ∑ x, (if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0)
        = ∑ x, (if ∀ i, h i ((φ x ∘ σ.symm) i) ≥ ENNReal.ofReal (c i)
                then (p.permute σ).prob (φ x) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [h1 x]
          congr 1
          exact propext (h2 x)
      _ = ∑ y, (if ∀ i, h i ((y ∘ σ.symm) i) ≥ ENNReal.ofReal (c i)
                then (p.permute σ).prob y else 0) := by
          exact Equiv.sum_comp φ (fun y => if ∀ i, h i ((y ∘ σ.symm) i) ≥ ENNReal.ofReal (c i)
                                           then (p.permute σ).prob y else 0)
  -- Step 2: Reindex the condition: ∀i, h i (y (σ.symm i)) ≥ c i ↔ ∀j, h (σ j) (y j) ≥ c (σ j)
  -- where j = σ.symm i
  have reindex_cond : ∀ y, (∀ i, h i ((y ∘ σ.symm) i) ≥ ENNReal.ofReal (c i)) ↔
                          (∀ j, h (σ j) (y j) ≥ ENNReal.ofReal (c (σ j))) := by
    intro y
    constructor
    · intro hy j
      have := hy (σ j)
      simp only [Function.comp_apply, Equiv.symm_apply_apply] at this
      exact this
    · intro hy i
      have := hy (σ.symm i)
      simp only [Equiv.apply_symm_apply] at this
      simp only [Function.comp_apply]
      exact this
  -- Rewrite using the reindexed condition
  have sum_reindex : ∑ y : Fin n → α, (if ∀ i, h i ((y ∘ σ.symm) i) ≥ ENNReal.ofReal (c i)
                                        then (p.permute σ).prob y else 0) =
      ∑ y : Fin n → α, (if ∀ j, h (σ j) (y j) ≥ ENNReal.ofReal (c (σ j))
                        then (p.permute σ).prob y else 0) := by
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    exact propext (reindex_cond y)
  -- Step 3: Apply multivariate_markov to (p.permute σ) with h' j = h (σ j) and c' j = c (σ j)
  have hc' : ∀ j, c (σ j) > 0 := fun j => hc (σ j)
  have markov_applied := multivariate_markov hn (p.permute σ) (fun j => h (σ j)) (fun j => c (σ j)) hc'
  -- Step 4: Show the RHS of Markov equals permutationBoundUniform
  -- The product of c's is unchanged by permutation
  have prod_c_eq : ∏ j : Fin n, ENNReal.ofReal (c (σ j)) = ∏ i : Fin n, ENNReal.ofReal (c i) := by
    -- Use Equiv.prod_comp: ∏ i, f (e i) = ∏ i, f i
    exact Equiv.prod_comp σ (fun i => ENNReal.ofReal (c i))
  -- Combine
  calc ∑ x : Fin n → α, (if ∀ i, h i (x i) ≥ ENNReal.ofReal (c i) then p.prob x else 0)
      = ∑ y, (if ∀ i, h i ((y ∘ σ.symm) i) ≥ ENNReal.ofReal (c i)
              then (p.permute σ).prob y else 0) := change_vars
    _ = ∑ y, (if ∀ j, h (σ j) (y j) ≥ ENNReal.ofReal (c (σ j))
              then (p.permute σ).prob y else 0) := sum_reindex
    _ ≤ (carberyFunctional hn (p.permute σ) / ∏ j, ENNReal.ofReal (c (σ j))) *
        ∏ j, lpNormFinite (n + 1 : ℝ) (h (σ j)) :=
        markov_applied
    _ = (carberyFunctional hn (p.permute σ) / ∏ i, ENNReal.ofReal (c i)) *
        ∏ i, lpNormFinite (n + 1 : ℝ) (h (σ i)) := by
        rw [prod_c_eq]
    _ = permutationBoundUniform hn p h c σ := rfl

/-- The bound is attained by some permutation (the infimum is a minimum).

    **Paper contribution**: Proved. -/
theorem permutation_bound_attained_uniform (hn : n ≥ 1) (p : UniformJointPMF n α)
    (h : Fin n → α → ℝ≥0∞) (c : Fin n → ℝ) :
    ∃ σ_opt : Equiv.Perm (Fin n),
      ⨅ σ : Equiv.Perm (Fin n), permutationBoundUniform hn p h c σ =
      permutationBoundUniform hn p h c σ_opt := by
  -- Since Equiv.Perm (Fin n) is finite and nonempty, the infimum is a minimum
  -- Use Finset.exists_min_image
  obtain ⟨σ_opt, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (permutationBoundUniform hn p h c) Finset.univ_nonempty
  use σ_opt
  apply le_antisymm
  · have hbdd : BddBelow (Set.range fun σ => permutationBoundUniform hn p h c σ) :=
      ⟨0, fun _ _ => zero_le _⟩
    exact ciInf_le hbdd σ_opt
  · exact le_ciInf fun σ => hmin σ (Finset.mem_univ σ)

/-- The optimal permutation for uniform state spaces. -/
def optimalPermutationUniform (hn : n ≥ 1) (p : UniformJointPMF n α)
    (h : Fin n → α → ℝ≥0∞) (c : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  (permutation_bound_attained_uniform hn p h c).choose

/-!
## Computational Complexity

Finding the optimal permutation requires checking n! possibilities.
For small n this is feasible. The paper discusses greedy heuristics for larger n,
but these are practical algorithms rather than formal results.
-/

/-- Number of permutations of Fin n is n!. -/
theorem card_perm_fin' : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
  simp [Fintype.card_perm]

end
