# Carbery's Inequality - Proof Strategy (CORRECTED)

Based on Terry Tao's blog post: "A generalized Cauchy-Schwarz inequality via the Gibbs variational formula" (December 2023).

**IMPORTANT CORRECTION**: The inequality uses COUNTING MEASURE norms (unweighted sums), NOT marginal-weighted norms. The previous formulation with marginal-weighted norms was DISPROVED.

## The Theorem (Finite Case - CORRECTED)

For finite state spaces Ω₀, ..., Ωₙ₋₁, a joint PMF K, and functions fᵢ : Ωᵢ → ℝ≥0∞:

∑_x K(x) ∏ᵢ fᵢ(xᵢ) ≤ Qₙ(K) · ∏ᵢ ‖fᵢ‖_{L^{n+1}(counting)}

where:
- Qₙ(K) is the Carbery functional involving boundary marginals and consecutive bivariate marginals
- ‖fᵢ‖_{L^{n+1}(counting)} = (∑_s fᵢ(s)^{n+1})^{1/(n+1)} is the COUNTING MEASURE norm (unweighted)

This is NOT the same as the marginal-weighted norm (∑_s μᵢ(s) · fᵢ(s)^{n+1})^{1/(n+1)}.

## Proof Strategy 1: Induction with Hölder's Inequality

### Base Case (n=1)
For n=1, we need to show:
∑_{x₀,x₁} K(x₀,x₁) · f₀(x₀) · f₁(x₁) ≤ Q₁(K) · ‖f₀‖_{L²} · ‖f₁‖_{L²}

where Q₁(K) involves the boundary marginals K₀, K₁ and the joint K.

This follows from Cauchy-Schwarz applied appropriately.

### Inductive Step
Use Hölder's inequality to "integrate out" one variable at a time.

Key idea: Fix the last coordinate xₙ₋₁, apply the induction hypothesis to the remaining n-1 coordinates, then use Hölder to recombine.

## Proof Strategy 2: Gibbs Variational Formula (Tao's approach)

### Lemma (Gibbs Variational Formula)
For f: S → ℝ on finite set S:
log ∑_{s∈S} exp(f(s)) = sup_X [𝔼[f(X)] + H[X]]

where H[X] is Shannon entropy and the sup is over all probability distributions on S.

### Key Insight
Take logarithms of both sides of Carbery's inequality and use the variational formula.
This reduces the inequality to a statement about conditional entropy.

### Lemma (Entropy Identity)
For tuples (X₀,...,Xₙ₋₁) satisfying certain constraints:
H[X₀,...,Xₙ₋₁] ≤ sum of individual and pairwise entropies

This is proven by induction, using the chain rule for entropy:
H[X,Y] = H[X] + H[Y|X]

### The Logarithmic Form
Taking logs, the inequality becomes:
log(∑_x K(x) ∏ᵢ fᵢ(xᵢ)) ≤ (1/(n+1)) · log(Qₙ^{n+1}(K)) + ∑ᵢ (1/(n+1)) · log(∑_s fᵢ(s)^{n+1})

## Key Mathlib Lemmas

- `ENNReal.inner_le_Lp_mul_Lq` - Hölder's inequality for ENNReal
- `ENNReal.rpow_add`, `ENNReal.rpow_mul` - Power arithmetic
- `Finset.sum_product`, `Finset.prod_mul_distrib` - Sum/product manipulation
- `Real.inner_le_Lp_mul_Lq` - Hölder's inequality for Real
- `NNReal.inner_le_Lp_mul_Lq` - Hölder's inequality for NNReal

## Proof Sketch for Lean

1. **Induction on n**
2. **Base case n=1**: Apply Cauchy-Schwarz
   - The key is showing Q₁(K) · ‖f₀‖_{L²} · ‖f₁‖_{L²} bounds the bilinear form
3. **Inductive step**:
   - Fix the last coordinate xₙ₋₁
   - Apply induction hypothesis to the remaining n-1 coordinates
   - Use Hölder's inequality with exponents (n+1, (n+1)/n) to recombine
   - Show the Carbery functional structure correctly captures the dependencies

## Alternative: Direct Verification for Small n

For n=2:
∑_{x₀,x₁,x₂} K(x₀,x₁,x₂) · f₀(x₀) · f₁(x₁) · f₂(x₂) ≤ Q₂(K) · ‖f₀‖_{L³} · ‖f₁‖_{L³} · ‖f₂‖_{L³}

Use Hölder with exponents (3, 3, 3) after appropriate manipulation.

## References

- Carbery, A. (2004). "A multilinear generalisation of the Cauchy-Schwarz inequality". Proc. Amer. Math. Soc.
- Tao, T. (2023). "A generalized Cauchy-Schwarz inequality via the Gibbs variational formula". Blog post.
