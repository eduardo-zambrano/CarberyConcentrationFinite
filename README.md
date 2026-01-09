# Carbery Concentration Inequalities - Lean 4 Formalization

A Lean 4 formalization of concentration inequalities based on Carbery's multilinear generalization of the Cauchy-Schwarz inequality, as presented in:

> **Dependence-Aware Concentration Inequalities: A Multivariate Extension via Carbery's Inequality**
> Eduardo Zambrano (2025)

## Overview

This formalization develops multivariate extensions of classical concentration inequalities (Markov, Chebyshev, Chernoff) using Carbery's inequality. The key innovation is capturing dependence structure through the Carbery functional Q_n, which encodes relationships via consecutive bivariate marginals.

## Main Results

| Theorem | Paper Reference | File | Status |
|---------|-----------------|------|--------|
| Carbery's Inequality | Theorem 2.3 | `Basic.lean` | Axiomatized* |
| Independence Structure | Lemma 2.5 | `Basic.lean` | Proved |
| Multivariate Markov | Theorem 3.1 | `ConcentrationInequalities.lean` | Proved |
| Multivariate Chebyshev | Theorem 3.2 | `ConcentrationInequalities.lean` | Proved |
| General Moment Bound | Theorem 3.4 | `ConcentrationInequalities.lean` | Proved |
| MGF Inequality | Theorem 3.5 | `MGF.lean` | Depends on axiom* |
| Sum Concentration | Corollary 3.6 | `MGF.lean` | Proved |
| Sub-Gaussian Concentration | Theorem 3.7 | `MGF.lean` | Proved |
| Tensorization | Proposition 4.1(ii) | `Basic.lean` | Proved |
| Markov Chain Structure | Proposition 4.3 | `Basic.lean` | Proved |
| Permutation Bound | Proposition 6.1 | `Permutation.lean` | Depends on axiom* |
| Marginal Sufficiency | Proposition 7.1 | `Basic.lean` | Proved |

*Carbery's inequality (Theorem 2.3, from Carbery 2004) is axiomatized as a well-established result. Results marked "Depends on axiom" have complete proof structure but inherit a `sorry` from the axiomatized Carbery inequality.

## Project Structure

```
CarberyConcentrationFinite/
├── Basic.lean                     # Core definitions, Carbery's inequality, independence, tensorization, marginal sufficiency
├── ConcentrationInequalities.lean # Markov, Chebyshev, general moment bounds
├── MGF.lean                       # MGF bounds, Chernoff, sub-Gaussian concentration
└── Permutation.lean               # Variable reordering optimization
```

### File-to-Paper Mapping

| File | Paper Sections |
|------|----------------|
| `Basic.lean` | §2 (Preliminaries), §4.1 (Tensorization), §4.2 (Markov Chains), §7.1 (Marginal Sufficiency) |
| `ConcentrationInequalities.lean` | §3.1-3.2 (Markov, Chebyshev, General Moment) |
| `MGF.lean` | §3.4 (MGF, Chernoff, Sub-Gaussian) |
| `Permutation.lean` | §6 (Variable Reordering) |

## Building

```bash
# Install dependencies
lake update

# Build
lake build
```

Requires Lean 4 (v4.24.0) and Mathlib.

## Key Definitions

### Carbery Functional

```lean
def carberyFunctionalPow (hn : n ≥ 1) (p : JointPMF Ω) : ℝ≥0∞ :=
  ∑ s : ∀ i, Ω i,
    p.marginal ⟨0, _⟩ (s ⟨0, _⟩) *
    (∏ j : Fin (n - 1), p.bivariateMarginai j (s ⟨j.val, _⟩) (s ⟨j.val + 1, _⟩)) *
    p.marginal ⟨n - 1, _⟩ (s ⟨n - 1, _⟩)

def carberyFunctional (hn : n ≥ 1) (p : JointPMF Ω) : ℝ≥0∞ :=
  (carberyFunctionalPow hn p) ^ (1 / (n + 1 : ℝ))
```

### Carbery's Inequality

```lean
theorem carberyInequality (hn : n ≥ 1) (K : JointPMF Ω) (f : ∀ i, Ω i → ℝ≥0∞) :
    ∑ x : ∀ i, Ω i, K.prob x * ∏ i, f i (x i) ≤
    carberyFunctional hn K * ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (f i)
```

**Note:** Uses counting measure norms `lpNormFinite`, not marginal-weighted norms.

## References

- Carbery, A. (2004). "A multilinear generalisation of the Cauchy-Schwarz inequality." *Proceedings of the AMS*, 132(11), 3141-3152.
- Tao, T. (2023). "A generalized Cauchy-Schwarz inequality via the Gibbs variational formula." Blog post.
- Zambrano, E. (2025). "Dependence-Aware Concentration Inequalities: A Multivariate Extension via Carbery's Inequality."

## License

Apache 2.0
