# Carbery Concentration Inequalities - Lean 4 Formalization

A Lean 4 formalization of concentration inequalities based on Carbery's multilinear generalization of the Cauchy-Schwarz inequality, as presented in:

> **Dependence-Aware Concentration Inequalities: A Multivariate Extension via Carbery's Inequality**
> Eduardo Zambrano (2025)

## Overview

This formalization develops multivariate extensions of classical concentration inequalities (Markov, Chebyshev, Chernoff) using Carbery's inequality. The key innovation is capturing dependence structure through the Carbery functional Q_n, which encodes relationships via consecutive bivariate marginals.

## Main Results

| Theorem | File | Status |
|---------|------|--------|
| Carbery's Inequality | `Basic.lean` | Axiomatized* |
| Multivariate Markov | `ConcentrationInequalities.lean` | Proved |
| Multivariate Chebyshev | `ConcentrationInequalities.lean` | Proved |
| General Moment Bound | `ConcentrationInequalities.lean` | Proved |
| MGF Inequality (counting measure) | `MGF.lean` | Proved |
| Sum Concentration (Chernoff) | `MGF.lean` | Proved |
| Sub-Gaussian Concentration | `MGF.lean` | Proved |
| Independence Structure of Q_n | `Basic.lean` | Proved |
| Permutation Optimization | `Permutation.lean` | Proved |

*Carbery's inequality (2004) is axiomatized as a well-established result from the literature. The novel contributions of the paper are fully proved.

## Project Structure

```
CarberyConcentrationFinite/
├── Basic.lean                     # Core definitions, Carbery's inequality, independence structure
├── ConcentrationInequalities.lean # Markov, Chebyshev, general moment bounds
├── MGF.lean                       # MGF bounds, Chernoff, sub-Gaussian concentration
└── Permutation.lean               # Variable reordering optimization
```

### File-to-Paper Mapping

| File | Paper Section |
|------|---------------|
| `Basic.lean` | Section 2 (Preliminaries) + Section 4 (Properties of Q_n) |
| `ConcentrationInequalities.lean` | Section 3.1-3.2 (Markov, Chebyshev) |
| `MGF.lean` | Section 3.3-3.5 (MGF, Chernoff, Sub-Gaussian) |
| `Permutation.lean` | Section 6 (Variable Reordering) |

## Building

```bash
# Install dependencies
lake update

# Build
lake build
```

Requires Lean 4 and Mathlib.

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
