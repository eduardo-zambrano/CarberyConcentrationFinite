/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Carbery Concentration Inequalities (Finite State Spaces)

This library formalizes concentration inequalities based on Carbery's multilinear
generalization of the Cauchy-Schwarz inequality, specialized to finite state spaces.

## Overview

By restricting to finite state spaces, we avoid measure-theoretic technicalities:
- Integrals become finite sums
- Measurability is automatic
- Marginals are computed by direct summation

This follows Terry Tao's pedagogical approach of reducing to finite settings
before addressing general cases.

## Axiomatization Strategy

This formalization adopts a **pragmatic approach**:

### Axiomatized (well-established results):
- **Carbery's Inequality** [Carbery, Proc. AMS 2004]: The multilinear generalization
  of Cauchy-Schwarz is a published, peer-reviewed result that the paper builds upon.

### To be proved (paper contributions - Zambrano 2025):
1. **Concentration Inequalities**: Multivariate extensions of Markov, Chebyshev,
   and Chernoff bounds that explicitly incorporate dependence structure.

2. **Independence Structure**: Characterization of Q_n under independence,
   showing boundary variables appear with power 2, interior with power 3.

3. **Variable Reordering**: Optimization over permutations to capture general
   dependence structures within the consecutive-pair framework.

4. **MGF Bounds**: Moment generating function inequalities and sub-Gaussian
   concentration for dependent random variables.

## Main results to prove

* `multivariate_markov`: Theorem 3.1 - Multivariate Markov inequality
* `multivariate_chebyshev`: Theorem 3.2 - Multivariate Chebyshev inequality
* `general_moment_bound`: Theorem 3.4 - General moment inequality
* `mgf_inequality`: Theorem 3.5 - MGF bound
* `sum_concentration`: Corollary 3.6 - Chernoff-type bound
* `subgaussian_concentration`: Theorem 3.7 - Sub-Gaussian concentration
* `carberyFunctional_of_independent`: Q_n structure under independence
* `permutation_bound_uniform`: Optimized bound over permutations

## Files

- `Basic.lean`: Core definitions and axiomatized Carbery inequality
- `ConcentrationInequalities.lean`: Markov, Chebyshev, general moment bounds
- `MGF.lean`: MGF inequality and Chernoff-type bounds
- `Permutation.lean`: Variable reordering and optimization

## Note on Gaussian Results

The continuous Gaussian characterization (Section 5 of the paper) does not have
a direct finite analog. For finite approximations to Gaussian distributions,
discretization techniques would be needed.

## References

* Carbery, A. (2004). A multilinear generalisation of the Cauchy-Schwarz inequality.
  Proceedings of the AMS, 132(11), 3141-3152.

* Zambrano, E. (2025). Dependence-Aware Concentration Inequalities:
  A Multivariate Extension via Carbery's Inequality. (Under review)

* Tao, T. Blog post on Cauchy-Schwarz in finite settings.
  https://terrytao.wordpress.com/tag/cauchy-schwarz/
-/

import CarberyConcentrationFinite.Basic
import CarberyConcentrationFinite.ConcentrationInequalities
import CarberyConcentrationFinite.MGF
import CarberyConcentrationFinite.Permutation
