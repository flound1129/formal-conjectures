/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Schur deficit-growth certificate-shape conjecture

*Source:* the `schur-numbers` project (`~/projects/schur-numbers`), where the
dyadic deficit-growth program is being developed for the PID-failing family
`n = 55 * 2^a`.

This file records the exact conjecture shape we are working toward:
every PID-failing dyadic row with at least two support cells should admit one
of the three currently formalized certificate branches.
-/

namespace SchurDeficitGrowth

universe u

/--
For every PID-failing deficit-growth row in the dyadic family `n = 55 * 2^a`
with `|P| ≥ 2`, the normalized cell should admit one of three certificate
shapes:

1. Whole-axis exact duality.
2. Reduced two-axis scanner exactness.
3. Carrier-backed AET exactness.
-/
@[category research open, AMS 5 11]
theorem deficit_growth_dyadic_certificate_shape
    {Cell : Type u}
    (IsPIDFailingDyadicDeficitGrowth : Cell → Finset ℕ → Prop)
    (WholeAxisCertificate : Cell → Finset ℕ → Prop)
    (ReducedTwoAxisCertificateShape : Cell → Finset ℕ → Prop)
    (hasCornerClusterCarrierAET : Cell → Finset ℕ → Prop) :
    ∀ cell P,
      IsPIDFailingDyadicDeficitGrowth cell P →
      2 ≤ P.card →
      WholeAxisCertificate cell P ∨
        ReducedTwoAxisCertificateShape cell P ∨
        hasCornerClusterCarrierAET cell P := by
  sorry

end SchurDeficitGrowth
