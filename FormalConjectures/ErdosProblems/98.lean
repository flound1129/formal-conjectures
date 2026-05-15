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
# Erdős Problem 98

*Reference:* [erdosproblems.com/98](https://www.erdosproblems.com/98)
-/

open Finset EuclideanGeometry Filter

namespace Erdos98

/-- $h(n)$ is the minimum number of distinct distances determined by any
$n$-point set in $\mathbb{R}^2$ in general position (no three collinear, no four
cocyclic). -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ points : Finset ℝ², points.card = n ∧
    InGeneralPosition points ∧ k = distinctDistances points}

/--
Let $h(n)$ be such that any $n$ points in $\mathbb{R}^2$, with no three on a line
and no four on a circle, determine at least $h(n)$ distinct distances. Does
$h(n)/n\to \infty$?
-/
@[category research open, AMS 52]
theorem erdos_98 :
    answer(sorry) ↔ Tendsto (fun n : ℕ ↦ ((h n : ℝ) / (n : ℝ))) atTop atTop := by
  sorry

end Erdos98
