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
# Erdős Problem 809

*References:*
- [erdosproblems.com/809](https://www.erdosproblems.com/809)
- [BEGS89] Burr, S. A. and Erdős, P. and Graham, R. L. and Sós, V. T., Maximal anti-Ramsey graphs
  and the strong chromatic number. J. Graph Theory (1989), 263--282.
- [BCM26] Bucić, M. and Chen, K. and Ma, J., On a maximal anti-Ramsey conjecture of Burr, Erdős,
  Graham, and Sós. arXiv:2603.18952 (2026).
-/

open SimpleGraph Asymptotics Filter

namespace Erdos809

/--
The anti-Ramsey number $\chi_S(n, e, G)$ (called the *strong chromatic number* in [BEGS89]):
the smallest $r$ such that there is a graph with $n$ vertices and $e$ edges together with an
$r$-colouring of its edges in which every copy of $G$ has entirely distinct edge colours.

Copies of $G$ are taken to be embeddings `G ↪g H`; a colouring making every embedded copy
rainbow is exactly a colouring in which no two edges lying on a common copy of $G$ share a
colour. If no graph with `n` vertices and `e` edges exists, the value is `sInf ∅ = 0` by
convention.
-/
noncomputable def minRainbowNumber {α : Type*} (G : SimpleGraph α) (n e : ℕ) : ℕ :=
  sInf {r | ∃ H : SimpleGraph (Fin n), H.edgeSet.ncard = e ∧
    ∃ c : Sym2 (Fin n) → Fin r, ∀ f : G ↪g H, IsRainbow f.toHom c}

/--
Is it true that, for all $k \geq 3$,
$$\chi_S(n, \lfloor n^2/4\rfloor + 1, C_{2k+1}) \sim n^2/8?$$

A problem of Burr, Erdős, Graham, and Sós [BEGS89]. Solved in the affirmative for all
$k \geq 4$ by Bucić, Chen, and Ma [BCM26]; the case $k = 3$ remains open.
-/
@[category research open, AMS 5]
theorem erdos_809 : answer(sorry) ↔ ∀ k : ℕ, 3 ≤ k →
    (fun n : ℕ ↦ (minRainbowNumber (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ))
      ~[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2 / 8) := by
  sorry

/--
Burr, Erdős, Graham, and Sós [BEGS89] proved that, for every $k \geq 3$,
$$\chi_S(n, \lfloor n^2/4\rfloor + 1, C_{2k+1}) \gg_k n^2.$$
-/
@[category research solved, AMS 5]
theorem erdos_809.variants.lower_bound (k : ℕ) (hk : 3 ≤ k) :
    (fun n : ℕ ↦ (minRainbowNumber (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ))
      ≫ (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  sorry

/--
Bucić, Chen, and Ma [BCM26] proved that, for every $k \geq 4$,
$$\chi_S(n, \lfloor n^2/4\rfloor + 1, C_{2k+1}) \sim n^2/8.$$
-/
@[category research solved, AMS 5]
theorem erdos_809.variants.k_ge_four (k : ℕ) (hk : 4 ≤ k) :
    (fun n : ℕ ↦ (minRainbowNumber (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ))
      ~[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2 / 8) := by
  sorry

/--
The only remaining open case of [erdos_809]: is it true that
$$\chi_S(n, \lfloor n^2/4\rfloor + 1, C_7) \sim n^2/8?$$
-/
@[category research open, AMS 5]
theorem erdos_809.variants.seven_cycle : answer(sorry) ↔
    (fun n : ℕ ↦ (minRainbowNumber (cycleGraph 7) n (n ^ 2 / 4 + 1) : ℝ))
      ~[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2 / 8) := by
  sorry

/--
The situation for shorter odd cycles is quite different: it is easy to see that
$$\chi_S(n, \lfloor n^2/4\rfloor + 1, C_3) = 3$$
for all $n \geq 3$.
-/
@[category research solved, AMS 5]
theorem erdos_809.variants.triangle (n : ℕ) (hn : 3 ≤ n) :
    minRainbowNumber (cycleGraph 3) n (n ^ 2 / 4 + 1) = 3 := by
  sorry

/--
Erdős and Simonovits proved (as reported in [BEGS89]) that
$$\chi_S(n, \lfloor n^2/4\rfloor + 1, C_5) = \lfloor n/2\rfloor + 3$$
for all large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_809.variants.five_cycle : ∀ᶠ n : ℕ in atTop,
    minRainbowNumber (cycleGraph 5) n (n ^ 2 / 4 + 1) = n / 2 + 3 := by
  sorry

end Erdos809
