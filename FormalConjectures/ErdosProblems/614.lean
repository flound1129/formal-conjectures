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
# Erdős Problem 614

*References:*
* [erdosproblems.com/614](https://www.erdosproblems.com/614)
* [Ma and Tang, Erdős 614 Turán-type reduction note](https://github.com/QuanyuTang/erdos-614-turan-reduction/blob/main/erdos614_note.pdf)
-/

open Classical
open SimpleGraph Finset

namespace Erdos614

/-- A finite forbidden family of graphs, each graph carrying its own finite vertex set. -/
abbrev ForbiddenGraph := Sigma fun n : ℕ => SimpleGraph (Fin n)

/-- A finite forbidden family of graphs. -/
abbrev ForbiddenFamily := Finset ForbiddenGraph

/-- A graph `G` avoids a family `F` if none of the family members appears as a copy in `G`. -/
def FamilyFree {n : ℕ} (G : SimpleGraph (Fin n)) (F : ForbiddenFamily) : Prop :=
  ∀ H ∈ F, ¬ H.2 ⊑ G

/-- The Turán extremal number for a finite family of forbidden graphs. -/
noncomputable def ex (n : ℕ) (F : ForbiddenFamily) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), FamilyFree G F ∧ G.edgeSet.ncard = m}

/-- The original Erdős quantity from the problem statement.

This is the least number of edges in a graph on `k` vertices such that every subset of `n + 2`
vertices induces a subgraph of maximum degree at least `n`.
-/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin k), G.edgeSet.ncard = m → ∀ S : Finset (Fin k),
    S.card = n + 2 → (G.induce (S : Set (Fin k))).maxDegree ≥ n}

/--
The Turán-type reformulation of Erdős problem 614.

For each fixed `k`, there exists a finite family of graphs `F_k^min`, depending only on `k`, such
that

`f(n,k) = (n choose 2) - ex(n, F_k^min)`.
-/
@[category research solved, AMS 5, formal_proof using other_system at
  "https://github.com/QuanyuTang/erdos-614-turan-reduction"]
theorem erdos_614 :
    ∀ k : ℕ, ∃ Fkmin : ForbiddenFamily,
      ∀ n : ℕ, f n k = Nat.choose n 2 - ex n Fkmin := by
  sorry

/--
Ma and Tang's Turán-type reformulation of Erdős problem 614.

For each fixed `k`, there exists a finite family of graphs `F_k^min`, depending only on `k`, such
that

`f(n,k) = (n choose 2) - ex(n, F_k^min)`.
-/
@[category research solved, AMS 5, formal_proof using other_system at
  "https://github.com/QuanyuTang/erdos-614-turan-reduction"]
theorem erdos_614.variants.ma_tang_reformulation :
    ∀ k : ℕ, ∃ Fkmin : ForbiddenFamily,
      ∀ n : ℕ, f n k = Nat.choose n 2 - ex n Fkmin := by
  sorry

end Erdos614
