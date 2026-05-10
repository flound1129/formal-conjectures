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

This is the direct asymptotic formulation of the problem statement:
does the minimum number of distinct distances determined by an
`n`-point set in the plane, subject to the usual general-position
conditions, grow superlinearly?

The theorem below packages the question in the same style used by the
`formal-conjectures` repository for other open Erdős problems.
-/

open Classical
open scoped EuclideanGeometry

namespace Erdos98

/-- The ambient plane for Problem 98. -/
abbrev Point := ℝ²

/-- The set of distinct pairwise distances determined by a finite point set. -/
noncomputable def DistinctDistances {n : ℕ} (p : Fin n → Point) : Finset ℝ :=
  Finset.image (fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
    ((Finset.univ.product Finset.univ).filter (fun ij : Fin n × Fin n => ij.1 < ij.2))

/-- A triple of points is noncollinear if they do not lie on a common line. -/
def NoThreeCollinear {n : ℕ} (p : Fin n → Point) : Prop :=
  ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
    ¬ Collinear ℝ ({p i, p j, p k} : Set Point)

/-- Four points are cocyclic if they lie on a common circle. -/
def FourCocyclic (a b c d : Point) : Prop :=
  ∃ o : Point, ∃ r : ℝ,
    dist a o = r ∧ dist b o = r ∧ dist c o = r ∧ dist d o = r

/-- No four points are cocyclic if no four distinct points lie on a common circle. -/
def NoFourCocyclic {n : ℕ} (p : Fin n → Point) : Prop :=
  ∀ i j k l : Fin n, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    ¬ FourCocyclic (p i) (p j) (p k) (p l)

/-- General position for an `n`-point set in the plane. -/
def GeneralPosition {n : ℕ} (p : Fin n → Point) : Prop :=
  Function.Injective p ∧ NoThreeCollinear p ∧ NoFourCocyclic p

/--
Erdős Problem 98: do the minimum numbers of distinct distances determined by
general-position `n`-point sets grow superlinearly?

This is the direct `formal-conjectures`-style reformulation of the English
question "does `h(n) / n → ∞`?".
-/
@[category research open, AMS 52]
theorem erdos_98 :
    answer(sorry) ↔
      ∀ C : ℝ, 0 < C →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ p : Fin n → Point,
            GeneralPosition p →
            (C : ℝ) * (n : ℝ) ≤ (DistinctDistances p).card := by
  sorry

end Erdos98
