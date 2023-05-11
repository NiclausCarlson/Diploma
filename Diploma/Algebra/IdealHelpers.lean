import Mathlib.RingTheory.Ideal.Basic

import Diploma.Polynomials.Polynomial
import Diploma.Algebra.PolynomialRing

namespace IdealHelpers

open algebra Ideal polynomial

def asSet (l: List α): Set α := {x | x ∈ l }

theorem listInSet (l: List α): ∀x ∈ l, x ∈ asSet l := by
  intros y h
  simp [asSet]
  exact h

theorem list_union_as_set (l₁ l₂: List α): asSet (l₁ ++ l₂) = asSet l₁ ∪ asSet l₂ :=
  by
    induction l₂
    simp [asSet]
    simp [asSet]
    constructor

def asIdeal [Semiring α] (l: List α): Ideal α := Ideal.span $ asSet l

theorem listInIdeal [Semiring α] (l: List α): ∀x ∈ l, x ∈ asIdeal l := by
  intros y h
  rw [asIdeal, asSet]
  have in_set := listInSet l y h
  rw [asSet] at in_set
  apply Ideal.subset_span
  exact in_set  

theorem subsets_h (l: List α) (s: Set α) (h: ∀e ∈ l, e ∈ s): asSet l ⊆ s := 
  by
    rw [asSet]
    exact h

theorem generators_extension [MonomialOrder $ Variables n ord] 
                             (generators: List $ Polynomial n ord)
                             (extension: List $ Polynomial n ord)
                             (in_ideal: ∀e ∈ extension, e ∈ asIdeal generators)
                              : asIdeal (generators ++ extension) = asIdeal generators :=
  by
    rw [asIdeal, asIdeal, list_union_as_set, span_union]
    have subset := subsets_h extension (asIdeal generators) in_ideal
    simp [span_mono]
    simp [←span_le] at *
    rw [asIdeal] at subset
    exact subset

end IdealHelpers
