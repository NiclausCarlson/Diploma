import Mathlib.RingTheory.Ideal.Basic

import Diploma.Polynomials.Polynomial
import Diploma.Algebra.PolynomialRing

namespace IdealHelpers

open algebra Ideal polynomial

def asSet [MonomialOrder $ Variables n ord] 
          (ps: List $ Polynomial n ord): Set $ Polynomial n ord := {x | x ∈ ps }

theorem listInSet [MonomialOrder $ Variables n ord] 
                  (l: List $ Polynomial n ord): ∀x ∈ l, x ∈ asSet l := by
  intros y h
  simp [asSet]
  exact h
    
def asIdeal [MonomialOrder $ Variables n ord] 
            (l: List $ Polynomial n ord):
            Ideal $ Polynomial n ord := Ideal.span $ asSet l

theorem listInIdeal [MonomialOrder $ Variables n ord] 
                    (l: List $ Polynomial n ord): ∀x ∈ l, x ∈ asIdeal l := by
  intros y h
  rw [asIdeal, asSet]
  have in_set := listInSet l y h
  rw [asSet] at in_set
  apply Ideal.subset_span
  exact in_set  

end IdealHelpers
