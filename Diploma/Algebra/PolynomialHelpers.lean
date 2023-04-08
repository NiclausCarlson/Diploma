import Diploma.Polynomials.DegsFunctions
import Diploma.tests.Common

namespace polynomial

theorem mul_minus_one_change_sign: 
  ∀ p: Polynomial n _cmp, (p.contains m == true) → ((p.invert_sign.contains) ⟨-1 * m.fst, m.snd⟩ == true) := by 
  sorry

theorem not_contains_without_it: 
  ∀ p: Polynomial n _cmp, (p.contains m == true) → (p - (Polynomial.of_monomial m _cmp)).contains m == false := by
    simp
    intros p h
    simp [HSub.hSub, HMul.hMul, ofRat, Polynomial.mul]
    sorry
     
end polynomial
