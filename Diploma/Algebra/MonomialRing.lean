import Diploma.Polynomials.Polynomial
import Mathlib.Algebra.Ring.Defs 
import Std.Data.RBMap


namespace algebra
open polynomial

-- TODO: nonempty polynomials
instance: CommRing (Polynomial n cmp) where
   zero := 0
   one  := 1
   add p₁ p₂ := Polynomial.add p₁ p₂
   zero_add := sorry
   add_zero := sorry
   add_comm := sorry
   add_assoc := sorry
   mul := sorry
   one_mul := sorry
   mul_one := sorry
   zero_mul := sorry
   mul_zero := sorry
   neg := sorry
   left_distrib := sorry
   right_distrib := sorry
   mul_assoc := sorry
   add_left_neg := sorry
   mul_comm := sorry   

end algebra
