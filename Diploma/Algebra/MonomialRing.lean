import Diploma.Polynomials.Polynomial
import Mathlib.Algebra.Ring.Defs 
import Std.Data.RBMap


namespace algebra
open polynomial
open Std.RBNode
open Std.RBSet

theorem t_zero_add: ∀ (a : Polynomial n cmp), Polynomial.add 0 a = a := by
   intros a
   let rec aux (p: Polynomial n cmp): Polynomial.add 0 p = p := by
      match p with
         | ⟨f, l⟩ => match f with 
                      | nil => sorry -- newer true
                      | node c nil r nil => simp [Polynomial.add, mergeWith, Std.RBSet.foldl]
                                            split
                                            simp [Std.RBSet.insert]
                                            sorry
                                            sorry          
                      | node c u r v => sorry  
 
   apply aux a

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
