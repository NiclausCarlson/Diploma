import Diploma.Polynomials.Groebner
import Diploma.Algebra.PolynomialRing

open polynomial

namespace prooved_division


def build_division_remainder (divisible: Polynomial n _cmp) (dividers: List (Polynomial n _cmp)): Polynomial n _cmp := 
  if dividers == [] then divisible
  else if dividers.any (fun p => p == 0) then divisible
  else impl divisible dividers 0 0 (by simp) 
  where 
    impl (p: Polynomial n _cmp)
         (ps: List (Polynomial n _cmp)) 
         (quotient: Polynomial n _cmp)
         (remainder: Polynomial n _cmp)
         (sum_eq : divisible = p + quotient + remainder) : Polynomial n _cmp :=
      if p == 0 then remainder
      else match ps with
               | []    => impl (p - p.Lt) dividers quotient 
                               (remainder + p.Lt) 
                               (
                                by 
                                  have h: remainder + Polynomial.Lt p = Polynomial.Lt p + remainder := 
                                    add_comm remainder (Polynomial.Lt p)
                                  have h₂: -Polynomial.Lt p + quotient = quotient + -Polynomial.Lt p :=
                                    add_comm (-Polynomial.Lt p) quotient
                                  rw [h, sub_eq_add_neg, add_assoc,
                                      add_assoc, add_comm, ←add_assoc,
                                      ←add_assoc, add_comm, h₂, add_comm, add_assoc, add_comm, 
                                      add_assoc, add_assoc, add_left_neg, add_zero, add_comm
                                      ]
                                  exact sum_eq
                               )
               | a::as => if p.lt.is_div a.lt then 
                             let reducer := (p.lt.div a.lt) * a
                             impl (p - reducer) dividers (quotient + reducer) 
                                  (remainder) 
                                  ( 
                                    by 
                                      have h: -reducer + (quotient + reducer) = (quotient + reducer) + -reducer := 
                                        add_comm (-reducer) (quotient + reducer) 
                                      rw [sub_eq_add_neg, ←add_assoc, add_comm, add_assoc,
                                          add_assoc, h, add_assoc, add_right_neg, add_zero, add_comm]
                                      exact sum_eq
                                  )
                          else impl p as quotient remainder sum_eq                                       
     termination_by impl p ps quotient remainder sum_eq => p == 0
     decreasing_by {
       sorry
     }
 
def divide_many (divisible: Polynomial n _cmp) (dividers: List (Polynomial n _cmp)): DivisionResult n _cmp := 
   let remainder := build_division_remainder divisible dividers
   DivisionResult.mk (divisible - remainder) remainder
   
end prooved_division