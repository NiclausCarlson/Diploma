import Diploma.Polynomials.Groebner
import Diploma.Algebra.PolynomialRing

open polynomial

namespace prooved_division

structure DivisionResult (n: Nat) (_cmp: Monomial n → Monomial n → Ordering) where
  p: Polynomial n _cmp
  r: Polynomial n _cmp

def build_division_remainder (divisible: Polynomial n _cmp) (dividers: List (Polynomial n _cmp)): Polynomial n _cmp :=
  if dividers == [] then divisible 
  else if dividers.any (fun p => p == 0) then panic!"division by zero" 
  else impl divisible dividers 0 (by simp)
  where
    impl (p: Polynomial n _cmp)
         (ps: List (Polynomial n _cmp))
         (cur_remainder: Polynomial n _cmp)
         (sum_eq: 
          p + cur_remainder = divisible -- ∨
    --      ps == [] → p + cur_remainder = divisible -- ∨
          --dividers == a::as ∧ p.lt.is_div a.lt == true → p + (p.lt.div a.lt) * a + cur_remainder = divisible
          -- ∨ 
          -- ∃a, a ∈ dividers ∧ p + (p.lt.div a.lt) * a + cur_remainder = divisible
          ) : Polynomial n _cmp :=
        if p == 0 then cur_remainder
        else match ps with
              | []    => impl (p - p.Lt) dividers (cur_remainder + p.Lt)
                                             (
                                                by 
                                                  have h: cur_remainder + Polynomial.Lt p = 
                                                          Polynomial.Lt p + cur_remainder := 
                                                            add_comm cur_remainder (Polynomial.Lt p)
                                                  rw [h, sub_eq_add_neg, add_assoc,
                                                      add_comm, ← add_assoc, add_left_neg,
                                                      zero_add, add_comm]
                                                  exact sum_eq 
                                             )
              | a::as => if p.lt.is_div a.lt then 
                            let reducer := (p.lt.div a.lt) * a
                            impl (p - reducer) dividers cur_remainder 
                                                        (
                                                          by

                                                            sorry 
                                                        )
                         else impl p as cur_remainder sum_eq                                     
    termination_by impl p ps psp h => p == 0
    decreasing_by {
      sorry
    }


def divide_many (divisible: Polynomial n _cmp) (dividers: List (Polynomial n _cmp)): DivisionResult n _cmp := 
  let remainder := build_division_remainder divisible dividers
  DivisionResult.mk (divisible - remainder) remainder
  
end prooved_division
