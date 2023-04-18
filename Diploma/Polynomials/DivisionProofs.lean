import Diploma.Polynomials.Groebner
import Diploma.Algebra.PolynomialRing

open polynomial

namespace prooved_division
-- Делим p на [f₁...fₛ]. Результат деления - DivisionResult{p - , r - остаток}
-- Нужно доказать:
-- DivisionResult.p + DivisionResult.r = p
-- (DivisionResult.p / [f₁...fₛ]).r = 0
-- (DivisionResult.r = 0) ∨ (∀m ∈ DivisionResult.r - моном, который не делится на LT(fᵢ) ∀i)

structure DivisionResult (n: Nat) (_cmp: Monomial n → Monomial n → Ordering) where
  p: Polynomial n _cmp
  r: Polynomial n _cmp


def divide_many (divisible: Polynomial n _cmp) (dividers: List (Polynomial n _cmp)): DivisionResult n _cmp := 
  if dividers == [] then DivisionResult.mk divisible 0 
  else impl divisible dividers (DivisionResult.mk divisible 0) (by simp) 
  where
    impl (p: Polynomial n _cmp) (ps: List (Polynomial n _cmp)) (step: DivisionResult n _cmp)
          (sum_eq: p + step.r = divisible): DivisionResult n _cmp :=
        if p == 0 then step
        else match ps with
              | []    => let new_p := p - p.Lt
                         impl new_p dividers {
                                              p := step.p,
                                              r := step.r + p.Lt
                                             } 
                                             (by simp; exact sum_eq)
              | a::as => let reduced_lt := reduce_lt p a
                         match reduced_lt with
                           | none     => impl p as step sum_eq
                           | some res => impl res.reduced dividers { 
                                                                     p := step.p + res.reducer,
                                                                     r := step.r
                                                                   } 
                                                                   (by 
                                                                      simp
                                                                      sorry
                                                                    )
    termination_by impl p ps psp h => p == 0
    decreasing_by {
      simp_wf
      sorry
    }

end prooved_division
