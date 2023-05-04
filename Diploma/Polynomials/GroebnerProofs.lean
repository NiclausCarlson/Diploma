import Mathlib.RingTheory.Ideal.Basic

import Diploma.Algebra.PolynomialRing
import Diploma.Polynomials.Groebner

open polynomial algebra

namespace profs
open Ideal

structure GroebnerBasis (n: Nat) (ord: Type) [MonomialOrder $ Variables n ord] where
  basis : List $ Polynomial n ord
  buchberger_criterion : ∀ p ∈ basis, ∀ q ∈ basis, p ≠ q → (divide_many (build_s_polynomial p q) basis).r = 0

private def step [MonomialOrder $ Variables n ord] (p q: Polynomial n ord) (ps: List (Polynomial n ord)) : Bool × Polynomial n ord := 
  if p == q then (false, 0)
  else
    let div_result := divide_many (build_s_polynomial p q) ps
    (div_result.r == 0, div_result.r)

private def build [MonomialOrder $ Variables n ord]
                  (e: Polynomial n ord) 
                  (ps: List (Polynomial n ord)) 
                  (dividers: List (Polynomial n ord)) : List (Polynomial n ord) := 
  match ps with
    | []    => []
    | a::as => let s := step e a dividers 
               if s.fst then build e as dividers 
               else [s.snd] ++ (build e (as ++ [s.snd]) (dividers ++ [s.snd]))
termination_by build pl result => pl == []
decreasing_by {
  simp_wf
  sorry
}

def build_groebner_basis [MonomialOrder $ Variables n ord] (pl: List (Polynomial n ord)): List (Polynomial n ord) := impl pl pl
  where 
    impl (pl: List (Polynomial n ord)) (dividers: List (Polynomial n ord)): List (Polynomial n ord) := 
      match pl with
        | []    => dividers 
        | p::ps => let res := build p ps dividers
                   impl (ps ++ res) (dividers ++ res)
    termination_by impl pl result => pl == []
    decreasing_by {
      simp_wf
      sorry
    }

end profs
