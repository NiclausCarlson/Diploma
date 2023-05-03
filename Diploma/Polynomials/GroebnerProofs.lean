import Mathlib.RingTheory.Ideal.Basic

import Diploma.Algebra.PolynomialRing
import Diploma.Polynomials.Groebner

open polynomial algebra

namespace profs
open Ideal

structure SIdeal [MonomialOrder $ Variables n ord] where
  generators: List $ Polynomial n ord
  ideal     : Ideal $ Polynomial n ord
  eq        : ideal = asIdeal generators 

theorem div_from_ideal_to_ideal [MonomialOrder $ Variables n ord]
                                (p: Polynomial n ord)
                                (ideal : SIdeal)
                                (in_ideal: p ∈ ideal.ideal)
                                (div_result: DivisionResult p)
                                (h_div_result: div_result = divide_many p ideal.generators)
                                  : div_result.r ∈ ideal.ideal := 
  by
    cases ideal
    rename_i generators ideal eq
    simp at *
    rw [divide_many] at h_div_result
    split at h_div_result
    rw [h_div_result]
    simp
    split at h_div_result
    rw [h_div_result]
    simp
    rw [h_div_result]
    sorry
                                

theorem s_poly_in_ideal [MonomialOrder $ Variables n ord] 
                        (i: Ideal $ Polynomial n ord)
                        (p q: Polynomial n ord)
                        (h₁: p ∈ i)
                        (h₂: q ∈ i) : build_s_polynomial p q ∈ i :=
by
  rw [build_s_polynomial]
  have left_in_ideal := mul_mem_left i (build_s_polynomial.div_lcm_lt 
                                          (Monomial.lcm (Polynomial.lm p) (Polynomial.lm q))
                                          (Polynomial.lt p)) h₁
  have right_in_ideal := mul_mem_left i (build_s_polynomial.div_lcm_lt 
                                           (Monomial.lcm (Polynomial.lm p) (Polynomial.lm q))
                                           (Polynomial.lt q)) h₂
  rw [build_s_polynomial.lcm]
  exact sub_mem left_in_ideal right_in_ideal

theorem s_remainder_in_ideal [MonomialOrder $ Variables n ord] 
                           (ideal: SIdeal)
                           (p q: Polynomial n ord)
                           (s_poly: Polynomial n ord)
                           (hs_poly: s_poly = build_s_polynomial p q)
                           (in_ideal: p ∈ ideal.ideal ∧ q ∈ ideal.ideal) 
                           (div_res: DivisionResult s_poly)
                           (hh: div_res = divide_many s_poly ideal.generators): div_res.r ∈ ideal.ideal  := 
by
  cases in_ideal
  cases ideal
  rename_i generators ideal eq p_in_ideal q_in_ideal
  simp at *
  have s_poly_ideal := s_poly_in_ideal ideal p q p_in_ideal q_in_ideal
  rw [← hs_poly] at s_poly_ideal
  cases div_res
  rename_i quotient remainder q_sum_r
  simp at *
  sorry


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
