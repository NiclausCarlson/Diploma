import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.List.Defs
import Diploma.tests.Common

import Diploma.Algebra.PolynomialRing
import Diploma.Polynomials.Groebner
import Diploma.Algebra.IdealHelpers

open polynomial algebra

namespace profs
open Ideal IdealHelpers

theorem s_poly_in_ideal [MonomialOrder $ Variables n ord] (ideal: Ideal $ Polynomial n ord)
                         : ∀p ∈ ideal, ∀ q ∈ ideal, build_s_polynomial p q ∈ ideal := by
  intros p h_in_p q h_in_q
  rw [build_s_polynomial]
  have left_mem
    : build_s_polynomial.div_lcm_lt (build_s_polynomial.lcm p q) (Polynomial.lt p) * p ∈ ideal
  exact mul_mem_left ideal 
                     (build_s_polynomial.div_lcm_lt (build_s_polynomial.lcm p q) (Polynomial.lt p)) 
                     h_in_p
  have right_mem
    : build_s_polynomial.div_lcm_lt (build_s_polynomial.lcm p q) (Polynomial.lt q) * q ∈ ideal 
  exact mul_mem_left ideal 
                     (build_s_polynomial.div_lcm_lt (build_s_polynomial.lcm p q) (Polynomial.lt q)) 
                     h_in_q
  exact sub_mem left_mem right_mem  

structure GroebnerBasis [MonomialOrder $ Variables n ord] 
                        (ideal: Ideal $ Polynomial n ord) where
 generators: List $ Polynomial n ord
 groebner_def: ∀p ∈ ideal, ∃f ∈ generators, Monomial.is_div p.lt f.lt == true 

structure PolynomialPairs [MonomialOrder $ Variables n ord] 
                          (generators: List $ Polynomial n ord) where
  pairs: List $ Polynomial n ord × Polynomial n ord 
  all_in_generators: ∀p ∈ pairs, p.fst ∈ generators ∧ p.snd ∈ generators    

def build_pairs (l: List α): List $ α × α :=
  match l with
    | [] => []
    | a::as => (pairs a as) ++ build_pairs as
 where 
  pairs (a: α) (l: List α): List $ α × α := l.map (fun x => (a, x))

def build_polynomial_pairs [MonomialOrder $ Variables n ord] 
                           (l: List $ Polynomial n ord): PolynomialPairs l := ⟨build_pairs l, sorry⟩  

structure NonZeroRemainders [MonomialOrder $ Variables n ord] 
                            (ideal: Ideal $ Polynomial n ord) where
  remainders: List $ Polynomial n ord
  not_contains_zero: ∀r ∈ remainders, r != 0
  remainders_in_ideal: ∀r ∈ remainders, r ∈ ideal

def build_non_zero_remainders [MonomialOrder $ Variables n ord]
          (ideal: Ideal $ Polynomial n ord)  
          (generators: List $ Polynomial n ord)
          (ideals_are_equals: asIdeal generators = ideal)
          (ps: PolynomialPairs generators) 
          (generators_non_empty: Not (generators == []))
          (not_div_by_zero: Not $ generators.any (fun p => p == 0)): NonZeroRemainders ideal :=
  match ps with
    | ⟨[], _⟩              => ⟨[], by simp, by simp⟩ 
    | ⟨head::tail, in_gen⟩ => 
                    let tail_res := build_non_zero_remainders ideal generators ideals_are_equals
                                                              ⟨
                                                                tail,
                                                                by simp at in_gen; simp; exact in_gen.right
                                                              ⟩ generators_non_empty not_div_by_zero
                    let s_poly   := build_s_polynomial head.fst head.snd
                    let div_res  := divide_many s_poly generators generators_non_empty not_div_by_zero
                    if tail_res.remainders.elem div_res.r then tail_res
                    else if h: div_res.r != 0 then
                      ⟨
                       [div_res.r] ++ tail_res.remainders,
                       (
                        by 
                         cases tail_res
                         simp at h
                         simp
                         constructor
                         exact h
                         rename_i hh _
                         exact hh
                       ),
                       (
                        by
                          cases div_res
                          intros r h₁
                          simp at *
                          apply Or.elim h₁
                          intros eq
                          rw [eq]
--                          have s_poly_in_ideal: s_poly ∈ ideal
                          sorry
                          intros h_in
                          exact tail_res.remainders_in_ideal r h_in
                       ) 
                      ⟩ 
                    else
                      tail_res

structure BbCriterionStruct [MonomialOrder $ Variables n ord] 
                            (ideal: Ideal $ Polynomial n ord) where
  generators: List $ Polynomial n ord
  ideals_are_equals: asIdeal generators = ideal
  remainders: NonZeroRemainders ideal
  empty: remainders.remainders == []

axiom bb_criterion {n: Nat} {ord: Type}
                   [MonomialOrder $ Variables n ord]
                   (ideal: Ideal $ Polynomial n ord)
                   (bb_struct: BbCriterionStruct ideal)
                    : ∀p ∈ ideal, ∃f ∈ bb_struct.generators, Monomial.is_div p.lt f.lt == true

def build_groebner_basis [MonomialOrder $ Variables n ord] 
                         (polynomials: List $ Polynomial n ord)
                         : GroebnerBasis $ asIdeal polynomials := 
if h₁: polynomials == [] then GroebnerBasis.mk [] sorry
else if h₂: polynomials.any (fun p => p == 0) then GroebnerBasis.mk [] sorry
else 
  let res := impl (asIdeal polynomials) polynomials (by simp) h₁ h₂
  ⟨ 
    res.generators,
    --by
    --  cases res
    --  rename_i generators ideals_are_equals pairs h_pairs generators_non_empty not_div_by_zero remainders h empty
    --  have t := bb_criterion generators pairs h_pairs generators_non_empty not_div_by_zero (asIdeal generators) (by simp)
    --  simp at t
    --  rw [h] at empty
    --  have tt := t empty
    --  simp
      sorry
  ⟩ 
where 
    impl (ideal: Ideal $ Polynomial n ord) 
         (ps: List $ Polynomial n ord) 
         (ideals_are_equals: asIdeal ps = ideal)
         (h₁: Not (ps == []))
         (h₂: Not $ ps.any (fun p => p == 0))
          : BbCriterionStruct $ ideal := 
      let pairs := build_polynomial_pairs ps
      let res := build_non_zero_remainders ideal ps ideals_are_equals pairs h₁ h₂ 
      if h: res.remainders == [] then ⟨ps, ideals_are_equals, res, h⟩  
      else impl ideal (ps ++ res.remainders)
                (
                  by 
                    cases res
                    rename_i remainders _ remainders_in_ideal
                    rw [← ideals_are_equals] at remainders_in_ideal
                    simp [← ideals_are_equals]
                    exact generators_extension ps remainders remainders_in_ideal
                )
                (sorry)
                (sorry)
    termination_by impl ps ideals_are_equals h₁ h₂ => ps == []
    decreasing_by {
      simp_wf
      sorry
    }

private def parse_list (ps: List String): List (Polynomial Dimension order.Lex) := ps.map parse_lex!

private def check_groebner (input expected: List String): Except String String := 
  let parsed          := parse_list input
  let parsed_expected := parse_list expected
  let groebner := build_groebner_basis parsed
  AssertTrue (groebner.generators == parsed_expected) s!"expected {parsed_expected}; actual {groebner.generators}"

#eval check_groebner ["x0x1-x1", "x0"] ["x0x1-x1", "x0", "-x1"]
#eval check_groebner ["x0+x1-1", "x1-x2", "x2-x0x1"] ["x0+x1-1", "x1-x2", "-x0x1+x2", "x2^2"]
#eval check_groebner ["x0^2+x0x1x2^4+x1", "x0+x1+x2"] ["x0^2+x0x1x2^4+x1", "x0+x1+x2", "-x1^2x2^4+x1^2-x1x2^5+2x1x2+x1+x2^2"]

end profs  
