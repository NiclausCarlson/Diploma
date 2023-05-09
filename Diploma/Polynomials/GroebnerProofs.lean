import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.List.Defs
import Diploma.tests.Common

import Diploma.Algebra.PolynomialRing
import Diploma.Polynomials.Groebner
import Diploma.Algebra.IdealHelpers

open polynomial algebra

namespace profs
open Ideal IdealHelpers

def build_pairs (l: List α): List (α × α) :=
  match l with
    | [] => []
    | a::as => (pairs a as) ++ build_pairs as
 where 
  pairs (a: α) (l: List α): List (α × α) := l.map (fun x => (a, x))

structure GroebnerBasis [MonomialOrder $ Variables n ord] 
                        (ideal: Ideal $ Polynomial n ord) where
 generators: List $ Polynomial n ord
 groebner_def: ∀p ∈ ideal, ∃f ∈ generators, Monomial.is_div p.lt f.lt == true 

structure NonZeroRemainders (n: Nat) (ord: Type) [MonomialOrder $ Variables n ord] where
  remainders: List $ Polynomial n ord
  not_contains_zero: ∀p ∈ remainders, p != 0

def build_non_zero_remainders [MonomialOrder $ Variables n ord]
          (ps: List $ (Polynomial n ord) × (Polynomial n ord)) 
          (dividers: List $ Polynomial n ord)
          (dividers_non_empty: Not (dividers == []))
          (not_div_by_zero: Not $ dividers.any (fun p => p == 0)): NonZeroRemainders n ord :=
  match ps with
    | []         => ⟨[], by simp⟩ 
    | head::tail => let tail_res := build_non_zero_remainders tail dividers dividers_non_empty not_div_by_zero
                    let s_poly   := build_s_polynomial head.fst head.snd
                    let div_res  := divide_many s_poly dividers dividers_non_empty not_div_by_zero
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
                         rename_i hh
                         exact hh
                       )
                      ⟩ 
                    else
                      tail_res

theorem bb_criterion [MonomialOrder $ Variables n ord]
                     (generators: List $ Polynomial n ord)
                     (pairs: List $ (Polynomial n ord) × (Polynomial n ord))
                     (h_pairs: pairs = build_pairs generators)
                     (non_empty: Not (generators == []))
                     (not_div_by_zero: Not $ generators.any (fun p => p == 0))
                     (ideal: Ideal $ Polynomial n ord)
                     (ideal_generated_by: ideal = asIdeal generators)
                     (d: NonZeroRemainders n ord)
                     (h: d=build_non_zero_remainders pairs generators non_empty not_div_by_zero)
                      : d.remainders == [] → 
                        ∀p ∈ ideal, ∃f ∈ generators, Monomial.is_div p.lt f.lt == true := sorry

structure BbCriterionStruct (n: Nat) (ord: Type) 
                            [MonomialOrder $ Variables n ord] where
  generators: List $ Polynomial n ord
  pairs: List $ (Polynomial n ord) × (Polynomial n ord)
  h_pairs: pairs = build_pairs generators

  generators_non_empty: Not (generators == [])
  not_div_by_zero: Not $ generators.any (fun p => p == 0)

  remainders: NonZeroRemainders n ord
  h: remainders = build_non_zero_remainders pairs generators generators_non_empty not_div_by_zero
  empty: remainders.remainders == []

def build_groebner_basis [MonomialOrder $ Variables n ord] 
                         (polynomials: List $ Polynomial n ord)
                         : GroebnerBasis $ asIdeal polynomials := 
if h₁: polynomials == [] then GroebnerBasis.mk [] sorry
else if h₂: polynomials.any (fun p => p == 0) then GroebnerBasis.mk [] sorry
else 
  let res := impl polynomials polynomials h₁ h₂
  ⟨ 
    res.generators,
    by
      cases res
      rename_i generators pairs h_pairs generators_non_empty not_div_by_zero remainders h empty
      have t := bb_criterion generators pairs h_pairs generators_non_empty not_div_by_zero (asIdeal generators) (by simp)
      simp at t
      rw [h] at empty
      have tt := t empty
      simp 
      sorry
  ⟩ 
where 
    impl (polynomials: List $ Polynomial n ord) 
         (result: List $ Polynomial n ord)
         (h₁: Not (polynomials == []))
         (h₂: Not $ polynomials.any (fun p => p == 0))
          : BbCriterionStruct n ord := 
      let pairs := build_pairs polynomials
      let res := build_non_zero_remainders pairs polynomials h₁ h₂ 
      if h: res.remainders == [] then ⟨polynomials, pairs, by simp, h₁, h₂, res, by simp, h⟩  
      else impl (polynomials ++ res.remainders)
                (result ++ res.remainders)
                (sorry)
                (sorry)
    termination_by impl polynomials result h₁ h₂ => polynomials == []
    decreasing_by {
      simp_wf
      sorry
    }

end profs  
