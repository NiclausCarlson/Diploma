import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.List.Basic

import Diploma.Polynomials.Polynomial
import Diploma.Algebra.IdealHelpers
import Diploma.Polynomials.DegsFunctions
import Diploma.Algebra.PolynomialRing
import Diploma.Polynomials.Division

namespace polynomial
open algebra Ideal IdealHelpers

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

theorem pair_in_list₁ (l: List α) (pairs: List $ α × α) (h: pairs = build_pairs l)
        : ∀p ∈ pairs, p.fst ∈ l:= by 
  let rec aux (l: List α) (pairs: List $ α × α) (h: pairs = build_pairs l)
        : ∀p ∈ pairs, p.fst ∈ l:= by
    intros p in_pairs
    rw [h] at in_pairs
    match l with
      | [] => simp [build_pairs] at in_pairs
      | x::xs => simp [build_pairs, build_pairs.pairs] at in_pairs
                 cases in_pairs
                 rename_i hh
                 let ⟨y, t⟩ := hh
                 simp
                 have right := Eq.symm t.right
                 constructor
                 simp [right]
                 simp [build_pairs, build_pairs.pairs] at h
                 simp
                 have res := aux xs (build_pairs xs) (by simp) p
                 rename_i rr
                 simp [res rr]
  exact aux l pairs h

theorem pair_in_list₂ (a: α) (l: List α) (pairs: List $ α × α) (h: pairs = build_pairs.pairs a l)
                       : ∀p ∈ pairs, p.snd ∈ l := by
  intros p in_pairs
  rw [h, build_pairs.pairs] at in_pairs
  simp at *
  let ⟨y, t⟩ := in_pairs
  have left := t.left
  have right := Eq.symm t.right
  simp [right, left]

theorem pair_in_list₃ (l: List α) (pairs: List $ α × α) (h: pairs = build_pairs l)
        : ∀p ∈ pairs, p.snd ∈ l:= by 
  intros p in_pairs
  rw [h] at in_pairs
  
  sorry
theorem pair_in_list (l: List α) (pairs: List $ α × α) (h: pairs = build_pairs l)
        : ∀p ∈ pairs, p.fst ∈ l ∧ p.snd ∈ l:= by
  intros p in_pairs
  constructor
  exact pair_in_list₁ l pairs h p in_pairs
  
  sorry
  
def build_polynomial_pairs [MonomialOrder $ Variables n ord] 
                           (l: List $ Polynomial n ord): PolynomialPairs l := 
  let pairs := build_pairs l
  ⟨pairs, pair_in_list l pairs (by simp)⟩  

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
                          have s_poly_in_ideal: s_poly ∈ ideal
                          have head_in_generators := in_gen head
                          simp at head_in_generators
                          have left_in_ideal := elemInListElemInIdeal generators head.fst head_in_generators.left
                          have right_in_ideal := elemInListElemInIdeal generators head.snd head_in_generators.right
                          have s_poly_in_ideal := s_poly_in_ideal (asIdeal generators) head.fst left_in_ideal head.snd right_in_ideal
                          rw [ideals_are_equals] at s_poly_in_ideal
                          simp 
                          exact s_poly_in_ideal
                          rename_i r_in_ideal
                          rw [ideals_are_equals] at r_in_ideal
                          apply r_in_ideal s_poly_in_ideal
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
  let ideal := (asIdeal polynomials)
  let res := impl ideal polynomials (by simp) h₁ h₂
  ⟨res.generators, bb_criterion ideal res⟩ 
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

theorem sufficiency_poly_in_ideal [MonomialOrder $ Variables n ord] 
                                  (p: Polynomial n ord)
                                  (dividers: List $ Polynomial n ord)
                                  (dividers_non_empty: Not $ dividers == [])
                                  (not_div_by_zero: Not $ dividers.any (fun p => p == 0))
                                  (div_res : DivisionResult p dividers)
                                  (h: div_res = divide_many p dividers dividers_non_empty not_div_by_zero)
                                    : div_res.r = 0 → p ∈ asIdeal dividers :=
by
  intros is_zero
  cases div_res
  rename_i q r sum_eq _ p_in_ideal r_in_ideal
  simp at *
  simp [is_zero] at sum_eq
  rw [sum_eq]
  exact p_in_ideal

def is_in_basis [MonomialOrder $ Variables n ord]
                (p: Polynomial n ord)
                (groebner_basis: List (Polynomial n ord))
                (dividers_non_empty: Not $ groebner_basis == [])
                (not_div_by_zero: Not $ groebner_basis.any (fun p => p == 0)) : Bool :=
  (divide_many p groebner_basis dividers_non_empty not_div_by_zero).r == 0

end polynomial
