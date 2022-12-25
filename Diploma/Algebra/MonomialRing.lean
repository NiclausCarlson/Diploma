import Diploma.Polynomials.Polynomials
import Diploma.Algebra.MonomialOrder
import Mathlib.Algebra.Ring.Defs 
import Std.Data.RBMap


namespace algebra
  open polynomials

  def m_cmp (m₁ m₂: String) : Ordering := if m₁ = m₂ then Ordering.eq
                                          else compare m₁ m₂
    
  def fill_rb_map (monomials: List Monomial) (rb_map: Std.RBMap String Monomial m_cmp) :
                  (Std.RBMap String Monomial m_cmp) :=
    match monomials with
      | [] => rb_map
      | [a] => insert_monomial a rb_map
      | a :: as => insert_monomial a (fill_rb_map as rb_map) 
    where insert_monomial (m: Monomial) (rb_map: Std.RBMap String Monomial m_cmp) :
                          (Std.RBMap String Monomial m_cmp) := 
          match rb_map.find? (VariablesToStr m.vars) with
            | none   => rb_map.insert (VariablesToStr m.vars) m
            | some v => rb_map.insert (VariablesToStr m.vars) {coeff := Int.add v.coeff m.coeff,
                                                               vars  := v.vars} 

  private def simplify (l: List Monomial) : List Monomial :=
    match simplify_impl l with
      | [] => [{coeff := 0, vars := {}}]
      | as => as
    where 
      simplify_impl (l: List Monomial) : List Monomial :=
        match l with
          | []  => []
          | [a] => check_coeff (simp_vars a)
          | a :: as => (check_coeff a) ++ (simplify_impl as)
      check_coeff (m: Monomial) : List Monomial := if m.coeff == 0 then [] else [m] 
      simp_vars (m: Monomial) : Monomial :=
        match simp_vars_impl m.vars with 
          | [] => {coeff := m.coeff, vars := []}
          | vs => {coeff := m.coeff, vars := simp_vars_impl vs}
      simp_vars_impl (vs: List Variable) : List Variable :=
        match vs with 
          | [] => []
          | [v] => simp_deg v
          | v :: vss => simp_deg v ++ simp_vars_impl vss
      simp_deg (v: Variable) : List Variable :=
        if v.deg == 0 then []
        else [v] 

  private def get_monomials_list (l: List (String × Monomial)) : List Monomial :=
    List.map Prod.snd l

  private def construct_polynomial (rb_map: Std.RBMap String Monomial m_cmp) : Polynomial :=
    {
      monomials := simplify (get_monomials_list rb_map.toList)
    }

  private def sum (p₁ p₂: Polynomial): Polynomial :=
    construct_polynomial (fill_rb_map p₂.monomials
                         (fill_rb_map p₁.monomials (Std.mkRBMap String Monomial m_cmp)))

  #eval sum 0 {monomials := [{coeff:=1, vars:=[{name:="x", deg := 5}]}]}

  theorem p_zero_add : ∀ p : Polynomial, sum 0 p = p := sorry
  

  instance : CommRing Polynomial where
    zero := 0
    one  := 1
    add p₁ p₂ := sum p₁ p₂
    zero_add := p_zero_add
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
