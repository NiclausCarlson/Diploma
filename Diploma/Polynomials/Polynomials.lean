import Std.Data.HashMap

import Diploma.Computational
import Mathlib.Algebra.Field.Defs
import Mathlib.Init.Set

namespace polynomials 
  open computational
  open List

  def Var := Nat × Nat 
  instance : BEq Var where
    beq v₁ v₂ := (v₁.fst == v₂.fst) ∧ (v₁.snd == v₂.snd)
  
  def Monom := Rat × (List Var) 

  def Poly := List Monom
  
  instance : HAppend Poly (List Monom) Poly where
      hAppend p ms := p.append ms

  def Monom.simp (m : Monom) : Monom :=
    if m.fst == 0 then (0, [])
    else match m.snd with
      | []    => (m.fst, [])
      | [v]   => (m.fst, elim_deg v)
      | v::vs => (m.fst, (elim_deg v) ++ 
                         (elim_degs vs)) 
    where
      elim_deg (v: Var) : List Var :=
        if v.snd == 0 then []
        else [v]
      elim_degs (l: List Var) : List Var :=
        match l with 
          | [] => []
          | [v] => elim_deg v
          | l::ls => (elim_deg l) ++ (elim_degs ls)
  
  -- Not for prooving. 
  def list_var_eq_ (m₁ m₂: List Var) : Bool := are_equals m₁ m₂ 
    where
       are_equals (vs₁ vs₂: List Var) : Bool := 
        match vs₁, vs₂ with
          | [], []         => True
          | [], _          => False
          | _, []          => False
          | [v₁], [v₂]     => v₁ == v₂
          | [_], _::_      => False
          | _::_, [_]      => False
          | v₁::t₁, v₂::t₂ => (v₁ == v₂) ∧ (are_equals t₁ t₂)  

  def Monom.sum (m₁ m₂ : Monom) : Poly :=
    if (list_var_eq_ m₁.snd m₂.snd) then [simp (Rat.add m₁.fst m₂.fst, m₁.snd)]
    else if m₁.fst == 0 then [simp m₂]
    else [m₁, m₂]
    where
      simp (m: Monom) : Monom :=
        if m.fst == 0 then (0, [])
        else m

  def Monom.var_mul (v: Var) (m: Monom) : Monom := (m.fst, variables_match m.snd)
    where
      variables_match (vs: List Var) : List Var := 
        match vs with
          | [] => [v]
          | [other_v] => var_var_mul v other_v
          | other_v::vs => match var_vars_mul_skipped v other_v with
                                  | none => [other_v] ++ (variables_match vs)
                                  | some res => [res] ++ vs
      var_var_mul (v₁ v₂ : Var) : List Var :=
        if v₁.fst = v₂.fst then [(v₁.fst, Nat.add v₁.snd v₂.snd)]
        else [v₁, v₂]
      var_vars_mul_skipped (v₁ v₂ : Var) : Option Var :=
        if v₁.fst = v₂.fst then Option.some (v₁.fst, Nat.add v₁.snd v₂.snd)
        else Option.none

  def Monom.mul (m₁ m₂: Monom): Monom := (Rat.mul m₁.fst m₂.fst, (mul m₁.snd m₂).snd)
    where
      mul (l: List Var) (m: Monom) : Monom :=
        match l with
          | [] => m
          | [v] => Monom.var_mul v m
          | v::vs => mul vs (Monom.var_mul v m)

  def Poly.monom_sum (m : Monom) (p : Poly) : Poly := 
      match p with 
        | []     => []
        | [m']   => Monom.sum m' m
        | m'::ms => if list_var_eq_ m'.snd m.snd then (Monom.sum m' m) ++ ms
                    else (Poly.monom_sum m ms) ++ [m']

  def Poly.monom_mul (m : Monom) (p: Poly) : Poly :=
    match p with
      | []     => []
      | [m']   => [Monom.mul m m']
      | m'::ms => (Poly.monom_mul m ms) ++ [Monom.mul m m']

  def Poly.simp (p: Poly) : Poly := sorry

  section ToString
    instance : ToString Var where
      toString v := (toString (Char.ofNat v.fst)) ++ if v.snd != 1 then "^" ++ toString v.snd else ""
    
    private def variables_to_string (vs: List Var): String :=
      match vs with 
        | [] => ""
        | [v] => toString v
        | v :: vs => (toString v) ++ (variables_to_string vs)

    instance : ToString Monom where
      toString m := (toString m.fst) ++ variables_to_string m.snd

    private def monomials_to_string (ms: List Monom): String :=
     match ms with 
      | [] => ""
      | [m] => toString m
      | m :: ms => toString m ++ " + " ++ (monomials_to_string ms)
    
    instance : ToString Poly where
      toString p := monomials_to_string p
  
    def num_of_char (ch: Char) : Nat := ch.toNat
    def get_var (ch: Char) (deg: Nat) : Var := 
        ((num_of_char ch), deg)
    #eval get_var 'x' 5

    def get_monom (q: Rat) (ms: List Var) : Monom := (q, ms) 
    #eval get_monom 4 [get_var 'x' 5, get_var 'y' 7]

    def get_poly (ms: List Monom) : Poly := ms 
    #eval get_poly [(get_monom 2 [get_var 'x' 5, get_var 'y' 7]), 
                    (get_monom 2 [get_var 'x' 5, get_var 'z' 7])]

  end ToString

  structure Variable where
    deg  : Nat
    name : String
  
  structure Monomial where
    coeff : Int
    vars  : List Variable

  structure Polynomial where
    monomials : List Monomial

  instance : OfNat Monomial n where
    ofNat := {coeff := n, vars := []}

  instance : OfNat Polynomial n where
    ofNat := {monomials := [{coeff := n, vars := []}]}

section ToString

  instance : ToString Variable where
    toString v := v.name ++ if v.deg != 1 then "^" ++ toString v.deg else ""

  private def VariablesToString (vs: List Variable): String :=
    match vs with 
      | [] => ""
      | [a] => toString a
      | a₁ :: as => (toString a₁) ++ (VariablesToString as)

  instance : ToString Monomial where
    toString m := (toString m.coeff) ++ (VariablesToString m.vars)

  private def MonomialsToString  (monomials: List Monomial): String :=
     match monomials with 
      | [] => ""
      | [a] => toString a
      | a₁ :: as => toString a₁ ++ " + " ++ (MonomialsToString as)

  instance : ToString Polynomial where
    toString p := MonomialsToString p.monomials

end ToString                                   
  
  def varSub (var : Variable) (vs: Std.HashMap String Int) : Int := 
    Int.pow (vs.find! var.name) var.deg

  private def monomialSubImpl  (f: List Variable) (vs: Std.HashMap String Int) : Int := 
      match f with
        | [] => panic! "Found empty variables list"
        | a₁ :: as => Int.add (varSub a₁ vs ) (monomialSubImpl as vs)

  def monomialSub (f: Monomial) (vs: Std.HashMap String Int) : Int :=
    Int.mul f.coeff (monomialSubImpl f.vars vs)

  private def polynomialSubImpl  (f: List Monomial) (vs: Std.HashMap String Int) : Int :=
    match f with
        | [] => panic! "Found empty monomials list"
        | a₁ :: as => Int.add (monomialSub a₁ vs) (polynomialSubImpl as vs)

  def polynomialSub  (f: Polynomial) (vs: Std.HashMap String Int) : Int :=
      polynomialSubImpl f.monomials vs

end polynomials
