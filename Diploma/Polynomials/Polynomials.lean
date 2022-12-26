import Std.Data.HashMap

import Diploma.Computational
import Mathlib.Algebra.Field.Defs


namespace polynomials 
  open computational
  open List

  def Var := Nat × Nat 
  instance : BEq Var where
    beq v₁ v₂ := (v₁.fst == v₂.fst) ∧ (v₁.snd == v₂.snd)
  
  def Monom := Rat × (List Var) 

  def Poly := List Monom

  structure CmpStruct where
    mk::
    arr      : Array Int
    is_empty : Bool
  deriving BEq
  
  instance : ToString CmpStruct where
    toString m := toString m.is_empty  ++ toString m.arr

  private def monomial_eq (m₁ m₂: Monom) : Bool := (set_elems m₁.snd get_comp_struct) == 
                                                   (set_elems m₂.snd get_comp_struct)
    where
     get_comp_struct : CmpStruct := CmpStruct.mk (Array.ofFn add) true
     add (_: Fin 255) : Int := -1 

     set_elems (vs: List Var) (cmp : CmpStruct) : CmpStruct :=
       match vs with 
         | []       => cmp
         | [v]      => set_elem v.fst v.snd cmp
         | v :: vvs => set_elem v.fst v.snd (set_elems vvs cmp)

     set_elem (v deg: Nat) (cmp: CmpStruct) : CmpStruct :=
       CmpStruct.mk (cmp.arr.set! v (merge_equals deg v cmp.arr)) false

     merge_equals (new_value: Nat) (idx: Nat) (arr: Array Int): Int := 
       merge_equals_impl new_value (arr.get! idx)
     merge_equals_impl (new_value old_value: Int) : Int := 
       if old_value < 0 then new_value 
       else Int.add old_value new_value
      
      
  instance : BEq Monom where
    beq m₁ m₂ := monomial_eq m₁ m₂

  instance : HAppend Poly (List Monom) Poly where
      hAppend p ms := p.append ms

  def Monom.sum (m₁ m₂ : Monom) : Poly :=
    if (monomial_eq m₁ m₂) then [(Rat.add m₁.fst m₂.fst, m₁.snd)]
    else if m₁.fst == 0 then [m₂]
    else [m₁, m₂]

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
        | m'::ms => if monomial_eq m' m then (Monom.sum m' m) ++ ms
                    else (Poly.monom_sum m ms) ++ [m']

  def Poly.monom_mul (m : Monom) (p: Poly) : Poly :=
    match p with
      | []     => []
      | [m']   => [Monom.mul m m']
      | m'::ms => (Poly.monom_mul m ms) ++ [Monom.mul m m']


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
    #eval num_of_char 'x'
    def get_var (ch: Char) (deg: Nat) : Var := 
        ((num_of_char ch), deg)
    #eval get_var 'x' 5

    def get_monom (q: Rat) (ms: List Var) : Monom := (q, ms) 
    #eval get_monom 4 [get_var 'x' 5, get_var 'y' 7]

    def get_poly (ms: List Monom) : Poly := ms 
    #eval get_poly [(get_monom 2 [get_var 'x' 5, get_var 'y' 7]), 
                    (get_monom 2 [get_var 'x' 5, get_var 'z' 7])]

    #eval monomial_eq (get_monom 2 [get_var 'y' 5, get_var 'z' 5, get_var 'x' 5])
                      (get_monom 2 [get_var 'x' 5, get_var 'y' 5, get_var 'z' 5])


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
