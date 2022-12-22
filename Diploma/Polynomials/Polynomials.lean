import Std.Data.HashMap

import Diploma.Computational


namespace polynomials 
  open computational
  
  structure Variable where
    deg  : Nat
    name : String
  
  structure Monomial (α : Type) [ToString α] [Inhabited α] [Computational α] where
    coeff : α
    vars  : List Variable

  structure Polynomial (α : Type) [ToString α] [Inhabited α] [Computational α] where
    monomials : List (Monomial α)


namespace ToString

  instance : ToString Variable where
    toString v := v.name ++ if v.deg != 1 then "^" ++ toString v.deg else ""

  private def VariablesToString (vs: List Variable): String :=
    match vs with 
      | [] => ""
      | [a] => toString a
      | a₁ :: as => (toString a₁) ++ (VariablesToString as)

  instance [ToString α] [Inhabited α] [Computational α]: ToString (Monomial α) where
    toString m := (toString m.coeff) ++ (ToString.VariablesToString m.vars)

  private def MonomialsToString [ToString α] [Inhabited α] [Computational α] (monomials: List (Monomial α)): String :=
     match monomials with 
      | [] => ""
      | [a] => toString a
      | a₁ :: as => toString a₁ ++ " + " ++ (MonomialsToString as)

  instance [ToString α] [Inhabited α] [Computational α] : ToString (Polynomial α) where
    toString p := MonomialsToString p.monomials

end ToString                                   

  def varSub [ToString α] [Inhabited α] [Computational α] (var : Variable) (vs: Std.HashMap String α) : α := 
    (vs.find! var.name) ^ var.deg

  def monomialSubImpl [ToString α] [Inhabited α] [Computational α] (f: List Variable) (vs: Std.HashMap String α) : α := 
      match f with
        | [] => panic! "Found empty variables list"
        | a₁ :: as => ( varSub a₁ vs ) + (monomialSubImpl as vs)

  def monomialSub [ToString α] [Inhabited α] [Computational α] (f: Monomial α) (vs: Std.HashMap String α) : α :=
     f.coeff * monomialSubImpl f.vars vs

  def polynomialSubImpl [ToString α] [Inhabited α] [Computational α] (f: List (Monomial α)) (vs: Std.HashMap String α) : α :=
    match f with
        | [] => panic! "Found empty monomials list"
        | a₁ :: as => (monomialSub a₁ vs) + (polynomialSubImpl as vs)

  def polynomialSub [ToString α] [Inhabited α] [Computational α] (f: Polynomial α) (vs: Std.HashMap String α) : α :=
      polynomialSubImpl f.monomials vs

  #eval varSub {deg:=5, name:="x"} (Std.HashMap.ofList [("x", 5)])
  #eval monomialSub {coeff:=5, vars:=[{deg:=5, name:="x"}]}
                   (Std.HashMap.ofList [("x", 5)])
  #eval polynomialSub {monomials:=[{coeff:=5,
                                    vars:=[{deg:=5, name:="x"}]
                                    }]} (Std.HashMap.ofList [("x", 5)])

end polynomials
