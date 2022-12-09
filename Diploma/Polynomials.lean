import Std.Data.HashMap

import Diploma.Computational


namespace Polynomials 
  open Computational
  structure Variable where
    deg: Nat
    name: String

  structure Monomial where
    coeff : Nat 
    vars: List Variable

  structure Polynomial where
    monomials : List Monomial

  def var_sub (var : Variable) (vs: Std.HashMap String Nat) : Nat := 
     (vs.find! var.name)  ^ var.deg

  def monomial_sub_impl (f: List Variable) (vs: Std.HashMap String Nat) : Nat := 
      match f with
        | [] => panic! "Found empty variables list"
        | a₁ :: as => ( var_sub a₁ vs ) + (monomial_sub_impl as vs)

  def monomial_sub (f: Monomial) (vs: Std.HashMap String Nat) : Nat :=
     f.coeff * monomial_sub_impl f.vars vs
  
  def polynomial_sub_impl (f: List Monomial) (vs: Std.HashMap String Nat) : Nat :=
    match f with
        | [] => panic! "Found empty monomials list"
        | a₁ :: as => (monomial_sub a₁ vs) + (polynomial_sub_impl as vs)

  def polynomial_sub (f: Polynomial) (vs: Std.HashMap String Nat) : Nat :=
      polynomial_sub_impl f.monomials vs

  #eval var_sub {deg:=5, name:="x"} (Std.HashMap.ofList [("x", 5)])

  #eval monomial_sub {coeff:=5, vars:=[{deg:=5, name:="x"}]}
                   (Std.HashMap.ofList [("x", 5)])

  #eval polynomial_sub {monomials:=[{coeff:=5,
                                      vars:=[{deg:=5, name:="x"}]
                                      }]} (Std.HashMap.ofList [("x", 5)])


end Polynomials
