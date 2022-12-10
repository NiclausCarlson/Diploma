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


namespace ToString

  instance : ToString Variable where
    toString v := v.name ++ "^" ++ toString v.deg

  instance : ToString (List Variable) where
    toString v := match v with 
                   | [] => ""
                   | [a] => toString a
                   | a₁ :: as => (toString a₁) ++ (toString as)

  instance : ToString Monomial where
    toString m := (toString m.coeff) ++ (toString m.vars)
  
  instance : ToString (List Monomial) where
    toString monomials := match monomials with 
                    | [] => ""
                    | [a₁] => toString a₁
                    | a₁ :: as => toString a₁ ++ " + " ++ toString as

  instance : ToString Polynomial where
    toString p := toString p.monomials

end ToString

#eval toString {monomials:=[{coeff:=5,
                                      vars:=[{deg:=5, name:="x"}]
                                      }]: Polynomial}
                                      

  def var_sub (var : Variable) (vs: Std.HashMap String Nat) : Nat := 
    (vs.find! var.name) ^ var.deg

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
