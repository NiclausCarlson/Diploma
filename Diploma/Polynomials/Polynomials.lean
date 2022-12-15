import Std.Data.HashMap

import Diploma.Computational


namespace polynomials 
  open computational
  
  structure Variable where
    deg: Nat
    name: String
  
  structure Monomial (α : Type) [ToString α] [Inhabited α] [Computational α] where
    coeff : α
    vars: List Variable

  structure Polynomial (α : Type) [ToString α] [Inhabited α] [Computational α] where
    monomials : List (Monomial α)


namespace ToString

  instance : ToString Variable where
    toString v := v.name ++ "^" ++ toString v.deg

  instance : ToString (List Variable) where
    toString v := match v with 
                   | [] => ""
                   | [a] => toString a
                   | a₁ :: as => (toString a₁) ++ (toString as)

  instance (α : Type) [ToString α] [Inhabited α]  [Computational α]: ToString (Monomial α) where
    toString m := (toString m.coeff) ++ (toString m.vars)
  
  instance (α : Type) [ToString α] [Inhabited α] [Computational α] : ToString (List (Monomial α)) where
    toString monomials := match monomials with 
                    | [] => ""
                    | [a₁] => toString a₁
                    | a₁ :: as => toString a₁ ++ " + " ++ toString as

  instance (α : Type) [ToString α] [Inhabited α] [Computational α] : ToString (Polynomial α) where
    toString p := toString p.monomials

end ToString

#eval toString {monomials:=[{coeff:=5,
                                      vars:=[{deg:=5, name:="x"}]
                                      }]: Polynomial Nat}
                                      

def var_sub [ToString α] [Inhabited α] [Computational α] (var : Variable) (vs: Std.HashMap String α) : α := 
  (vs.find! var.name) ^ var.deg

def monomial_sub_impl [ToString α] [Inhabited α] [Computational α] (f: List Variable) (vs: Std.HashMap String α) : α := 
    match f with
      | [] => panic! "Found empty variables list"
      | a₁ :: as => ( var_sub a₁ vs ) + (monomial_sub_impl as vs)

def monomial_sub [ToString α] [Inhabited α] [Computational α] (f: Monomial α) (vs: Std.HashMap String α) : α :=
   f.coeff * monomial_sub_impl f.vars vs

def polynomial_sub_impl [ToString α] [Inhabited α] [Computational α] (f: List (Monomial α)) (vs: Std.HashMap String α) : α :=
  match f with
      | [] => panic! "Found empty monomials list"
      | a₁ :: as => (monomial_sub a₁ vs) + (polynomial_sub_impl as vs)

def polynomial_sub [ToString α] [Inhabited α] [Computational α] (f: Polynomial α) (vs: Std.HashMap String α) : α :=
    polynomial_sub_impl f.monomials vs
    
#eval var_sub {deg:=5, name:="x"} (Std.HashMap.ofList [("x", 5)])
#eval monomial_sub {coeff:=5, vars:=[{deg:=5, name:="x"}]}
                 (Std.HashMap.ofList [("x", 5)])
#eval polynomial_sub {monomials:=[{coeff:=5,
                                    vars:=[{deg:=5, name:="x"}]
                                    }]} (Std.HashMap.ofList [("x", 5)])


end polynomials
