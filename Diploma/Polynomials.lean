import Std.Data.HashMap


namespace Polynomials 
  
  structure Variable (α: Type) where
    deg: Nat
    name: String

  structure Monomial (α: Type) where
    coeff : α 
    vars: List (Variable α)

  structure Polynomial (α: Type) where
    monomials : List (Monomial α)

  structure VariableSub (α: Type) where
    name: String
    value: α 


  def v_sub (f : Variable Nat) (x: Nat) : Nat := x ^ f.deg

-- хочу поматчить список переменных. Найти каждую переменную в vs и выполнить подстановку.
-- если не удалось, то выдать ошибку
  def m_sub_impl (f: List (Variable Nat)) (vs: List (VariableSub Nat)) : Nat
    | nil => 1
    | cons head tail => 1

  def m_sub (f: Monomial Nat) (vs: List (VariableSub Nat)) : Nat := 
      f.coeff * (m_sub_impl f.vars vs)


end Polynomials
