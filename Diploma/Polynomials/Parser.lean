import Lean.Data.Parsec

import Diploma.Polynomials.Polynomial
import Diploma.Algebra.MonomialOrder
import Std.Data.List.Basic

namespace polynomial
open Lean Parsec
open algebra

def Dimension := 3

structure Variable where
  deg: Nat
  name: Nat
deriving instance Inhabited for Variable
deriving instance Repr for Variable


def setI {n: Nat} (i: Nat) (value: Nat): Vector Nat n → Vector Nat n
  | ⟨l, h⟩ => ⟨List.set l i value, by simp; exact h⟩ 

def toInnerName (ch: Char) : Nat := ch.toNat - NameShift

def toVariables (vars: Array Variable) (n: Nat): Variables n := 
 impl vars.toList (get_variables n)
 where
  impl (arr: List Variable) (res: Variables n): Variables n := 
    match arr with
      | []    => res
      | [v]   => setI v.name v.deg res
      | v::vs => setI v.name v.deg (impl vs res)

def Zero      : Parsec String   := Parsec.pure "0"
def One       : Parsec String   := Parsec.pure "1"
def Deg       : Parsec String   := skipChar '^' *> (manyChars digit) <|> One
def Var       : Parsec Variable := do
                                    let name ← asciiLetter
                                    let deg  ← String.toNat! <$> Deg
                                    return {
                                        deg := deg
                                        name:= toInnerName name
                                    }
                              
def Plus   : Parsec Char := pchar '+' 
def Number : Parsec Nat  := (String.toNat! <$> ((many1Chars digit) <|> One))
def Coeff  : Parsec Nat  := Number

def MonomialParser : Parsec (Monomial Dimension) := do
  let coeff ← Coeff
  let vars  ← many Var
  return (coeff, toVariables vars Dimension)

def PolynomialParser : Parsec (Polynomial Dimension Ordering.lex) := do
  let monomial ← MonomialParser
  let monomials ← many (Plus *> MonomialParser)
  return (Polynomial.of_monomial monomial Ordering.lex) +                    
        (List.foldl (fun x (y: Monomial Dimension) => 
                     x + (Polynomial.of_monomial y Ordering.lex)) 0 monomials.toList)

def parse (s: String) : Except String (Polynomial Dimension Ordering.lex) :=
  match PolynomialParser s.mkIterator with
    | Parsec.ParseResult.success _ res => Except.ok res
    | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"

-- #eval parse "123a"
-- #eval parse "1234a^3+ab" failed with stack overflow :(

end polynomial
