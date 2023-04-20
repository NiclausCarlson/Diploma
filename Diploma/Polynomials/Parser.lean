import Lean.Data.Parsec

import Std.Data.List.Basic

import Diploma.Polynomials.Polynomial
import Diploma.Order.MonomialOrder
import Diploma.Order.AvailableOrders

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

def toInnerName (ch: Char) : Option Nat := if NameShift > ch.toNat then none
                                           else ch.toNat - NameShift

def toVariables (vars: Array Variable) (n: Nat): Variables n order.Lex := 
 impl vars.toList (get_variables n)
 where
  impl (arr: List Variable) (res: Variables n order.Lex): Variables n order.Lex := 
    match arr with
      | []    => res
      | [v]   => setI v.name v.deg res
      | v::vs => setI v.name v.deg (impl vs res)

open ParseResult in
open String.Iterator in
@[inline]
private def getCurr : Parsec Char := λ it =>
  if ¬(atEnd it) then success it (curr it) else error it unexpectedEndOfInput

def Zero : Parsec String := Parsec.pure "0"
def One  : Parsec String := Parsec.pure "1"

def Number: Parsec String := many1Chars digit

def Deg  : Parsec String   := (skipChar '^' *> Number) <|> One
def Var  : Parsec Variable := do
                                let name ← asciiLetter
                                let deg  ← String.toNat! <$> Deg
                                let inner_name := toInnerName name
                                match inner_name with
                                  | none => fail s!"Unexpected letter {name}"
                                  | some val => return { deg := deg, name:= val}
                              
def Plus  : Parsec Char := pchar '+' 
def Minus : Parsec Char := pchar '-'

private def CharNone : Parsec (Option Char) := do return none  
def Sign : Parsec (Option Char) := (Option.some <$> (Minus <|> Plus)) <|> CharNone
                         
def Coeff : Parsec (Option Int) := do 
                                      let digits ← manyChars digit
                                      if digits.isEmpty then return none
                                      else return some (String.toInt! digits)  
def SignToInt (sign: Option Char): Int := 
   match sign with
      | none => 1
      | some val => if val == '-' then -1 else 1  

def Monom (ord: Type) [MonomialOrder $ Variables Dimension ord]: Parsec (Monomial Dimension ord) := do
  let sign  ← ws *> Sign
  let coeff ← ws *> Coeff
  let vs  ← many Var
  let sign_int := SignToInt sign
  let vars := toVariables vs Dimension
  match coeff with
    | none     => if vs.isEmpty then fail s!"expected coeff or vars after sign `{sign}`"
                  else return (sign_int, vars)
    | some val => if vs.isEmpty then return (sign_int * val, vars)
                  else return (sign_int * val, vars)

def Polynom (ord: Type) [MonomialOrder $ Variables Dimension ord]: Parsec (Polynomial Dimension ord) := do
  let monomial  ← Monom ord <* ws
  let monomials ← many (Monom ord <* ws)
  return (Polynomial.of_monomial monomial) +                    
         (Array.foldl (fun x (y: Monomial Dimension ord) => 
                          x + (Polynomial.of_monomial y)) 0 monomials)

def parse (s: String) (ord: Type) [MonomialOrder $ Variables Dimension ord]: Except String (Polynomial Dimension ord) :=
  match Polynom ord s.mkIterator with
    | Parsec.ParseResult.success _ res => Except.ok res.Simplify
    | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"

instance [MonomialOrder $ Variables Dimension ord]: Inhabited (Polynomial Dimension ord) where
default := {}

def parse! (s: String) (ord: Type) [MonomialOrder $ Variables Dimension ord]: Polynomial Dimension ord:=
  match (parse s ord) with
    | .ok res  => res
    | .error err => panic! err

def PolynomialWithSemilcon (ord: Type) [MonomialOrder $ Variables Dimension ord]: Parsec (Polynomial Dimension ord) := do
  (Polynom ord <* ws) <* skipChar ';'

def Polynomials (ord: Type) [MonomialOrder $ Variables Dimension ord]: Parsec (List (Polynomial Dimension ord)) := do 
 let ps ← many (PolynomialWithSemilcon ord <* ws) 
 return ps.toList

def parse_polynomials (s: String) (ord: Type) [MonomialOrder $ Variables Dimension ord]: Except String (List (Polynomial Dimension ord)) :=
  match Polynomials ord s.mkIterator with
    | Parsec.ParseResult.success _ res => Except.ok res
    | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"

def parse_polynomials! (s: String) (ord: Type) [MonomialOrder $ Variables Dimension ord]: List (Polynomial Dimension ord) :=
   match (parse_polynomials s ord) with
    | .ok res  => res
    | .error err => panic! err

end polynomial
