import Lean.Data.Parsec

import Diploma.Polynomials.Parser

open Lean Parsec 
open polynomial
open algebra

namespace interactive

section commands
private def GroebnerCmd := "groebner"
private def SimpCmd     := "simp"
private def IsInCmd     := "is_in"
end commands


private def PolynomialsToString {cmp : Monomial Dimension → Monomial Dimension → Ordering} (ps: List (Polynomial Dimension cmp)): String :=
  match ps with
    | []    => ""
    | a::as => toString a ++ "\n" ++ PolynomialsToString as

private structure Groebner (cmp : Monomial Dimension → Monomial Dimension → Ordering) where
  mk ::
  ordering_type: String
  input : List (Polynomial Dimension cmp)
  result : List (Polynomial Dimension cmp)

instance {cmp : Monomial Dimension → Monomial Dimension → Ordering}: ToString (Groebner cmp) where
  toString s := s!"Groebner basis for ideal [{PolynomialsToString s.input}] \n
                   with ordering [{s.ordering_type}] is [{PolynomialsToString s.result}]"

private structure Simp (cmp : Monomial Dimension → Monomial Dimension → Ordering) where
  mk ::
  ordering_type: String
  result : List (Polynomial Dimension cmp)

instance {cmp : Monomial Dimension → Monomial Dimension → Ordering}: ToString (Simp cmp) where
  toString s := s!"Ordering type: {s.ordering_type}; Result:\n[{PolynomialsToString s.result}]"

private structure IsIn (cmp : Monomial Dimension → Monomial Dimension → Ordering) where
  mk ::
  polynomial: Polynomial Dimension cmp
  ideal: List (Polynomial Dimension cmp)
  result: Bool

private def IsInStr (b: Bool): String := 
  if b then "is in"
  else "is not in"

instance {cmp : Monomial Dimension → Monomial Dimension → Ordering}: ToString (IsIn cmp) where
  toString s := s!"Polynomial: {s.polynomial} {IsInStr s.result} ideal [{PolynomialsToString s.ideal}]"

private def OrdType : Parsec ((Monomial Dimension → Monomial Dimension → Ordering) × String) := do
  let lex   := "lex"
  let grlex := "grlex"
  skipChar '[' 
  let name ← ws *> (pstring lex <|> pstring grlex) 
  ws *> skipChar ']' 
  if name == lex then return (Ordering.lex, lex)
  else if name == grlex then return (Ordering.grlex, grlex)
  else fail s!"Unknown ordering {name}"

private def PolynomialBlock (cmp: Monomial Dimension → Monomial Dimension → Ordering): Parsec (List (Polynomial Dimension cmp)) := 
  skipChar '{' *> Polynomials cmp <* skipChar '}'

private def EvalSimp : Parsec String := do
  let ord_type ← OrdType
  ws *> skipChar ':' *> ws
  let polynomials ← PolynomialBlock ord_type.fst
  ws *> skipChar ':' *> ws
  return toString (Simp.mk ord_type.snd polynomials)

def EvalCommand : Parsec String := do
  let command ← ws *> (pstring GroebnerCmd <|> pstring SimpCmd <|> pstring IsInCmd)
  if command == SimpCmd then EvalSimp
  else if command == GroebnerCmd then sorry
  else if command == IsInCmd then sorry
  else fail s!"unsupported command {command}"

def Eval: Parsec (Array String) := many EvalCommand

def eval (s: String) : Except String (List String) :=
  match Eval s.mkIterator with
      | Parsec.ParseResult.success _ res => Except.ok res.toList
      | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"
  
end interactive
