import Lean.Data.Parsec

import Diploma.Polynomials.Parser

open Lean Parsec 
open polynomial
open algebra

namespace interactive

section commands
private def Help        := "help"
private def GroebnerCmd := "groebner"
private def SimpCmd     := "simp"
private def IsInCmd     := "is_in"
private def Exit        := "exit"
end commands

private structure HelpStruct where
  mk ::
  grammar: List String
  commands: List String

private def HelpImpl : HelpStruct := HelpStruct.mk
  [
    "Available [ord] - [lex], [grlex]",
    "polynomial is a polynomial with integer coefficients",
    "{polynomials} ::= polynomial;"
  ]
  [ 
    "simp [ord]: {polynomials}; - simplifie polynomial system with selected ordering",
    "is_in: polynomial; {polynomials}; - check is polynomial in <polynomials>",
    "groebner [ord]: {polynomials}; - returns groebner basis of <polynomials>"
  ]

instance : ToString HelpStruct where
  toString h := "Grammar:\n" ++
                (List.foldl (fun s₁ s₂ => s₁ ++ "\n" ++ s₂) 
                           ""
                           (List.map (fun s => "*** " ++ s) h.grammar)) ++
                           "\n------------------------------------------\n" ++
                           "Commands:\n"++
                (List.foldl (fun s₁ s₂ => s₁ ++ "\n" ++ s₂) 
                           ""
                           (List.map (fun s => "-- " ++ s) h.commands))  ++ "\n"          

private def PolynomialsToString {cmp : Monomial Dimension → Monomial Dimension → Ordering} (ps: List (Polynomial Dimension cmp)): String :=
  match ps with
    | []    => ""
    | a::as => " " ++ toString a ++ ";\n" ++ PolynomialsToString as

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
  toString s := s!"[\n{PolynomialsToString s.result}]"

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
  ws *> skipChar '[' 
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
  ws *> skipChar ';' *> ws
  return toString (Simp.mk ord_type.snd polynomials)

private def Commands: Parsec String := 
  pstring Help        <|>
  pstring GroebnerCmd <|> 
  pstring SimpCmd     <|>
  pstring IsInCmd

def Eval : Parsec (Option String) := do
  let command ← ws *> Commands
  if command == Help then return toString HelpImpl
  else if command == SimpCmd then EvalSimp
 -- else if command == GroebnerCmd then sorry
 -- else if command == IsInCmd then sorry
  else if command == Exit then return none
  else fail s!"unsupported command {command}"

def eval (s: String) : Except String (Option String) :=
  match Eval s.mkIterator with
      | Parsec.ParseResult.success _ res => Except.ok res
      | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"
  
end interactive
