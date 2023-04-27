import Lean.Data.Parsec

import Diploma.Polynomials.Parser
import Diploma.Polynomials.Groebner
import Diploma.Order.AvailableOrders

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

inductive Orders where
  | lex
  | grlex

open Orders in 
private def toStr (ord: Orders): String := 
  match ord with
   | lex   => "lex"
   | grlex => "grlex"  

instance: ToString Orders where
  toString ord := toStr ord

private def PolynomialsToString {ord: Type} [MonomialOrder $ Variables Dimension ord] (ps: List (Polynomial Dimension ord)): String :=
  List.foldl (fun x y => x ++ toString y ++ ";") "" ps

private def OrdType: Parsec Orders := do
  let lex   := "lex"
  let grlex := "grlex"
  ws *> skipChar '[' 
  let name ← ws *> (pstring lex <|> pstring grlex) 
  ws *> skipChar ']' 
  if name == lex then return Orders.lex
  else if name == grlex then return Orders.grlex
  else fail s!"Unknown ordering {name}"

private def PolynomialsBlock (ord: Type) [MonomialOrder $ Variables Dimension ord]: Parsec (List (Polynomial Dimension ord)) := 
  skipChar '{' *> Polynomials ord <* skipChar '}'

--# Help command
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
  [ "set_n Nat; - set dimension for next commands. Dimension by default is 3",
    "simp [ord]: {polynomials}; - simplifie polynomial system with selected ordering",
    "is_in polynomial; {polynomials}; - check is polynomial in <polynomials>",
    "groebner [ord]: {polynomials}; - returns groebner basis of <polynomials>",
    "exit - to exit"
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


--# Groebner command
private structure Groebner (ord: Type) [MonomialOrder $ Variables Dimension ord] where
  mk ::
  ordering_type: String
  input : List (Polynomial Dimension ord)
  result : List (Polynomial Dimension ord)

instance (ord: Type) [MonomialOrder $ Variables Dimension ord]: ToString (Groebner ord) where
  toString s := s!"groebner ⟨{PolynomialsToString s.input}⟩ [{s.ordering_type}] = ⟨{PolynomialsToString s.result}⟩"

open Orders in 
private def BuildGroebner: Parsec String := do
  let ord_type ← OrdType
  ws *> skipChar ':' *> ws
  match ord_type with
    | lex   => let polynomials ← PolynomialsBlock order.Lex
               return toString $ Groebner.mk (toString ord_type) polynomials (build_groebner_basis polynomials)
    | grlex => let polynomials ← PolynomialsBlock order.GrLex
               return toString $ Groebner.mk (toString ord_type) polynomials (build_groebner_basis polynomials)

--# Simp command
private structure Simp (ord: Type) [MonomialOrder $ Variables Dimension ord] where
  mk ::
  ordering_type: String
  result : List (Polynomial Dimension ord)

instance {ord: Type} [MonomialOrder $ Variables Dimension ord]: ToString (Simp ord) where
  toString s := s!"[{PolynomialsToString s.result}]"

open Orders in 
private def EvalSimp : Parsec String := do
  let ord_type ← OrdType
  ws *> skipChar ':' *> ws
  match ord_type with
    | lex   => let polynomials ← PolynomialsBlock order.Lex
               ws *> skipChar ';' *> ws
               return toString $ Simp.mk (toString ord_type) polynomials
    | grlex => let polynomials ← PolynomialsBlock order.GrLex
               ws *> skipChar ';' *> ws
               return toString $ Simp.mk (toString ord_type) polynomials


--# Is in command 
private structure IsIn (ord: Type) [MonomialOrder $ Variables Dimension ord] where
  mk ::
  polynomial: Polynomial Dimension ord
  ideal: List (Polynomial Dimension ord)
  result: Bool

private def IsInStr (b: Bool): String := 
  if b then "is in"
  else "is not in"

instance (ord: Type) [MonomialOrder $ Variables Dimension ord]: ToString (IsIn ord) where
  toString s := s!"{s.polynomial} {IsInStr s.result} ⟨{PolynomialsToString s.ideal}⟩"

private def EvalIsIn: Parsec String := do
  let p  ← PolynomialWithSemilcon order.GrLex <* ws
  let ps ← PolynomialsBlock order.GrLex
  let basis := build_groebner_basis ps
  return toString $ IsIn.mk p basis (is_in_basis p basis)

--# Main parser
private def Commands: Parsec String := 
  pstring Help        <|>
  pstring GroebnerCmd <|> 
  pstring SimpCmd     <|>
  pstring IsInCmd     <|>
  pstring Exit        <|>
  pure ""

def Eval : Parsec (Option String) := do
  let command ← ws *> Commands
  if command == Help then return toString HelpImpl
  else if command == SimpCmd then EvalSimp
  else if command == GroebnerCmd then BuildGroebner
  else if command == IsInCmd then EvalIsIn
  else if command == Exit then return none
  else fail s!"unsupported command {command}"

def eval (s: String) : Except String (Option String) :=
  match Eval s.mkIterator with
      | Parsec.ParseResult.success _ res => Except.ok res
      | Parsec.ParseResult.error _ err  => Except.error s!"{err}"
  
end interactive
