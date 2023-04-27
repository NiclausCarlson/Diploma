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

private def PolynomialsToString {dimension: Nat} {ord: Type} [MonomialOrder $ Variables dimension ord] (ps: List (Polynomial dimension ord)): String :=
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

private def PolynomialsBlock (dimension: Nat) (ord: Type) [MonomialOrder $ Variables dimension ord]: Parsec (List (Polynomial dimension ord)) := 
  skipChar '{' *> Polynomials dimension ord <* skipChar '}'

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
private structure Groebner (dimension: Nat) (ord: Type) [MonomialOrder $ Variables dimension ord] where
  mk ::
  ordering_type: String
  input : List (Polynomial dimension ord)
  result : List (Polynomial dimension ord)

instance {dimension: Nat} {ord: Type} [MonomialOrder $ Variables dimension ord]: ToString (Groebner dimension ord) where
  toString s := s!"groebner ⟨{PolynomialsToString s.input}⟩ [{s.ordering_type}] = ⟨{PolynomialsToString s.result}⟩"

open Orders in 
private def BuildGroebner (dimension: Nat): Parsec String := do
  let ord_type ← OrdType
  ws *> skipChar ':' *> ws
  match ord_type with
    | lex   => let polynomials ← PolynomialsBlock dimension order.Lex
               return toString $ Groebner.mk (toString ord_type) polynomials (build_groebner_basis polynomials)
    | grlex => let polynomials ← PolynomialsBlock dimension order.GrLex
               return toString $ Groebner.mk (toString ord_type) polynomials (build_groebner_basis polynomials)

--# Simp command
private structure Simp (dimension: Nat) (ord: Type) [MonomialOrder $ Variables dimension ord] where
  mk ::
  ordering_type: String
  result : List (Polynomial dimension ord)

instance {dimension: Nat} {ord: Type} [MonomialOrder $ Variables dimension ord]: ToString (Simp dimension ord) where
  toString s := s!"[{PolynomialsToString s.result}]"

open Orders in 
private def EvalSimp (dimension: Nat): Parsec String := do
  let ord_type ← OrdType
  ws *> skipChar ':' *> ws
  match ord_type with
    | lex   => let polynomials ← PolynomialsBlock dimension order.Lex
               ws *> skipChar ';' *> ws
               return toString $ Simp.mk (toString ord_type) polynomials
    | grlex => let polynomials ← PolynomialsBlock dimension order.GrLex
               ws *> skipChar ';' *> ws
               return toString $ Simp.mk (toString ord_type) polynomials


--# Is in command 
private structure IsIn (dimension: Nat) (ord: Type) [MonomialOrder $ Variables dimension ord] where
  mk ::
  polynomial: Polynomial dimension ord
  ideal: List (Polynomial dimension ord)
  result: Bool

private def IsInStr (b: Bool): String := 
  if b then "is in"
  else "is not in"

instance {dimension: Nat} {ord: Type} [MonomialOrder $ Variables dimension ord]: ToString (IsIn dimension ord) where
  toString s := s!"{s.polynomial} {IsInStr s.result} ⟨{PolynomialsToString s.ideal}⟩"

private def EvalIsIn (dimension: Nat): Parsec String := do
  let p  ← PolynomialWithSemilcon dimension order.GrLex <* ws
  let ps ← PolynomialsBlock dimension order.GrLex
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

def Eval (dimension: Nat): Parsec (Option String) := do
  let command ← ws *> Commands
  if command == Help then return toString HelpImpl
  else if command == SimpCmd then EvalSimp dimension
  else if command == GroebnerCmd then BuildGroebner dimension
  else if command == IsInCmd then EvalIsIn dimension
  else if command == Exit then return none
  else fail s!"unsupported command {command}"

def eval (s: String) (dimension: Nat): Except String (Option String) :=
  match Eval dimension s.mkIterator with
      | Parsec.ParseResult.success _ res => Except.ok res
      | Parsec.ParseResult.error _ err  => Except.error s!"{err}"
  
end interactive
