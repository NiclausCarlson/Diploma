import Diploma.tests.Common
import Diploma.Polynomials.Parser
import Diploma.Polynomials.Groebner

open polynomial algebra IdealHelpers

def sum (p₁ p₂: String): String :=
  toString (parse_lex! p₁ + parse_lex! p₂)
 
--# Test sum
#eval AssertEq (sum "1" "0")                               "1"
#eval AssertEq (sum "0" "1")                               "1"
#eval AssertEq (sum "0" "2")                               "2"
#eval AssertEq (sum "2" "0")                               "2"
#eval AssertEq (sum "2" "2")                               "4"
#eval AssertEq (sum "x0" "0")                              "x0"
#eval AssertEq (sum "x0" "x0")                             "2x0"
#eval AssertEq (sum "2x0" "x0")                            "3x0"
#eval AssertEq (sum "x0^4" "x0")                           "x0^4+x0"
#eval AssertEq (sum "3x0^4" "x0")                          "3x0^4+x0"
#eval AssertEq (sum "3x0^4" "x0^4")                        "4x0^4"
#eval AssertEq (sum "3x0^4x1^2" "x0^4")                    "3x0^4x1^2+x0^4"
#eval AssertEq (sum "3x0^4x1^2+x0^4x1^2+10x2" "x0^4+15x2") "4x0^4x1^2+x0^4+25x2"

#eval AssertEq (sum "-x1+1" "x1+1") "2"
#eval AssertEq (sum "x0x1^2+1" "-x0x1^2+1") "2"


def sub (p₁ p₂: String): String :=
  toString (parse_lex! p₁ - parse_lex! p₂)

--# Test sub
#eval AssertEq (sub "1" "0")                                 "1"
#eval AssertEq (sub "0" "1")                                 "-1"
#eval AssertEq (sub "0" "2")                                 "-2"
#eval AssertEq (sub "2" "0")                                 "2"
#eval AssertEq (sub "2" "2")                                 "0"
#eval AssertEq (sub "x0" "0")                                "x0"
#eval AssertEq (sub "x0" "x0")                               "0"
#eval AssertEq (sub "3x0" "3x0")                             "0"
#eval AssertEq (sub "2x0" "x0")                              "x0"
#eval AssertEq (sub "x0^4" "x0")                             "x0^4-x0"
#eval AssertEq (sub "3x0^4" "x0")                            "3x0^4-x0"
#eval AssertEq (sub "3x0^4" "x0^4")                          "2x0^4"
#eval AssertEq (sub "3x0^4x1^2" "x0^4")                      "3x0^4x1^2-x0^4"
#eval AssertEq (sub "3x0^4x1^2+x0^4x1^2+10x2" "x0^4+15x2")   "4x0^4x1^2-x0^4-5x2"
#eval AssertEq (sub "3x0^4x1^2+x0^4x1^2+10x2+1" "x0^4+15x2") "4x0^4x1^2-x0^4-5x2+1"


def mul (p₁ p₂: String): String :=
  toString (parse_lex! p₁ * parse_lex! p₂)

--# Test mul
#eval AssertEq (mul "1" "0")                                            "0"
#eval AssertEq (mul "x0" "x0")                                          "x0^2"
#eval AssertEq (mul "2x0" "x0")                                         "2x0^2"
#eval AssertEq (mul "2x0" "3x0^5")                                      "6x0^6"
#eval AssertEq (mul "x0+x1" "x0-x1")                                    "x0^2-x1^2"
#eval AssertEq (mul "x0+x1-x2" "x0-x1")                                 "x0^2-x0x2-x1^2+x1x2"
#eval AssertEq (mul "6x0^7+18x0^4x1^2x2^2-x0x1x2" "17x0^18-14x1^34+x2") "102x0^25+306x0^22x1^2x2^2-17x0^19x1x2-84x0^7x1^34+6x0^7x2-252x0^4x1^36x2^2+18x0^4x1^2x2^3+14x0x1^35x2-x0x1x2^2"


--# Check monomials div
private def monomial_div_check(p₁ p₂: String) (is_divides: Bool) (expected: String) : Except String String :=
  let m₁ := parseMonomial! p₁
  let m₂ := parseMonomial! p₂
  let ex := parseMonomial! expected
  if m₁.is_div m₂ then 
    let d := m₁.div m₂
    AssertTrue (d == ex) s!"Unexpected divide result: expected - {expected} actual - {toString d}"
  else if ¬is_divides then Except.ok "OK"
       else Except.error "Monomials are not divides"

#eval monomial_div_check "x0" "x0"                     true "1"
#eval monomial_div_check "2x0" "x0"                    true "2"
#eval monomial_div_check "x0^2" "x0"                   true "x0"
#eval monomial_div_check "2x0^2" "x0"                  true "2x0"
#eval monomial_div_check "4x0^3x1^3x2^8" "x0"          true "4x0^2x1^3x2^8"
#eval monomial_div_check "4x0^3x1^3x2^8" "2x0"         true "2x0^2x1^3x2^8"
#eval monomial_div_check "4x0^3x1^3x2^8" "2x0x1^3x2^6" true "2x0^2x2^2"
#eval monomial_div_check "4x0^3x1^3x2^8" "2x0x1^3x2^6" true "2x0^2x2^2"

#eval monomial_div_check "x0"        "x1"   false "0"
#eval monomial_div_check "4x0^3x1^3" "x2"   false "0"
#eval monomial_div_check "4x1^3"     "x0"   false "0"
#eval monomial_div_check "4x1^3"     "x0x1" false "0"

--# Test div
private def parse_list (ps: List String): List (Polynomial Dimension order.Lex) := ps.map parse_lex!

def div (p: String) (ps: List String): Except String (DivisionResult (parse_lex! p) (asIdeal$ parse_list ps)) := 
  let divivders :=  parse_list ps
  if h₁: divivders == [] then Except.error s!"divivders is empty"
  else if h₂: divivders.any (fun p => p == 0) then Except.error s!"divivders contains zero" 
  else Except.ok $ divide_many (parse_lex! p) (divivders) h₁ h₂

private def check_div (divisible: String) (ps: List String) (poly: String) (remainder: String): Except String String :=
  let res := div divisible ps
  match res with
    | Except.error err => Except.error err
    | Except.ok ok => let p := parse_lex! poly
                      let r := parse_lex! remainder
                      match AssertTrue (ok.p == p) s!"expected poly {toString p} actual {toString ok.p}" with
                        | Except.ok _ =>  match AssertTrue (ok.r == r) s!"expected remainder {toString r} actual {toString ok.r}" with
                                            | Except.ok _      => AssertTrue ((parse_lex! divisible) == (p + r)) s!"divisible ≠ p + r"
                                            | Except.error err => Except.error err
                        | Except.error err => Except.error err

#eval check_div "x0^2" ["x0"] "x0^2" "0"
#eval check_div "x0x1^2+1" ["x0x1+1"] "x0x1^2+x1" "-x1+1"
#eval check_div "x0x1^2+1" ["x0x1+1", "x1+1"] "x0x1^2-1" "2"
#eval check_div "x0+x1" ["x1"] "x1" "x0" 
#eval check_div "x0+x1^2+x1" ["x0x1-1", "x1^2-1"] "x1^2-1" "x0+x1+1"
#eval check_div "x0^2x1+x0x1^2+x1^2" ["x0x1-1", "x1^2-1"] "x0^2x1+x0x1^2-x0+x1^2-x1-1" "x0+x1+1"

--# Test s_polynomials
private def check_s_polynomial (p₁ p₂ expected: String) : Except String String :=
  let parsed₁ := parse_lex! p₁
  let parsed₂ := parse_lex! p₂
  let s_p     := build_s_polynomial parsed₁ parsed₂
  AssertEq (toString s_p) expected 

private def check_s_polynomial_grlex (p₁ p₂ expected: String) : Except String String :=
  let parsed₁ := parse_grlex! p₁
  let parsed₂ := parse_grlex! p₂
  let s_p     := build_s_polynomial parsed₁ parsed₂
  AssertEq (toString s_p) expected 

#eval check_s_polynomial "x0" "x0" "0"
#eval check_s_polynomial "x0x1" "x0" "0"
#eval check_s_polynomial "x0x1^2" "x0" "0"
#eval check_s_polynomial "x0x1^2" "x2" "0"
#eval check_s_polynomial "x0x1^2+1" "x2" "x2"
#eval check_s_polynomial "x0x1^2+1" "x0" "1"
#eval check_s_polynomial "x0^3x1^2-x0^2x1^3+x0" "3x0^4x1+x1^2" "-x0^3x1^3+x0^2-1/3x1^3"

#eval check_s_polynomial_grlex "x0^3x1^2-x0^2x1^3+x0" "3x0^4x1+x1^2" "-x0^3x1^3-1/3x1^3+x0^2"
#eval check_s_polynomial_grlex "x0^3-2x0x1" "x0^2x1-2x1^2+x0" "-x0^2"

--# Test Groebner
private def check_groebner (input expected: List String): Except String String := 
  let parsed          := parse_list input
  let parsed_expected := parse_list expected
  let groebner := build_groebner_basis parsed
  AssertTrue (groebner == parsed_expected) s!"expected {parsed_expected}; actual {groebner}"

#eval check_groebner ["x0x1-x1", "x0"] ["x0x1-x1", "x0", "-x1"]
#eval check_groebner ["x0+x1-1", "x1-x2", "x2-x0x1"] ["x0+x1-1", "x1-x2", "-x0x1+x2", "x2^2"]

def get_remainder (div_res: Except String (DivisionResult (parse_lex! p) (asIdeal$ parse_list ps))): String := 
  match div_res with
    | Except.ok res => toString res.r
    | Except.error err => err

-- Demostration that ⟨x+y-1, y-z, -xy+z, z^2⟩ is Groebner basis
def f₁ := "x0+x1-1"
def f₂ := "x1-x2"
def f₃ := "-x0x1+x2"
def f₄ := "x2^2"
#eval build_s_polynomial (parse_lex! f₁) (parse_lex! f₂)
#eval get_remainder (div "x0x2+x1^2-x1" ["x0+x1-1", "x1-x2", "-x0x1+x2"]) -- zero
#eval build_s_polynomial (parse_lex! f₁) (parse_lex! f₃)
#eval get_remainder (div "x1^2-x1+x2" ["x0+x1-1", "x1-x2", "-x0x1+x2", "x2^2"]) -- zero
#eval build_s_polynomial (parse_lex! f₁) (parse_lex! f₄)
#eval get_remainder (div "x1x2^2-x2^2" ["x0+x1-1", "x1-x2", "-x0x1+x2", "x2^2"]) -- zero
#eval build_s_polynomial (parse_lex! f₂) (parse_lex! f₃)
#eval get_remainder (div "-x0x2+x2" ["x0+x1-1", "x1-x2", "-x0x1+x2", "x2^2"]) -- zero
#eval build_s_polynomial (parse_lex! f₂) (parse_lex! f₄)
#eval get_remainder (div "-x2^3" ["x0+x1-1", "x1-x2", "-x0x1+x2", "x2^2"]) -- zero
#eval build_s_polynomial (parse_lex! f₃) (parse_lex! f₄)
#eval get_remainder (div "-x2^3" ["x0+x1-1", "x1-x2", "-x0x1+x2", "x2^2"]) -- zero

#eval check_groebner ["x0^2+x0x1x2^4+x1", "x0+x1+x2"] ["x0^2+x0x1x2^4+x1", "x0+x1+x2", "-x1^2x2^4+x1^2-x1x2^5+2x1x2+x1+x2^2"]
#eval check_groebner ["17x0^5x1^8+4x0x1x2^12", "x0x1^4x2", "x1-1"] ["17x0^5x1^8+4x0x1x2^12", "x0x1^4x2", "x1-1", "4/17x0x2^13", "x0^5+4/17x0x2^12", "4/17x0x2^12", "x0x2"]

--# Test eval
#eval (parse_lex! "x0^2").eval ⟨[1, 0, 0], by rfl⟩                                      == 1
#eval (parse_lex! "x0^2").eval ⟨[1, 4, 3], by rfl⟩                                      == 1
#eval (parse_lex! "x0^2").eval ⟨[2, 0, 0], by rfl⟩                                      == 4
#eval (parse_lex! "x0^2x1").eval ⟨[2, 0, 0], by rfl⟩                                    == 0
#eval (parse_lex! "x0^2x1").eval ⟨[2, 1, 0], by rfl⟩                                    == 4
#eval (parse_lex! "x0^2x1^3").eval ⟨[2, 2, 0], by rfl⟩                                  == 32
#eval (parse_lex! "x0^2x1^3x2^4").eval ⟨[2, 2, 5], by rfl⟩                              == 20000
#eval (parse_lex! "5x0^2x1^3x2^4").eval ⟨[2, 2, 5], by rfl⟩                             == 100000
#eval (parse_lex! "5x0^2x1^3x2^4 + x0 + x1^3x2^7 + x0^3 + 27").eval ⟨[2, 2, 5], by rfl⟩ == 725037
 