import Diploma.tests.Common
import Diploma.Polynomials.Parser
import Diploma.Polynomials.Groebner

open polynomial
open algebra

def sum (p₁ p₂: String): String :=
  toString (parse_lex! p₁ + parse_lex! p₂)
 
--# Test sum
#eval AssertEq (sum "1" "0")                        "1"
#eval AssertEq (sum "0" "1")                        "1"
#eval AssertEq (sum "0" "2")                        "2"
#eval AssertEq (sum "2" "0")                        "2"
#eval AssertEq (sum "2" "2")                        "4"
#eval AssertEq (sum "x" "0")                        "x"
#eval AssertEq (sum "x" "x")                        "2x"
#eval AssertEq (sum "2x" "x")                       "3x"
#eval AssertEq (sum "x^4" "x")                      "x^4+x"
#eval AssertEq (sum "3x^4" "x")                     "3x^4+x"
#eval AssertEq (sum "3x^4" "x^4")                   "4x^4"
#eval AssertEq (sum "3x^4y^2" "x^4")                "3x^4y^2+x^4"
#eval AssertEq (sum "3x^4y^2+x^4y^2+10z" "x^4+15z") "4x^4y^2+x^4+25z"

#eval AssertEq (sum "-y+1" "y+1") "2"
#eval AssertEq (sum "xy^2+1" "-xy^2+1") "2"


def sub (p₁ p₂: String): String :=
  toString (parse_lex! p₁ - parse_lex! p₂)

--# Test sub
#eval AssertEq (sub "1" "0")                        "1"
#eval AssertEq (sub "0" "1")                        "-1"
#eval AssertEq (sub "0" "2")                        "-2"
#eval AssertEq (sub "2" "0")                        "2"
#eval AssertEq (sub "2" "2")                        "0"
#eval AssertEq (sub "x" "0")                        "x"
#eval AssertEq (sub "x" "x")                        "0"
#eval AssertEq (sub "3x" "3x")                      "0"
#eval AssertEq (sub "2x" "x")                       "x"
#eval AssertEq (sub "x^4" "x")                      "x^4-x"
#eval AssertEq (sub "3x^4" "x")                     "3x^4-x"
#eval AssertEq (sub "3x^4" "x^4")                   "2x^4"
#eval AssertEq (sub "3x^4y^2" "x^4")                "3x^4y^2-x^4"
#eval AssertEq (sub "3x^4y^2+x^4y^2+10z" "x^4+15z") "4x^4y^2-x^4-5z"


def mul (p₁ p₂: String): String :=
  toString (parse_lex! p₁ * parse_lex! p₂)

--# Test mul
#eval AssertEq (mul "1" "0")                                  "0"
#eval AssertEq (mul "x" "x")                                  "x^2"
#eval AssertEq (mul "2x" "x")                                 "2x^2"
#eval AssertEq (mul "2x" "3x^5")                              "6x^6"
#eval AssertEq (mul "x+y" "x-y")                              "x^2-y^2"
#eval AssertEq (mul "x+y-z" "x-y")                            "x^2-xz-y^2+yz"
#eval AssertEq (mul "6x^7+18x^4y^2z^2-xyz" "17x^18-14y^34+z") "102x^25+306x^22y^2z^2-17x^19yz-84x^7y^34+6x^7z-252x^4y^36z^2+18x^4y^2z^3+14xy^35z-xyz^2"


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

#eval monomial_div_check "x" "x"                 true "1"
#eval monomial_div_check "2x" "x"                true "2"
#eval monomial_div_check "x^2" "x"               true "x"
#eval monomial_div_check "2x^2" "x"              true "2x"
#eval monomial_div_check "4x^3y^3z^8" "x"        true "4x^2y^3z^8"
#eval monomial_div_check "4x^3y^3z^8" "2x"       true "2x^2y^3z^8"
#eval monomial_div_check "4x^3y^3z^8" "2xy^3z^6" true "2x^2z^2"
#eval monomial_div_check "4x^3y^3z^8" "2xy^3z^6" true "2x^2z^2"

#eval monomial_div_check "x"       "y"  false ""
#eval monomial_div_check "4x^3y^3" "z"  false ""
#eval monomial_div_check "4y^3"    "x"  false ""
#eval monomial_div_check "4y^3"    "xy" false ""


private def reduce_lt_check (p₁ p₂: String) (expected_reduced: String) (expected_reducer: String): Except String String :=
  let q   := parse_lex! expected_reduced
  let r   := parse_lex! expected_reducer
  match reduce_lt (parse_lex! p₁) (parse_lex! p₂) with
    | none     => AssertTrue ((expected_reduced == "") ∧ (expected_reducer == "")) s!"expected values are no empty"
    | some res => match AssertTrue (res.reduced == q) 
                            s!"expected reduced {toString q} actual {toString res.reduced}" with
                    | Except.ok _ => AssertTrue (res.reducer == r) s!"expected reducer {toString r} actual {toString res.reducer}"
                    | Except.error err => Except.error err

#eval reduce_lt_check "x" "x" "0" "x"
#eval reduce_lt_check "x^2" "x" "0" "x^2"
#eval reduce_lt_check "2x" "x" "0" "2x"
#eval reduce_lt_check "xy" "x" "0" "xy"
#eval reduce_lt_check "2xy" "x" "0" "2xy"
#eval reduce_lt_check "y" "y" "0" "y"

#eval reduce_lt_check "2xy+z" "x" "z" "2xy"
#eval reduce_lt_check "2x^2y+z" "x" "z" "2x^2y"
#eval reduce_lt_check "2x^2yz+z" "x" "z" "2x^2yz"
#eval reduce_lt_check "2x^2y^4z+x+y+z" "x" "x+y+z" "2x^2y^4z"
#eval reduce_lt_check "3x^2y^4z+x+y+z" "xy" "x+y+z" "3x^2y^4z"
#eval reduce_lt_check "3x^2y^4z+x" "xy^3" "x" "3x^2y^4z"
#eval reduce_lt_check "xy^2+1" "xy+1" "-y+1" "xy^2+y"
#eval reduce_lt_check "-y+1" "y+1" "2" "-y-1"
#eval reduce_lt_check "2" "xy-1" "" ""
#eval reduce_lt_check "2" "y+1" "" ""

--# Test div
private def parse_list (ps: List String): List (Polynomial Dimension Ordering.lex) := ps.map parse_lex!
def div (p: String) (ps: List String): DivisionResult Dimension Ordering.lex := 
  divide_many (parse_lex! p) (parse_list ps)

private def check_div (p: String) (ps: List String) (poly: String) (remainder: String): Except String String :=
  let res := div p ps
  let p   := parse_lex! poly
  let r   := parse_lex! remainder
  match AssertTrue (res.p == p) s!"expected poly {toString p} actual {toString res.p}" with
    | Except.ok _ =>  AssertTrue (res.r == r) s!"expected remainder {toString r} actual {toString res.r}" 
    | Except.error err => Except.error err

#eval check_div "x^2" ["x"] "x^2" "0"
#eval check_div "xy^2+1" ["xy+1"] "xy^2+y" "-y+1"
#eval check_div "xy^2+1" ["xy+1", "y+1"] "xy^2-1" "2"
#eval check_div "x+y" ["y"] "y" "x" 
#eval check_div "x+y^2+y" ["xy-1", "y^2-1"] "y^2-1" "x+y+1"
#eval check_div "x^2y+xy^2+y^2" ["xy-1", "y^2-1"] "x^2y+xy^2-x+y^2-y-1" "x+y+1"

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

#eval check_s_polynomial "x" "x" "0"
#eval check_s_polynomial "xy" "x" "0"
#eval check_s_polynomial "xy^2" "x" "0"
#eval check_s_polynomial "xy^2" "z" "0"
#eval check_s_polynomial "xy^2+1" "z" "z"
#eval check_s_polynomial "xy^2+1" "x" "1"
#eval check_s_polynomial "x^3y^2-x^2y^3+x" "3x^4y+y^2" "-x^3y^3+x^2-1/3y^3"

#eval check_s_polynomial_grlex "x^3y^2-x^2y^3+x" "3x^4y+y^2" "-x^3y^3-1/3y^3+x^2"
#eval check_s_polynomial_grlex "x^3-2xy" "x^2-2y^2+x" "-x^2"

--#Test Groebner
private def check_groebner (input expected: List String): Except String String := 
  let parsed          := parse_list input
  let parsed_expected := parse_list expected
  let groebner := build_groebner_basis parsed
  AssertTrue (groebner == parsed_expected) s!"expected {parsed_expected}; actual {groebner}"

--#eval check_groebner ["x^3-2xy", "x^2-2y^2+x"] ["x^3-2xy", "x^2-2y^2", "-x^2", "-2xy", "-2y^2+x"]
#eval check_groebner ["xy^2+1", "x"] []
