import Diploma.tests.Common
import Diploma.Polynomials.Parser
import Diploma.Polynomials.Groebner

open polynomial
open algebra

def sum (p₁ p₂: String): String :=
  toString (parse! p₁ + parse! p₂)
 
--# Test sum
#eval AssertEq (sum "1" "0")                        "1"
#eval AssertEq (sum "0" "1")                        "1"
#eval AssertEq (sum "0" "2")                        "2"
#eval AssertEq (sum "2" "0")                        "2"
#eval AssertEq (sum "2" "2")                        "4"
#eval AssertEq (sum "a" "0")                        "a"
#eval AssertEq (sum "a" "a")                        "2a"
#eval AssertEq (sum "2a" "a")                       "3a"
#eval AssertEq (sum "a^4" "a")                      "a^4+a"
#eval AssertEq (sum "3a^4" "a")                     "3a^4+a"
#eval AssertEq (sum "3a^4" "a^4")                   "4a^4"
#eval AssertEq (sum "3a^4b^2" "a^4")                "3a^4b^2+a^4"
#eval AssertEq (sum "3a^4b^2+a^4b^2+10c" "a^4+15c") "4a^4b^2+a^4+25c"

#eval AssertEq (sum "-b+1" "b+1") "2"
#eval AssertEq (sum "ab^2+1" "-ab^2+1") "2"


def sub (p₁ p₂: String): String :=
  toString (parse! p₁ - parse! p₂)

--# Test sub
#eval AssertEq (sub "1" "0")                        "1"
#eval AssertEq (sub "0" "1")                        "-1"
#eval AssertEq (sub "0" "2")                        "-2"
#eval AssertEq (sub "2" "0")                        "2"
#eval AssertEq (sub "2" "2")                        "0"
#eval AssertEq (sub "a" "0")                        "a"
#eval AssertEq (sub "a" "a")                        "0"
#eval AssertEq (sub "3a" "3a")                      "0"
#eval AssertEq (sub "2a" "a")                       "a"
#eval AssertEq (sub "a^4" "a")                      "a^4-a"
#eval AssertEq (sub "3a^4" "a")                     "3a^4-a"
#eval AssertEq (sub "3a^4" "a^4")                   "2a^4"
#eval AssertEq (sub "3a^4b^2" "a^4")                "3a^4b^2-a^4"
#eval AssertEq (sub "3a^4b^2+a^4b^2+10c" "a^4+15c") "4a^4b^2-a^4-5c"


def mul (p₁ p₂: String): String :=
  toString (parse! p₁ * parse! p₂)

--# Test mul
#eval AssertEq (mul "1" "0")                                  "0"
#eval AssertEq (mul "a" "a")                                  "a^2"
#eval AssertEq (mul "2a" "a")                                 "2a^2"
#eval AssertEq (mul "2a" "3a^5")                              "6a^6"
#eval AssertEq (mul "a+b" "a-b")                              "a^2-b^2"
#eval AssertEq (mul "a+b-c" "a-b")                            "a^2-ac-b^2+bc"
#eval AssertEq (mul "6a^7+18a^4b^2c^2-abc" "17a^18-14b^34+c") "102a^25+306a^22b^2c^2-17a^19bc-84a^7b^34+6a^7c-252a^4b^36c^2+18a^4b^2c^3+14ab^35c-abc^2"


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

#eval monomial_div_check "a" "a"                 true "1"
#eval monomial_div_check "2a" "a"                true "2"
#eval monomial_div_check "a^2" "a"               true "a"
#eval monomial_div_check "2a^2" "a"              true "2a"
#eval monomial_div_check "4a^3b^3c^8" "a"        true "4a^2b^3c^8"
#eval monomial_div_check "4a^3b^3c^8" "2a"       true "2a^2b^3c^8"
#eval monomial_div_check "4a^3b^3c^8" "2ab^3c^6" true "2a^2c^2"
#eval monomial_div_check "4a^3b^3c^8" "2ab^3c^6" true "2a^2c^2"

#eval monomial_div_check "a"       "b"  false ""
#eval monomial_div_check "4a^3b^3" "c"  false ""
#eval monomial_div_check "4b^3"    "a"  false ""
#eval monomial_div_check "4b^3"    "ab" false ""


private def reduce_lt_check (p₁ p₂: String) (expected_reduced: String) (expected_reducer: String): Except String String :=
  let q   := parse! expected_reduced
  let r   := parse! expected_reducer
  match reduce_lt (parse! p₁) (parse! p₂) with
    | none     => AssertTrue ((expected_reduced == "") ∧ (expected_reducer == "")) s!"expected values are no empty"
    | some res => match AssertTrue (res.reduced == q) 
                            s!"expected reduced {toString q} actual {toString res.reduced}" with
                    | Except.ok _ => AssertTrue (res.reducer == r) s!"expected reducer {toString r} actual {toString res.reducer}"
                    | Except.error err => Except.error err

#eval reduce_lt_check "a" "a" "0" "a"
#eval reduce_lt_check "a^2" "a" "0" "a^2"
#eval reduce_lt_check "2a" "a" "0" "2a"
#eval reduce_lt_check "ab" "a" "0" "ab"
#eval reduce_lt_check "2ab" "a" "0" "2ab"
#eval reduce_lt_check "b" "b" "0" "b"

#eval reduce_lt_check "2ab+c" "a" "c" "2ab"
#eval reduce_lt_check "2a^2b+c" "a" "c" "2a^2b"
#eval reduce_lt_check "2a^2bc+c" "a" "c" "2a^2bc"
#eval reduce_lt_check "2a^2b^4c+a+b+c" "a" "a+b+c" "2a^2b^4c"
#eval reduce_lt_check "3a^2b^4c+a+b+c" "ab" "a+b+c" "3a^2b^4c"
#eval reduce_lt_check "3a^2b^4c+a" "ab^3" "a" "3a^2b^4c"
#eval reduce_lt_check "ab^2+1" "ab+1" "-b+1" "ab^2+b"
#eval reduce_lt_check "-b+1" "b+1" "2" "-b-1"
#eval reduce_lt_check "2" "ab-1" "" ""
#eval reduce_lt_check "2" "b+1" "" ""

--# Test div
private def parse_list (ps: List String): List (Polynomial Dimension Ordering.lex) := ps.map parse!
def div (p: String) (ps: List String): DivisionResult Dimension Ordering.lex := 
  divide_many (parse! p) (parse_list ps)

private def check_div (p: String) (ps: List String) (poly: String) (remainder: String): Except String String :=
  let res := div p ps
  let p   := parse! poly
  let r   := parse! remainder
  match AssertTrue (res.p == p) s!"expected poly {toString p} actual {toString res.p}" with
    | Except.ok _ =>  AssertTrue (res.r == r) s!"expected remainder {toString r} actual {toString res.r}" 
    | Except.error err => Except.error err

#eval check_div "a^2" ["a"] "a^2" "0"
#eval check_div "ab^2+1" ["ab+1"] "ab^2+b" "-b+1"
#eval check_div "ab^2+1" ["ab+1", "b+1"] "ab^2-1" "2"
#eval check_div "a+b" ["b"] "b" "a" 
#eval check_div "a+b^2+b" ["ab-1", "b^2-1"] "b^2-1" "a+b+1"
#eval check_div "a^2b+ab^2+b^2" ["ab-1", "b^2-1"] "a^2b+ab^2-a+b^2-b-1" "a+b+1"
