import Diploma.Polynomials.Parser
import Diploma.tests.Common
import Diploma.Order.MonomialOrder

open polynomial
open algebra

#eval ExpectTrue $ Order.lex (parseMonomial! "x0").snd (parseMonomial! "x0^2").snd
#eval ExpectTrue $ Order.lex (parseMonomial! "x0x1").snd (parseMonomial! "x0^2").snd
#eval ExpectTrue $ Order.lex (parseMonomial! "x").snd (parseMonomial! "xy").snd

#eval ExpectTrue $ Order.grlex (parseMonomial! "x0").snd (parseMonomial! "x0^2").snd
#eval ExpectTrue $ Order.grlex (parseMonomial! "x0^2").snd (parseMonomial! "x0x1x2").snd
#eval ExpectTrue $ Order.grlex (parseMonomial! "x0x1x2").snd (parseMonomial! "x0^5").snd
