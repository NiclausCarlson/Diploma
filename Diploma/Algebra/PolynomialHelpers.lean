import Diploma.Polynomials.DegsFunctions

import Mathlib.Data.Vector

namespace polynomial
open Vector algebra ordering 
     
theorem minus_lt [MonomialOrder $ Variables n ord] 
        (p: Polynomial n ord) (not_empty: p.isEmpty = false): m_cmp p.lt (p - p.Lt).lt == Ordering.lt := 
  by
    simp [Polynomial.Lt, Polynomial.lt, not_empty]
    split
    simp [Polynomial.invert_sign, Polynomial.add]
    sorry
    sorry

end polynomial
