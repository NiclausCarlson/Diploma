import Diploma.Polynomials.Polynomial

namespace polynomial
open algebra

def Polynomial.multideg [MonomialOrder $ Variables n ord] (p: Polynomial n ord): Variables n ord := 
  if p.size != 0 then p.min!.snd
  else get_variables n 

def Polynomial.lc [MonomialOrder $ Variables n ord] (p: Polynomial n ord): Rat :=
  if p.size != 0 then p.min!.fst
  else 0

def Polynomial.lm [MonomialOrder $ Variables n ord] (p: Polynomial n ord): Monomial n ord :=
  if p.size != 0 then (1, p.min!.snd)
  else (1, get_variables n) 

def Polynomial.lt [MonomialOrder $ Variables n ord] (p: Polynomial n ord): Monomial n ord :=
  if p.size != 0 then p.min!
  else (1, get_variables n)

def Polynomial.Lt [MonomialOrder $ Variables n ord] (p: Polynomial n ord): Polynomial n ord :=
  if p.size != 0 then Polynomial.single p.min!
  else Polynomial.single (1, get_variables n)

end polynomial
