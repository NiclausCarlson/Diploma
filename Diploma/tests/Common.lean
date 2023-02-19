
def AssertEq {α:Type} [BEq α] [ToString α] (a b: α): Except String String :=
  if (a != b) then Except.error ("Values: " ++ (toString a) ++ " and " ++
                                (toString b) ++ " not equals")
  else Except.ok "Ok"


