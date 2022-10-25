distinctValues::usage = "distinctValues[f][X] returns the size of f(X), that is,
the number of distinct values f attains on X."
distinctValues[f_][S_] := Length[Union[f/@S]]

getFibres[f_][S_] := GatherBy[S,f]

subinvariantQ::usage = "subinvariantQ[f][g][X] returns true if each fibre of g
is a subset of some fibre of f, that is, if f is a weaker invariant than g."
subinvariantQ[f_][g_][S_List] := 
