distinctValues::usage = "distinctValues[f][X] returns the size of f(X), that is,
the number of distinct values f attains on X."
distinctValues[f_][S_] := Length[Union[f/@S]]

getFibres[f_][S_] := GatherBy[S,f]
