Module[
  {i, j, L, Q, P},
  VerificationTest[
    getDomain@toMixed[Subscript[\[DoubleStruckCapitalE], {i}->{j}][L,Q,P]],
    {{i},{}},
TestID->"toMixed adds empty indices for closed components to domain"]]

Module[
  {i, j, L, Q, P},
  VerificationTest[
    getCodomain@toMixed[Subscript[\[DoubleStruckCapitalE], {i}->{j}][L,Q,P]],
    {{j},{}},
TestID->"toMixed adds empty indices for closed components to domain"]]

Module[
  { L, P, Q,
    EE = Subscript[\[DoubleStruckCapitalE], {{1,2},{3,4}}->{{1},{2,3,4}}][L,Q,P]
  },
  VerificationTest[
    toMixed@EE,
    EE,
TestID->"toMixed is null operation on expressions with closed domain"]]
