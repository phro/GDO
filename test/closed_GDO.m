Module[
  {i, j, L, Q, P},
  VerificationTest[
    getDomain@toMixed[GDO[{i}->{j}][L,Q,P]],
    {{i},{}},
TestID->"toMixed adds empty indices for closed components to domain"]]

Module[
  {i, j, L, Q, P},
  VerificationTest[
    getCodomain@toMixed[GDO[{i}->{j}][L,Q,P]],
    {{j},{}},
TestID->"toMixed adds empty indices for closed components to domain"]]

Module[
  { L, P, Q,
    EE = GDO[{{1,2},{3,4}}->{{1},{2,3,4}}][L,Q,P]
  },
  VerificationTest[
    toMixed@EE,
    EE,
TestID->"toMixed is null operation on expressions with closed domain"]]

Module[
  { L, P, Q,
    EE = GDO[{{1,2},{3,4}}->{{1},{2,3,4}}][L,Q,P]
  },
  VerificationTest[
    getDomain@addClosedDomain[{2,5}]@EE,
    {{1,2},{2,3,4,5}},
TestID->"addClosedDomain adds new components to GDO"]]

Module[
  { L, P, Q,
    EE = GDO[{{1,2},{3,4}}->{{1},{2,3,4}}][L,Q,P]
  },
  VerificationTest[
    addClosedDomain[{3}]@EE,
    EE,
TestID->"addClosedDomain is identity when domain is already present."]]

Module[
  { L, P, Q,
    EE = GDO[{{1,2},{3,4}}->{{1},{2,3,4}}][L,Q,P]
  },
  VerificationTest[
    getCodomain@addClosedCodomain[{4,5,6}]@EE,
    {{1},{2,3,4,5,6}},
TestID->"addClosedCodomain adds new components to GDO"]]

Module[
  { L, P, Q,
    EE = GDO[{{1,2},{3,4}}->{{1},{2,3,4}}][L,Q,P]
  },
  VerificationTest[
    addClosedCodomain[{3}]@EE,
    EE,
TestID->"addClosedCodomain is identity when codomain is already present."]]

Module[
        {i = "i", j = "j", k = "k"},
        VerificationTest[
                closeComponent[i][{{i, j, k},{1, 2, 3}}],
                {{j, k},{1, 2, 3, i}},
TestID->"closeComponent moves indices from open to closed."]]
