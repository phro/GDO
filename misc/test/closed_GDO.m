Module[
        {
                dominfo       = {1,2}->{3},
                dominfoClosed = {{1,2},{}}->{{},{3}},
                exp1          = 1/2x + 1/2y,
                exp2          = (x+y)/2
        },
        VerificationTest[
                exp1//CF,
                exp2//CF,
TestID->"Ensure two simple expressions are deemed equal."];
        VerificationTest[
                GDO[dominfo][exp1,0,1]//CF,
                GDO[dominfo][exp2,0,1]//CF,
TestID->"GDO elements with simple equivalent terms are deemed equal."];
        VerificationTest[
                GDO[dominfoClosed][exp1,0,1]//CF,
                GDO[dominfoClosed][exp2,0,1]//CF,
TestID->"Closed GDO elements with simple equivalent terms are deemed equal."]]

Module[
        {
                exp1 = (
                        a[3] A[1] A[2] α[1] +
                        a[3] A[1] A[2] α[2] -
                        t[3] β[1] -
                        t[3] β[2] +
                        t[3] A[1] A[2] β[1] +
                        t[3] A[1] A[2] β[2]
                )/(A[1] A[2]),
                exp2 = α[1] a[3] + α[2] a[3] +
                        β[1] t[3] + β[2] t[3] -
                        (t[3] β[1])/(A[1] A[2]) -
                        (t[3] β[2])/(A[1] A[2]),
                gdo1,
                gdo2,
                gdoClosed1,
                gdoClosed2
        },
        gdo1 = GDO[{{1,2},{}}->{{},{3}}][exp1,0,1];
        gdo2 = GDO[{{1,2},{}}->{{},{3}}][exp2,0,1];
        gdoClosed1 = GDO[{1,2}->{3}][exp1,0,1];
        gdoClosed2 = GDO[{1,2}->{3}][exp2,0,1];
        VerificationTest[
                exp1 // Expand,
                exp2 // Expand,
TestID->"two test expressions are equivalent"];
        VerificationTest[
                gdo1//CF,
                gdo2//CF,
TestID->"GDO elements with equivalent terms are deemed equal"];
        VerificationTest[
                gdoClosed1//CF,
                gdoClosed2//CF,
TestID->"Closed GDO elements with equivalent terms are deemed equal"]]

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
