# GDO #

## Summary ##
Mathematica implementation of Perturbed Gaussian generating functions for
universal knot invariants by Dror Bar-Natan and Roland van der Veen, September
2021\. (Standard version)

Additional code implementing a trace operator by Jesse Frohlich.

## Code clean-up & test suite to do ##
- [X] Consolidate all GDO and trace code to one repository.
- [ ] Define types and descriptions for each function.
  - [X] `coinv`
  - [X] `trGenFunc`
  - [X] `trDeg`
  - [X] `ScaleByLambda`
  - [ ] `getDomain`
  - [ ] `getCodomain`
  - [ ] `getExponent`
  - [ ] `getIndices`
  - [ ] `isolateSubscripts`
  - [ ] `getPLength`
  - [ ] `TruncateToDegree`
  - [ ] `SXForm`
  - [ ] `RVT`
  - [ ] `Writhe`
  - [ ] `Unwrithe`
  - [ ] `Reindex`
  - [ ] `cR`
  - [ ] `cRi`
  - [ ] `CC`
  - [ ] `CCi`
  - [ ] `CCn`
  - [ ] `ZFramed`
  - [ ] `Z`
  - [ ] `Zdeg`
  - [ ] `Ztr`
  - [ ] `ptr`
- [ ] Build MUnit test files for each file.
- [ ] Add code coverage tracker to test suite ([reference on code coverage in
     mathematica™](https://mathematica.stackexchange.com/questions/257309/what-are-some-approaches-to-measuring-code-coverage)).
