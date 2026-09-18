import RiemannRoch

/-!
# Public API smoke test

This file is compiled directly by CI. It intentionally imports only the library
root and checks representative declarations from the completed projective-line
and twisting-sheaf infrastructure. Its purpose is to catch accidental root
export or public-name regressions without making test code part of the library.
-/

open RiemannRoch.ProjectiveLine

#check scheme
#check standardOpenCover
#check standardNormalizedCechComplex
#check twistingSheaf
#check twistingSheafZeroIso
#check twistingSheafTensorIso
#check twistingSheafTensorNegIso
#check twistingSheafTensorInverse
#check restrictSchemeModuleSheafTensorIso
