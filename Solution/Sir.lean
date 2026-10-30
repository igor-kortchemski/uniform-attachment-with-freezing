module

public import Freezing1

/-!
# Solution for the SIR interface

The compared declarations are proved in the development imported here: `Freezing1.SIRPhysicalLimits`
(Theorem `thm:SIRlocallimit` (I), (II) and Theorem `thm:SIR` (I)(a), (II)(a), (II)(b) for the physical
full-contact epidemic), `Freezing1.SIRPhysicalFiniteLimits` (Theorem `thm:SIR` (I)(b)), and, for the two
extra sanity targets, `Freezing1.SIRPoissonFirstArrival` (`PoissonContact.first_law`) and
`Freezing1.SIRPhysicalLaws` (`PoissonSIRData.treePathLaw_eq`), together with the modules they import
(`MainSIREmbedded`, `MainSIRFluid`, `SIRStrongCounts`, `MainSIRUniformSamplesStrong`,
`MainSIRStrongMaximum`, `MainSIRUniformSamplesFinite`, `SIRPoissonFullContactLaw`, ...). This module
does not import `Challenge`; the two declaration environments are compared separately by Comparator.
-/
