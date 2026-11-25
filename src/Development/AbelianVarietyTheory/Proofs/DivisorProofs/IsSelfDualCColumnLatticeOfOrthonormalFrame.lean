module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj

noncomputable section

namespace GlobalTheory.FunObj.OrthoFrame

alias isSelfDualC_colLat_of_orthonormal := _root_.GlobalTheory.FunObj.VecEx.isSelfDualC_colLat

end GlobalTheory.FunObj.OrthoFrame
