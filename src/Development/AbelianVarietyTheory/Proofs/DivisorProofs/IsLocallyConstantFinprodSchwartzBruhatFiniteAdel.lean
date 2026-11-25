module

import Development.WeilBound.ThetaLifts.ConeHypotheses.IsLocallyConstantFinprodEvalV
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

namespace GlobalTheory.WeilM
open Filter Topology

theorem isLocallyConstant_finprod_evalV {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hcof : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    IsLocallyConstant (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  apply PositivityTheory.ThKG.isLocallyConstant_finprod_evalV <;> assumption

end GlobalTheory.WeilM
