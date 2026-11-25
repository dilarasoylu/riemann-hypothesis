module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FrameBasisMatrixOrthogonalProperties
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
public import Mathlib.Analysis.Complex.Conformal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsHeisenbergDerivativeLinearOperators
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FockOrthogonalDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmType
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponents
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubmoduleThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeCommutatorRelation
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDirectionalDerivFormulaAndSmooth
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Mathlib.Analysis.Matrix.Order
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RealAdeleExtAndStandardCharacterFormula
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SpanRealProjectionRationalPointsEqTop
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticRealPartVanish
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijectiveStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant

@[expose] public section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.exists_isArchimedeanAdeleChart_of_real_chart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ → (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) → (∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0) → ∃ σ : (D.what₂.Tau → ℂ) →+ AE D, Chart θ σ := by
  first | exact @GlobalTheory.FockCompare.RealChart.exists_chart
theorem _root_.GlobalTheory.T.exists_real_chart_infiniteAdeles_cmType : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) → ∃ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ ∧ (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) ∧ ∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0 := by
  first | exact @GlobalTheory.FockCompare.exists_real_chart
end
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
namespace GlobalTheory.FockCompare
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}
theorem exists_chart (hθ : IsInfFam θ) : ∃ σ, Chart θ σ := by
  obtain ⟨ρ, h1, h2, h3⟩ := GlobalTheory.T.exists_real_chart_infiniteAdeles_cmType D θ hθ (GlobalTheory.T.cmType_restrict_realSubfield_infinitePlace_bijective D)
  exact GlobalTheory.T.exists_isArchimedeanAdeleChart_of_real_chart D θ hθ ρ h1 h2 h3
