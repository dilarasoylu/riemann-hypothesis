module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIdempotentWeightZeroSectionOfComponent
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IdemMulMemCusp
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
namespace GlobalTheory.Reg
private theorem evC_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (h : GenFrEx Xo c) (Z : Comp Xo c)
    (f g : Rul Xo c) : evC h Z (f * g) = evC h Z f * evC h Z g := by
  show evR Xo c (f * g) (genFr h Z) = evR Xo c f (genFr h Z) * evR Xo c g (genFr h Z)
  unfold evR evalAt
  split
  · exact map_mul _ _ _
  · simp

theorem exists_cusp_restrict_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (Z : Comp Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, ∃ g' ∈ Formalism.L2.PjFree.cusp Xo c U a n, evC h Z g' = evC h Z g ∧ ∀ Z', Z' ≠ Z → evC h Z' g' = 0 := by
  intro E _ _ _ H Dw l Xo c hL h hA r U hU Z a n g hg
  obtain ⟨χ, hχ, hidem, h1, h0⟩ := _root_.GlobalTheory.Reg.exists_idem_section E H Dw l Xo c hL h hA Z
  refine ⟨χ * g, GlobalTheory.Reg.IdemCusp.idem_mul_mem_cusp E H Dw l Xo c r U hU χ hχ hidem a n g hg, ?_, ?_⟩
  · rw [evC_mul' h Z, h1, _root_.one_mul]
  · intro Z' hZ'
    rw [evC_mul' h Z', h0 Z' hZ']
    simp
end GlobalTheory.Reg
end
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace GlobalTheory.Reg
theorem compSplit_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (hG : GenFrEx (T.Q.Xo j) T.Q.c), CompSplitSt h j hG := by
  intro D T h j hj hG Z w g
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  have hg : (g : T.R j) ∈ T.C j w := cutR_le T.C j w g.2
  obtain ⟨g', hg', h1, h0⟩ := exists_cusp_restrict_comp _ _ _ _ (T.Q.Xo j) T.Q.c hL hG (hA hG) _
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (fun σ hσ => h.unf j hj σ hσ) Z (wtA w) w.n (g : T.R j) hg
  have hm : g' ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]; exact hg'
  exact ⟨⟨g', hm⟩, h1, h0⟩
