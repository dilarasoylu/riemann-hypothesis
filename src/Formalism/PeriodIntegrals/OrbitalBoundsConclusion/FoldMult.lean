module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MultiplicityMeasurability.MeasurableMult

@[expose] public section
section
open MeasureTheory
open scoped ENNReal NNReal
namespace PI.FoldMult
def FoldMult : Prop :=
  ∀ (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G), DiscreteTopology Γ →
  ∀ (Ω : Set G), IsCompact Ω → (1 : G) ∈ Ω →
    (∀ x : G, 1 ≤ Formalism.L2.SG.FoldBound.mult Γ Ω x) ∧
    (∀ x : G, Formalism.L2.SG.FoldBound.mult Γ Ω x < ⊤) ∧
    (∀ γ ∈ Γ, ∀ x : G, Formalism.L2.SG.FoldBound.mult Γ Ω (γ * x) = Formalism.L2.SG.FoldBound.mult Γ Ω x) ∧
    Measurable (Formalism.L2.SG.FoldBound.mult Γ Ω)
end PI.FoldMult
end
open PI.FoldMult.UnitaryGroupMassFormula
theorem overlapMultiplicityProperties : PI.FoldMult.FoldMult := by
  intro G _ _ _ _ _ _ _ Γ hΓ Ω hΩ h1
  exact ⟨fun x => one_le_mult Γ Ω h1 x, fun x => mult_lt_top Γ Ω hΩ x,
    fun γ hγ x => mult_mul_left Γ Ω γ hγ x, measurable_mult Γ Ω hΩ⟩
