module

public import Formalism.GaussJetBounds.StatementN
public import Formalism.GaussJetBounds.StatementI
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights
def IntOp : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type) (Th : MvPowerSeries ι K),
    JetsIntegral Th → ∀ P : MvPolynomial ι K, (∀ n, ‖AddMonoidAlgebra.coeff P n‖ ≤ 1) →
      ‖jetPair P Th‖ ≤ 1
end Formalism.DworkPowerSeriesWeights
end
universe u
namespace Formalism.DworkPowerSeriesWeights
theorem intOp : IntOp.{u} := by
  unfold IntOp
  intro K _ _ ι Th hTh P hP
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro κ _
  rw [mul_assoc, norm_mul]
  exact mul_le_one₀ (hP κ) (norm_nonneg _) (hTh κ)
