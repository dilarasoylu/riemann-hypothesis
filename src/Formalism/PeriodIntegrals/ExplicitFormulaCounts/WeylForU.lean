module

public import Formalism.PeriodIntegrals.HwIrred
public import Formalism.PeriodIntegrals.UnitaryDense
public import Formalism.PeriodIntegrals.WeylForU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.DetSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.LowerInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.ModelMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.PolyExt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.TorusEigenvalueFormula
public import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGroupIntegrability.IsPositiveDefiniteMatrixCoefficientOfMemAlgA
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDense
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylProduct.WeylProd
import Formalism.LocalRingCardinality.Params

@[expose] public section
theorem modelIso_of : PI.PolyCoef → PI.UnitaryDense → PI.HwIrred → PI.ModelIso :=
  fun hp hu hh => PI.WMI.modelIso_of_steps (PI.WMI.polyExt_of hp hu) PI.WMI.lambda_integrality
    PI.WMI.torus_eigenvalue_formula PI.WMI.lower_triangular_invariance PI.WMI.model_map_equivariance PI.WMI.determinant_splitting_formula hh
noncomputable section
namespace PI.WeylForUWork
open Finset PI.UpqRep Formalism.BasicNotions
theorem denom_range (n : ℕ) :
    ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  apply PI.WeylProdWork.denom_eq

theorem row_fin (n : ℕ) (a : Fin n) :
    ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ j ∈ Ico ((a : ℕ) + 1) n, ((j : ℝ) - ((a : ℕ) : ℝ)) := by
  refine Finset.prod_nbij (fun b : Fin n => (b : ℕ)) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [Finset.mem_Ico]
    exact ⟨hb.2, b.isLt⟩
  · intro x _ y _ h
    exact Fin.ext h
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_Ico] at hj
    refine ⟨⟨j, hj.2⟩, ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hj.1⟩
  · intro b _
    rfl

theorem denom_fin (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  exact (Finset.prod_congr rfl (fun a _ => row_fin n a)).trans ((Fin.prod_univ_eq_prod_range (fun i : ℕ => ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ))) n).trans (denom_range n))

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW :=
  fun _ _ hij => Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)

theorem natW_cast {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.detShift := by
  have hN0 : 0 < N := Fin.pos i
  have hle : lam.w ⟨N - 1, by omega⟩ ≤ lam.w i :=
    lam.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))
  unfold DomWeight.natW DomWeight.detShift
  rw [dite_eq_left hN0]
  exact Int.toNat_of_nonneg (by omega)

theorem natW_cast_real {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℝ) = ((lam.w i : ℤ) : ℝ) - ((lam.detShift : ℤ) : ℝ) := by
  exact_mod_cast natW_cast lam i

theorem weylForU_of : PI.ModelIso → PI.NablaDim → PI.WeylForU := by
  intro hM hN N Λ H _ _ σ S hU hK
  obtain ⟨lam, hΛ, hdim⟩ := hM N Λ H σ S hU hK
  rw [hdim]
  have h2 : ((Module.finrank ℂ ↥(nablaSq ℂ N lam) : ℕ) : ℚ) =
      (∏ i : Fin N, ∏ j ∈ univ.filter (fun j : Fin N => i < j), (((lam.natW i : ℕ) : ℚ) -
        ((lam.natW j : ℕ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) /
      ∏ i : Fin N, ∏ j ∈ univ.filter (fun j : Fin N => i < j), (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := by
    rw [← Finset.prod_div_distrib]
    refine (hN N lam.natW (natW_anti lam)).trans (Finset.prod_congr rfl (fun i _ => ?_))
    rw [← Finset.prod_div_distrib, Finset.prod_filter]
  have h3 := congrArg (fun q : ℚ => (q : ℝ)) h2
  push_cast at h3
  rw [h3, denom_fin]
  congr 1
  refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => ?_))
  rw [natW_cast_real, natW_cast_real, hΛ a, hΛ b]
  ring
end PI.WeylForUWork
end
theorem weylForU_of : PI.ModelIso → PI.NablaDim → PI.WeylForU := PI.WeylForUWork.weylForU_of
theorem nablaDim_closed : PI.NablaDim := fun n nu h => Formalism.L2.G.Model.weyl_dualWeyl ℂ n nu h

theorem modelIso_closed : PI.ModelIso := modelIso_of _root_.PI.UnitaryGroupMassFormula.PolyCoef.polyCoef unitaryGroupDense_holds highest_weight_irreducible

theorem weylForU_closed : PI.WeylForU := _root_.PI.WeylForUWork.weylForU_of modelIso_closed nablaDim_closed
