module

public import Formalism.CharacterColumnKernels.StatGlobalModule
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.CupKillAdm
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.GenFin
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalConcreteOf
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RightIdealImageOfSurjective

@[expose] public section
noncomputable section
open Finset
namespace Formalism.NG
universe u v w x
theorem globalModule_of (hF : StatFinPres.{max u w, x}) : StatGlobalModule.{u, v, w, x} := by
  intro O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' _ hdet NN _ _ g₀ n hspan hφ π' ρπ hρπ α _ _ bl hbl
    ρk hsurj hblk _ hcard
  obtain ⟨m, P, ⟨eM⟩⟩ := hF R' NN g₀ n hspan
  have hφ' : ∀ x', p x' ∉ Z → ∃ φ : Coker P →ₗ[R'] EvalSp O d R' x', φ ≠ 0 := by
    intro x' hx
    obtain ⟨φ, hφ0⟩ := hφ x' hx
    refine ⟨φ.comp eM.symm.toLinearMap, fun h => hφ0 ?_⟩
    refine LinearMap.ext fun y => ?_
    have hy := LinearMap.congr_fun h (eM y)
    simpa using hy
  have hcard' : ((Fintype.card (Fin g₀) * ∑ k : α, Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
      Cardinal.mk (IsLocalRing.ResidueField O) := by
    rw [Fintype.card_fin]
    exact hcard
  refine (globalConcrete O X X' T T' Z p q b hT hZ d R' (Fin m) (Fin g₀) P (fun Θ => hdet (Fin g₀) Θ)
    hφ' π' ρπ hρπ α bl hbl ρk hsurj hblk hcard').trans
    (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  have hk := kerHomRect R' O (Fin m) (Fin g₀) {a // bl a = k} (ρk k).toRingHom P
  let eqv : (Coker P →ₗ[R'] LatQ O {a // bl a = k} (ρk k).toRingHom) ≃ₗ[O]
      (NN →ₗ[R'] LatQ O {a // bl a = k} (ρk k).toRingHom) :=
    { toFun := fun f => f.comp eM.toLinearMap
      invFun := fun f => f.comp eM.symm.toLinearMap
      map_add' := fun _ _ => LinearMap.ext fun _ => rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => rfl
      left_inv := fun f => LinearMap.ext fun y => congrArg f (eM.apply_symm_apply y)
      right_inv := fun f => LinearMap.ext fun y => congrArg f (eM.symm_apply_apply y) }
  exact hk.trans eqv.length_eq

theorem globalModule : StatGlobalModule := globalModule_of finPres
end Formalism.NG
open Classical
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
theorem resConst : StatResConst := by
  unfold StatResConst
  intro O _ _ X T hT f hf x y
  set g : T := ⟨f, hf⟩ - algebraMap O T (f x) with hg
  have hgnu : ¬ IsUnit g := by
    intro hu
    have := hu.map ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom)
    simp [hg] at this
  let ψ : T →+* IsLocalRing.ResidueField O :=
    (IsLocalRing.residue O).comp ((Pi.evalRingHom (fun _ : X => O) y).comp T.val.toRingHom)
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective z
    exact ⟨algebraMap O T c, by simp [ψ]⟩
  have hmax : (RingHom.ker ψ).IsMaximal := RingHom.ker_isMaximal_of_surjective ψ hsurj
  have hker : RingHom.ker ψ = IsLocalRing.maximalIdeal T := IsLocalRing.eq_maximalIdeal hmax
  have hgm : g ∈ RingHom.ker ψ := by
    rw [hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hgnu
  rw [RingHom.mem_ker] at hgm
  simp [ψ, hg, sub_eq_zero] at hgm
  exact hgm.symm

theorem rootsInt : StatRootsInt := by
  unfold StatRootsInt
  intro O _ _ _ P t α hP
  have hinj : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  have hmon : (P.map (algebraMap O (FractionRing O))).Monic := by
    rw [hP]
    exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hPm : P.Monic := by
    first
    | exact Polynomial.monic_of_injective hinj hmon
  have hint : ∀ i, ∃ b : O, algebraMap O (FractionRing O) b = α i := by
    intro i
    have hroot : Polynomial.eval₂ (algebraMap O (FractionRing O)) (α i) P = 0 := by
      rw [Polynomial.eval₂_eq_eval_map, hP, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    exact IsIntegrallyClosed.isIntegral_iff.1 ⟨P, hPm, hroot⟩
  choose β hβ using hint
  refine ⟨β, hβ, ?_⟩
  apply Polynomial.map_injective _ hinj
  rw [hP, Polynomial.map_prod]
  simp [hβ]

theorem lemma_five_three_holds : BlockRingDecompositionLemma := by
  unfold BlockRingDecompositionLemma
  intro O _ _ _ X d G _ _ _ t ht bl T D _ _ hTop Z NN _ _ g₀ n hspan hZ hcard
  unfold RingData.Top RingTop at hTop
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9, h10, -⟩ := hTop

  have hsum : ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} = Fintype.card d := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv bl)
  have hcard' : ((g₀ * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
      Cardinal.mk (IsLocalRing.ResidueField O) := by
    rw [hsum]; exact hcard

  have hmain := Formalism.NG.globalModule O X D.X' T D.T' Z D.p D.q D.b h1 (fun x _ => h2 x) d D.R' h3
    NN g₀ n hspan hZ D.π' D.ρπ h7 (Fin (t + 1)) bl h8 D.ρk h9 h10 hcard'
  exact hmain.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
