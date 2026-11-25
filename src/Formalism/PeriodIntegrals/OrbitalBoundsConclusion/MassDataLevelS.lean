module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelSOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.TypedNeOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLeMaximalCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LevelCongruenceTypedPlaces
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.CMInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.EvalVOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatAdapted
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.UnipotentIntegralInLevel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocFrom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uGrpHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uLeKfHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge

@[expose] public section
noncomputable section
namespace MassDataLevelSSteps
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
section
open Formalism.L2.SG.Volumes
theorem globFromParts_holds : GlobFromParts := by
  intro hLS h1 h2 h3 h4 D X hb _ _ w
  obtain ⟨hCM, hJ⟩ := h1 X
  obtain ⟨T, hT⟩ := h2 X w
  obtain ⟨ΛX, ΛW, ΛY, hA, hK⟩ := h3 X w
  obtain ⟨-, -, hHf, -, -, hNf, hSf, -⟩ := X.measW_norm w
  have key := (hLS X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hJ hJ D.R.rS (frameOf X w) T hT
    ΛX ΛW ΛY hA (X.measW w).μNf hNf (X.measW w).μHf hHf).2 (X.measW w).μSf ⟨hSf, h4 X w⟩
  simp only [KS, NO, KH, Subgroup.mem_inf, hK, SetLike.coe_mem, true_and] at key
  unfold muSf muNf muHf
  rw [← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal key
end
theorem clauses_word (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) {D : D7} (X : HidaSetting D)
    (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hT : X.MeasTie hb) (hL : X.LevelSubgroupNormalized) (w : D.what₂.Word) :
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSv X w p = muNf X w * muHf X w ∧
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSvpp X hb w p = muNf X w * muHfpp X hb w := by
  have hne : ∏ p : TypX X, muSv X w p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => hA X hb hT hL w p)
  have hS := hB X hb hT hL w
  have hR := hC X hb hK hT hL w
  refine ⟨?_, ?_⟩
  · rw [div_mul_cancel₀ _ hne, hS]
  · rw [hS, div_mul_eq_mul_div, div_eq_iff hne]
    linear_combination (-muNf X w) * hR

theorem inLevelSAt_of (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hH
  obtain ⟨hT, hL, -, -⟩ := hH
  obtain ⟨h1, h2⟩ := clauses_word hA hB hC X hb hK hT hL u
  obtain ⟨h3, h4⟩ := clauses_word hA hB hC X hb hK hT hL u'
  exact ⟨h1, h2, h3, h4⟩
end
section
open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes
theorem inLevelSAt_of_parts (hLS : LevelSAll) (a1 : KSpCompact) (a2 : KSpOpen) (b1 : CMInst) (b2 : FrameStd)
    (b3 : LatAdapted) (b4 : ProdNH) (b5 : GlobFromParts) (c1 : HaarIdxLoc) (c2 : HaarIdxGlob) (c3 : LocLevi)
    (c4 : GlobProd) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  inLevelSAt_of (typedNe_of a1 a2) (b5 hLS b1 b2 b3 b4) (ratioH_of c1 c2 c3 c4)
end
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
theorem finiteDimensional_of_numberField (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : FiniteDimensional F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

theorem kSpCompact_holds : KSpCompact := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isClosed_Ssub p.1 X.B.I.cm.sig X.B.I.J (frameOf X w)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (LatTop.isCompact_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J)

theorem kSpOpen_holds : KSpOpen := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isOpen_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J).preimage
    continuous_subtype_val
end
end MassDataLevelSSteps
namespace MassDataLevelSSteps.ProdW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes MeasureTheory NumberField IsDedekindDomain Topology PI.AdicCompletionValuation
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
theorem isClosed_stabT (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R]
    {a : ℕ} (X0 : Fin a → Fin n → E) :
    IsClosed ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) := by
  have hcont : Continuous fun g : HA R σ J => g • ratTup (F := F) R X0 := by
    show Continuous fun g : HA R σ J => actTup R (HA.mat R σ J g) (ratTup (F := F) R X0)
    unfold actTup HA.mat
    refine continuous_pi fun b => Continuous.matrix_mulVec ?_ continuous_const
    exact Units.continuous_val.comp
      (continuous_subtype_val : Continuous fun g : HR R σ J => (g : GL (Fin n) (R ⊗[F] E)))
  have : ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) =
      {g | g • ratTup (F := F) R X0 = ratTup (F := F) R X0} := by
    ext g
    exact MulAction.mem_stabilizer_iff
  rw [this]
  exact isClosed_eq hcont continuous_const

instance secondCountable_HAf : SecondCountableTopology (HA (Af F) σ J) :=
  PI.VolStabSW.TopoAF.secondCountable_HA_of (Af F) σ J

theorem prodNH_of {r : ℕ} (P : Frame E n r) (M : MeasW σ J P) (hM : M.IsTextNorm) :
    IsProdNH F E σ n J (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P) M.μSf M.μNf M.μHf := by
  obtain ⟨-, -, hH, -, -, -, -, -, -, -, hS⟩ := hM
  have hcl : IsClosed ((Hsub (Af F) σ J P : Subgroup (HA (Af F) σ J)) : Set (HA (Af F) σ J)) :=
    isClosed_stabT σ J (Af F) (tupH P)
  have : LocallyCompactSpace (Hsub (Af F) σ J P) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have := hH
  have : SecondCountableTopology (HA (Af F) σ J) := secondCountable_HAf σ J
  have : SecondCountableTopology (Hsub (Af F) σ J P) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : WeaklyLocallyCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : IsFiniteMeasureOnCompacts M.μHf := inferInstance
  have : IsLocallyFiniteMeasure M.μHf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  have : SigmaFinite M.μHf := sigmaFinite_of_locallyFinite
  have : SFinite (amb M.μHf) := inferInstance
  have hmul : Measurable fun p : HA (Af F) σ J × HA (Af F) σ J => p.1 * p.2 := measurable_mul
  intro f hf
  have e1 : ∫⁻ k, f (k : HA (Af F) σ J) ∂M.μSf = ∫⁻ x, f x ∂(amb M.μSf) :=
    (lintegral_map hf measurable_subtype_coe).symm
  rw [e1, hS, lintegral_map hf hmul, lintegral_prod (fun p : HA (Af F) σ J × HA (Af F) σ J => f (p.1 * p.2)) (hf.comp hmul).aemeasurable]
  have hin : Measurable fun x : HA (Af F) σ J => ∫⁻ y, f (x * y) ∂(amb M.μHf) :=
    Measurable.lintegral_prod_right' (f := fun p : HA (Af F) σ J × HA (Af F) σ J => f (p.1 * p.2))
      (hf.comp hmul)
  rw [lintegral_map hin measurable_subtype_coe]
  refine lintegral_congr fun m => ?_
  exact lintegral_map (hf.comp (measurable_const_mul _)) measurable_subtype_coe

end MassDataLevelSSteps.ProdW

namespace MassDataLevelSSteps

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

theorem prodNH_holds : ProdNH := by
  intro D X w
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  exact ProdW.prodNH_of X.B.I.cm.sig X.B.I.J _ (X.measW w) (X.measW_norm w)

end MassDataLevelSSteps
namespace MassDataLevelSSteps
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct
open Matrix
section
variable {D : D7} (X : HidaSetting D)
theorem g_cast_ne_zero : (X.B.g : X.B.I.F) ≠ 0 := by
  rw [X.g_eq]
  push_cast
  exact mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)

theorem ginv_int (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (hv : v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1)) :
    (algebraMap X.B.I.F (Fv X.B.I.F v) ((X.B.g : X.B.I.F)⁻¹)) ∈ v.adicCompletionIntegers X.B.I.F := by
  rw [mem_typSet X.B.I.F _ _ (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero] at hv
  unfold IsTyped at hv
  rw [not_or] at hv
  have hg : ((X.B.g : 𝓞 X.B.I.F)) ∉ v.asIdeal := by
    rw [X.g_eq]
    push_cast
    intro h
    rcases v.isPrime.mem_or_mem h with h | h
    exacts [hv.1 h, hv.2 h]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : algebraMap X.B.I.F (Fv X.B.I.F v) ((X.B.g : X.B.I.F)⁻¹) =
      (((X.B.g : X.B.I.F)⁻¹ : X.B.I.F) : v.adicCompletion X.B.I.F) := rfl
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have : v.valuation X.B.I.F (X.B.g : X.B.I.F) = 1 := by
    rw [show (X.B.g : X.B.I.F) = algebraMap (𝓞 X.B.I.F) X.B.I.F (X.B.g : 𝓞 X.B.I.F) by simp,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hg]
  rw [this, inv_one]
end

theorem smul_latLoc {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (hv : v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1))
    (u : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)
    (hu : u ∈ latLoc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    (fun i => algebraMap X.B.I.F (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((X.B.g : X.B.I.F)⁻¹) * u i) ∈
      latLoc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have := Submodule.smul_mem _ (⟨_, ginv_int X v hv⟩ : v.adicCompletionIntegers X.B.I.F) hu
  convert this using 1
  funext i
  rw [Pi.smul_apply, IsScalarTower.algebraMap_apply X.B.I.F (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E),
    ← Algebra.smul_def]
  rfl

theorem kgLoc_holds : KgLoc := by
  intro D X hb κ hκ hT
  refine ⟨hκ, fun y hy => ?_⟩
  let c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := algebraMap X.B.I.F _ ((X.B.g : X.B.I.F)⁻¹)
  refine ⟨fun i => c * ((X.B.I.fmat κ - 1) *ᵥ y) i, ?_, ?_⟩
  · apply PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective
    intro v
    have hy' := PI.FinKW.LocTo.mem_local_lattice_iff X.B.I y hy v
    have hmat : (X.B.I.fmat κ).map (PI.FinKW.psiV X.B.I v) =
        ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ)) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) := by
      change _ = (((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.tf X.B.I hb κ) :
        GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map
          (tensMap (E := X.B.I.E) (evalV X.B.I.F v))
      rw [PI.MassDataKppVolLemmas.Bridge_mat X.B.I hb κ, Matrix.map_map]
      rfl
    have hvec : PI.FinKW.vecV X.B.I v (fun i => c * ((X.B.I.fmat κ - 1) *ᵥ y) i) =
        fun i => algebraMap X.B.I.F (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((X.B.g : X.B.I.F)⁻¹) *
          ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ)) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
            PI.FinKW.vecV X.B.I v y) i := by
      funext i
      simp only [PI.FinKW.vecV, map_mul, c, AlgHom.commutes]
      congr 1
      have h1 := RingHom.map_mulVec (PI.FinKW.psiV X.B.I v).toRingHom (X.B.I.fmat κ - 1) y i
      rw [← hmat, ← Matrix.map_one (PI.FinKW.psiV X.B.I v).toRingHom (map_zero _) (map_one _)]
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b)] at h1
      exact h1
    rw [hvec]
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · have e := hT ⟨v, hv⟩
      simp only at e
      rw [e]
      have : ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (1 : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :
          GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = 1 := rfl
      rw [this, sub_self, Matrix.zero_mulVec]
      simp only [Pi.zero_apply, mul_zero]
      exact Submodule.zero_mem _
    · apply smul_latLoc X v hv
      have hK := compK_holds X v (finHA X hb κ) (finHA_mem_Kf X hb κ hκ)
      have hm := (hK (PI.FinKW.vecV X.B.I v y)).1 hy'
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact Submodule.sub_mem _ hm hy'
  · funext i
    simp only [Pi.smul_apply, smul_eq_mul, c, ← mul_assoc]
    rw [show ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = algebraMap X.B.I.F _ (X.B.g : X.B.I.F) by simp,
      ← map_mul, mul_inv_cancel₀ (g_cast_ne_zero X), map_one, one_mul]

theorem globProd_of_k2LocT (ht : LevelCongruenceTypedPlaces) : GlobProd := globProd_of_loc kgLoc_holds ht
section
open Classical
section Idem

variable {D : D7} (X : HidaSetting D)

def idemAf (p : HeightOneSpectrum (𝓞 X.B.I.F)) : Af X.B.I.F :=
  RestrictedProduct.mk (fun v => if v = p then (1 : Fv X.B.I.F v) else 0)
    (Filter.Eventually.of_forall (fun v => by
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _))

theorem idemAf_int (p : HeightOneSpectrum (𝓞 X.B.I.F)) : idemAf X p ∈ Formalism.UG.intAd X.B.I.F := by
  intro v
  show (if v = p then (1 : Fv X.B.I.F v) else 0) ∈ v.adicCompletionIntegers X.B.I.F
  split_ifs
  · exact one_mem _
  · exact zero_mem _

def idemT (p : HeightOneSpectrum (𝓞 X.B.I.F)) : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
  ⟨(1 : X.B.I.E) ⊗ₜ[X.B.I.F] idemAf X p,
    Subring.subset_closure (Or.inr ⟨⟨idemAf X p, idemAf_int X p⟩, rfl⟩)⟩

theorem psiV_idemT (p v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    PI.FinKW.psiV X.B.I v ((idemT X p : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      if v = p then 1 else 0 := by
  show (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV X.B.I.F v) (AlgHom.id X.B.I.F X.B.I.E))
      ((Algebra.TensorProduct.comm X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F))
        ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] idemAf X p)) = _
  rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have he : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV X.B.I.F v (idemAf X p) = if v = p then 1 else 0 := rfl
  rw [he]
  split_ifs
  · exact Algebra.TensorProduct.one_def.symm
  · exact TensorProduct.zero_tmul _ _

section
variable (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) (v : HeightOneSpectrum (𝓞 X.B.I.F))
theorem fmat_psiV :
    (X.B.I.fmat x).map (PI.FinKW.psiV X.B.I v) =
      ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
        (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb x)) : GL (Fin X.B.I.n) _) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) := by
  change _ = (((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.tf X.B.I hb x) :
    GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map
      (tensMap (E := X.B.I.E) (evalV X.B.I.F v))
  rw [PI.MassDataKppVolLemmas.Bridge_mat X.B.I hb x, Matrix.map_map]
  rfl

theorem psiV_mulVec (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (i : Fin X.B.I.n) :
    PI.FinKW.psiV X.B.I v (((X.B.I.fmat x - 1) *ᵥ w) i) =
      ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
        (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb x)) : GL (Fin X.B.I.n) _) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
          PI.FinKW.vecV X.B.I v w) i := by
  rw [← fmat_psiV X hb x v]
  have h := RingHom.map_mulVec (PI.FinKW.psiV X.B.I v).toRingHom (X.B.I.fmat x - 1) w i
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  congr 1
  ext a b
  simp [Matrix.sub_apply, Matrix.one_apply]
end

end Idem

theorem level_congruence_typed_places : LevelCongruenceTypedPlaces := by
  intro D X hb hK hL κ hκ hO hloc
  classical
  choose κ' hκ' heq using hloc
  have decomp : ∀ w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F,
      (X.B.I.fmat κ - 1) *ᵥ w = ∑ p : TypX X, idemT X p.1 • ((X.B.I.fmat (κ' p) - 1) *ᵥ w) := by
    intro w
    funext i
    rw [← sub_eq_zero]
    apply PI.FinKW.local_vector_injective X.B.I
    intro v

    rw [map_sub, psiV_mulVec X hb κ v w i, Finset.sum_apply, map_sum]
    simp only [Pi.smul_apply]
    have hs : ∀ p : TypX X, PI.FinKW.psiV X.B.I v ((idemT X p.1 • ((X.B.I.fmat (κ' p) - 1) *ᵥ w)) i) =
        (if v = p.1 then 1 else 0) * ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb (κ' p))) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
            PI.FinKW.vecV X.B.I v w) i := by
      intro p
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, psiV_idemT, psiV_mulVec X hb (κ' p) v w i]
    simp only [Pi.smul_apply] at hs
    rw [Finset.sum_congr rfl (fun p _ => hs p)]
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · rw [Finset.sum_eq_single (⟨v, hv⟩ : TypX X)]
      · rw [if_pos rfl, one_mul, ← heq ⟨v, hv⟩, sub_self]
      · intro p _ hp
        rw [if_neg (fun h => hp (Subtype.ext h.symm)), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero (fun p _ => by rw [if_neg (fun h => hv (by rw [h]; exact p.2)), zero_mul])]
      rw [hO v hv]
      have : ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (1 : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :
          GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = 1 := rfl
      rw [this, sub_self, Matrix.zero_mulVec, Pi.zero_apply, sub_zero]
  have hmem : ∀ (S : Set (Formalism.L2.SG.HidaSetting.VA X.B.I)) (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
      (∀ p : TypX X, InMod X.B.I X.B.g S ((X.B.I.fmat (κ' p) - 1) *ᵥ w)) →
        InMod X.B.I X.B.g S ((X.B.I.fmat κ - 1) *ᵥ w) := by
    intro S w h
    unfold InMod at h ⊢
    rw [decomp w]
    exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (h p))
  refine ⟨hκ, ?_, ?_, ?_⟩
  · exact fun a => hmem _ _ (fun p => (hκ' p).2.1 a)
  · exact hmem _ _ (fun p => (hκ' p).2.2.1)
  · exact fun i => hmem _ _ (fun p => (hκ' p).2.2.2 i)

theorem globProd_holds : GlobProd := globProd_of_k2LocT level_congruence_typed_places
end
end
section
open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
abbrev levelSAll_holds := @_root_.level_s_all_split

theorem inLevelSAt_holds :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  inLevelSAt_of_parts levelSAll_holds kSpCompact_holds kSpOpen_holds cmInst_holds frameStd_holds
    latAdapted_holds prodNH_holds globFromParts_holds haarIdxLoc_holds haarIdxGlob_holds locLevi_holds
    globProd_holds
end
end MassDataLevelSSteps
end
alias level_s_at_instance := _root_.MassDataLevelSSteps.inLevelSAt_holds
