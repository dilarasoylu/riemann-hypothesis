module

public import Formalism.HermitianLattices.StatementMass
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.FiniteDimensionalOfOrtho
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.GmapLocEqOfFrame
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsHermSemilocalLocRing
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapNeZeroOfMemHcompl
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.ExistsIsomFrame
public import Formalism.HermitianLattices.StatementLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.Development
public import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.StdLatEqSpan
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.UnimodLocalOfLocDual
public import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
public import Formalism.PeriodIntegrals.UnimodGenus

@[expose] public section
noncomputable section
open NumberField Module
namespace ReciprocityTheory.ChartRestriction.L3
open Formalism.HermitianLattices.Ext.L3 (isTotPosDef_of_ortho)
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
theorem exists_isom_loc (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (p : Ideal (𝓞 K)) (hp : p.IsMaximal)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p I) = Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  have hpos := isTotPosDef_of_ortho hK hs hI
  have hd : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpos x hne φ
    rw [hx, map_zero] at this
    simp at this
  obtain ⟨e, -, hspan, rfl, he⟩ := hI
  have hS : Formalism.HermitianLattices.Ext.L3.WA.IsHermSemilocal (Formalism.HermitianLattices.Ext.L3.WA.locRing p) :=
    { star_mem := fun _ ha => Formalism.HermitianLattices.Ext.L3.WA.star_mem_locRing hp.isPrime ha
      frac := Formalism.HermitianLattices.Ext.L3.WA.frac_locRing p
      unram := Formalism.HermitianLattices.Ext.L3.WA.unram_locRing hK hp
      principal := Formalism.HermitianLattices.Ext.L3.WA.principal_locRing hK hp
      unit_or := fun a ha κ hκ μ hna hμ => Formalism.HermitianLattices.Ext.L3.WA.unit_or_locRing hp.isPrime a ha κ hκ μ hna hμ }
  obtain ⟨g, hg, hge⟩ := WA.exists_isom_frame hS hs hd
    (Formalism.HermitianLattices.Ext.L3.WA.isSelfDualMod_loc hL hp.isPrime hu) e he
  exact ⟨g, hg, WA.gmap_loc_eq_of_frame hp.isPrime hu hspan he hg hge⟩
end ReciprocityTheory.ChartRestriction.L3
end
namespace PI.UG.W
open NumberField Module
open Formalism.HermitianLatticesTheory (locBasic_hcompl_not_mem locDual_mem_dualAt)
theorem isomLocStd : IsomLocStd := by
  intro E _ _ _ n hE N hN p hp hu
  have hs := hStd_isSymm E n
  have hI := stdLat_isOrtho E n
  have hFull : Submodule.IsFullLattice E N := by
    refine { toIsLattice := hN, span_eq_top := ?_ }
    let W := Submodule.span E (N : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let g : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : finrank E (Module.Dual E W) < finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have horth (y : Sp E n) (hy : y ∈ W) : hStd E n y (e x) = 0 := by
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, hy⟩) (LinearMap.mem_ker.mp hx)
      rw [← (LinearMap.isSymm_def.mp hs) (e x) y, hxy, map_zero]
    -- Localization preserves the ambient span, and self-duality puts the orthogonal vector in it.
    let : p.IsPrime := hp.isPrime
    have hloc {y : Sp E n}
        (hy : y ∈ Formalism.HermitianLatticesTheory.loc (K := E) p N) : y ∈ W := by
      obtain ⟨s, hs', hsy⟩ := hy
      have hs₀ : algebraMap (𝓞 E) E s ≠ 0 := by
        intro hzero
        have : s = 0 := IsFractionRing.injective (𝓞 E) E (by simpa using hzero)
        exact locBasic_hcompl_not_mem p s hs' (this ▸ p.zero_mem)
      exact (W.smul_mem_iff hs₀).mp
        (by rw [algebraMap_smul]; exact Submodule.subset_span hsy)
    have hxW : e x ∈ W := by
      apply hloc
      change Formalism.HermitianLatticesTheory.IsUnimodularAt (hStd E n) p N at hu
      rw [Formalism.HermitianLatticesTheory.IsUnimodularAt] at hu
      rw [← hu, locDual_mem_dualAt]
      intro y hy
      rw [horth y (hloc hy)]
      exact Submodule.zero_mem _
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hpos := Formalism.HermitianLattices.Ext.L3.isTotPosDef_of_ortho hE hs hI (e x)
      (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) φ
    simp [horth (e x) hxW] at hpos
  exact ReciprocityTheory.ChartRestriction.L3.exists_isom_loc hE hs hI hFull p hp hu
end PI.UG.W
theorem unimodular_genus_unique : PI.UnimodGenus :=
  PI.UG.W.unimodGenus_of PI.UG.W.unimodLocal PI.UG.W.isomLocStd
