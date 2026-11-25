module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexAcyclicIffQuasiIsoCechAug
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGrFreeFiniteAndExactAt
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsGradedMapLinearCombination
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar

@[expose] public section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
namespace GlobalTheory
theorem finite_cycles_of_finite_homology {R : Type} [Ring R] {α : Type} {c : ComplexShape α}
    (K : HomologicalComplex (ModuleCat.{0} R) c) (i j : α) (hij : c.prev j = i)
    [Module.Finite R (K.X i)] [Module.Finite R (K.homology j)] :
    Module.Finite R (K.cycles j) := by
  have hex : (ShortComplex.mk (K.toCycles i j) (K.homologyπ j)
      (K.toCycles_comp_homologyπ i j)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j hij)
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex
  exact Module.Finite.of_exact hex
    ((ModuleCat.epi_iff_surjective (K.homologyπ j)).1 inferInstance)

theorem finite_cechHomology_of_finite_cubeHomology (ι : Type) [LinearOrder ι] (R : Type)
    [CommRing R] [IsNoetherianRing R] (A : Cube.{0} ι R) (h₀ : Module.Finite R (A.obj ∅))
    (h : ∀ p, Module.Finite R ((cubeComplex A).homology p)) (p : ℕ) :
    Module.Finite R ((cechComplex A).homology p) := by
  cases p with
  | zero =>
    have h1 := h 1
    have h2 : Module.Finite R ((cubeComplex A).X 0) :=
      Module.Finite.equiv (Cube.termZeroEquiv A).symm
    have h3 := finite_cycles_of_finite_homology (cubeComplex A) 0 1 (by simp)
    exact Module.Finite.equiv
      (cubeCyclesIso A 1 ≪≫ (cechHomologyZeroIso A).symm).toLinearEquiv
  | succ p =>
    have h1 := h (p + 2)
    exact Module.Finite.equiv (cechHomologySuccIso A p).symm.toLinearEquiv
private theorem finite_of_exact_of_finite {R A B C : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g) (hA : Module.Finite R A)
    (hC : Module.Finite R C) : Module.Finite R B :=
  have := isNoetherian_of_range_eq_ker f g h.linearMap_ker_eq.symm
  inferInstance

theorem finite_cubeComplex_grCube_homology :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R]
      (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∀ n p, Module.Finite R ((cubeComplex (grCube ι ℳ n)).homology p) := by
  intro ι _ _ R _ _
  suffices key : ∀ (j p : ℕ), Fintype.card ι < p + j →
      ∀ (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∀ n, Module.Finite R ((cubeComplex (grCube ι ℳ n)).homology p) by
    intro M _ _ _ _ ℳ _ _ hM n p
    exact key (Fintype.card ι + 1) p (by omega) M ℳ hM n
  intro j
  induction j with
  | zero =>
    intro p hp M _ _ _ _ ℳ _ _ _ n
    have := ModuleCat.subsingleton_of_isZero
      (isZero_cubeComplex_homology (grCube ι ℳ n) (p := p) hp)
    infer_instance
  | succ j ih =>
    intro p hp M _ _ _ _ ℳ _ _ hM n
    obtain ⟨r, d, g, hg, hs⟩ := exists_graded_surjection (ι := ι) ℳ
    let _ := grSubDecomposition (grFree ι R d) hg.isHomogeneous_ker
    have hK := ih (p + 1) (by omega) _ (grSub (grFree ι R d) (LinearMap.ker g)) inferInstance n
    have hF := (cubeComplex_grFree_finite_and_exactAt ι R r d).1 n p
    have hse := (hg.shortExact_ker hs).cubeComplex_shortExact n
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hse.homology_exact₃ p (p + 1) rfl)
    exact finite_of_exact_of_finite hex hF hK
theorem finite_piece_of_polyGradedSMul : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∀ n, Module.Finite R (ℳ n) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ _ n
  refine GradedHilbert.finite_piece (ι := ι) ℳ (fun i k m hm => ?_) n
  have := grSMul_mem ℳ (X_mem_polyGrading i) hm
  first
    | exact this
theorem finite_grCech_homology : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R]
    [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∀ n p, Module.Finite R ((cechComplex (grCube ι ℳ n)).homology p) := by
  intro ι _ _ R _ _ M _ _ _ _ ℳ _ _ hM n p
  have h₀ : Module.Finite R (ℳ n) := finite_piece_of_polyGradedSMul ι R M ℳ hM n
  have h₁ : Module.Finite R ((grCube ι ℳ n).obj ∅) :=
    Module.Finite.equiv (homLocEmptyEquiv ι ℳ n)
  exact finite_cechHomology_of_finite_cubeHomology ι R (grCube ι ℳ n) h₁
    (_root_.GlobalTheory.finite_cubeComplex_grCube_homology ι R M ℳ hM n) p
