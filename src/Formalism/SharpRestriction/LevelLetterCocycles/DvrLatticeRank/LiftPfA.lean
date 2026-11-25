module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section
noncomputable section
namespace Formalism.MainNotions.N.PreambleDegrees
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.PreambleDegrees.Loc Module
variable {l : ℕ} [Fact l.Prime]
theorem finrank_sup_adjoin (F : IntermediateField ℚ_[l] (Om l)) (y : Om l) :
    finrank ℚ_[l] ↥(F ⊔ IntermediateField.adjoin ℚ_[l] {y}) = finrank ℚ_[l] ↥F * (minpoly F y).natDegree := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup, ← IntermediateField.adjoin.finrank hint]
  set_option synthInstance.maxHeartbeats 200000 in
    exact (Module.finrank_mul_finrank ℚ_[l] ↥F ↥(IntermediateField.adjoin F {y})).symm

section
variable (K : FinExt l)
theorem Ks_eq (s : ℕ) {z : Om l} (hz : IsPrimitiveRoot z (l ^ s)) :
    Ks K s = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {z} := by
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  unfold Ks
  congr 1
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one (show x ^ (l ^ s) = 1 from hx)
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  · exact IntermediateField.adjoin.mono _ _ _ (by rintro x rfl; exact hz.pow_eq_one)

theorem finrank_Ks {s : ℕ} (hs : 0 < s) :
    finrank ℚ_[l] ↥(Ks K s) = finrank ℚ_[l] ↥(K0 K) * (l ^ (s - 1) * (l - 1)) := by
  have hz := ζQ_primitive l s
  rw [Ks_eq K s hz, finrank_sup_adjoin, natDegree_minpoly_eq (F := K0 K) inf_le_right hs hz,
    Nat.totient_prime_pow Fact.out hs]

theorem finrank_maxUnramifiedSubfield_padicFinExt_pos : 0 < finrank ℚ_[l] ↥(K0 K) := by
  have := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).injective
  exact finrank_pos
end
end Formalism.MainNotions.N.PreambleDegrees
namespace Formalism.MainNotions.N.Ln34.CyclotomicLifting
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module
variable {l : ℕ} [Fact l.Prime]
theorem finite_roots_l : {x : Om l | x ^ (l ^ 1) = 1}.Finite := by
  classical
  have hl : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
  refine Set.Finite.subset (Polynomial.nthRoots (l ^ 1) (1 : Om l)).toFinset.finite_toSet ?_
  intro x hx
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hl]
  exact hx

theorem fd_Ks (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(Ks K 1) := by
  have h0 : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    Module.finite_of_finrank_pos (Formalism.MainNotions.N.PreambleDegrees.finrank_maxUnramifiedSubfield_padicFinExt_pos K)
  have : Finite {x : Om l | x ^ (l ^ 1) = 1} := finite_roots_l.to_subtype
  have h1 : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}) :=
    IntermediateField.finiteDimensional_adjoin (fun x hx => by
      have hl : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
      apply IsIntegral.of_pow hl
      rw [show x ^ (l ^ 1) = 1 from hx]
      exact isIntegral_one)
  unfold Ks
  infer_instance

def cycL (K : FinExt l) : FinExt l := ⟨Ks K 1, fd_Ks K⟩

section
variable (K : FinExt l)
theorem cycL_val : (cycL K).1 = Ks K 1 := rfl

theorem max_unramified_le_cyclotomic : K0 K ≤ K0 (cycL K) :=
  le_inf (le_sup_left : K0 K ≤ Ks K 1) inf_le_right

theorem Ks_cycL : Ks (cycL K) 1 = Ks K 1 := by
  apply le_antisymm
  · exact sup_le (inf_le_left : K0 (cycL K) ≤ (cycL K).1) le_sup_right
  · exact sup_le_sup_right (max_unramified_le_cyclotomic K) _

theorem cyclotomic_degree_max_unramified : (K0 K).relfinrank (Ks K 1) = l - 1 := by
  have hp : 0 < finrank ℚ_[l] ↥(K0 K) := Formalism.MainNotions.N.PreambleDegrees.finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have h1 := IntermediateField.finrank_bot_mul_relfinrank (le_sup_left : K0 K ≤ Ks K 1)
  have h2 := Formalism.MainNotions.N.PreambleDegrees.finrank_Ks K one_pos
  rw [Nat.sub_self, pow_zero, one_mul] at h2
  exact Nat.eq_of_mul_eq_mul_left hp (h1.trans h2)

theorem max_unramified_cyclotomic_eq : K0 (cycL K) = K0 K := by
  have h1 := cyclotomic_degree_max_unramified K
  have h2 := cyclotomic_degree_max_unramified (cycL K)
  rw [Ks_cycL] at h2
  have hm := IntermediateField.relfinrank_mul_relfinrank (max_unramified_le_cyclotomic K)
    (inf_le_left : K0 (cycL K) ≤ (cycL K).1)
  rw [cycL_val, h1, h2] at hm
  have hpos : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have h3 : (K0 K).relfinrank (K0 (cycL K)) = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [hm, one_mul])
  exact le_antisymm (IntermediateField.relfinrank_eq_one_iff.1 h3) (max_unramified_le_cyclotomic K)

theorem finrank_eq_relfinrank :
    finrank ↥(K0 K) ↥K.1 = (K0 K).relfinrank K.1 := by
  have hle : K0 K ≤ K.1 := inf_le_left
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  exact LinearEquiv.finrank_eq
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem finrank_cycL : finrank ↥(K0 (cycL K)) ↥(cycL K).1 = l - 1 := by
  rw [finrank_eq_relfinrank, cycL_val, ← Ks_cycL K, cyclotomic_degree_max_unramified]
end
