module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
public import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLt
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup

@[expose] public section
noncomputable section
namespace Formalism.MainNotions.J
open Formalism.BasicNotions NumberField
theorem level_prime_splits_totally_real (D : D7) (u : D.what₂.Word) : StandardLattice.SplitsF D (D.mem u).A.T := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have h := Formalism.BasicNotions.Examples₂.placesOver_ncard_of_split D.host (D.mem u).A.T (D.T_mod_cond u)
  have h' := splits_sub D.host.F (D.mem u).A.T D.host.E (D.mem u).A.T_prime h
  rw [finrank_F_eq] at h'
  exact h'
end Formalism.MainNotions.J
namespace Formalism.MainNotions.Ext.Lw
open Formalism.BasicNotions Formalism.MainNotions
theorem rank_conditions_iff_lowest_space {eps : ℝ} (Fm : FamP eps) :
    RankTiesF Fm ↔ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u := by
  unfold RankTiesF
  constructor
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i u => ((hx0 x hx i).2 u).2⟩
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i => ⟨_root_.Formalism.MainNotions.J.splitsF_g (Fm.D x i), fun u => ⟨_root_.Formalism.MainNotions.J.level_prime_splits_totally_real (Fm.D x i) u, hx0 x hx i u⟩⟩⟩

theorem rank_conditions_of_lowest_space {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u) : RankTiesF Fm :=
  (rank_conditions_iff_lowest_space Fm).2 h
