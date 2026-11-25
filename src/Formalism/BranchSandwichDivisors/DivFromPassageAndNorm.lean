module

public import Formalism.BranchSandwichDivisors.StatementR
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Formalism.BranchSandwichDivisors.StatementL
public import Formalism.BranchSandwichDivisors.StatementW
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MapScale
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.TransferMean
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm
import Mathlib.Algebra.Order.Star.Int
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Transfer

@[expose] public section
section
open Finset
namespace Formalism.BranchingDeterminantCap
theorem interlaceIdentities : InterlaceIdent := by
  intro n lam sg h
  have hsum : ∑ i, lam i = lam 0 + ∑ i : Fin n, lam i.succ := Fin.sum_univ_succ lam
  have hsum' : ∑ i, lam i = ∑ i : Fin n, lam i.castSucc + lam (Fin.last n) := Fin.sum_univ_castSucc lam
  have hd0 : d0 lam sg = ∑ i, sg i - ∑ i : Fin n, lam i.succ := by
    rw [d0, Finset.sum_sub_distrib]
  have hnn : ∀ i, 0 ≤ sg i - lam i.succ := fun i => by linarith [(h i).2]
  have h3 : 0 ≤ d0 lam sg := Finset.sum_nonneg fun i _ => hnn i
  have hle : ∀ i, sg i - lam i.succ ≤ d0 lam sg := fun i =>
    Finset.single_le_sum (f := fun i => sg i - lam i.succ) (fun j _ => hnn j) (Finset.mem_univ i)
  have h5 : ∀ i, sg i ∈ rset lam sg i := by
    intro i
    rw [rset, Finset.mem_Icc]
    have := (h i).1
    have := (h i).2
    have := hle i
    omega
  refine ⟨by linarith, ?_, h3, ?_, h5, ?_⟩
  · rw [Finset.sum_sub_distrib]; linarith
  · refine Finset.sum_nonneg fun i _ => ?_
    have := (h i).1
    have := (h i).2
    omega
  · intro i
    have hmem := h5 i
    rw [Finset.card_erase_of_mem hmem]
    rw [rset, Finset.mem_Icc] at hmem
    rw [rset, Int.card_Icc]
    have hc : 0 ≤ min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ := by omega
    have ht : ((min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ).toNat : ℤ) =
        min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ := Int.toNat_of_nonneg hc
    have h1 : 1 ≤ (min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ).toNat := by omega
    rw [Nat.cast_sub h1, ht]
    push_cast
    omega
end Formalism.BranchingDeterminantCap
end
namespace Formalism.BranchingDeterminantCap
alias orthSum := _root_.Formalism.BranchingDeterminantCap.orthogonal_sum_slope
theorem transferPart : TransferPart := transferPart_of _root_.Formalism.BranchingDeterminantCap.map_slope_mu _root_.Formalism.BranchingDeterminantCap.power_slope_mu
theorem transferMuMax : TransferMuMax := transferMuMax_of _root_.Formalism.BranchingDeterminantCap.scale_sandwich_bound orthSum _root_.Formalism.BranchingDeterminantCap.power_slope_mu
theorem interlaceIdent : InterlaceIdent := interlaceIdentities
alias capConst := _root_.Formalism.BranchingDeterminantCap.capacity_constant_bound
alias weylDimBound := _root_.Formalism.BranchingDeterminantCap.weyl_dimension_bound
alias xiNorm := _root_.Formalism.BranchingDeterminantCap.xi_norm_bound
