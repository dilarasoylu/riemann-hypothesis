module

public import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
import Mathlib.RingTheory.PiTensorProduct

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}

def Phi (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → K) : ι → Fin r → ℂ :=
  fun i => Q i *ᵥ embVec (σ i) v

def Theta (p : ℕ) (w : ι → Fin r → ℂ) : ι → Fin r → ℂ := fun i a => sgn p a * w i a

theorem sgn_conj (p : ℕ) (a : Fin r) : conj (sgn p a) = sgn p a := by
  unfold sgn
  split_ifs <;> simp







section Herm

variable (S : HermForm K r)









end Herm

end Formalism.L2.Pj.FundamentalDomainD5
