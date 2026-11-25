module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Star.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic.TypeStar

@[expose] public section
noncomputable section
open Finset
section
open scoped ComplexOrder
namespace Formalism.A
def mfact {σ : Type*} (g : σ →₀ ℕ) : ℕ := g.prod fun _ n => n.factorial
end Formalism.A
end
open Matrix MvPolynomial
namespace Formalism.E
def fock {R τ : Type*} [CommRing R] [StarRing R] (f g : MvPolynomial τ R) : R :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)
