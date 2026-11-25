module

public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Formalism.LocalRingCardinality.SpanPowerMembership.GatRing
public import Mathlib.RingTheory.WittVector.Complete
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section
noncomputable section
namespace Formalism.BasicNotions.Examples₂.LevelValuationRings
open Formalism.MainNotions.G QuadraticAlgebra
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
abbrev Wn : Type := WittVector p (GaloisField p n)

abbrev Qn : Type := FractionRing (Wn p n)

abbrev On : Type := QuadraticAlgebra (Wn p n) (p : Wn p n) 0

instance instDomOn : IsDomain (On p n) := GatR.isDomain (WittVector.irreducible p)
instance instDvrOn : IsDiscreteValuationRing (On p n) := GatR.isDVR (WittVector.irreducible p)

abbrev Kn : Type := FractionRing (On p n)
end Formalism.BasicNotions.Examples₂.LevelValuationRings
namespace Formalism.BasicNotions.Examples₂.LevelValuationRings
open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField QuadraticAlgebra
section Orbit

variable {G : Type} [Group G] [Finite G] (g : G)

abbrev Quo : Type := G ⧸ Subgroup.zpowers g

def eQuo : Fin (Nat.card (Quo g)) ≃ Quo g := (Finite.equivFin (Quo g)).symm


open Classical in
def secOf (T : Set G) (q : Quo g) : G :=
  if h : ∃ x ∈ T, (QuotientGroup.mk x : Quo g) = q then h.choose else q.out

theorem mk_secOf (T : Set G) (q : Quo g) : (QuotientGroup.mk (secOf g T q) : Quo g) = q := by
  unfold secOf
  split_ifs with h
  · exact h.choose_spec.2
  · exact QuotientGroup.out_eq' q

def orbFun (T : Set G) (x : Σ _ : Fin (Nat.card (Quo g)), Fin (orderOf g)) : G :=
  secOf g T (eQuo g x.1) * g ^ (x.2 : ℕ)

theorem orbFun_bij (T : Set G) : Function.Bijective (orbFun g T) := by
  have key : ∀ (q : Quo g) (n : ℕ), (QuotientGroup.mk (secOf g T q * g ^ n) : Quo g) = q := by
    intro q n
    have h1 : (QuotientGroup.mk (secOf g T q) : Quo g) = QuotientGroup.mk (secOf g T q * g ^ n) := by
      rw [QuotientGroup.eq, inv_mul_cancel_left]
      exact Subgroup.npow_mem_zpowers g n
    rw [← h1, mk_secOf]
  have hinj : Function.Injective (orbFun g T) := by
    rintro ⟨v1, s1⟩ ⟨v2, s2⟩ h
    simp only [orbFun] at h
    have hv : v1 = v2 := by
      have h3 := congrArg (fun y => (QuotientGroup.mk y : Quo g)) h
      simp only [key] at h3
      exact (eQuo g).injective h3
    subst hv
    have hs : g ^ (s1 : ℕ) = g ^ (s2 : ℕ) := mul_left_cancel h
    have h4 : (s1 : ℕ) = s2 := pow_injOn_Iio_orderOf s1.2 s2.2 hs
    rw [Fin.ext h4]
  refine hinj.bijective_of_nat_card_le ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers g), Nat.card_zpowers,
    Nat.card_eq_fintype_card (α := Σ _ : Fin (Nat.card (Quo g)), Fin (orderOf g)), Fintype.card_sigma]
  simp

def orbEquiv (T : Set G) : (Σ _ : Fin (Nat.card (Quo g)), Fin (orderOf g)) ≃ G :=
  Equiv.ofBijective (orbFun g T) (orbFun_bij g T)

end Orbit

variable {R : Ranks} (H : Host R) (p : ℕ)

theorem of_cls (h : H.cls p = .inertClass) : p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d ∧
    jacobiSym (-(H.d : ℤ)) p ≠ 1 ∧ H.psAt p ≠ 1 := by
  unfold Host.cls primeClass at h
  by_cases h1 : p ∈ H.small
  · rw [if_pos h1] at h
    cases h
  rw [if_neg h1] at h
  by_cases h2 : p = H.q
  · rw [if_pos h2] at h
    cases h
  rw [if_neg h2] at h
  by_cases h3 : p = H.d
  · rw [if_pos h3] at h
    cases h
  rw [if_neg h3] at h
  by_cases h4 : jacobiSym (-(H.d : ℤ)) p = 1
  · rw [if_pos h4] at h
    cases h
  rw [if_neg h4] at h
  by_cases h5 : H.psAt p = 1
  · rw [if_pos h5] at h
    cases h
  exact ⟨h1, h2, h3, h4, h5⟩

private theorem coprime_of_cls (hp : p.Prime) (hc : H.cls p = .inertClass) : p.Coprime H.condN := by
  obtain ⟨h2, hq, hd, -, -⟩ := of_cls H p hc
  have h1 : ¬ p ∣ H.QS := fun h => h2 (Nat.mem_primeFactors.2 ⟨hp, h, H.QS_pos.ne'⟩)
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.2 h1)
    ((Nat.coprime_primes hp H.hyp.1).2 hq)) ((Nat.coprime_primes hp H.hyp.2.1).2 hd)

def hOf : R.MA :=
  if h : p.Coprime H.condN then (H.art (ZMod.unitOfCoprime p h)).2 else 1

theorem hOf_of_coprime (h : p.Coprime H.condN) : hOf H p = (H.art (ZMod.unitOfCoprime p h)).2 := by
  rw [hOf, dite_eq_left h]

theorem unit_eq_neg_one (x : ℤˣ) (h : (x : ℤ) ≠ 1) : x = -1 := by
  rcases Int.units_eq_one_or x with hx | hx
  · rw [hx] at h
    exact absurd rfl h
  · exact hx

theorem frob_val (hp : p.Prime) (hc : H.cls p = .inertClass) (P : Ideal (𝓞 H.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    H.galE σ = (c0, hOf H p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hco := coprime_of_cls H p hp hc
  obtain ⟨h2, hq, hd, hjd, hjq⟩ := of_cls H p hc
  obtain ⟨-, hiff, hval, -⟩ := H.der.frob p (hp.coprime_iff_not_dvd.1 hco) P
  obtain ⟨h1, h3, -⟩ := hval σ hσ
  have h4 := (hiff σ (ZMod.unitOfCoprime p hco) (ZMod.coe_unitOfCoprime p hco)).1 hσ
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · exact unit_eq_neg_one _ (by rw [h1]; exact hjq)
  · exact unit_eq_neg_one _ (by rw [h3]; exact hjd)
  · show (H.gal σ).2 = hOf H p
    rw [hOf_of_coprime H p hco, h4]

open Ideal in
theorem exists_frob (hp : p.Prime) (hc : H.cls p = .inertClass) :
    ∃ (P : Ideal (𝓞 H.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P := by
  have : Fact p.Prime := ⟨hp⟩
  have hco := coprime_of_cls H p hp hc
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (span {(p : ℤ)}).IsPrime := (span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(p : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  obtain ⟨⟨σ, hσ⟩, -, -⟩ := H.der.frob p (hp.coprime_iff_not_dvd.1 hco) P
  exact ⟨P, hPp, hPl, σ, hσ⟩

def inPsi (φ : Formalism.HC.Frame) : φ.MA →* ↥φ.Psi :=
  (MonoidHom.inr G0 φ.MA).codRestrict φ.Psi (fun _ => rfl)

instance (φ : Formalism.HC.Frame) : Finite ↥φ.Psi := inferInstance

structure Served {R : Ranks} (H : Host R) (p : ℕ) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  cls : H.cls p = .inertClass
  hne : HNeZero H p

variable {H p}

def gPsi (S : Served H p) : ↥(R.Psi) := inPsi R.toFrame (hOf H p)

abbrev nOrb (S : Served H p) : ℕ := Nat.card (Quo (gPsi S))

end Formalism.BasicNotions.Examples₂.LevelValuationRings

namespace Formalism.BasicNotions.Examples₂

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField LevelValuationRings

variable (D : D7) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
  (rOf : D.what₂.Word → ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

end Formalism.BasicNotions.Examples₂
