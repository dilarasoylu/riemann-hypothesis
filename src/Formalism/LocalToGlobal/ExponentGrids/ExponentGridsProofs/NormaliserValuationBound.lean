module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Formalism.QuotientMetricDivisors.Statement
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.QuotientMetricDivisors.Complement2Normaliser
import Mathlib.Algebra.Order.Star.Int
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds

@[expose] public section
namespace Formalism.CG
open Finset
def HCrank (k t j : ℕ) : ℕ := k + j * (t + 1)

def HCparam (k t : ℕ) (u e : ℕ → ℚ) (l : ℕ) : ℚ :=
  if l ≤ k then u l
  else -e ((l - k - 1) / (t + 1) + 1) + (t : ℚ) / 2 - (((l - k - 1) % (t + 1) : ℕ) : ℚ)

def HCnu (k t : ℕ) (u e : ℕ → ℚ) (j l : ℕ) : ℚ :=
  HCparam k t u e l - ((HCrank k t (j - 1) : ℚ) + 1 - 2 * (l : ℚ)) / 2 + e j
    - (HCrank k t j : ℚ) / 2

def HCdeg (k t : ℕ) (u e : ℕ → ℚ) (j : ℕ) : ℚ :=
  ∑ l ∈ Icc 1 (HCrank k t (j - 1)), HCnu k t u e j l

def HCsparam (k t j : ℕ) (v b e : ℕ → ℚ) (l : ℕ) : ℚ :=
  if l + 1 ≤ k then v (l + 1)
  else if l + 1 ≤ k + j then -b (l + 1 - k)
  else if l + 1 ≤ k + j + t then -e j + ((t : ℚ) - 1) / 2 - (((l + 1 - (k + j) : ℕ) : ℚ) - 1)
  else -b (l + 1 - k - t)

def HCkap (k t m j : ℕ) (v b e : ℕ → ℚ) (l : ℕ) : ℚ :=
  HCsparam k t j v b e l - (((k : ℚ) + m + t - 1) + 1 - 2 * (l : ℚ)) / 2
    + (e j - (t : ℚ) / 2 + ((k : ℚ) + m + t - 1) / 2 - ((k : ℚ) + j - 1))

def HCDplus (k t m j : ℕ) (v b e : ℕ → ℚ) : ℚ := ∑ l ∈ Ico 1 (k + j), HCkap k t m j v b e l

def HCDminus (k t m j : ℕ) (v b e : ℕ → ℚ) : ℚ :=
  ∑ l ∈ Ico (k + j + t) (k + m + t), -HCkap k t m j v b e l
end Formalism.CG
noncomputable section
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl lw PlOver IsConjAt)
open Formalism.CG (HCdeg HCDplus HCDminus)
namespace Formalism.AtG
namespace ValuationJets
open Formalism.DivisionValues.ValuationRepresentative Formalism.DivisionValues.PlaceSumConjugation
variable {K : Type} [Field K] [NumberField K] [StarRing K]
section
variable (w : HeightOneSpectrum (𝓞 K))
theorem val_int (x : 𝓞 K) (hx : x ≠ 0) :
    w.valuation K (x : K) = WithZero.exp (-(vw w (x : K))) := by
  rw [show (x : K) = algebraMap (𝓞 K) K x from rfl,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hx]
  congr 1
  rw [neg_inj]
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w (by simpa using hx)]

theorem val_eq (a : K) (ha : a ≠ 0) :
    w.valuation K a = WithZero.exp (-(vw w a)) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hy0 : algebraMap (𝓞 K) K y ≠ 0 := (div_ne_zero_iff.mp ha).2
  have hx : x ≠ 0 := fun h => ha (by simp [h])
  have vx := val_int w x hx
  have vy := val_int w y (nonZeroDivisors.ne_zero hy)
  rw [show ((x : K)) = algebraMap (𝓞 K) K x from rfl] at vx
  rw [show ((y : K)) = algebraMap (𝓞 K) K y from rfl] at vy
  have hmul : vw w (algebraMap (𝓞 K) K x) =
      vw w (algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K y) + vw w (algebraMap (𝓞 K) K y) := by
    rw [← vw_mul w _ _ ha hy0, div_mul_cancel₀ _ hy0]
  rw [map_div₀, vx, vy, ← WithZero.exp_sub]
  congr 1
  linarith

theorem vw_add (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (vw w a) (vw w b) ≤ vw w (a + b) := by
  have h1 := (w.valuation K).map_add a b
  rw [val_eq w a ha, val_eq w b hb, val_eq w _ hab] at h1
  rcases le_max_iff.mp h1 with h | h
  · exact le_trans (min_le_left _ _) (neg_le_neg_iff.mp (WithZero.exp_le_exp.mp h))
  · exact le_trans (min_le_right _ _) (neg_le_neg_iff.mp (WithZero.exp_le_exp.mp h))
end


end ValuationJets

open ValuationJets Formalism.DivisionValues.ValuationRepresentative Formalism.DivisionValues.PlaceSumConjugation

end Formalism.AtG
