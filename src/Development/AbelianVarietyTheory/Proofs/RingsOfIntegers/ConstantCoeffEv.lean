module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.IntSeries
variable {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] {σ τ : Type}
theorem intAA_map (f : MvPowerSeries σ R) :
    IntAA (R := R) k (MvPowerSeries.map (algebraMap R k) f) := fun n => by
  rw [coeff_map]; exact ⟨_, rfl⟩

theorem intAA_one : IntAA (R := R) k (1 : MvPowerSeries σ k) := by
  simpa using intAA_map (k := k) (1 : MvPowerSeries σ R)

theorem intAA_add {f g : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (hg : IntAA (R := R) k g) :
    IntAA (R := R) k (f + g) := fun n => by
  rw [map_add (f := _)]; exact Subring.add_mem _ (hf n) (hg n)

theorem intAA_sub {f g : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (hg : IntAA (R := R) k g) :
    IntAA (R := R) k (f - g) := fun n => by
  rw [map_sub]; exact Subring.sub_mem _ (hf n) (hg n)

theorem intAA_mul {f g : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (hg : IntAA (R := R) k g) :
    IntAA (R := R) k (f * g) := fun n => by
  classical
  rw [coeff_mul]
  exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (hf _) (hg _)

theorem intAA_pow {f : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (m : ℕ) :
    IntAA (R := R) k (f ^ m) := by
  induction m with
  | zero => simpa using intAA_one
  | succ m ih => rw [pow_succ]; exact intAA_mul ih hf

theorem intAA_prod {ι : Type*} (t : Finset ι) {f : ι → MvPowerSeries σ k}
    (hf : ∀ i ∈ t, IntAA (R := R) k (f i)) : IntAA (R := R) k (∏ i ∈ t, f i) :=
  Finset.prod_induction f (IntAA (R := R) k) (fun _ _ => intAA_mul) intAA_one hf

theorem intAA_pderiv {f : MvPowerSeries σ k} (s : σ) (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (pderiv s f) := fun n => by
  rw [coeff_pderiv]
  exact Subring.mul_mem _ (hf _) (Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _))

theorem intAA_subst_of_hasSubst {a : σ → MvPowerSeries τ k} (ha : HasSubst a)
    {f : MvPowerSeries σ k} (hai : ∀ s, IntAA (R := R) k (a s)) (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (MvPowerSeries.subst a f) := fun n => by
  rw [coeff_subst ha]
  refine finsum_induction (· ∈ (algebraMap R k).range) (Subring.zero_mem _)
    (fun _ _ => Subring.add_mem _) fun d => ?_
  rw [smul_eq_mul]
  exact Subring.mul_mem _ (hf d) (intAA_prod _ (fun s _ => intAA_pow (hai s) _) n)

theorem intAA_subst [Finite σ] {a : σ → MvPowerSeries τ k} {f : MvPowerSeries σ k}
    (ha : ∀ s, constantCoeff (a s) = 0) (hai : ∀ s, IntAA (R := R) k (a s))
    (hf : IntAA (R := R) k f) : IntAA (R := R) k (MvPowerSeries.subst a f) :=
  intAA_subst_of_hasSubst (hasSubst_of_constantCoeff_zero ha) hai hf

theorem main : ∀ (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k],
  (∀ (σ : Type) (f g : MvPowerSeries σ k), IntAA (R := R) k f → IntAA (R := R) k g → IntAA (R := R) k (f + g) ∧ IntAA (R := R) k (f - g) ∧ IntAA (R := R) k (f * g)) ∧
  (∀ (σ : Type) (f : MvPowerSeries σ k) (s : σ), IntAA (R := R) k f → IntAA (R := R) k (pderiv s f)) ∧
  (∀ (σ : Type) (f : MvPowerSeries σ R), IntAA (R := R) k (MvPowerSeries.map (algebraMap R k) f)) ∧
  (∀ (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ k) (f : MvPowerSeries σ k), (∀ s, constantCoeff (a s) = 0) → (∀ s, IntAA (R := R) k (a s)) → IntAA (R := R) k f → IntAA (R := R) k (MvPowerSeries.subst a f)) :=
  fun _ _ _ _ _ =>
    ⟨fun _ _ _ hf hg => ⟨intAA_add hf hg, intAA_sub hf hg, intAA_mul hf hg⟩,
      fun _ _ s hf => intAA_pderiv s hf, fun _ f => intAA_map f,
      fun _ _ _ _ _ ha hai hf => intAA_subst ha hai hf⟩
end GlobalTheory.IntSeries
namespace GlobalTheory.GaugeAdjoint
open GlobalTheory.FormalCalc GlobalTheory.IntSeries
section Ev

variable {k : Type} [CommRing k] {d m n p : ℕ}

section
variable {a : Fin m → Pt k n d}
theorem hasSubst_pts (ha : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun q : Fin m × Fin d => a q.1 q.2) := hasSubst_of_constantCoeff_zero fun q => ha q.1 q.2

theorem constantCoeff_ev (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS k m d) : constantCoeff (ev a f) = constantCoeff f := by
  have hs := hasSubst_pts ha
  have hsplit : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  unfold ev
  conv_lhs => rw [hsplit]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs (fun q => ha q.1 q.2) h0, add_zero]
  simp

theorem ev_ev (ha : ∀ j i, constantCoeff (a j i) = 0)
    {b : Fin n → Pt k p d} (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS k m d) :
    ev b (ev a f) = ev (fun j i => ev b (a j i)) f := by
  unfold ev
  rw [subst_comp_subst_apply (hasSubst_pts ha) (hasSubst_pts hb)]

theorem ev_pt (ha : ∀ j i, constantCoeff (a j i) = 0) (j : Fin m)
    (i : Fin d) : ev a (pt k d j i) = a j i := by
  unfold ev pt
  rw [subst_X (hasSubst_pts ha)]

theorem ev_zero (ha : ∀ j i, constantCoeff (a j i) = 0) :
    ev a (0 : PS k m d) = 0 := by
  unfold ev
  rw [← substAlgHom_apply (hasSubst_pts ha), map_zero]
end

section
variable {σ τ : Type}
private theorem coeff_subst_congr_lemma [Finite σ] [Finite τ] {A : σ → MvPowerSeries τ k}
    (hA : ∀ q, constantCoeff (A q) = 0) {g g' : MvPowerSeries σ k} {x : τ →₀ ℕ}
    (hgg : ∀ y : σ →₀ ℕ, y.degree ≤ x.degree → coeff y g = coeff y g') :
    coeff x (subst A g) = coeff x (subst A g') := by
  have hT : truncTotal (x.degree + 1) g = truncTotal (x.degree + 1) g' := by
    ext y
    rw [coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite]
    split_ifs with hy
    · exact hgg y (Nat.lt_succ_iff.mp hy)
    · rfl
  have e1 := congrArg (AddMonoidAlgebra.coeff · x)
    (truncTotal_subst_eq_truncTotal_truncTotal_subst (k := x.degree + 1) (f := g) hA)
  have e2 := congrArg (AddMonoidAlgebra.coeff · x)
    (truncTotal_subst_eq_truncTotal_truncTotal_subst (k := x.degree + 1) (f := g') hA)
  rw [coeff_truncTotal _ (Nat.lt_succ_self _)] at e1 e2
  rw [e1, e2, hT]

private theorem pderiv_subst_coe_mvPolynomial_eq_sum [Fintype σ] [DecidableEq σ]
    {A : σ → MvPowerSeries τ k} (hA : HasSubst A) (s : τ) (q : MvPolynomial σ k) :
    pderiv s (subst A (q : MvPowerSeries σ k)) =
      ∑ r, subst A (pderiv r (q : MvPowerSeries σ k)) * pderiv s (A r) := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.coe_C, subst_C, pderiv_C]
    symm
    apply Finset.sum_eq_zero
    intro r _
    rw [pderiv_C, ← substAlgHom_apply hA, map_zero, zero_mul]
  | add f g hf hg =>
    simp only [MvPolynomial.coe_add, subst_add hA, map_add (f := _), hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f r0 hf =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X]
    simp only [← substAlgHom_apply hA] at hf ⊢
    have hX : ∀ r, substAlgHom hA (pderiv r (X r0 : MvPowerSeries σ k)) = if r = r0 then 1 else 0 := by
      intro r
      split_ifs with hr
      · subst hr
        rw [pderiv_X_self, map_one]
      · rw [pderiv_X_of_ne (Ne.symm hr), map_zero]
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, substAlgHom_X, hX, hf, mul_ite,
      mul_one, mul_zero, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]

private theorem pderiv_subst_eq_sum_of_constantCoeff_eq_zero [Fintype σ] [DecidableEq σ] [Finite τ]
    {A : σ → MvPowerSeries τ k} (hA : ∀ r, constantCoeff (A r) = 0) (f : MvPowerSeries σ k) (s : τ) :
    pderiv s (subst A f) = ∑ r, subst A (pderiv r f) * pderiv s (A r) := by
  classical
  have hS : HasSubst A := hasSubst_of_constantCoeff_zero hA
  ext x
  have h1 : coeff (x + Finsupp.single s 1) (subst A f) =
      coeff (x + Finsupp.single s 1)
        (subst A ((truncTotal (x.degree + 2) f : MvPolynomial σ k) : MvPowerSeries σ k)) := by
    apply coeff_subst_congr_lemma hA
    intro z hz
    rw [MvPolynomial.coeff_coe, coeff_truncTotal]
    rw [map_add (f := _), Finsupp.degree_single] at hz
    omega
  rw [coeff_pderiv, h1, ← coeff_pderiv, pderiv_subst_coe_mvPolynomial_eq_sum hS]

  simp only [map_sum, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun y hy => ?_
  congr 1
  apply coeff_subst_congr_lemma hA
  intro z hz
  have hxy := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
  have h2 : y.1.degree ≤ x.degree := by
    rw [← hxy, map_add (f := _)]
    omega
  rw [coeff_pderiv, coeff_pderiv, MvPolynomial.coeff_coe, coeff_truncTotal]
  rw [map_add (f := _), Finsupp.degree_single]
  omega
end

theorem pderiv_ev {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS k m d) (s : Fin n × Fin d) :
    pderiv s (ev a f) = ∑ j, ∑ i, ev a (pderiv (j, i) f) * pderiv s (a j i) := by
  unfold ev
  rw [pderiv_subst_eq_sum_of_constantCoeff_eq_zero (A := fun q : Fin m × Fin d => a q.1 q.2) (fun q => ha q.1 q.2),
    Fintype.sum_prod_type]

theorem const_pt (j : Fin n) (i : Fin d) : constantCoeff (pt k d j i) = 0 := by
  unfold pt
  exact constantCoeff_X _

theorem const_one {x : Pt k n d} (hx : ∀ i, constantCoeff (x i) = 0) (j : Fin 1) (i : Fin d) :
    constantCoeff ((![x] : Fin 1 → Pt k n d) j i) = 0 := by
  fin_cases j
  simpa using hx i

theorem const_two {x y : Pt k n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (j : Fin 2) (i : Fin d) :
    constantCoeff ((![x, y] : Fin 2 → Pt k n d) j i) = 0 := by
  fin_cases j
  · simpa using hx i
  · simpa using hy i

theorem const_zero (i : Fin d) : constantCoeff ((0 : Pt k n d) i) = 0 := by simp

theorem const_comp1 {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) {x : Pt k n d}
    (hx : ∀ i, constantCoeff (x i) = 0) (i : Fin d) : constantCoeff (comp1 φ x i) = 0 := by
  unfold comp1
  rw [constantCoeff_ev (const_one hx)]
  exact hφ i

theorem ev_origin (f : PS k 1 d) : ev (n := n) ![0] f = C (constantCoeff f) := by
  have hz : (fun q : Fin 1 × Fin d => (![0] : Fin 1 → Pt k n d) q.1 q.2) = 0 := by
    funext q
    simp
  unfold ev
  rw [hz, subst_zero_eq_C_constantCoeff]
  simp

theorem ev_ev_one {x : Pt k n d} (hx : ∀ i, constantCoeff (x i) = 0)
    {b : Fin n → Pt k p d} (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS k 1 d) :
    ev b (ev ![x] f) = ev ![fun i => ev b (x i)] f := by
  rw [ev_ev (const_one hx) hb]
  congr 1
  funext j
  fin_cases j
  rfl

theorem ev_ev_two {x y : Pt k n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0)
    {b : Fin n → Pt k p d} (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS k 2 d) :
    ev b (ev ![x, y] f) = ev ![fun i => ev b (x i), fun i => ev b (y i)] f := by
  rw [ev_ev (const_two hx hy) hb]
  congr 1
  funext j
  fin_cases j
  · rfl
  · rfl

theorem const_axis (j : Fin 2) (i : Fin d) :
    constantCoeff ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j i) = 0 := by
  fin_cases j
  · simpa using const_pt 0 i
  · simp

theorem axis_pt_zero :
    (fun i => ev (n := 1) ![pt k d 0, 0] (pt k d (0 : Fin 2) i)) = pt k d 0 := by
  funext i
  rw [ev_pt const_axis]
  rfl

theorem axis_pt_one : (fun i => ev (n := 1) ![pt k d 0, 0] (pt k d (1 : Fin 2) i)) = 0 := by
  funext i
  rw [ev_pt const_axis]
  rfl



theorem pderiv_pt (j j' : Fin n) (i i' : Fin d) :
    pderiv (j, i) (pt k d j' i') = if j' = j ∧ i' = i then 1 else 0 := by
  unfold pt
  by_cases hc : j' = j ∧ i' = i
  · obtain ⟨rfl, rfl⟩ := hc
    simp
  · rw [if_neg hc, pderiv_X_of_ne]
    intro he
    exact hc ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩




theorem axis_pderiv (φ : PS k 1 d) (i : Fin d) :
    ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] (pderiv ((0 : Fin 1), i) φ)) =
      C (coeff (Finsupp.single ((0 : Fin 1), i) 1) φ) := by
  rw [ev_ev_one (fun i => const_pt 1 i) const_axis, axis_pt_one, ev_origin]
  congr 1
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp








end Ev
