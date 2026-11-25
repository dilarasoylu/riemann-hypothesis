module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GenericUnitary

namespace GlobalTheory.TempSatUnr

open GlobalTheory.TempSat

theorem isSpherical_of_hasSatGL {E : Type} [Field E] [NumberField E] {a : ℕ} {w : HeightOneSpectrum (𝓞 E)}
    {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V}
    {S : Multiset ℂˣ} (hS : GlobalTheory.LFun.HasSatGL w ρ S) : GlobalTheory.SmGL.IsSpherical ρ := by
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w (n := a) :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [hK]
  exact hS.1

end GlobalTheory.TempSatUnr
