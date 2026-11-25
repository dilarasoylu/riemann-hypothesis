module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.StableSubspaceCompleteReducibility
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.HighestWeightModuleBounds
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectionCommutesOperators
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MonomialsAreWeightVectors
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialOperatorsGlRelations
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.V2repResIsGLRep
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.DescendingProdEqFactorialChoose

@[expose] public section
namespace Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees
theorem generated_weight_lemma_of_formulas (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (hV1 : ValuationsAdditive D) (hDP : DividedPowerFormulaCharZero) (hBin : BinomialFormulaCharZero) :
    ShaLengthVersionTwo D :=
  generated_weight_lemma_char_zero D hV1 (stable_subspace_complete_reducibility D h2) highest_weight_module_bounds polynomial_operators_gl_relations monomials_are_weight_vectors polynomial_locally_finite hDP hBin
theorem generated_weight_lemma_of_reducibility (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (hV1 : ValuationsAdditive D) : ShaLengthVersionTwo D :=
  generated_weight_lemma_of_formulas D h2 hV1 dividedPower_formula_char_zero binomial_formula_char_zero
