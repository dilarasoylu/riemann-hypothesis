module

public import Formalism.LocalToGlobal.GlobalTheory.HLatOps
import Formalism.HermitianLattices.StatementLat

@[expose] public section

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps

section
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  (K' : Type) [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']


end




end Formalism.L2.Geo.ExtensionFiltration.ExtInvSk
