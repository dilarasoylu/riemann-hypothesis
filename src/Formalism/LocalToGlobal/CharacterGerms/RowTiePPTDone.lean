module

public import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelfEx
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePCartSelfSt
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLieSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEig2

@[expose] public section
namespace Formalism.L2.FormalSeriesBounds
theorem ptSelf_of_start2 (hS : AllStartSelfSt) : PTSelfSt :=
  ptSelf_of_start hS OActSelf.oActSelf_holds hStabSelf_holds
theorem ptSelf_of_eig (hE : RowTiePKey.KeyEigSt) : PTSelfSt :=
  ptSelf_of_start2 (allStartSelf_of_eig hE)
theorem ptSelf_holds : PTSelfSt := ptSelf_of_eig RowTiePKey.keyEig_holds
