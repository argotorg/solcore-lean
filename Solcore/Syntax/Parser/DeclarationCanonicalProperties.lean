import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.Impl
import Solcore.Syntax.Parser.TermCanonicalProperties

/-! Canonical recursive-validity instances for body-bearing declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public functions retain canonical Core statements in their bodies. -/
theorem functionDecl_canonical_validFor (location : FunctionLocation) :
    (functionDecl location).ValidFor
      (FunctionDecl.ValidFor CoreStatement.ValidFor) :=
  functionDecl_validFor CoreStatement.ValidFor location
    (block_canonical_validFor .allow)

/-- Constructors retain canonical Core statements in their bodies. -/
theorem constructorDecl_canonical_validFor :
    constructorDecl.ValidFor
      (ConstructorDecl.ValidFor CoreStatement.ValidFor) :=
  constructorDecl_validFor CoreStatement.ValidFor
    (block_canonical_validFor .require)

/-- Fallback declarations retain canonical Core statements in their bodies. -/
theorem fallbackDecl_canonical_validFor :
    fallbackDecl.ValidFor
      (FallbackDecl.ValidFor CoreStatement.ValidFor) :=
  fallbackDecl_validFor CoreStatement.ValidFor
    (block_canonical_validFor .require)

/-- Implementations retain canonical Core statements in every method body. -/
theorem implDecl_canonical_validFor :
    implDecl.ValidFor (ImplDecl.ValidFor CoreStatement.ValidFor) :=
  implDecl_validFor CoreStatement.ValidFor
    (block_canonical_validFor .allow)
    (block_canonical_preservesTokenWindow .allow)

end Solcore.Syntax.Parser
