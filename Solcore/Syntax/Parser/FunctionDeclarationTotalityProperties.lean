import Solcore.Syntax.Parser.FunctionSignatureTotalityProperties
import Solcore.Syntax.Parser.PublicCoreTermTotalityProperties

/-! Valid-input totality for complete canonical function declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem functionDecl_invariantFreeOnValid
    (location : FunctionLocation) :
    Parser.InvariantFreeOnValid (functionDecl location) := by
  unfold functionDecl
  apply Parser.bind_invariantFreeOnValid
    (functionSignature_validFor location)
    (functionSignature_invariantFreeOnValid location)
  intro signature
  apply Parser.bind_invariantFreeOnValid
    (isolateBlock_validFor CoreStatement.ValidFor (block .allow)
      (block_canonical_validFor .allow))
    (BlockInternals.isolateBlock_invariantFreeOnValid
      (block .allow) (block_invariantFreeOnValid .allow))
  intro body
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover signature.span body.span
    value := { signature, body }
  } : FunctionDecl)

theorem functionDecl_ordinary
    (location : FunctionLocation)
    (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next,
      functionDecl location input = .ok declaration next) ∨
      (∃ failure next,
        functionDecl location input = .reject failure next) :=
  functionDecl_invariantFreeOnValid location input inputValid

theorem functionDecl_ne_invariant
    (location : FunctionLocation)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    functionDecl location input ≠ .invariant error :=
  (functionDecl_invariantFreeOnValid location).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser
