import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.TermStatementProperties

/-! Valid-input totality for the recognized-statement fallback boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/--
Recognized-statement fallback is ordinary when both parsers are ordinary on
valid input. After a primary rejection, the fallback is rerun at the original
input; a successful fallback keeps its value and cursor while replacing its
diagnostics with the primary failure diagnostic.
-/
theorem recognizedStatementOrFallback_invariantFreeOnValid
    (primary fallback : Parser Statement)
    (primaryFree : Parser.InvariantFreeOnValid primary)
    (fallbackFree : Parser.InvariantFreeOnValid fallback) :
    Parser.InvariantFreeOnValid
      (recognizedStatementOrFallback primary fallback) := by
  intro input inputValid
  rcases primaryFree input inputValid with
    ⟨value, next, primaryResult⟩ |
    ⟨failure, rejected, primaryResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [recognizedStatementOrFallback, primaryResult]⟩
  · rcases fallbackFree input inputValid with
      ⟨value, next, fallbackResult⟩ |
      ⟨fallbackFailure, fallbackRejected, fallbackResult⟩
    · let reset : State := {
        next with diagnosticsRev := input.diagnosticsRev
      }
      exact Or.inl ⟨value, reset.emit failure.toDiagnostic, by
        simp only [recognizedStatementOrFallback, primaryResult,
          fallbackResult, reset]⟩
    · exact Or.inr ⟨failure, input, by
        simp only [recognizedStatementOrFallback, primaryResult,
          fallbackResult]⟩

/-- No invariant reply can escape the recognized fallback boundary. -/
theorem recognizedStatementOrFallback_ne_invariant
    (primary fallback : Parser Statement)
    (primaryFree : Parser.InvariantFreeOnValid primary)
    (fallbackFree : Parser.InvariantFreeOnValid fallback)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    recognizedStatementOrFallback primary fallback input ≠
      .invariant error :=
  (recognizedStatementOrFallback_invariantFreeOnValid primary fallback
    primaryFree fallbackFree).ne_invariant input inputValid error

/-- Statement provenance/state contracts paired with valid-input totality. -/
structure StatementTotalityContract
    (valueValid : SourceFile → Statement → Prop)
    (parser : Parser Statement) : Prop
    extends StatementParserContract valueValid parser where
  invariantFree : Parser.InvariantFreeOnValid parser

namespace StatementTotalityContract

/-- A totality contract excludes every invariant reply on valid input. -/
theorem ne_invariant
    {valueValid : SourceFile → Statement → Prop}
    {parser : Parser Statement}
    (contract : StatementTotalityContract valueValid parser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error :=
  contract.invariantFree.ne_invariant input inputValid error

end StatementTotalityContract

/-- Both complete branch contracts compose through recognized fallback. -/
theorem recognizedStatementOrFallback_totalityContract
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement)
    (primaryContract : StatementTotalityContract valueValid primary)
    (fallbackContract : StatementTotalityContract valueValid fallback) :
    StatementTotalityContract valueValid
      (recognizedStatementOrFallback primary fallback) := {
  toStatementParserContract :=
    recognizedStatementOrFallback_contract primary fallback
      primaryContract.toStatementParserContract
      fallbackContract.toStatementParserContract
  invariantFree := recognizedStatementOrFallback_invariantFreeOnValid
    primary fallback primaryContract.invariantFree
      fallbackContract.invariantFree
}

end Solcore.Syntax.Parser.TermInternals
