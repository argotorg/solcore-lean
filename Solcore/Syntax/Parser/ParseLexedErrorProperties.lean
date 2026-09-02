import Solcore.Syntax.Parser.CanonicalParserTotalityProperties

/-! Exact origin of exceptional results at the public token-to-file boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- An exceptional token-to-file result is exactly its preflight validation
failure. Once validation succeeds, production parsing is total. -/
theorem productionParseLexed_error_iff_validateLexed_error
    (file : SourceFile) (lexed : LexedFile) (error : ParserInvariantError) :
    parseLexed file lexed = .error error ↔
      validateLexed file lexed = .error error := by
  constructor
  · intro failed
    cases validation : validateLexed file lexed with
    | error validationError =>
        unfold parseLexed at failed
        rw [validation] at failed
        change Except.error validationError = Except.error error at failed
        cases failed
        rfl
    | ok witness =>
        cases witness
        have valid := validateLexed_ok_validFor file lexed validation
        exact (productionParseLexed_ne_error file lexed valid error failed).elim
  · intro failed
    unfold parseLexed
    rw [failed]
    simp only [bind, Except.bind]

end Solcore.Syntax.Parser
