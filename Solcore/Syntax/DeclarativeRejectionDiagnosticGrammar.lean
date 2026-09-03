import Solcore.Syntax.DeclarativeGrammar
import Solcore.Syntax.Parser.Diagnostic

/-!
Independent observations and uncommitted rejection reports. The source and
window-end byte are explicit context, separate from the token remainder.
Only the shared diagnostic data catalog is used; reports emit no event yet.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Current-token observation, including unavailable carriers and window ends. -/
inductive CurrentInputAt (source : SourceId) (endByte : Nat) :
    Remainder → SourceSpan → Option TokenKind → Prop where
  | token {input : Remainder} {current : Token}
      (present : TokenAt input.tokens input.endIndex input.cursor current) :
      CurrentInputAt source endByte input current.span (some current.value)
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      CurrentInputAt source endByte input
        { source, startByte := endByte, endByte } none
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      CurrentInputAt source endByte input
        { source, startByte := endByte, endByte } none

/-- Exact unexpected report selected by an expectation and grammar context.
The caller, not this judgment, decides whether to commit it as a diagnostic. -/
inductive RejectAtReports (source : SourceId) (endByte : Nat)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (input : Remainder) : ParseDiagnostic → Prop where
  | reported {span : SourceSpan} {found : Option TokenKind}
      (current : CurrentInputAt source endByte input span found) :
      RejectAtReports source endByte expected context input
        { span, kind := .unexpected found expected context }

end Solcore.Syntax.DeclarativeGrammar
