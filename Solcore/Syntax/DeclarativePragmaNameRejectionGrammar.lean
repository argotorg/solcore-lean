import Solcore.Syntax.DeclarativePragmaOutcomeGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Independent exact first-name rejection of a pragma declaration. The
uncommitted failure report is distinguished from an emitted diagnostic. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A pragma marker is consumed, then an unavailable raw name selects the
current-input failure span and found token under fixed source/byte context. -/
inductive PragmaNameMissingAt (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → SourceSpan → Option TokenKind → Prop where
  | missing {input afterKeyword : Remainder} {marker failureSpan : SourceSpan}
      {found : Option TokenKind}
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
      (nameAbsent : IdentifierAbsentAt afterKeyword)
      (current : CurrentInputAt source endByte afterKeyword failureSpan found) :
      PragmaNameMissingAt source endByte input afterKeyword failureSpan found

/-- The exact missing-name report refines the existing ordinary pragma rejection. -/
theorem PragmaNameMissingAt.rejects
    {source : SourceId} {endByte : Nat} {input after : Remainder}
    {failureSpan : SourceSpan} {found : Option TokenKind}
    (missing : PragmaNameMissingAt source endByte input after failureSpan found) :
    PragmaDeclRejects input after := by
  cases missing with
  | missing keywordParsed nameAbsent _ =>
      exact .nameRejected _ keywordParsed (.absent nameAbsent)

end Solcore.Syntax.DeclarativeGrammar
