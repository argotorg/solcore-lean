import Solcore.Syntax.DeclarativeImportTerminatorOutcomeGrammar

/-!
Parser-independent exact ordinary outcomes for top-item recovery. Recovery
consumes one mandatory token, scans up to the next top-item boundary, and
returns an error item without consuming that boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact stops of the scan after recovery consumed its mandatory first
token. A missing carrier slot inside the active window finishes recovery. -/
inductive TopItemRecoveryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      TopItemRecoveryStops input
  | boundary {input : Remainder}
      (starts : ImportTerminatorTopItemStartsAt input) :
      TopItemRecoveryStops input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      TopItemRecoveryStops input

/-- Canonical error item produced from the first and last consumed spans. -/
def recoveredTopItemValue (first last : SourceSpan) : Syntax.TopItem := {
  span := SourceSpan.cover first last
  leadingComments := []
  value := .error
}

/-- Exact priority-ordered scan after the mandatory first recovery token. -/
inductive TopItemRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.TopItem → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : TopItemRecoveryStops input) :
      TopItemRecoveryScanParses first last input
        (recoveredTopItemValue first last) input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {item : Syntax.TopItem}
      (continues : ¬ TopItemRecoveryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : TopItemRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } item output) :
      TopItemRecoveryScanParses first last input item output

/-- Successful recovery consumes one arbitrary current token before scanning. -/
inductive TopItemRecoveryParses :
    Remainder → Syntax.TopItem → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {item : Syntax.TopItem}
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : TopItemRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } item output) :
      TopItemRecoveryParses input item output

/-- Recovery rejects only when its mandatory first token is unavailable. -/
inductive TopItemRecoveryRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      TopItemRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      TopItemRecoveryRejects input input

end Solcore.Syntax.DeclarativeGrammar
