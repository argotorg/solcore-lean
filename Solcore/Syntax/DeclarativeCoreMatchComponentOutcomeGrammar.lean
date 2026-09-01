import Solcore.Syntax.DeclarativeCoreBlockOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreMatchStatementGrammar

/-!
Diagnostic-inclusive ordinary success and exact rejection for Core match
components.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One ordinary `case pattern { ... }` arm.  Raw block-tail diagnostics do
not remove the successful syntax value. -/
inductive MatchCaseOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → Syntax.MatchCase → Remainder → Prop where
  | parsed {input afterMarker afterPattern output : Remainder}
      {pattern : Syntax.Pattern} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (patternParsed : patternOrdinary afterMarker pattern afterPattern)
      (bodyParsed : CoreBlockOrdinaryParses statementOrdinary .require
        afterPattern body output) :
      MatchCaseOrdinaryParses statementOrdinary patternOrdinary input {
        span := SourceSpan.cover markerSpan body.span
        value := { pattern, body }
      } output

/-- Exact first failing stage of one Core match case. -/
inductive MatchCaseRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (patternRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .caseKw)) :
      MatchCaseRejects statementOrdinary statementRejects patternOrdinary
        patternRejects input input
  | patternRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (patternRejected : patternRejects afterMarker rejected) :
      MatchCaseRejects statementOrdinary statementRejects patternOrdinary
        patternRejects input rejected
  | bodyRejected {input afterMarker afterPattern rejected : Remainder}
      {pattern : Syntax.Pattern} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (patternParsed : patternOrdinary afterMarker pattern afterPattern)
      (bodyRejected : CoreBlockRejects statementOrdinary statementRejects
        .require afterPattern rejected) :
      MatchCaseRejects statementOrdinary statementRejects patternOrdinary
        patternRejects input rejected

/-- Prioritized optional `default` success, including raw block-tail
diagnostics. -/
inductive OptionalDefaultBodyOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop) :
    Remainder → Option Syntax.Block → Remainder → Prop where
  | absent {input : Remainder}
      (defaultAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .defaultKw)) :
      OptionalDefaultBodyOrdinaryParses statementOrdinary input none input
  | present {input afterMarker output : Remainder} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .defaultKw) input markerSpan
        afterMarker)
      (bodyParsed : CoreBlockOrdinaryParses statementOrdinary .require
        afterMarker body output) :
      OptionalDefaultBodyOrdinaryParses statementOrdinary input (some body)
        output

/-- A present optional `default` rejects only through its raw body. -/
inductive OptionalDefaultBodyRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | bodyRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .defaultKw) input markerSpan
        afterMarker)
      (bodyRejected : CoreBlockRejects statementOrdinary statementRejects
        .require afterMarker rejected) :
      OptionalDefaultBodyRejects statementOrdinary statementRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
