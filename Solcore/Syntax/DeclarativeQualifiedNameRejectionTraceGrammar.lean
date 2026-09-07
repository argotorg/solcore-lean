import Solcore.Syntax.DeclarativeQualifiedNameTraceGrammar
import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Independent dotted-name rejection reports and earlier checked-name events.
An absent dot ends a successful tail; only a selected dot can expose failure. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive DottedIdentifierTailTraceRejects (context : ParseContext)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | componentRejected {input afterDot : Remainder} {report : ParseDiagnostic}
      (dotSpan : SourceSpan)
      (dot : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (absent : IdentifierAbsentAt afterDot)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] }
        context afterDot report) :
      DottedIdentifierTailTraceRejects context source endByte input afterDot report []
  | laterRejected {input afterDot afterComponent rejected : Remainder}
      {component : Syntax.Identifier} {report : ParseDiagnostic}
      {headTrace tailTrace : List ParseDiagnostic}
      (dotSpan : SourceSpan)
      (dot : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (name : IdentifierTraceParses afterDot component afterComponent headTrace)
      (tail : DottedIdentifierTailTraceRejects context source endByte
        afterComponent rejected report tailTrace) :
      DottedIdentifierTailTraceRejects context source endByte input rejected report
        (headTrace ++ tailTrace)

inductive QualifiedNameTraceRejects (context : ParseContext)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | firstRejected {input : Remainder} {report : ParseDiagnostic}
      (absent : IdentifierAbsentAt input)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] }
        context input report) :
      QualifiedNameTraceRejects context source endByte input input report []
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.Identifier} {report : ParseDiagnostic}
      {firstTrace tailTrace : List ParseDiagnostic}
      (head : IdentifierTraceParses input first afterFirst firstTrace)
      (tail : DottedIdentifierTailTraceRejects context source endByte
        afterFirst rejected report tailTrace) :
      QualifiedNameTraceRejects context source endByte input rejected report
        (firstTrace ++ tailTrace)

end Solcore.Syntax.DeclarativeGrammar
