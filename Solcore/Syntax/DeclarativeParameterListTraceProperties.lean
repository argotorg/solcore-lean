import Solcore.Syntax.DeclarativeParameterListTraceGrammar
import Solcore.Syntax.DeclarativeNamedParameterTraceProperties
import Solcore.Syntax.DeclarativeLambdaParameterTraceProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceAgreementProperties

/-! Exactness lifts from the public parameter outcomes. No child existence or
carrier premise is needed. Recovered events and committed terminal reports are
not asserted to be unconditionally protected against lexical suppression. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem functionParametersTraceExactOutcomeSpec :
    TraceExactOutcomeSpec FunctionParametersTraceParses FunctionParametersTraceRejects source endByte :=
  (trailingDelimitedListTraceOutcomeAgreement (opening := .leftParen) (closing := .rightParen)
    (allowEmpty := true) (context := .parameter)
    namedParameterTraceExactOutcomeSpec.toTraceOutcomeAgreement).toTraceExactOutcomeSpec

theorem lambdaParametersTraceExactOutcomeSpec :
    TraceExactOutcomeSpec LambdaParametersTraceParses LambdaParametersTraceRejects source endByte :=
  (trailingDelimitedListTraceOutcomeAgreement (opening := .leftParen) (closing := .rightParen)
    (allowEmpty := true) (context := .parameter)
    lambdaParameterTraceExactOutcomeSpec.toTraceOutcomeAgreement).toTraceExactOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
