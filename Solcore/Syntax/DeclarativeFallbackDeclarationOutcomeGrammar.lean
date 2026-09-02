import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeGrammar

/-!
Parser-independent ordinary success and exact sequential rejection for
canonical contract fallback declarations.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Fallback parameter validation is a pure stage.  Empty parameters pass
silently, while retained nonempty parameters take the diagnosed success path;
neither branch consumes a token. -/
inductive FallbackParameterValidationOrdinaryParses
    (parameters : DelimitedList Syntax.FunctionParameter) :
    Remainder → Remainder → Prop where
  | empty {input : Remainder}
      (parameterless : parameters.elements = []) :
      FallbackParameterValidationOrdinaryParses parameters input input
  | diagnosed {input : Remainder}
      (nonempty : parameters.elements ≠ []) :
      FallbackParameterValidationOrdinaryParses parameters input input

/-- Exact ordinary fallback success, including retained invalid parameters,
their diagnostic-only validation, fixed-order entry modifiers, and balanced
required-body recovery. -/
inductive FallbackDeclOrdinaryParses :
    Remainder → Syntax.FallbackDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterParameters afterValidation afterModifiers
        output : Remainder}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {payableMarker : Option SourceSpan} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .fallbackKw)
        input markerSpan afterMarker)
      (parametersParsed : FunctionParametersOrdinaryParses afterMarker
        parameters afterParameters)
      (validationParsed : FallbackParameterValidationOrdinaryParses parameters
        afterParameters afterValidation)
      (modifiersParsed : ContractEntryModifiersOrdinaryParses afterValidation
        payableMarker afterModifiers)
      (bodyParsed : IsolatedCoreBlockPublicOrdinaryParses .require
        afterModifiers body output) :
      FallbackDeclOrdinaryParses input {
        span := SourceSpan.cover markerSpan body.span
        value := { parameters, payableMarker, body }
      } output

/-- Exact first rejecting stage of an ordinary fallback attempt.  Parameter
validation and entry modifiers cannot reject, so only the marker, parameter
list, or uncaptured required body can reject. -/
inductive FallbackDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw)) :
      FallbackDeclRejects input input
  | parametersRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .fallbackKw)
        input markerSpan afterMarker)
      (parametersRejected : FunctionParametersRejects afterMarker rejected) :
      FallbackDeclRejects input rejected
  | bodyRejected
      {input afterMarker afterParameters afterValidation afterModifiers
        rejected : Remainder}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {payableMarker : Option SourceSpan} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .fallbackKw)
        input markerSpan afterMarker)
      (parametersParsed : FunctionParametersOrdinaryParses afterMarker
        parameters afterParameters)
      (validationParsed : FallbackParameterValidationOrdinaryParses parameters
        afterParameters afterValidation)
      (modifiersParsed : ContractEntryModifiersOrdinaryParses afterValidation
        payableMarker afterModifiers)
      (bodyRejected : IsolatedCoreBlockPublicRejects .require afterModifiers
        rejected) :
      FallbackDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
