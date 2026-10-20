import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionContracts

/-! Statement typing in a retained final source closes the recursive state
invariant using the actual inference call. Only the lexical context fields
are read from the judgment, so the source need not be the intermediate table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem RecursiveStatementInvariant.of_retained_statement_typing
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {finalized : Frontend.SourceInference.Result}
    {initialContext finalContext : SourceSemantics.Context}
    {semanticSource : TypedSource} {facts : StatementFacts}
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial initialContext)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (resultActive : ActiveLocalContextInvariant result.state
      finalized.substitution finalContext)
    (resultBindersBelow : result.state.LocalBindersBelowNextLocal)
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (resultSchemeIsolation : ActiveSchemeQuantifierIsolation result.state)
    (typing : StatementHasType
      semanticSource
      { returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      initialContext result.id finalContext facts) :
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      result.state finalContext := by
  have properties := Detail.inferStatementFuel_inferenceProperties
    initialInvariant.ready signatureFormation functionsCanonical
    initialInvariant.returnBelow success
  have fields := statementHasType_nonlocal_fields_eq typing
  refine {
    active := resultActive
    ready := properties.2.1
    returnBelow := initialInvariant.returnBelow.weaken properties.1.next_le
    bindersBelow := resultBindersBelow
    nodesBelow := (Detail.inferStatementFuel_occurrenceBoundExtends success
      ).nodesBelowNextOccurrence initialInvariant.nodesBelow
    schemeIsolation := resultSchemeIsolation
    substitutionExtension := resultSubstitutionExtension
    signaturesEq := fields.1.trans initialInvariant.signaturesEq
    typeParametersEq := fields.2.1.trans initialInvariant.typeParametersEq
    declarationEq := fields.2.2.1.trans initialInvariant.declarationEq
    residual := fields.2.2.2.1.trans initialInvariant.residual
    solvedRequirementsEq := fields.2.2.2.2.1.trans
      initialInvariant.solvedRequirementsEq
    assumptionsMono := ?_
  }
  rw [fields.2.2.2.2.2]
  exact initialInvariant.assumptionsMono

end Solcore.SourceSemantics.SourceInferenceSoundness
