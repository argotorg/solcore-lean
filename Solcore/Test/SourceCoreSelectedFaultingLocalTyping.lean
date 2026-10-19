import Solcore.Test.SourceCoreSelectedGeneralizedLocalTypingValidation
import Solcore.Test.SourceCoreSelectedFaultingLocalFixture

/-! The actual original generalized identity body receives independent
declarative typing, including its principal initializer and both instances.
The observer checks finite metadata and constructs every typing rule. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

def resultType : TypeSystem.Ty := .product .word .bool

def returnFacts (type : TypeSystem.Ty) : StatementFacts :=
  {type, hasValue := true, sawReturn := true, control := .returned}

def localFacts : StatementFacts :=
  {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}

def bodyFacts : BodyFacts := .cons localFacts (.cons localFacts (.cons localFacts (.singleton (returnFacts resultType))))

structure BodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) where
  statements : List StatementId
  roots : function.typedBody.roots = statements.map NodeId.statement
  context : SourceSemantics.Context
  finalContext : SourceSemantics.Context
  inputs : MonoBindersExtend signature.id (checkedBodyContext signatures signature function)
    function.typedBody.inputs signature.parameterTypes context
  typed : StatementsHaveType function.typedBody {returnType := resultType} context statements finalContext bodyFacts
  result : TypeSystem.Ty.productMany signature.returnTypes = resultType

private theorem roots_injective {left right : List StatementId}
    (mapped : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
    cases right with
    | nil => simp at mapped
    | cons other rest =>
      simp only [List.map_cons, List.cons.injEq] at mapped
      have headEq := NodeId.statement.inj mapped.1
      have tailEq := ih mapped.2
      rw [headEq, tailEq]

theorem BodyTyping.statements_typed {signatures : ProgramSignatures} {function : CheckedFunction}
    {signature : ProgramFunctionSignature} (certificate : BodyTyping signatures function signature) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = certificate.statements := roots_injective (roots.symm.trans certificate.roots)
  subst statements
  refine ⟨bodyFacts, ?_, ?_⟩
  · rw [certificate.result]; rfl
  · intro context extension
    have same := certificate.inputs.functional extension
    subst context
    exact ⟨certificate.finalContext, by simpa only [certificate.result] using certificate.typed⟩

private def originalCall {source : TypedSource} {binder : TypedBinder} {argument : ExpressionId} {type : TypeSystem.Ty}
    (shape : CallShape source binder argument type) :
    Tests.SourceCoreSelectedGeneralizedLocal.CallShape source binder argument type :=
  ⟨shape.callee, shape.node, shape.metadata, shape.found, shape.form, shape.arity,
    shape.argumentCoercions, shape.requirements, shape.coercions⟩

private def originalWord {source : TypedSource} (shape : WordNode source) :
    Tests.SourceCoreSelectedGeneralizedLocal.WordNode source :=
  ⟨shape.node, shape.literal, shape.resolution, shape.found, shape.form, shape.target,
    shape.requirements, shape.coercions⟩

def observeBodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let shape ← observeShape function.typedBody
  let ⟨inputTypes⟩ ← observe (signature.parameterTypes = [.bool]) "generalized original signature input"
  let ⟨result⟩ ← observe (TypeSystem.Ty.productMany signature.returnTypes = resultType)
    "generalized original signature result"
  let base := checkedBodyContext signatures signature function
  let lexical := base.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
  let ⟨flagExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder base signature.id shape.flag
  let ⟨flagRequirements⟩ ← observe (shape.flag.schemeRequirements = []) "generalized input requirements"
  have inputs : MonoBindersExtend signature.id base function.typedBody.inputs signature.parameterTypes lexical := by
    rw [shape.inputs, inputTypes]
    exact .cons shape.flagScheme flagExtended (.nil _)
  let principal := localSchemeInitializerContext lexical shape.binder
  let parameterContext := principal.withLocal shape.parameter.id shape.parameter.scheme shape.parameter.schemeRequirements
  let ⟨parameterExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder principal function.typedBody.owner shape.parameter
  let ⟨parameterTyped⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.parameterRead parameterContext
    parameterExtended.local_self parameterExtended.local_scheme_requirements_self
  let ⟨identityType⟩ ← observe (shape.identityReturn.type = .variable shape.typeVariable)
    "generalized original identity return type"
  have identity : StatementHasType function.typedBody {returnType := .variable shape.typeVariable}
      parameterContext shape.identityReturn.id parameterContext (returnFacts (.variable shape.typeVariable)) :=
    .returnValue (lookupStatement?_sound shape.identityFound) shape.identityForm parameterTyped identityType
  have parameterInputs : MonoBindersExtend function.typedBody.owner principal [shape.parameter]
      [.variable shape.typeVariable] parameterContext :=
    .cons shape.parameterScheme parameterExtended (.nil _)
  have lambdaForm : ExpressionFormHasRawType function.typedBody principal shape.lambda.form
      (.function (.variable shape.typeVariable) (.variable shape.typeVariable)) (.ordinary []) := by
    rw [shape.lambdaForm]
    exact .lambda (by simp) parameterInputs (.singleton identity) (by simp [BodyCompletes, BodyFacts.singleton, returnFacts, ControlSummary.returned])
  let ⟨initializerTyped⟩ ← uncoerced principal shape.lambda
    (.function (.variable shape.typeVariable) (.variable shape.typeVariable)) shape.lambdaFound lambdaForm
  let generalizedContext := lexical.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements
  let ⟨localExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder lexical function.typedBody.owner shape.binder
  let ⟨generalized⟩ ← generalizes lexical shape.binder
  let ⟨initializedType⟩ ← observe (shape.initialized.type = .unit) "generalized original let type"
  have initialized : StatementHasType function.typedBody {returnType := resultType} lexical
      shape.initialized.id generalizedContext localFacts := by
    refine .letInitializedGeneralized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      (by rw [shape.scheme]; simp) (LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements)
      generalized ?_ localExtended initializedType
    simpa only [shape.scheme] using initializerTyped
  let ⟨wordRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.wordCall.callee generalizedContext
    localExtended.local_self localExtended.local_scheme_requirements_self
  let ⟨literalTyped⟩ ← word (originalWord shape.literal) generalizedContext
  let ⟨wordCall⟩ ← call (originalCall shape.wordCall) generalizedContext wordRead literalTyped
  let valueContext := generalizedContext.withLocal shape.valueBinder.id shape.valueBinder.scheme shape.valueBinder.schemeRequirements
  let ⟨valueExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder generalizedContext function.typedBody.owner shape.valueBinder
  let ⟨valueType⟩ ← observe (shape.valueInitialized.type = .unit) "interleaved ordinary initialized type"
  let valueGeneralizes : PLift (SchemeGeneralizes generalizedContext shape.valueBinder.scheme) ←
    match accepted : validateSchemeGeneralizes generalizedContext shape.valueBinder.scheme with
    | .error _ => throw (IO.userError "interleaved exact ordinary generalization")
    | .ok () => pure ⟨validateSchemeGeneralizes_success accepted⟩
  have valueInitialized : StatementHasType function.typedBody {returnType := resultType} generalizedContext
      shape.valueInitialized.id valueContext localFacts :=
    .letInitialized (lookupStatement?_sound shape.valueFound) shape.valueForm
      (by simpa only [shape.valueScheme, originalCall, TypeSystem.Scheme.mono] using wordCall)
      (by rw [shape.valueScheme]; rfl) valueGeneralizes.down valueExtended valueType
  let finalContext := valueContext.withLocal shape.absentBinder.id shape.absentBinder.scheme shape.absentBinder.schemeRequirements
  let ⟨absentExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder valueContext function.typedBody.owner shape.absentBinder
  let ⟨absentType⟩ ← observe (shape.absentDeclared.type = .unit) "faulting absent declaration type"
  let absentGeneralizes : PLift (SchemeGeneralizes valueContext shape.absentBinder.scheme) ←
    match accepted : validateSchemeGeneralizes valueContext shape.absentBinder.scheme with
    | .error _ => throw (IO.userError "faulting absent generalization")
    | .ok () => pure ⟨validateSchemeGeneralizes_success accepted⟩
  have absentDeclared : StatementHasType function.typedBody {returnType := resultType} valueContext
      shape.absentDeclared.id finalContext localFacts :=
    .letUninitialized (lookupStatement?_sound shape.absentFound) shape.absentForm
      (by rw [shape.absentScheme]; rfl) absentGeneralizes.down absentExtended absentType
  let ⟨absentDifferent⟩ ← observe (shape.absentBinder.id ≠ shape.binder.id) "faulting distinct generalized and absent binders"
  let ⟨absentFlagDifferent⟩ ← observe (shape.absentBinder.id ≠ shape.flag.id) "faulting distinct input and absent binder"
  let ⟨different⟩ ← observe (shape.binder.id ≠ shape.flag.id) "interleaved distinct input and generalized local"
  let ⟨valueDifferent⟩ ← observe (shape.valueBinder.id ≠ shape.binder.id) "interleaved distinct local binders"
  let ⟨flagDifferent⟩ ← observe (shape.valueBinder.id ≠ shape.flag.id) "interleaved distinct input and ordinary local"
  let ⟨boolRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.boolCall.callee finalContext
    (.tail absentDifferent (.tail valueDifferent localExtended.local_self))
    (.tail absentDifferent (.tail valueDifferent localExtended.local_scheme_requirements_self))
  let ⟨flagRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.flagRead finalContext
    (.tail absentFlagDifferent (.tail flagDifferent (.tail different flagExtended.local_self)))
    (.tail absentFlagDifferent (.tail flagDifferent (.tail different flagExtended.local_scheme_requirements_self)))
  let ⟨absentRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.absentRead finalContext
    absentExtended.local_self absentExtended.local_scheme_requirements_self
  let ⟨boolCall⟩ ← call (originalCall shape.boolCall) finalContext boolRead flagRead
  have tupleForm : ExpressionFormHasRawType function.typedBody finalContext shape.tuple.form resultType (.ordinary []) := by
    rw [shape.tupleForm]
    exact .tuple (.cons absentRead (.cons boolCall (.nil _)))
  let ⟨tupleTyped⟩ ← uncoerced finalContext shape.tuple resultType shape.tupleFound tupleForm
  let ⟨returnedType⟩ ← observe (shape.returned.type = resultType) "generalized original return type"
  have returned : StatementHasType function.typedBody {returnType := resultType} finalContext
      shape.returned.id finalContext (returnFacts resultType) :=
    .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tupleTyped returnedType
  return {
    statements := [shape.initialized.id, shape.valueInitialized.id, shape.absentDeclared.id, shape.returned.id]
    roots := shape.roots
    context := lexical
    finalContext := finalContext
    inputs := inputs
    typed := .cons initialized (.cons valueInitialized (.cons absentDeclared (.singleton returned)))
    result := result }

end Tests.SourceCoreSelectedFaultingLocal
