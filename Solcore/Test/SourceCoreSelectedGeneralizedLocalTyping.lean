import Solcore.Test.SourceCoreSelectedGeneralizedLocalTypingValidation
import Solcore.Test.SourceCoreSelectedGeneralizedLocalFixture

/-! The actual original generalized identity body receives independent
declarative typing, including its principal initializer and both instances.
The observer checks finite metadata and constructs every typing rule. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics
open TypingValidation

def resultType : TypeSystem.Ty := .product .word .bool

def returnFacts (type : TypeSystem.Ty) : StatementFacts :=
  {type, hasValue := true, sawReturn := true, control := .returned}

def localFacts : StatementFacts :=
  {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}

def bodyFacts : BodyFacts := .cons localFacts (.singleton (returnFacts resultType))

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

def observeBodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let shape ← observeShape function.typedBody
  let ⟨inputTypes⟩ ← observe (signature.parameterTypes = [.bool]) "generalized original signature input"
  let ⟨result⟩ ← observe (TypeSystem.Ty.productMany signature.returnTypes = resultType)
    "generalized original signature result"
  let base := checkedBodyContext signatures signature function
  let lexical := base.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
  let ⟨flagExtended⟩ ← TypingValidation.binder base signature.id shape.flag
  let ⟨flagRequirements⟩ ← observe (shape.flag.schemeRequirements = []) "generalized input requirements"
  have inputs : MonoBindersExtend signature.id base function.typedBody.inputs signature.parameterTypes lexical := by
    rw [shape.inputs, inputTypes]
    exact .cons shape.flagScheme flagExtended (.nil _)
  let principal := localSchemeInitializerContext lexical shape.binder
  let parameterContext := principal.withLocal shape.parameter.id shape.parameter.scheme shape.parameter.schemeRequirements
  let ⟨parameterExtended⟩ ← TypingValidation.binder principal function.typedBody.owner shape.parameter
  let ⟨parameterTyped⟩ ← TypingValidation.read shape.parameterRead parameterContext
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
  let finalContext := lexical.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements
  let ⟨localExtended⟩ ← TypingValidation.binder lexical function.typedBody.owner shape.binder
  let ⟨generalized⟩ ← generalizes lexical shape.binder
  let ⟨initializedType⟩ ← observe (shape.initialized.type = .unit) "generalized original let type"
  have initialized : StatementHasType function.typedBody {returnType := resultType} lexical
      shape.initialized.id finalContext localFacts := by
    refine .letInitializedGeneralized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      (by rw [shape.scheme]; simp) (LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements)
      generalized ?_ localExtended initializedType
    simpa only [shape.scheme] using initializerTyped
  let ⟨wordRead⟩ ← TypingValidation.read shape.wordCall.callee finalContext
    localExtended.local_self localExtended.local_scheme_requirements_self
  let ⟨boolRead⟩ ← TypingValidation.read shape.boolCall.callee finalContext
    localExtended.local_self localExtended.local_scheme_requirements_self
  let ⟨different⟩ ← observe (shape.binder.id ≠ shape.flag.id) "generalized distinct input and local"
  let ⟨flagRead⟩ ← TypingValidation.read shape.flagRead finalContext
    (.tail different flagExtended.local_self) (.tail different flagExtended.local_scheme_requirements_self)
  let ⟨literalTyped⟩ ← word shape.literal finalContext
  let ⟨wordCall⟩ ← call shape.wordCall finalContext wordRead literalTyped
  let ⟨boolCall⟩ ← call shape.boolCall finalContext boolRead flagRead
  have tupleForm : ExpressionFormHasRawType function.typedBody finalContext shape.tuple.form resultType (.ordinary []) := by
    rw [shape.tupleForm]
    exact .tuple (.cons wordCall (.cons boolCall (.nil _)))
  let ⟨tupleTyped⟩ ← uncoerced finalContext shape.tuple resultType shape.tupleFound tupleForm
  let ⟨returnedType⟩ ← observe (shape.returned.type = resultType) "generalized original return type"
  have returned : StatementHasType function.typedBody {returnType := resultType} finalContext
      shape.returned.id finalContext (returnFacts resultType) :=
    .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tupleTyped returnedType
  return {
    statements := [shape.initialized.id, shape.returned.id]
    roots := shape.roots
    context := lexical
    finalContext := finalContext
    inputs := inputs
    typed := .cons initialized (.singleton returned)
    result := result }

end Tests.SourceCoreSelectedGeneralizedLocal
