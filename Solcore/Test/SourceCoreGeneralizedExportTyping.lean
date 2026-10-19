import Solcore.Test.SourceCoreGeneralizedExportSource
import Solcore.Test.SourceCoreSelectedGeneralizedLocalTypingValidation

/-! Declarative typing of all three original functions, constructed from
checked source observations. Compiler execution is not a typing premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

private def returnFacts (type : TypeSystem.Ty) : StatementFacts :=
  {type, hasValue := true, sawReturn := true, control := .returned}
private def localFacts : StatementFacts :=
  {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
private def factoryFacts (type : TypeSystem.Ty) : BodyFacts :=
  .cons localFacts (.singleton (returnFacts type))

structure BodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) where
  statements : List StatementId
  roots : function.typedBody.roots = statements.map NodeId.statement
  resultType : TypeSystem.Ty
  facts : BodyFacts
  factsType : facts.type = resultType
  context : SourceSemantics.Context
  finalContext : SourceSemantics.Context
  inputs : MonoBindersExtend signature.id (checkedBodyContext signatures signature function)
    function.typedBody.inputs signature.parameterTypes context
  typed : StatementsHaveType function.typedBody {returnType := resultType} context statements finalContext facts
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
  have same := roots_injective (roots.symm.trans certificate.roots)
  subst statements
  refine ⟨certificate.facts, ?_, ?_⟩
  · simpa only [certificate.result] using certificate.factsType
  · intro context extension
    have same := certificate.inputs.functional extension
    subst context
    exact ⟨certificate.finalContext, by simpa only [certificate.result] using certificate.typed⟩

def LambdaShape.initializerTyping {source : TypedSource} (shape : LambdaShape source)
    (lexical : SourceSemantics.Context)
    (inputLookup : lexical.LocalLookup shape.input.id shape.input.scheme)
    (inputRequirements : lexical.LocalSchemeRequirementsLookup shape.input.id shape.input.schemeRequirements) :
    IO (PLift (ExpressionHasType source (localSchemeInitializerContext lexical shape.binder)
      shape.lambda.id shape.binder.scheme.body)) := do
  let principal := localSchemeInitializerContext lexical shape.binder
  let parameterContext := principal.withLocal shape.parameter.id shape.parameter.scheme shape.parameter.schemeRequirements
  let ⟨extended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder principal source.owner shape.parameter
  let ⟨different⟩ ← observe (shape.parameter.id ≠ shape.input.id) "export distinct captured and lambda parameter"
  have lookup : parameterContext.LocalLookup shape.bodyBinder.id shape.bodyBinder.scheme := by
    rcases shape.bodyChoice with same | same
    · rw [same]; exact extended.local_self
    · rw [same]
      exact .tail different inputLookup
  have requirements : parameterContext.LocalSchemeRequirementsLookup
      shape.bodyBinder.id shape.bodyBinder.schemeRequirements := by
    rcases shape.bodyChoice with same | same
    · rw [same]; exact extended.local_scheme_requirements_self
    · rw [same]
      exact .tail different inputRequirements
  let ⟨readTyped⟩ ← read shape.bodyRead parameterContext lookup requirements
  let ⟨returnType⟩ ← observe (shape.bodyReturn.type = shape.resultType) "export original lambda return type"
  have returned : StatementHasType source {returnType := shape.resultType} parameterContext
      shape.bodyReturn.id parameterContext (returnFacts shape.resultType) :=
    .returnValue (lookupStatement?_sound shape.bodyFound) shape.bodyForm readTyped returnType
  have parameters : MonoBindersExtend source.owner principal [shape.parameter]
      [.variable shape.typeVariable] parameterContext :=
    .cons shape.parameterScheme extended (.nil _)
  have form : ExpressionFormHasRawType source principal shape.lambda.form
      (.function (.variable shape.typeVariable) shape.resultType) (.ordinary []) := by
    rw [shape.lambdaForm]
    exact .lambda (by simp) parameters (.singleton returned)
      (by simp [BodyCompletes, BodyFacts.singleton, returnFacts, ControlSummary.returned])
  let ⟨typed⟩ ← uncoerced principal shape.lambda
    (.function (.variable shape.typeVariable) shape.resultType) shape.lambdaFound form
  return ⟨by simpa only [shape.scheme] using typed⟩

private def factoryInitialization {source : TypedSource} (shape : LambdaShape source)
    (lexical : SourceSemantics.Context) (result : TypeSystem.Ty)
    (inputLookup : lexical.LocalLookup shape.input.id shape.input.scheme)
    (inputRequirements : lexical.LocalSchemeRequirementsLookup shape.input.id shape.input.schemeRequirements) :
    IO (PLift (StatementHasType source {returnType := result} lexical shape.initialized.id
      (lexical.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements) localFacts) ×
      PLift (BinderExtends source.owner lexical shape.binder
        (lexical.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements))) := do
  let ⟨initializer⟩ ← shape.initializerTyping lexical inputLookup inputRequirements
  let ⟨extended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder lexical source.owner shape.binder
  let ⟨generalized⟩ ← generalizes lexical shape.binder
  let ⟨type⟩ ← observe (shape.initialized.type = .unit) "export original generalized declaration type"
  return ⟨⟨.letInitializedGeneralized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
    (by rw [shape.scheme]; simp) (LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements)
    generalized initializer extended type⟩, ⟨extended⟩⟩

private def observeMakeTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let shape ← observeMake function.typedBody
  let resultType := TypeSystem.Ty.product (.function .word .word) (.function .bool .bool)
  let ⟨inputTypes⟩ ← observe (signature.parameterTypes = [shape.principal.inputType]) "make signature input"
  let ⟨result⟩ ← observe (TypeSystem.Ty.productMany signature.returnTypes = resultType) "make signature result"
  let base := checkedBodyContext signatures signature function
  let lexical := base.withLocal shape.principal.input.id shape.principal.input.scheme shape.principal.input.schemeRequirements
  let ⟨inputExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder base signature.id shape.principal.input
  have inputs : MonoBindersExtend signature.id base function.typedBody.inputs signature.parameterTypes lexical := by
    rw [shape.principal.inputs, inputTypes]
    exact .cons shape.principal.inputScheme inputExtended (.nil _)
  let ⟨⟨initialized⟩,⟨extended⟩⟩ ← factoryInitialization shape.principal lexical resultType
    inputExtended.local_self inputExtended.local_scheme_requirements_self
  let finalContext := lexical.withLocal shape.principal.binder.id shape.principal.binder.scheme shape.principal.binder.schemeRequirements
  let ⟨wordTyped⟩ ← read shape.wordRead finalContext extended.local_self extended.local_scheme_requirements_self
  let ⟨boolTyped⟩ ← read shape.boolRead finalContext extended.local_self extended.local_scheme_requirements_self
  have tupleForm : ExpressionFormHasRawType function.typedBody finalContext shape.tuple.form resultType (.ordinary []) := by
    rw [shape.tupleForm]; exact .tuple (.cons wordTyped (.cons boolTyped (.nil _)))
  let ⟨tupleTyped⟩ ← uncoerced finalContext shape.tuple resultType shape.tupleFound tupleForm
  let ⟨returnedType⟩ ← observe (shape.returned.type = resultType) "make return type"
  have returned : StatementHasType function.typedBody {returnType := resultType} finalContext
      shape.returned.id finalContext (returnFacts resultType) :=
    .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tupleTyped returnedType
  return ⟨[shape.principal.initialized.id,shape.returned.id],shape.roots,resultType,factoryFacts resultType,
    by rfl,
    lexical,finalContext,inputs,.cons initialized (.singleton returned),result⟩

private def observeCaptureTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let shape ← observeCapture function.typedBody
  let resultType := TypeSystem.Ty.function .bool .word
  let ⟨inputTypes⟩ ← observe (signature.parameterTypes = [shape.principal.inputType]) "capture signature input"
  let ⟨result⟩ ← observe (TypeSystem.Ty.productMany signature.returnTypes = resultType) "capture signature result"
  let base := checkedBodyContext signatures signature function
  let lexical := base.withLocal shape.principal.input.id shape.principal.input.scheme shape.principal.input.schemeRequirements
  let ⟨inputExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder base signature.id shape.principal.input
  have inputs : MonoBindersExtend signature.id base function.typedBody.inputs signature.parameterTypes lexical := by
    rw [shape.principal.inputs, inputTypes]
    exact .cons shape.principal.inputScheme inputExtended (.nil _)
  let ⟨⟨initialized⟩,⟨extended⟩⟩ ← factoryInitialization shape.principal lexical resultType
    inputExtended.local_self inputExtended.local_scheme_requirements_self
  let finalContext := lexical.withLocal shape.principal.binder.id shape.principal.binder.scheme shape.principal.binder.schemeRequirements
  let ⟨typed⟩ ← read shape.read finalContext extended.local_self extended.local_scheme_requirements_self
  let ⟨returnedType⟩ ← observe (shape.returned.type = resultType) "capture return type"
  have returned : StatementHasType function.typedBody {returnType := resultType} finalContext
      shape.returned.id finalContext (returnFacts resultType) :=
    .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm typed returnedType
  return ⟨[shape.principal.initialized.id,shape.returned.id],shape.roots,resultType,factoryFacts resultType,
    by rfl,
    lexical,finalContext,inputs,.cons initialized (.singleton returned),result⟩

private def observeTickTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let shape ← observeTick function.typedBody
  let ⟨inputTypes⟩ ← observe (signature.parameterTypes = [.bool]) "tick signature input"
  let ⟨result⟩ ← observe (TypeSystem.Ty.productMany signature.returnTypes = .bool) "tick signature result"
  let base := checkedBodyContext signatures signature function
  let lexical := base.withLocal shape.input.id shape.input.scheme shape.input.schemeRequirements
  let ⟨extended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder base signature.id shape.input
  have inputs : MonoBindersExtend signature.id base function.typedBody.inputs signature.parameterTypes lexical := by
    rw [shape.inputs, inputTypes]; exact .cons shape.inputScheme extended (.nil _)
  let ⟨typed⟩ ← read shape.read lexical extended.local_self extended.local_scheme_requirements_self
  let ⟨returnedType⟩ ← observe (shape.returned.type = .bool) "tick return type"
  have returned : StatementHasType function.typedBody {returnType := .bool} lexical
      shape.returned.id lexical (returnFacts .bool) :=
    .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm typed returnedType
  return ⟨[shape.returned.id],shape.roots,.bool,.singleton (returnFacts .bool),
    by rfl,
    lexical,lexical,inputs,.singleton returned,result⟩

def observeBodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  if signature.name == "make" then observeMakeTyping signatures function signature
  else if signature.name == "capture" then observeCaptureTyping signatures function signature
  else if signature.name == "tick" then observeTickTyping signatures function signature
  else throw (IO.userError "unexpected original export function")

end Tests.SourceCoreGeneralizedExport
