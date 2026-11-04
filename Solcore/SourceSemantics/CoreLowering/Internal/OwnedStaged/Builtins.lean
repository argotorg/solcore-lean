import Solcore.SourceSemantics.CoreLowering.BuiltinCallTypedCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers

/-!
# Staged bounds: builtin calls

Builtin application in staged bodies: call certificates, Source inversion, argument rows, parent bounds and the dispatch of indirect builtin application.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinCallCertificates
/-! A direct builtin call keeps the actual builtin inventory entry, callable
descriptor and accepted ordered argument actions. The callable hooks are the
real retained compiler policy; no child execution or callable body law is an
input. The synthetic callee is metadata, rather than an evaluated child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinCallCertificates
open Core Frontend SourceInference

structure Receipt (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (compilation : SourceCoreFunctions.Context)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id callee : ExpressionId)
    (ids : List ExpressionId) (function : BuiltinFunctionId)
    (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  node : ExpressionNode
  metadata : CompatibleExpressionReads.Metadata values.checked source id node lowered.type
  form : node.form = .call callee ids (.builtinFunction function)
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
    compilation source scope id reasonAt = .ok lowered
  validated : SourceCoreElaboration.validateBuiltinFunctionCall source node callee ids function = .ok ()
  native : SourceCoreGeneralFunctions.CallableContext
  active : TypeSystem.Substitution
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active
  descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function)
  index : Nat
  identity : Word
  inventory : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index)
  identitySelected : Word.ofNat? (compilation.globals.length + index + 1) = some identity
  calleeNode : ExpressionNode
  calleeReadType : Ty
  calleeRead : policy.readExpression source callee = .ok (calleeNode, calleeReadType)
  calleeType : calleeNode.type = function.type
  codes : List SourceCoreBasic.LoweredExpr
  generated : ids.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
    compilation source scope child reasonAt) = .ok codes
  parameter : (SourceCoreCalls.packArguments codes).type = SourceCoreInteger.builtinParameter function
  result : lowered.type = SourceCoreInteger.builtinResult function
  emitted : lowered.expression = CallableContract.call [⟨descriptor.id, none, none⟩]
    native.diagnostics.unknown (SourceCoreInteger.builtinResult function)
    (BuiltinCalls.Protocol.contracted function identity descriptor.id)
    (SourceCoreCalls.packArguments codes).expression

/-- The complete lowered expression is the authenticated builtin wrapper. -/
theorem Receipt.output
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {function : BuiltinFunctionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt policy body fuel compilation values source scope id callee ids function reasonAt lowered) :
    lowered = ⟨SourceCoreInteger.builtinResult function,
      CallableContract.call [⟨receipt.descriptor.id, none, none⟩] receipt.native.diagnostics.unknown
        (SourceCoreInteger.builtinResult function)
        (BuiltinCalls.Protocol.contracted function receipt.identity receipt.descriptor.id)
        (SourceCoreCalls.packArguments receipt.codes).expression⟩ := by
  cases lowered
  simp only [SourceCoreBasic.LoweredExpr.mk.injEq]
  exact ⟨receipt.result, receipt.emitted⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem descriptor_exists
    {native : SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {node : ExpressionNode}
    {callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
    {type : Ty} {calleeCode arguments expression : Expr}
    (form : node.form = .call callee ids (.builtinFunction function))
    (emitted : (SourceCoreGeneralFunctions.callablePolicy (some native) active).callCallable
      compilation source node type calleeCode arguments = .ok expression) :
    Nonempty (SourceCoreCallableContracts.Descriptor native.table (.builtin function)) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, form] at emitted
  cases selected : SourceCoreCallableContracts.descriptor native.table (.builtin function) with
  | error failure => simp [selected, Except.mapError, bind, Except.bind] at emitted
  | ok descriptor => exact ⟨descriptor⟩

/-- Authentic lowering determines the literal contracted builtin wrapper.
The source reader and callable policy are static equations from the producer. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.builtinFunction function))
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation values source scope id callee ids function reasonAt lowered) := by
  have original := accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
        compilation childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form] at accepted
      obtain ⟨pair, read, _remaining⟩ := bind_ok accepted
      rcases pair with ⟨other, type⟩
      have metadata := CompatibleExpressionReads.metadata_of_read (readPolicy.symm ▸ read)
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst other
      obtain ⟨calleeNode, calleeType, calleeCode, codes, expression, validated,
        calleeRead, reference, generated, parameter, result, emitted, rfl⟩ :=
        BuiltinCalls.call_of_accepted owner found read form (special _ _) original
      obtain ⟨descriptor⟩ := descriptor_exists form (callables ▸ emitted)
      cases reference with
      | @intro index identity calleeExpression _ calleeSourceType inventory identitySelected decorated =>
        rw [callables, ActualCallablePolicy.builtin_decoration native active compilation source calleeNode function
          (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) _ descriptor] at decorated
        cases decorated
        rw [callables, BuiltinCalls.Typed.builtin_call native active compilation source node callee ids function
          type _ _ descriptor form] at emitted
        cases emitted
        subst type
        exact ⟨{
          node := node
          metadata := metadata
          form := form
          accepted := original
          validated := validated
          native := native
          active := active
          callables := callables
          descriptor := descriptor
          index := index
          identity := identity
          inventory := inventory
          identitySelected := identitySelected
          calleeNode := calleeNode
          calleeReadType := calleeType
          calleeRead := calleeRead
          calleeType := calleeSourceType
          codes := codes
          generated := generated
          parameter := parameter
          result := rfl
          emitted := rfl }⟩
  · simp [owner, bind, Except.bind] at accepted

/-- The independent original typing fixes every argument's raw builtin type. -/
theorem source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.builtinFunction function))
    (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    DirectBuiltinCalleeValid source callee function ∧
      ExpressionsHaveTypes source context ids function.parameterTypes ∧ node.type = function.returnType := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | builtinCall calleeValid argumentsTyped => exact ⟨calleeValid, argumentsTyped, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinCallCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinSourceInversion
/-! Direct builtin calls execute their ordered argument vector and primitive.
Staging failures are inherited from those actual arguments. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinSourceInversion
open Frontend SourceInference Staging.Recursive

theorem source_types {source : TypedSource} {context : Context}
    {id callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.builtinFunction function))
    (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ExpressionsHaveTypes source context ids function.parameterTypes ∧ node.type = function.returnType := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize rawEq : node.type = actualType at raw
    cases raw with
    | builtinCall _calleeValid argumentsTyped => exact ⟨argumentsTyped, rfl⟩

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id callee : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Outcome}
  {function : BuiltinFunctionId} {arguments : List ExpressionId}

private theorem occurrence_form {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm requirements) : actualForm = node.form := by
  obtain ⟨actualNode, contains, actualFormEq, _, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact actualFormEq.symm.trans (congrArg ExpressionNode.form same)

theorem children
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.builtinFunction function))
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    (∃ sequenceSize invocationSize argumentsHeap values,
      size = Size.stepSize [sequenceSize, invocationSize] ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.values values) argumentsHeap ∧
      Size.Applies program registry invocationSize invocation context argumentsHeap
        (.builtin ⟨function⟩) values outcome after) ∨
    (∃ sequenceSize failure, size = Size.stepSize [sequenceSize] ∧
      outcome = .fault failure ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.fault failure) after) := by
  have actual : ∀ {actualForm requirements}, Occurrence invocation id actualForm requirements → actualForm = .call callee arguments (.builtinFunction function) :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | builtinApplied occurrence children applied =>
      obtain ⟨rfl, rfl, same⟩ := ExpressionForm.call.inj (actual occurrence)
      cases same
      exact .inl ⟨_, _, _, _, rfl, children, applied⟩
  | builtinArgumentsFault occurrence children =>
      obtain ⟨rfl, rfl, same⟩ := ExpressionForm.call.inj (actual occurrence)
      cases same
      exact .inr ⟨_, _, rfl, rfl, children⟩
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | tupleValue occurrence _ _ | tupleFault occurrence _ | constructorValue occurrence _ _ | constructorFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _
  | unaryInvalid occurrence _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _
  | binaryInvalid occurrence _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _
  | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _
  | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds
/-! A builtin applies at the actual heap and store reached by its arguments.
Ordered scalar representations exclude physical arity and type faults. The
literal contracted primitive runs once and keeps both endpoints unchanged.
Source and Core grades are independent. User applications and their staged
body hypotheses are separate from these three builtin constructors. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open BuiltinBodyMeaning CallableIndexedBuiltinValues BuiltinCalls
open CallableIndexedOwnedFunctionState
universe u

private theorem payload_evaluates {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (inputs : InputRep function arguments input)
    (identity contract : Word) (captured : Environment) (store : Store) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      Evaluates [BuiltinCalls.Protocol.contractedValue function identity contract captured, input]
        store CallableIndexedLambdaCalls.applyPayload (.inRight .word nativeResult) store := by
  obtain ⟨sourceResult, nativeResult, applied, represented, body⟩ := inputs.body_meaning captured store
  exact ⟨sourceResult, nativeResult, applied, represented,
    .apply (.second (.first (.var rfl))) (.var rfl) body⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {registry : SourceCoreRawMetadata.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : BuiltinFunctionId}
  {native : Value} {nativeType : Ty}
  (builtin : Represents compiled.indexed world function.type (.builtin ⟨function⟩) native nativeType)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : ValuesRep compiled.compatible.checked registry functions mapping world
    function.parameterTypes arguments payloads (CompatibleBuiltinMeaning.argumentTypes function))
  {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {before : Dynamic.Heap} {store : Store}

include observations represented in
/-- All three original builtin rules are inspected. The actual represented
inputs rule out both fault constructors without an accepted gate premise. -/
theorem source_value {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies program stages size invocation context
      before (.builtin ⟨function⟩) arguments outcome after) :
    ∃ value, outcome = .value value ∧ after = before ∧
      size = Staging.Recursive.Size.stepSize [] ∧ Dynamic.BuiltinApplies function arguments value := by
  have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
  cases called with
  | builtin applied => exact ⟨_, rfl, rfl, rfl, applied⟩
  | builtinArity mismatch =>
    exact False.elim (InputRep.excludes_callable_fault inputs
      (program := program) (context := context) (before := before)
      (caller := []) (invocation := []) (.builtinArity mismatch))
  | builtinType arity mismatch =>
    exact False.elim (InputRep.excludes_callable_fault inputs
      (program := program) (context := context) (before := before)
      (caller := []) (invocation := []) (.builtinArgumentType arity mismatch))

include observations builtin represented in
/-- The actual primitive yields a finite native trace at the argument store.
Its grade is recorded independently of the original Source grade. -/
theorem preserves {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies program stages sourceSize invocation context
      before (.builtin ⟨function⟩) arguments outcome after) :
    ∃ nativeSize value,
      EvaluationSize nativeSize [native, DataPatternValues.packValues payloads] store
        CallableIndexedLambdaCalls.applyPayload value store ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        mapping world function.returnType (SourceCoreInteger.builtinResult function) faults outcome value ∧
      after = before ∧ sourceSize = Staging.Recursive.Size.stepSize [] := by
  have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
  obtain ⟨sourceResult, sameOutcome, sameHeap, sourceGrade, applied⟩ :=
    source_value functions observations represented called
  subst outcome
  generalize typeEq : function.type = sourceType at builtin
  cases builtin with
  | builtin selected number descriptor typed =>
    obtain ⟨actualResult, nativeResult, actual, related, evaluated⟩ :=
      payload_evaluates inputs _ descriptor.id _ store
    have same := actual.functional applied
    subst actualResult
    obtain ⟨nativeSize, sized⟩ := evaluation_has_size evaluated
    exact ⟨nativeSize, _, sized,
      .value (CompatibleBuiltinMeaning.result_represents inputs applied related), sameHeap, sourceGrade⟩

include observations builtin represented in
/-- Original native completion determines the same primitive value and store.
The reflected Source constructor has its own constant application grade. -/
theorem reflects {nativeSize : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize nativeSize [native, DataPatternValues.packValues payloads]
      store CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sourceResult,
      Staging.Recursive.Size.Applies program stages (Staging.Recursive.Size.stepSize [])
        invocation context before (.builtin ⟨function⟩) arguments (.value sourceResult) before ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        mapping world function.returnType (SourceCoreInteger.builtinResult function) faults
        (.value sourceResult) value ∧
      Dynamic.BuiltinApplies function arguments sourceResult ∧ finalStore = store := by
  have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
  generalize typeEq : function.type = sourceType at builtin
  cases builtin with
  | builtin selected number descriptor typed =>
    obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ :=
      payload_evaluates inputs _ descriptor.id _ store
    obtain ⟨same, sameStore⟩ := evaluation_deterministic completed.sound evaluated
    subst value
    exact ⟨sourceResult, .builtin applied,
      .value (CompatibleBuiltinMeaning.result_represents inputs applied related), applied, sameStore⟩

section Caller
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (argumentState : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : CallableIndexedOwnedSourceAdmission.Admission bridge context argumentState)

include admitted in
/-- The same reached caller witness is the primitive post. Value typing comes
from the actual scalar Source primitive, and deep heap typing is unchanged. -/
theorem argument_post {sourceResult : Dynamic.Value}
    (applied : Dynamic.BuiltinApplies function arguments sourceResult) :
    ∃ reached : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      reached = argumentState ∧ callerProtocol.Relates argumentState reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        function.returnType (.value sourceResult) reached := by
  refine ⟨argumentState, rfl, callerProtocol.refl argumentState, admitted.rows, ?_⟩
  intro value same
  cases same
  exact ⟨applied.preserves.2, admitted.heap⟩
end Caller

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds
/-! The real contracted builtin call executes its ordered arguments once.
Its literal callee and both gates are pure; successful primitive application
keeps the reached heap, store and caller records. Child failures retain their
original Source scope and diagnostic. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open BuiltinCalls.Protocol
open GenericExpressionMeaning (agree_prefix rename_prefix)
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private theorem values_rep {checked : SourceCoreCompatibleCatalog.Checked} {receiving : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel checked receiving functions)
      mapping world types natives sources payloads) :
    ValuesRep checked receiving functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

private theorem prefixed_typed {definitions : DataEnvironment} {world : StoreTyping}
    {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (function : BuiltinFunctionId) (identity contract : Word) :
    RuntimeEnvironmentHasTypes world (.unit :: contractedValue function identity contract actual :: actual)
      (.unit :: CallableContract.functionType (SourceCoreInteger.builtinParameter function)
        (SourceCoreInteger.builtinResult function) :: actualContext) definitions := by
  have closureTyped := SourceCoreInteger.builtinClosure_hasType (scope := actualContext) (definitions := definitions) function
  cases closureTyped with
  | lambda _ _ body => exact .cons .unit (.cons (.pair (.pair (.inRight .word) (.closure typed body)) .word) typed)

private theorem contracted_rename (function : BuiltinFunctionId) (identity contract : Word) (ξ : Renaming) :
    (contracted function identity contract).rename ξ = contracted function identity contract := by
  cases function <;> rfl

private theorem call_rename (function : BuiltinFunctionId) (identity contract unknown : Word)
    (arguments : Expr) (ξ : Renaming) :
    (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (contracted function identity contract) arguments).rename ξ =
    CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (contracted function identity contract) (arguments.rename ξ) := by
  simp [CallableContract.call, LanguageResult.bind, CallableContract.dispatch, CallableContract.guardResult,
    CallableContract.Gate.reason, LanguageResult.success, LanguageResult.failure,
    contracted_rename, Expr.rename, Renaming.lift]

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
  {ids : List ExpressionId} {function : BuiltinFunctionId} {codes : List SourceCoreBasic.LoweredExpr}
  {identity contract unknown : Word}
  (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
    (SourceCoreInteger.builtinResult function))
  (form : node.form = .call callee ids (.builtinFunction function))
  (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "headCode" => SourceCoreBasic.LoweredExpr.mk (SourceCoreInteger.builtinResult function)
  (CallableContract.call [CallableContract.Gate.mk contract none none] unknown (SourceCoreInteger.builtinResult function)
    (contracted function identity contract) (SourceCoreBasic.LoweredExpr.expression (SourceCoreCalls.packArguments codes)))

include bridge functions observations faults unique wellFormed runtime covers metadata form nativeTypes in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids function.parameterTypes codes)
    (childMeaning : PreservesBelow bridge context model registry invocation children faults size) :
    PreservesAt bridge context model registry invocation (Point scope id headCode) faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨typing, sourceResult⟩ := CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types
    unique metadata.found form metadata.coercions typed
  have prefixed := prefixed_typed actualTyped function identity contract
  have agreesPrefix : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: contractedValue function identity contract actual :: actual) :=
    agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
  have originalTrace := trace
  rcases CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.children unique metadata.found form trace with
    ⟨sequenceSize, invocationSize, argumentsHeap, sources, sameSize, sourceTrace, applied⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, payloads, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_values bridge size sequence unique typing
        childMeaning environments heaps locals agreesPrefix prefixed initial admitted sourceTrace within
    have represented := values_rep payloads
    rw [nativeTypes] at represented
    have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
    obtain ⟨value, sameOutcome, sameHeap, _grade, primitive⟩ :=
      CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.source_value functions observations represented applied
    subst outcome
    subst after
    rw [rename_prefix, rename_prefix] at evaluated
    obtain ⟨actualResult, nativeResult, actualPrimitive, resultRep, completed⟩ := contracted_preserves
      (identity := identity) (contract := contract) (unknown := unknown) inputs evaluated
    have same := actualPrimitive.functional primitive
    subst actualResult
    refine ⟨.inRight .word nativeResult, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    · rw [call_rename]; exact completed
    · rw [sourceResult]
      exact .value (CompatibleBuiltinMeaning.result_represents inputs primitive resultRep)
    · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed originalTrace frame
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_fault bridge size sequence unique typing
        childMeaning environments heaps locals agreesPrefix prefixed initial admitted sourceTrace within
    rw [rename_prefix, rename_prefix] at evaluated
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    · rw [call_rename]
      exact CallableContract.call_argument_failure [⟨contract, none, none⟩] unknown
        (contracted_evaluates function identity contract actual store)
        (gates_accept contract unknown .beforeArguments) evaluated
    · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed originalTrace frame

include bridge functions observations faults unique wellFormed runtime covers metadata form nativeTypes in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids function.parameterTypes codes)
    (childMeaning : ReflectsBelow bridge context model registry invocation children faults size) :
    ReflectsAt bridge context model registry invocation (Point scope id headCode) faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨typing, sourceResult⟩ := CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types
    unique metadata.found form metadata.coercions typed
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.builtinFunction function)) :=
    ⟨node, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have prefixed := prefixed_typed actualTyped function identity contract
  have agreesPrefix : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: contractedValue function identity contract actual :: actual) :=
    agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
  rw [call_rename] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedBuiltinCallBounds.contracted_arguments_sized completed
  have shifted := argumentEvaluation
  rw [← rename_prefix, ← rename_prefix] at shifted
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
    CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge size sequence unique typing childMeaning
      environments heaps locals agreesPrefix prefixed initial admitted shifted smaller
  cases represented with
  | @values sources values payloads =>
    have represented := values_rep payloads
    rw [nativeTypes] at represented
    have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
    obtain ⟨sourceValue, nativeValue, primitive, resultRep, same, sameStore⟩ :=
      contracted_reflects inputs argumentEvaluation.sound completed.sound
    subst value
    subst finalStore
    have trace := Staging.Recursive.Size.Expression.builtinApplied occurrence sourceTrace
      (Staging.Recursive.Size.Applies.builtin primitive)
    refine ⟨_, _, argumentsHeap, finalMap, finalWorld, trace, ?_, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    · rw [sourceResult]
      exact .value (CompatibleBuiltinMeaning.result_represents inputs primitive resultRep)
    · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame
  | fault matched =>
    have failed := CallableContract.call_argument_failure
      (result := SourceCoreInteger.builtinResult function) [⟨contract, none, none⟩] unknown
      (contracted_evaluates function identity contract actual store)
      (gates_accept contract unknown .beforeArguments) argumentEvaluation.sound
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
    have trace := Staging.Recursive.Size.Expression.builtinArgumentsFault occurrence sourceTrace
    refine ⟨_, _, argumentsHeap, finalMap, finalWorld, trace, .fault matched, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinArgumentRows
/-! The actual builtin codebook row and the equal second gate supply physical
arity. Original callee typing and the independent Source/native pack receipts
then recover the ordered scalar arguments at the unchanged argument post.
This is a static input producer for the original builtin application proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {mapping : LocationMap} {world : StoreTyping}

private theorem function_builtin {sourceType : TypeSystem.Ty} {sourceValue : Dynamic.Value}
    {carrier : Value} {type : Ty}
    (positive : CallableIndexedOwnedContextualCellOrigins.FunctionOrigins
      headers keys bodyRegistry faults mapping world sourceType sourceValue carrier type) :
    ∀ function, sourceValue = .builtin function →
      CallableIndexedBuiltinValues.Represents compiled.indexed world sourceType sourceValue carrier type := by
  cases positive with
  | builtin related =>
    intro function _same
    cases related with
    | prior prior =>
      cases prior with
      | prior original =>
        cases original with
        | builtin builtin => exact builtin
  | closure member => intro function impossible; cases impossible
  | global related => intro function impossible; cases impossible

private theorem builtin_own_type {sourceType : TypeSystem.Ty} {function : Dynamic.BuiltinFunction}
    {carrier : Value} {type : Ty}
    (related : CallableIndexedBuiltinValues.Represents compiled.indexed world
      sourceType (.builtin function) carrier type) :
    CallableIndexedBuiltinValues.Represents compiled.indexed world
      function.id.type (.builtin function) carrier type := by
  cases related with
  | builtin selected number descriptor typed => exact .builtin selected number descriptor typed

/-- Only the actual contextual builtin branch is inverted. Compatible raw
views retain its same compiler descriptor, carrier and typed environment. -/
theorem builtin_member {sourceType : TypeSystem.Ty} {sourceValue : Dynamic.Value}
    {carrier : Value} {type : Ty}
    (represented : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world sourceType sourceValue carrier type) :
    ∀ function, sourceValue = .builtin function →
      CallableIndexedBuiltinValues.Represents compiled.indexed world
        function.id.type (.builtin function) carrier type := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    intro function same
    cases same
    exact builtin_own_type (function_builtin related function rfl)
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

private theorem native_type {function : Dynamic.BuiltinFunction} {carrier : Value} {type : Ty}
    (related : CallableIndexedBuiltinValues.Represents compiled.indexed world
      function.id.type (.builtin function) carrier type) :
    type = CallableContract.functionType (SourceCoreInteger.builtinParameter function.id)
      (SourceCoreInteger.builtinResult function.id) := by
  generalize sourceTypeEq : function.id.type = actualSourceType at related
  cases related
  rfl

private theorem native_count (function : BuiltinFunctionId) :
    (CompatibleBuiltinMeaning.argumentTypes function).length = function.parameterTypes.length := by
  cases function <;> rfl

private theorem values_represents
    {functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {sourceTypes : List TypeSystem.Ty} {nativeTypes : List Ty}
    {sources : List Dynamic.Value} {values : List Value}
    (represented : DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world sourceTypes nativeTypes sources values) :
    ValuesRep compiled.compatible.checked registry functions mapping world
      sourceTypes sources values nativeTypes := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

section Arguments
variable {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry faults profile}
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {function : Dynamic.BuiltinFunction} {carrier : Value}
  {sourceTypes : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
  {parameter result : TypeSystem.Ty}

/-- Every field concerns the same literal compiler, callee and ordered values.
No computation, body law, heap conversion or reached-state replacement is stored. -/
structure Rows : Prop where
  source_parameter : parameter = TypeSystem.Ty.productMany function.id.parameterTypes
  source_result : result = function.id.returnType
  original_result : compiler.original.type = function.id.returnType
  native_parameter : compiler.parameterType = SourceCoreInteger.builtinParameter function.id
  native_result : compiler.resultType = SourceCoreInteger.builtinResult function.id
  source_row : sourceTypes = function.id.parameterTypes
  native_row : compiler.codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function.id
  builtin : CallableIndexedBuiltinValues.Represents compiled.indexed world
    function.id.type (.builtin function) carrier compiler.calleeCode.type
  represented : ValuesRep compiled.compatible.checked registry
    (functionModel)
    mapping world function.id.parameterTypes sources values
    (CompatibleBuiltinMeaning.argumentTypes function.id)

include compiler in
/-- Equal physical count is the actual codebook branch, independent of packed
types. Those packs only identify rows after that count has been authenticated. -/
theorem at_arguments
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    {row : SourceCoreStageCodebook.Decision}
    (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
      sidecar site callee ids originalMetadata originalNode function carrier row)
    (equalCount : row.entry.parameterCount = ids.length)
    {context : SourceSemantics.Context} {calleeHeap : Dynamic.Heap}
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.builtin function) (.function parameter result))
    (calleeRelated : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world
      (.function parameter result) (.builtin function) carrier compiler.calleeCode.type)
    (represented : DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functionModel))
      mapping world sourceTypes (compiler.codes.map (·.type)) sources values)
    (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (originalResult : compiler.original.type = result) :
    Rows (functionModel := functionModel) (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (registry := registry) (faults := faults) (profile := profile)
      (mapping := mapping) (world := world) (function := function) (carrier := carrier)
      (sourceTypes := sourceTypes) (sources := sources) (values := values)
      (parameter := parameter) (result := result) compiler := by
  have builtin := builtin_member calleeRelated function rfl
  rcases calleeTyped.builtin_inv with ordinary | staged
  · change TypeSystem.Ty.function parameter result =
      TypeSystem.Ty.function (TypeSystem.Ty.productMany function.id.parameterTypes) function.id.returnType at ordinary
    have signature := TypeSystem.Ty.function.inj ordinary
    have nativeSignature : compiler.parameterType = SourceCoreInteger.builtinParameter function.id ∧
        compiler.resultType = SourceCoreInteger.builtinResult function.id := by
      have acceptedType := compiler.callableType
      rw [actualFunctionType] at acceptedType
      exact CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
        (acceptedType.trans (native_type builtin))
    have physical : function.id.parameterTypes.length = ids.length :=
      builtinAt.parameter_count.symm.trans equalCount
    have representedCount : compiler.codes.length = sources.length := by
      simpa only [List.length_map] using represented.length.1
    have actualCount : sources.length = function.id.parameterTypes.length :=
      representedCount.symm.trans (compiler.ordered_children.1.symm.trans physical.symm)
    have sourceRow : sourceTypes = function.id.parameterTypes :=
      CallableIndexedOwnedStoredArgumentAlignment.source_rows_of_bundle
        ((CallableIndexedOwnedStoredArgumentAlignment.source_length represented).trans actualCount)
        (bundle.trans signature.1)
    have nativePacked : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
        SourceCoreCompatibleCatalog.packTypes (CompatibleBuiltinMeaning.argumentTypes function.id) :=
      (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
        (compiler.packedType.symm.trans
          (nativeSignature.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function.id).symm))
    have nativeRow : compiler.codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function.id :=
      CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
        (represented.length.1.trans (actualCount.trans (native_count function.id).symm)) nativePacked
    have exactRows := values_represents represented
    rw [sourceRow, nativeRow] at exactRows
    exact ⟨signature.1, signature.2, originalResult.trans signature.2,
      nativeSignature.1, nativeSignature.2, sourceRow, nativeRow, builtin, exactRows⟩
  · obtain ⟨inner, impossible, _typed⟩ := staged
    cases impossible

section Caller
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {index : ProtectedStateTransition.Index}
  {calleeState : callerProtocol.State index} {calleeNode : ExpressionNode}

include bridge compiler in
/-- The actual strict callee post supplies original Source typing. Only its
value-typing field is used; the incoming caller state and all arguments stay literal. -/
theorem at_callee_post
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    {row : SourceCoreStageCodebook.Decision}
    (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
      sidecar site callee ids originalMetadata originalNode function carrier row)
    (equalCount : row.entry.parameterCount = ids.length)
    (calleePost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      bridge context calleeNode.type (.value (.builtin function)) calleeState)
    (calleeFunction : calleeNode.type = .function parameter result)
    (calleeRelated : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world
      calleeNode.type (.builtin function) carrier compiler.calleeCode.type)
    (represented : DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functionModel))
      mapping world sourceTypes (compiler.codes.map (·.type)) sources values)
    (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (originalResult : compiler.original.type = result) :
    Rows (functionModel := functionModel) (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (registry := registry) (faults := faults) (profile := profile)
      (mapping := mapping) (world := world) (function := function) (carrier := carrier)
      (sourceTypes := sourceTypes) (sources := sources) (values := values)
      (parameter := parameter) (result := result) compiler := by
  have typed := (CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value calleePost).1
  rw [calleeFunction] at typed calleeRelated
  exact at_arguments compiler actualFunctionType builtinAt equalCount typed calleeRelated represented bundle originalResult
end Caller
end Arguments
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinArgumentRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinParentBounds
/-! The accepted builtin suffix completes the original indirect parent at the
actual argument endpoint. The strict callee and argument producers supply their
literal traces and reached caller admission. The builtin primitive has no body
child and leaves this whole heap and store unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functionModel))
    finalMap finalWorld argumentsHeap argumentsStore)
  (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
  (frame : AdministrativePreserved mapping store finalMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (functionModel) identities)
  {function : Dynamic.BuiltinFunction} {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution} {row : SourceCoreStageCodebook.Decision}
  (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
    sidecar prepared.site callee ids originalMetadata originalNode function carrier row)
  (count : row.entry.parameterCount = ids.length)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.builtin function) (.function parameter result))
  (calleeRelated : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
    headers keys bodyRegistry registry semanticFaults profile finalMap finalWorld
    (.function parameter result) (.builtin function) carrier compiler.calleeCode.type)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functionModel)) finalMap finalWorld
    sourceTypes (compiler.codes.map (·.type)) sources values)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)

include bridge compiler prepared sourceParent occurrence related admitted heaps maps worlds frame heapMetadata
  observations builtinAt count actualFunctionType calleeTyped calleeRelated represented bundle originalResult in
omit positive in
/-- The genuine successful callee and ordered argument traces grow to the
original applied constructor. The actual accepted native suffix determines the
same primitive result; its reached caller witness is retained literally. -/
theorem reflects_suffix
    {calleeSize argumentsSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.builtin function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {budget suffixSize : Nat} {value : Value} {finalStore : Store}
    (suffix : EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : suffixSize ≤ budget) :
    ∃ sourceResult,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
        (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []])
        invocation context environment before id (.value sourceResult) argumentsHeap ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults (.value sourceResult) value ∧
      finalStore = argumentsStore ∧
      GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap argumentsStore ∧
      Dynamic.HeapMetadataExtend before argumentsHeap ∧
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type (.value sourceResult) reached := by
  have rows := CallableIndexedOwnedPreparedStagedBuiltinArgumentRows.at_arguments compiler
    actualFunctionType builtinAt count calleeTyped calleeRelated represented bundle originalResult
  obtain ⟨raw, shape⟩ := builtinAt.shape
  obtain ⟨applicationSize, _strict, appliedNative⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix shape
      builtinAt.selected builtinAt.selected.found count suffix within
  obtain ⟨sourceResult, appliedSource, resultRep, primitive, sameStore⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.reflects functions observations
      rows.builtin rows.represented appliedNative
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  have resultAt : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults (.value sourceResult) value := by
    rw [rows.original_result, loweredType, rows.native_result]
    exact resultRep
  obtain ⟨sameReached, same, _reflexive, primitivePost⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.argument_post bridge reached admitted primitive
  cases same
  have callerPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type (.value sourceResult) reached := by
    rw [rows.original_result]
    exact primitivePost
  exact ⟨sourceResult, .applied occurrence compiler.argumentCoercions calleeTrace
    (.builtin function) argumentsTrace sourceParent.arity appliedSource, resultAt, sameStore,
    heaps, maps, worlds, frame, heapMetadata, related, callerPost⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinParentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch
/-! The actual retained argument prefix classifies its selected payload once.
Builtin physical mismatch produces the receiving semantic arity post; equal
count uses the original primitive at the same argument endpoint. A user
payload keeps its authentic callee, ordered arguments and application suffix.
The strict prefix producer remains responsible for constructing this input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

/-- The user predicate concerns the same retained callee and suffix witness.
Its body, global provenance and physical-count decision remain future work. -/
def UserApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceValue, Staging.CallBoundary.UserCallable sourceValue ∧
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧ compiler.original.type = rawResult ∧
  ∃ calleeSize argumentsSize calleeHeap calleeStore calleeMap calleeWorld sources values carrier
      argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
    CalleePost (registry := completion.result.context.registry) (context := context)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      bridge functions compiler initial sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld ∧
    Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
      sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    ∃ suffixSize, EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ suffixSize < budget

omit positive in
/-- Forgetting only the positive user classification keeps the original full
retained callee post and every transient argument effect. -/
theorem UserApplicationPrefix.to_retained {budget : Nat} {value : Value} {finalStore : Store}
    (user : UserApplicationPrefix (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) :
    CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  obtain ⟨sourceValue, _user, rawParameter, rawResult, functionType, bundle, resultType,
    calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩ := user
  exact ⟨rawParameter, rawResult, functionType, bundle, resultType, calleeSize, argumentsSize,
    sourceValue, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩

/-- Full parent meaning is constructed only after the actual builtin row has
been classified. The reached caller and both independent grades stay literal. -/
def ParentResult (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize outcome after finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before id outcome after ∧
    Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults outcome value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome reached

section Classification
variable (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (functionModel) identities)

include positive sourceParent occurrence preparedStages receiver actualFunctionType observations in
/-- No callee or argument is replayed. The genuine prefix's selected BoundaryAt
either retains its user suffix, or decides builtin physical arity internally.
An accepted builtin uses the original complete parent reflection once. -/
theorem reflects_builtin_or_user {budget size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (retained : CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore) :
    UserApplicationPrefix (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore ∨
    ParentResult (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  obtain ⟨rawParameter, rawResult, functionType, bundle, resultType, calleeSize, argumentsSize,
    sourceValue, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    calleePost, valueTyped, child, accepted, arguments, representedValues, representedCallee,
    callView, boundary, finalHeaps, maps, worlds, frame, heapMetadata,
    ⟨reached, related, admitted⟩, suffixSize, suffix, strict⟩ := retained
  cases boundary with
  | user dispatch selected =>
    exact .inl ⟨sourceValue, (CallableLedger.frame sidecar).userCallable dispatch.bound,
      rawParameter, rawResult, functionType, bundle, resultType, calleeSize, argumentsSize,
      calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier, argumentsHeap,
      argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, calleePost, valueTyped,
      child, accepted, arguments, representedValues, representedCallee, callView, .user dispatch selected,
      finalHeaps, maps, worlds, frame, heapMetadata, ⟨reached, related, admitted⟩,
      suffixSize, suffix, strict⟩
  | builtin receipt =>
    rename_i function row
    by_cases count : row.entry.parameterCount = ids.length
    · rw [functionType] at valueTyped representedCallee
      obtain ⟨sourceResult, parentTrace, resultRep, sameStore, heaps, keptMaps, keptWorlds,
        keptFrame, keptMetadata, keptRelated, post⟩ :=
        CallableIndexedOwnedPreparedStagedBuiltinParentBounds.reflects_suffix
          bridge compiler prepared sourceParent occurrence initial reached related admitted
          finalHeaps maps worlds frame heapMetadata observations receipt count actualFunctionType
          valueTyped (representedCallee.map_functions (CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual.erase (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := semanticFaults) (profile := profile))) representedValues bundle resultType child arguments suffix (Nat.le_of_lt strict)
      cases sameStore
      exact .inr ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .value sourceResult, argumentsHeap, finalMap, finalWorld, parentTrace, completed.sound, resultRep,
        heaps, keptMaps, keptWorlds, keptFrame, keptMetadata, reached, keptRelated, post⟩
    · obtain ⟨raw, shape⟩ := receipt.shape
      obtain ⟨sameValue, sameStore⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
          shape receipt.selected receipt.selected.found count suffix
      cases sameStore
      have physical : function.id.parameterTypes.length ≠ ids.length := by
        simpa only [receipt.parameter_count] using count
      have sourceFault := CallableIndexedOwnedPreparedSecondCallGateRejection.builtin_source
        occurrence compiler.argumentCoercions sourceParent.arity arguments child physical
      obtain ⟨represented, keptHeaps, keptState, sameState, _keptRelated⟩ :=
        CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
          compiler prepared preparedStages receipt.selected receiver initial functions reached related finalHeaps
          (sourceResult := compiler.original.type) (resultCore := lowered.type) count
      cases sameState
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      have valueShape : value = .inLeft lowered.type (.word
          (prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
            (.argumentArityMismatch row.entry.parameterCount ids.length))) := by
        simpa only [loweredType] using sameValue
      have faultRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
          compiler.original.type lowered.type callFaults
          (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length))) value := by
        rw [valueShape]
        exact CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model represented
      refine .inr ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)), argumentsHeap,
        finalMap, finalWorld, ?_, completed.sound, faultRep, keptHeaps, maps, worlds, frame,
        heapMetadata, reached, related, ?_⟩
      · simpa only [receipt.parameter_count] using sourceFault
      · exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩

end Classification
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinParentPreservation
/-! The original builtin application supplies its accepted native suffix and
whole indirect parent at the actual argument endpoint. The strict callee and argument producers supply their
literal traces and reached caller admission. The builtin primitive has no body
child and leaves this whole heap and store unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinParentPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functionModel))
    finalMap finalWorld argumentsHeap argumentsStore)
  (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
  (frame : AdministrativePreserved mapping store finalMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (functionModel) identities)
  {function : Dynamic.BuiltinFunction} {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution} {row : SourceCoreStageCodebook.Decision}
  (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
    sidecar prepared.site callee ids originalMetadata originalNode function carrier row)
  (count : row.entry.parameterCount = ids.length)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.builtin function) (.function parameter result))
  (calleeRelated : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
    headers keys bodyRegistry registry semanticFaults profile finalMap finalWorld
    (.function parameter result) (.builtin function) carrier compiler.calleeCode.type)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functionModel)) finalMap finalWorld
    sourceTypes (compiler.codes.map (·.type)) sources values)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)

include bridge compiler prepared sourceParent occurrence related admitted heaps maps worlds frame heapMetadata
  observations builtinAt count actualFunctionType calleeTyped calleeRelated represented bundle originalResult in
omit positive in
/-- The real primitive supplies the accepted native application once. The
literal callee and ordered argument computations are the strict child outputs;
their original binds complete at the same reached caller state. -/
theorem preserves_parent
    {calleeSize argumentsSize applicationSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.builtin function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap (.builtin function) sources outcome after)
    {calleeStore : Store}
    (calleeNative : Evaluates actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore)
    (argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
      invocation context environment before id outcome after ∧
    ∃ value,
      Evaluates actual store (lowered.expression.rename ξ) value argumentsStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      after = argumentsHeap ∧
      GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap argumentsStore ∧
      Dynamic.HeapMetadataExtend before argumentsHeap ∧
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome reached := by
  have rows := CallableIndexedOwnedPreparedStagedBuiltinArgumentRows.at_arguments compiler
    actualFunctionType builtinAt count calleeTyped calleeRelated represented bundle originalResult
  obtain ⟨sourceResult, sameOutcome, sameHeap, _sourceGrade, primitive⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.source_value functions observations rows.represented called
  subst outcome
  obtain ⟨_nativeSize, nativeValue, appliedNative, resultRep, _heap, _grade⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.preserves functions observations
      (faults := faults) (store := argumentsStore) rows.builtin rows.represented called
  obtain ⟨raw, shape⟩ := builtinAt.shape
  have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
    (actual := actual) (store := argumentsStore) (result := compiler.resultType)
    (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
    shape builtinAt.selected builtinAt.selected.found count appliedNative.sound
  have gate := builtinAt.first_gate
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown actual calleeStore
  have whole : Evaluates actual store
      (CallableContract.call prepared.site.gates
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
        (compiler.calleeCode.expression.rename ξ)
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) nativeValue argumentsStore := by
    apply LanguageResult.bind_success compiler.resultType calleeNative
    apply LanguageResult.bind_success compiler.resultType gate
    apply LanguageResult.bind_success compiler.resultType
    · simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
    · exact suffix
  rw [← prepared.lowered_rename compiler ξ] at whole
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  have resultAt : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults (.value sourceResult) nativeValue := by
    rw [rows.original_result, loweredType, rows.native_result]
    exact resultRep
  obtain ⟨sameReached, same, _reflexive, primitivePost⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.argument_post bridge reached admitted primitive
  cases same
  have callerPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type (.value sourceResult) reached := by
    rw [rows.original_result]
    exact primitivePost
  exact ⟨.applied occurrence compiler.argumentCoercions calleeTrace (.builtin function)
    argumentsTrace sourceParent.arity called, nativeValue, whole, resultAt, sameHeap,
    heaps, maps, worlds, frame, heapMetadata, related, callerPost⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinParentPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch
/-! The constructed successful callee and argument prefix supplies builtin
parent preservation at its actual reached state. The selected physical count
is decided internally. A user callee retains the same full prefix for its
body producer. No complete application or body law is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


/-- The exact original Source parent and its native result share the actual
reached caller endpoint. The two traces have independent sizes. -/
def ParentAt (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
    invocation context environment before id outcome after ∧
  ∃ value finalStore finalMap finalWorld,
    Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults outcome value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome reached

variable (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (functionModel) identities)

include positive sourceParent occurrence preparedStages receiver actualFunctionType observations in
/-- The authentic prefix is classified once. Successful builtin execution
uses its original primitive; physical mismatch uses the actual receiving
arity word. Both branches construct the whole native parent without replay. -/
theorem preserves_builtin_or_user
    {calleeSize argumentsSize applicationSize : Nat}
    {sourceValue : Dynamic.Value} {calleeHeap argumentsHeap after : Dynamic.Heap}
    {sources : List Dynamic.Value} {outcome : Staging.Recursive.Outcome}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after)
    (prefixResult : CallableIndexedOwnedPreparedStagedIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources) :
    (Staging.CallBoundary.UserCallable sourceValue ∧
      CallableIndexedOwnedPreparedStagedIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
        (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
        (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
        (calleeNode := calleeNode) (sidecar := sidecar)
        bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources) ∨
    ParentAt (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize]) outcome after := by
  have originalPrefix := prefixResult
  obtain ⟨rawParameter, rawResult, functionType, bundle, resultType,
    calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
    originalNode, originalMetadata, calleePost, valueTyped, _gate, argumentsNative,
    representedValues, representedCallee, _callView, boundary, finalHeaps, maps, worlds,
    frame, heapMetadata, reached, related, admitted⟩ := prefixResult
  cases boundary with
  | user dispatch selected =>
      exact .inl ⟨(CallableLedger.frame sidecar).userCallable dispatch.bound, originalPrefix⟩
  | builtin receipt =>
      rename_i function row
      by_cases count : row.entry.parameterCount = ids.length
      · rw [functionType] at valueTyped representedCallee
        have completeParent :
            Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
              (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
              invocation context environment before id outcome after ∧
            ∃ value,
              Evaluates actual store (lowered.expression.rename ξ) value argumentsStore ∧
              RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
                compiler.original.type lowered.type callFaults outcome value ∧
              after = argumentsHeap ∧
              GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
              LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
              AdministrativePreserved mapping store finalMap argumentsStore ∧
              Dynamic.HeapMetadataExtend before argumentsHeap ∧
              callerProtocol.Relates initial reached ∧
              CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
                compiler.original.type outcome reached :=
          CallableIndexedOwnedPreparedStagedBuiltinParentPreservation.preserves_parent
            (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
            (registry := completion.result.context.registry) (semanticFaults := semanticFaults)
            (profile := profile) (faults := callFaults)
            (context := context) (stages := stages) (invocation := invocation)
            (environment := environment) (actual := actual) (ξ := ξ)
            (mapping := mapping) (finalMap := finalMap) (world := world) (finalWorld := finalWorld)
            (before := before) (calleeHeap := calleeHeap) (argumentsHeap := argumentsHeap)
            (store := store) (argumentsStore := argumentsStore) (canonical := canonical)
            (identities := identities) (function := function) (carrier := carrier) (row := row)
            (sources := sources) (values := values) (sourceTypes := sourceTypes)
            (parameter := rawParameter) (result := rawResult) (sidecar := sidecar)
            (originalNode := originalNode) (originalMetadata := originalMetadata)
            (calleeSize := calleeSize) (argumentsSize := argumentsSize) (applicationSize := applicationSize)
            (outcome := outcome) (after := after) (calleeStore := calleeStore)
            bridge compiler prepared sourceParent occurrence initial reached related admitted
            finalHeaps maps worlds frame heapMetadata observations receipt count actualFunctionType
            valueTyped (representedCallee.map_functions (CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual.erase (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := semanticFaults) (profile := profile))) representedValues bundle resultType calleeTrace argumentsTrace
            called calleePost.1 argumentsNative
        obtain ⟨parentSource, value, native, representation, sameHeap, heaps,
          keptMaps, keptWorlds, keptFrame, keptMetadata, keptRelated, post⟩ := completeParent
        cases sameHeap
        exact .inr ⟨parentSource, value, argumentsStore, finalMap, finalWorld,
          native, representation, heaps, keptMaps, keptWorlds, keptFrame, keptMetadata,
          reached, keptRelated, post⟩
      · have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
        have physical : function.id.parameterTypes.length ≠ ids.length := by
          simpa only [receipt.parameter_count] using count
        cases called with
        | builtin primitive =>
            have originalCount := Dynamic.BuiltinApplies.argument_count primitive
            exact False.elim (physical (valuesCount.symm.trans originalCount).symm)
        | builtinType arity mismatch =>
            exact False.elim (physical (arity.trans valuesCount))
        | builtinArity mismatch =>
            have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
                (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
                (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
              simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix]
                using argumentsNative
            have native := CallableIndexedOwnedPreparedSecondCallGateRejection.builtin_native_preserves
              (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
              (result := compiler.resultType) receipt physical calleePost.1 argumentsWeaken
            change Evaluates actual store
              (CallableContract.call prepared.site.gates
                compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
                (compiler.calleeCode.expression.rename ξ)
                ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at native
            rw [← prepared.lowered_rename compiler ξ] at native
            obtain ⟨represented, keptHeaps, keptState, sameState, _keptRelated⟩ :=
              CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
                compiler prepared preparedStages receipt.selected receiver initial functions reached related finalHeaps
                (sourceResult := compiler.original.type) (resultCore := lowered.type) count
            cases sameState
            have loweredType : lowered.type = compiler.resultType :=
              (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
            have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model represented
            have post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
                compiler.original.type
                (.fault (.semantic (.argumentArityMismatch function.id.parameterTypes.length sources.length))) reached :=
              ⟨admitted.rows, by intro value impossible; cases impossible⟩
            refine .inr ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted
              argumentsTrace sourceParent.arity (.builtinArity mismatch),
              .inLeft lowered.type (.word (prepared.site.reasonAt row.caller row.call row.entry.id
                .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length))),
              argumentsStore, finalMap, finalWorld, ?_, ?_, keptHeaps, maps, worlds, frame,
              heapMetadata, reached, related, post⟩
            · simpa only [loweredType] using native
            · simpa only [receipt.parameter_count, valuesCount] using faultRep

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch
end
