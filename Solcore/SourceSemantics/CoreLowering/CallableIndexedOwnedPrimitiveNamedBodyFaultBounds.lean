import Solcore.SourceSemantics.CoreLowering.ReachedNamedPrimitiveBodyFaultPaths
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBuiltinFaultBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeSourceBounds

/-! Actual singleton tail and return bodies obtain their primitive path from
the existing admitted builtin producer. Finite returnValue and finish steps
retain the actual child token and body store; both execution grades stay real. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrimitiveNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts
open ReachedNamedPrimitiveBodyFaultPaths

private def poolBridge {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)} :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

private theorem emitted_rename {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statement : StatementId}
    {node : StatementNode} {expression : ExpressionId} {expressionNode : ExpressionNode} {fuel : Nat}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {body : Expr} {fellThrough escaped : Word}
    (singleton : SingletonAt values function context scope statement node expression expressionNode fuel solved reasonAt
      lowered body fellThrough escaped) (ξ : Renaming) :
    body.rename ξ = CompatibleStatements.finish lowered.type
      (LocalLoop.returnValue lowered.type (lowered.expression.rename ξ)) fellThrough escaped := by
  rw [singleton.emitted, ImperativeFunctionFinish.rename, LoopRenaming.returnValue]

private def returnedControl : Dynamic.ExpressionOutcome → Dynamic.ControlOutcome
  | .value value => .returned value
  | .fault reason => .fault reason

private theorem fault_finished {actual : Environment} {initialStore bodyStore : Store} {type : Ty}
    {expression : Expr} {token fellThrough escaped : Word}
    (child : Evaluates actual initialStore expression (.inLeft type (.word token)) bodyStore) :
    Evaluates actual initialStore (CompatibleStatements.finish type (LocalLoop.returnValue type expression) fellThrough escaped)
      (.inLeft type (.word token)) bodyStore :=
  LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped (LocalLoop.returnValue_failure _ child))

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {locations : CallableIndexedOwnedFunctionValues.Header compiled program → Location} {capturePrefix : Nat}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  {statement : StatementId} {node : StatementNode} {expression : ExpressionId} {expressionNode : ExpressionNode}
  {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr} {fellThrough escaped : Word}
  (singleton : SingletonAt (.initial compiled.compatible.checked) header.function header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) statement node expression expressionNode
    fuel solved reasonAt lowered header.body fellThrough escaped)
  (nativeType : lowered.type = header.output)
  (source : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (valid : CompatibleExpressionLiterals.ContextValid solved header.context header.function.evidence)
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
    header.function.source functions registry program header.context header.function.evidence reasonAt faults)
  (unique : NodeOccurrencesUnique header.function.source) (wellFormed : ProgramWellFormed program)

include singleton nativeType source rows extension faithful observations functionTypes valid reads missing unique wellFormed in
/-- The actual sized Source singleton selects its strict child, whose builtin
producer returns the same full tuple and causal path at the body store. -/
theorem source_body_with_post (size : Nat) :
    SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  intro outcome after bodyTrace
  obtain ⟨finalContext, control, flowTrace, exit⟩ := RecursiveNamedFunctionFinishBounds.trace_flow bodyTrace
  rw [singleton.statements] at flowTrace
  have child : finalContext = header.context ∧ ∃ childSize expressionOutcome,
      RecursiveNamedCallBounds.ExpressionOutcome program childSize header.context header.function.evidence
        header.function.source entry.environment entry.heap expression expressionOutcome after ∧
      control = (returnedControl expressionOutcome) ∧
      childSize < size := by
    rcases singleton.form with tail | returning
    · exact RecursiveNamedStatementSourceBounds.tail_inv unique (lookupStatement?_sound singleton.found) tail flowTrace
    · exact RecursiveNamedLexicalTreeSourceBounds.returning unique singleton.found returning flowTrace
  obtain ⟨rfl, childSize, expressionOutcome, childTrace, rfl, _smaller⟩ := child
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached :=
    ⟨source.heapTyped, rows⟩
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, finalState, related, _postAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
      functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
      valid reads missing unique wellFormed source.runtime source.covers singleton.tree singleton.expressionFound singleton.expressionTyped
      entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted childTrace
  have rawUnit : ∀ next,
      (returnedControl expressionOutcome) =
        Dynamic.ControlOutcome.fallthrough next → header.function.resultType = .unit := by
    cases expressionOutcome <;> intro next same <;> cases same
  have transfers : ImperativeFunctionFinish.TransferFaults faults escaped
      (returnedControl expressionOutcome) := by
    cases expressionOutcome <;> constructor <;> intro next same <;> cases same
  obtain ⟨flowValue, flowEvaluation, flowRelated⟩ : ∃ flowValue,
      Evaluates entry.actualBody entry.store (LocalLoop.returnValue lowered.type (lowered.expression.rename entry.embedding)) flowValue bodyStore ∧
      TypedLexicalWhile.FlowRep (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry)
        functions finalMap finalWorld faults header.function.resultType lowered.type
        (returnedControl expressionOutcome) flowValue := by
    cases represented with
    | value payload => exact ⟨_, LocalLoop.returnValue_success _ evaluated, .returned (singleton.resultType ▸ payload)⟩
    | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ evaluated, .fault matched⟩
  obtain ⟨result, completed, finished⟩ := ImperativeFunctionFinish.from_flow_with_transfers
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (mapping := finalMap) (world := finalWorld) (faults := faults) (outcome := returnedControl expressionOutcome)
    functions rawUnit singleton.projection fellThrough escaped transfers flowRelated flowEvaluation
  have bodyEvaluation : Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) result bodyStore := by
    rw [emitted_rename singleton]
    exact completed
  refine ⟨result, bodyStore, finalMap, finalWorld, bodyEvaluation, ?_, finalHeaps, maps, worlds, frame,
    metadata, ⟨finalState, related⟩, ?_⟩
  · simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using ImperativeFunctionFinish.result finished exit
  · cases expressionOutcome with
    | value sourceValue => cases exit; trivial
    | fault reason =>
      cases exit
      cases childTrace with | fault failed =>
        obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained evaluated
        have faultChild : Evaluates entry.actualBody entry.store (lowered.expression.rename entry.embedding)
            (.inLeft lowered.type (.word token)) bodyStore := sameValue ▸ evaluated
        have faultBody : Evaluates entry.actualBody entry.store (header.body.rename entry.embedding)
            (.inLeft lowered.type (.word token)) bodyStore := by
          rw [emitted_rename singleton]
          exact fault_finished faultChild
        refine ⟨token, ?_, model_bodyPost.of_child singleton failed.sound origin faultChild faultBody⟩
        simpa only [nativeType] using (evaluation_deterministic bodyEvaluation faultBody).1

include singleton nativeType source rows extension faithful observations functionTypes valid reads missing unique wellFormed in
/-- The actual finish and returnValue children supply strict native bounds.
The singleton Source grade is constructed independently from its real child. -/
theorem native_body_with_post (size : Nat) :
    NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  intro value finalStore bodyCompletion
  have nativeFinish : EvaluationSize size entry.actualBody entry.store
      (CompatibleStatements.finish lowered.type
        (LocalLoop.returnValue lowered.type (lowered.expression.rename entry.embedding)) fellThrough escaped) value finalStore := by
    rw [← emitted_rename singleton]
    exact bodyCompletion
  obtain ⟨flowSize, flowValue, flowStore, _flowSmaller, flowCompletion⟩ := RecursiveNamedCallBounds.finish_flow nativeFinish
  obtain ⟨expressionSize, expressionStore, expressionValue, _expressionSmaller, expressionCompletion⟩ :=
    flowCompletion.bind_computation
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached :=
    ⟨source.heapTyped, rows⟩
  obtain ⟨sourceSize, expressionOutcome, after, finalMap, finalWorld, childTrace, represented, finalHeaps,
      maps, worlds, frame, metadata, finalState, related, _postAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects (poolBridge (headers := headers) (keys := keys))
      functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
      valid reads missing unique wellFormed source.runtime source.covers singleton.tree singleton.expressionFound singleton.expressionTyped
      entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted expressionCompletion
  have rawUnit : ∀ next,
      (returnedControl expressionOutcome) =
        Dynamic.ControlOutcome.fallthrough next → header.function.resultType = .unit := by
    cases expressionOutcome <;> intro next same <;> cases same
  have transfers : ImperativeFunctionFinish.TransferFaults faults escaped
      (returnedControl expressionOutcome) := by
    cases expressionOutcome <;> constructor <;> intro next same <;> cases same
  obtain ⟨returnValue, returnEvaluation, returnRelated⟩ : ∃ returnValue,
      Evaluates entry.actualBody entry.store (LocalLoop.returnValue lowered.type (lowered.expression.rename entry.embedding)) returnValue expressionStore ∧
      TypedLexicalWhile.FlowRep (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry)
        functions finalMap finalWorld faults header.function.resultType lowered.type
        (returnedControl expressionOutcome) returnValue := by
    cases represented with
    | value payload => exact ⟨_, LocalLoop.returnValue_success _ expressionCompletion.sound, .returned (singleton.resultType ▸ payload)⟩
    | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ expressionCompletion.sound, .fault matched⟩
  obtain ⟨result, completed, finished⟩ := ImperativeFunctionFinish.from_flow_with_transfers
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (mapping := finalMap) (world := finalWorld) (faults := faults) (outcome := returnedControl expressionOutcome)
    functions rawUnit singleton.projection fellThrough escaped transfers returnRelated returnEvaluation
  have bodyEvaluation : Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) result expressionStore := by
    rw [emitted_rename singleton]
    exact completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyCompletion.sound bodyEvaluation
  cases expressionOutcome with
  | value sourceValue =>
    cases childTrace with | value childEvaluated =>
      obtain ⟨bodySize, bodyTrace⟩ : ∃ bodySize,
          RecursiveNamedCallBounds.BodyTrace program bodySize header.function header.context
            entry.environment entry.heap (.value sourceValue) after := by
        rcases singleton.form with tail | returning
        · refine ⟨SourceExecutionSize.stepSize [sourceSize], .returned (finalContext := header.context) ?_⟩
          rw [singleton.statements]
          exact .tailExpression (lookupStatement?_sound singleton.found) tail childEvaluated
        · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [sourceSize]], .returned (finalContext := header.context) ?_⟩
          rw [singleton.statements]
          exact .singleton (lookupStatement?_sound singleton.found) (by intro expression; simp [returning])
            (.returnValue (lookupStatement?_sound singleton.found) returning childEvaluated)
      refine ⟨bodySize, .value sourceValue, after, finalMap, finalWorld, bodyTrace, ?_, finalHeaps,
        maps, worlds, frame, metadata, ⟨finalState, related⟩, trivial⟩
      simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using ImperativeFunctionFinish.result finished (CompatibleNamedBody.Exit.returned sourceValue)
  | fault reason =>
    cases childTrace with | fault childFailed =>
      obtain ⟨bodySize, bodyTrace⟩ : ∃ bodySize,
          RecursiveNamedCallBounds.BodyTrace program bodySize header.function header.context
            entry.environment entry.heap (.fault reason) after := by
        rcases singleton.form with tail | returning
        · refine ⟨SourceExecutionSize.stepSize [sourceSize], .fault (finalContext := header.context) ?_⟩
          rw [singleton.statements]
          exact .tailExpression (lookupStatement?_sound singleton.found) tail childFailed
        · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [sourceSize]], .fault (finalContext := header.context) ?_⟩
          rw [singleton.statements]
          exact .singleton (.returnValue (lookupStatement?_sound singleton.found) returning childFailed)
      refine ⟨bodySize, .fault reason, after, finalMap, finalWorld, bodyTrace, ?_, finalHeaps,
        maps, worlds, frame, metadata, ⟨finalState, related⟩, ?_⟩
      · simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using ImperativeFunctionFinish.result finished (CompatibleNamedBody.Exit.fault reason)
      · obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault
          retained expressionCompletion.sound
        have faultChild : Evaluates entry.actualBody entry.store (lowered.expression.rename entry.embedding)
            (.inLeft lowered.type (.word token)) finalStore := sameValue ▸ expressionCompletion.sound
        have faultBody : Evaluates entry.actualBody entry.store (header.body.rename entry.embedding)
            (.inLeft lowered.type (.word token)) finalStore := by
          rw [emitted_rename singleton]
          exact fault_finished faultChild
        refine ⟨token, ?_, model_bodyPost.of_child singleton childFailed.sound origin faultChild faultBody⟩
        simpa only [nativeType] using (evaluation_deterministic bodyEvaluation faultBody).1

include singleton nativeType source rows extension faithful observations functionTypes valid reads missing unique wellFormed in
/-- Every strict Source member is produced by the same concrete singleton theorem. -/
theorem source_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact source_body_with_post functions entry reached singleton nativeType source rows extension faithful
    observations functionTypes valid reads missing unique wellFormed child

include singleton nativeType source rows extension faithful observations functionTypes valid reads missing unique wellFormed in
/-- Native strict membership uses its actual measured body completion. -/
theorem native_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact native_body_with_post functions entry reached singleton nativeType source rows extension faithful
    observations functionTypes valid reads missing unique wellFormed child

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrimitiveNamedBodyFaultBounds
