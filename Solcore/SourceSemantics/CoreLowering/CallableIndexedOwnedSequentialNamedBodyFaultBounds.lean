import Solcore.SourceSemantics.CoreLowering.ReachedNamedSequentialBodyFaultPaths
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrimitiveNamedBodyFaultBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds

/-! Actual discard and singleton suffix children run the admitted builtin
producer once each. The reached middle State supplies the next admission. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSequentialNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts
open ReachedNamedSequentialBodyFaultPaths

private def poolBridge {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)} :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

private def returnedControl : Dynamic.ExpressionOutcome → Dynamic.ControlOutcome
  | .value value => .returned value
  | .fault reason => .fault reason

section Finite
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {program : Program}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {statement last : StatementId} {node lastNode : StatementNode} {expression lastExpression : ExpressionId}
  {expressionNode lastExpressionNode : ExpressionNode} {fuel lastFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {lowered lastLowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {fellThrough escaped : Word}
  (sequential : SequentialAt (.initial checked) function context scope statement node expression expressionNode fuel
    last lastNode lastExpression lastExpressionNode lastFuel solved reasonAt lowered lastLowered body fellThrough escaped)

include sequential in
private theorem emitted_rename (ξ : Renaming) :
    body.rename ξ = CompatibleStatements.finish lastLowered.type
      (LocalSequence.discard (LocalLoop.controlType lastLowered.type) (lowered.expression.rename ξ)
        (LocalLoop.returnValue lastLowered.type (lastLowered.expression.rename ξ))) fellThrough escaped := by
  rw [sequential.emitted, ImperativeFunctionFinish.rename, LoopRenaming.discard, LoopRenaming.returnValue]

include sequential in
private theorem finished_head {actual : Environment} {initialStore bodyStore : Store} {ξ : Renaming}
    {token : Word}
    (first : Evaluates actual initialStore (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) bodyStore) :
    Evaluates actual initialStore (body.rename ξ) (.inLeft lastLowered.type (.word token)) bodyStore := by
  rw [emitted_rename sequential]
  exact LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped
    (LocalSequence.discard_failure _ first))

include sequential in
private theorem finish_tail {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {sourceValue : Dynamic.Value} {payload value : Value} {outcome : Dynamic.ExpressionOutcome}
    {actual : Environment} {initialStore middleStore bodyStore : Store} {ξ : Renaming}
    {initialMap middleMap finalMap : LocationMap} {initialWorld middleWorld finalWorld : StoreTyping}
    (sourceFirst : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before expression sourceValue middle)
    (first : Evaluates actual initialStore (lowered.expression.rename ξ) (.inRight .word payload) middleStore)
    (middleHeaps : CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore)
    (firstMaps : LocationMap.Extends initialMap middleMap) (firstWorlds : WorldExtends initialWorld middleWorld)
    (firstFrame : AdministrativePreserved initialMap initialStore middleMap middleStore)
    (firstMetadata : Dynamic.HeapMetadataExtend before middle)
    (maps : LocationMap.Extends middleMap finalMap) (worlds : WorldExtends middleWorld finalWorld)
    (frame : AdministrativePreserved middleMap middleStore finalMap bodyStore) (metadata : Dynamic.HeapMetadataExtend middle after)
    (sourceLast : Dynamic.ExpressionEvaluatesOutcome program context function.evidence function.source environment middle lastExpression outcome after)
    (second : Evaluates (payload :: actual) middleStore
      (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) ξ)) value bodyStore)
    (represented : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
      finalMap finalWorld lastExpressionNode.type lastLowered.type faults outcome value)
    (retained : ExpressionFailurePostContracts.OutcomePost
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry)
      program context function.evidence function.source environment middle lastExpression lastLowered.type
      outcome after value finalMap finalWorld bodyStore) :
    ∃ result,
      Evaluates actual initialStore (body.rename ξ) result bodyStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        finalMap finalWorld function.resultType lastLowered.type faults outcome result ∧
      OutcomePost (model_bodyPost checked functions registry) program function context environment before
        actual initialStore (body.rename ξ) lastLowered.type outcome after result finalMap finalWorld bodyStore := by
  have rawUnit : ∀ next, returnedControl outcome = Dynamic.ControlOutcome.fallthrough next → function.resultType = .unit := by
    cases outcome <;> intro next same <;> cases same
  have transfers : ImperativeFunctionFinish.TransferFaults faults escaped (returnedControl outcome) := by
    cases outcome <;> constructor <;> intro next same <;> cases same
  obtain ⟨flowValue, returnEvaluation, flowRelated⟩ : ∃ flowValue,
      Evaluates (payload :: actual) middleStore
        (LocalLoop.returnValue lastLowered.type (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) ξ))) flowValue bodyStore ∧
      TypedLexicalWhile.FlowRep (values := .initial checked) (ambient := ambient) (registry := registry)
        functions finalMap finalWorld faults function.resultType lastLowered.type (returnedControl outcome) flowValue := by
    cases represented with
    | value related => exact ⟨_, LocalLoop.returnValue_success _ second, .returned (sequential.final.resultType ▸ related)⟩
    | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ second, .fault matched⟩
  have suffixEvaluation : Evaluates (payload :: actual) middleStore
      ((LocalLoop.returnValue lastLowered.type (lastLowered.expression.rename ξ)).weakenAt 0) flowValue bodyStore := by
    rw [← LoopRenaming.returnValue, ← GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
    exact returnEvaluation
  have flowEvaluation := LocalSequence.discard_success (LocalLoop.controlType lastLowered.type) first suffixEvaluation
  obtain ⟨result, completed, finished⟩ := ImperativeFunctionFinish.from_flow_with_transfers
    (values := .initial checked) (ambient := ambient) (mapping := finalMap) (world := finalWorld)
    (faults := faults) (outcome := returnedControl outcome)
    functions rawUnit sequential.final.projection fellThrough escaped transfers flowRelated flowEvaluation
  have bodyEvaluation : Evaluates actual initialStore (body.rename ξ) result bodyStore := by
    rw [emitted_rename sequential]
    exact completed
  refine ⟨result, bodyEvaluation, ?_, ?_⟩
  · cases outcome with
    | value source => exact ImperativeFunctionFinish.result finished (CompatibleNamedBody.Exit.returned source)
    | fault reason => exact ImperativeFunctionFinish.result finished (CompatibleNamedBody.Exit.fault reason)
  · cases outcome with
    | value source => trivial
    | fault reason =>
      cases sourceLast with | fault failed =>
        obtain ⟨token, sameValue, origin⟩ := retained
        have faultChild : Evaluates (payload :: actual) middleStore
            (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) ξ))
            (.inLeft lastLowered.type (.word token)) bodyStore := sameValue ▸ second
        have faultSuffix := LocalLoop.returnValue_failure _ faultChild
        have faultDiscard : Evaluates actual initialStore
            (LocalSequence.discard (LocalLoop.controlType lastLowered.type) (lowered.expression.rename ξ)
              (LocalLoop.returnValue lastLowered.type (lastLowered.expression.rename ξ)))
            (.inLeft (LocalLoop.controlType lastLowered.type) (.word token)) bodyStore := by
          apply LocalSequence.discard_success _ first
          rw [← LoopRenaming.returnValue, ← GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
          exact faultSuffix
        have faultBody : Evaluates actual initialStore (body.rename ξ) (.inLeft lastLowered.type (.word token)) bodyStore := by
          rw [emitted_rename sequential]
          exact LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped faultDiscard)
        exact ⟨token, (evaluation_deterministic bodyEvaluation faultBody).1,
          model_bodyPost.of_tail sequential sourceFirst first middleHeaps firstMaps firstWorlds firstFrame firstMetadata
            maps worlds frame metadata failed origin faultChild faultBody⟩
include sequential in
private theorem trace_head {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {childSize : Nat} {reason : Dynamic.SemanticFault}
    (failed : SourceExecutionSize.ExpressionFaults program childSize context function.evidence function.source
      environment before expression reason after) :
    ∃ size, RecursiveNamedCallBounds.BodyTrace program size function context environment before (.fault reason) after := by
  refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [childSize]], .fault (finalContext := context) ?_⟩
  rw [sequential.statements]
  exact .head (.expression (lookupStatement?_sound sequential.found) sequential.form failed)

include sequential in
private theorem trace_tail {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {sourceValue : Dynamic.Value} {firstSize lastSize : Nat} {outcome : Dynamic.ExpressionOutcome}
    (first : SourceExecutionSize.ExpressionEvaluates program firstSize context function.evidence function.source
      environment before expression sourceValue middle)
    (second : RecursiveNamedCallBounds.ExpressionOutcome program lastSize context function.evidence function.source
      environment middle lastExpression outcome after) :
    ∃ size, RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after := by
  have sourceHead : SourceExecutionSize.StatementExecutes program (SourceExecutionSize.stepSize [firstSize])
      context function.evidence function.source environment before statement context (.fallthrough environment) middle :=
    .expression (lookupStatement?_sound sequential.found) sequential.form first
  cases outcome with
  | value sourceValue =>
    cases second with | value child =>
      rcases sequential.final.form with tail | returning
      · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize], SourceExecutionSize.stepSize [lastSize]],
          .returned (finalContext := context) ?_⟩
        rw [sequential.statements]
        exact .cons sourceHead (.tailExpression (lookupStatement?_sound sequential.final.found) tail child)
      · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize],
          SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [lastSize]]], .returned (finalContext := context) ?_⟩
        rw [sequential.statements]
        exact .cons sourceHead (.singleton (lookupStatement?_sound sequential.final.found)
          (by intro expression; simp [returning]) (.returnValue (lookupStatement?_sound sequential.final.found) returning child))
  | fault reason =>
    cases second with | fault child =>
      rcases sequential.final.form with tail | returning
      · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize], SourceExecutionSize.stepSize [lastSize]],
          .fault (finalContext := context) ?_⟩
        rw [sequential.statements]
        exact .tail sourceHead (.tailExpression (lookupStatement?_sound sequential.final.found) tail child)
      · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize],
          SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [lastSize]]], .fault (finalContext := context) ?_⟩
        rw [sequential.statements]
        exact .tail sourceHead (.singleton (.returnValue (lookupStatement?_sound sequential.final.found) returning child))

end Finite

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
  {statement last : StatementId} {node lastNode : StatementNode} {expression lastExpression : ExpressionId}
  {expressionNode lastExpressionNode : ExpressionNode} {fuel lastFuel : Nat}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {lowered lastLowered : SourceCoreBasic.LoweredExpr} {fellThrough escaped : Word}
  (sequential : SequentialAt (.initial compiled.compatible.checked) header.function header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) statement node expression expressionNode fuel
    last lastNode lastExpression lastExpressionNode lastFuel solved reasonAt lowered lastLowered header.body fellThrough escaped)
  (nativeType : lastLowered.type = header.output)
  (source : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (valid : CompatibleExpressionLiterals.ContextValid solved header.context header.function.evidence)
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults)
  (lastReads : ReachedLoweredReadOutcomePorts.ReadPolicies lastFuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
    header.function.source functions registry program header.context header.function.evidence reasonAt faults)
  (unique : NodeOccurrencesUnique header.function.source) (wellFormed : ProgramWellFormed program)

include sequential nativeType source rows extension faithful observations functionTypes valid reads lastReads missing unique wellFormed in
/-- The original sized Source discard selects the real first child and actual
middle State before the admitted suffix producer is called. -/
theorem source_body_with_post (size : Nat) :
    SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  intro outcome after bodyTrace
  obtain ⟨finalContext, control, flowTrace, exit⟩ := RecursiveNamedFunctionFinishBounds.trace_flow bodyTrace
  rw [sequential.statements] at flowTrace
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached :=
    ⟨source.heapTyped, rows⟩
  rcases RecursiveNamedLexicalTreeSourceBounds.discard unique sequential.found sequential.form
      (by simp) flowTrace with
    ⟨childSize, reason, rfl, rfl, failed, _strict⟩ |
    ⟨childSize, tailSize, sourceValue, middle, firstTrace, tailTrace, _firstStrict, _tailStrict⟩
  · cases exit
    obtain ⟨value, bodyStore, finalMap, finalWorld, first, represented, finalHeaps,
        maps, worlds, frame, metadata, finalState, related, _postAdmission, retained⟩ :=
      CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
        functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
        valid reads missing unique wellFormed source.runtime source.covers sequential.tree sequential.expressionFound sequential.expressionTyped
        entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted (.fault failed)
    cases represented with | @fault _ oldToken matched =>
      obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained first
      have tokenSame : oldToken = token := by simpa using sameValue
      subst token
      have bodyEvaluation := finished_head sequential first
      refine ⟨_, bodyStore, finalMap, finalWorld, bodyEvaluation, ?_, finalHeaps, maps, worlds, frame,
        metadata, ⟨finalState, related⟩, ?_⟩
      · simpa only [nativeType] using (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (mapping := finalMap) (world := finalWorld) (sourceType := header.function.resultType) (type := lastLowered.type) matched)
      · exact ⟨oldToken, by simp [nativeType], model_bodyPost.of_head sequential failed.sound origin first bodyEvaluation⟩
  · have selected : finalContext = header.context ∧ ∃ finalSize finalOutcome,
        RecursiveNamedCallBounds.ExpressionOutcome program finalSize header.context header.function.evidence
          header.function.source entry.environment middle lastExpression finalOutcome after ∧
        control = returnedControl finalOutcome ∧ finalSize < tailSize := by
      rcases sequential.final.form with tail | returning
      · exact RecursiveNamedStatementSourceBounds.tail_inv unique (lookupStatement?_sound sequential.final.found) tail tailTrace
      · exact RecursiveNamedLexicalTreeSourceBounds.returning unique sequential.final.found returning tailTrace
    obtain ⟨rfl, finalSize, finalOutcome, finalTrace, rfl, _strict⟩ := selected
    obtain ⟨firstValue, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstAdmission, _retained⟩ :=
      CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
        functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
        valid reads missing unique wellFormed source.runtime source.covers sequential.tree sequential.expressionFound sequential.expressionTyped
        entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted (.value firstTrace)
    cases represented with | @value _ payload representedFirst =>
      obtain ⟨_sourceTyped, middleAdmission⟩ := firstAdmission.at_value
      obtain ⟨value, bodyStore, finalMap, finalWorld, second, represented, finalHeaps,
          maps, worlds, frame, metadata, finalState, finalRelated, _postAdmission, retained⟩ :=
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
          functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
          valid lastReads missing unique wellFormed source.runtime source.covers sequential.final.tree
          sequential.final.expressionFound sequential.final.expressionTyped
          (entry.environments.extend firstMaps firstWorlds) middleHeaps (source.locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix entry.lookups payload)
          (.cons representedFirst.runtime_hasType (entry.actualTyped.weaken firstWorlds)) middleState middleAdmission finalTrace
      have retainedAt : ExpressionFailurePostContracts.OutcomePost
          (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
          program header.context header.function.evidence header.function.source entry.environment middle
          lastExpression lastLowered.type finalOutcome after value finalMap finalWorld bodyStore := by
        cases finalOutcome with
        | value v => trivial
        | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained second
      obtain ⟨result, bodyEvaluation, finished, retainedBody⟩ := finish_tail sequential firstTrace.sound first
        middleHeaps firstMaps firstWorlds firstFrame firstMetadata maps worlds frame metadata
        finalTrace.sound second represented retainedAt
      refine ⟨result, bodyStore, finalMap, finalWorld, bodyEvaluation, ?_, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        ⟨finalState, (protocol headers keys).trans firstRelated finalRelated⟩, ?_⟩
      · cases finalOutcome <;> cases exit <;> simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using finished
      · cases finalOutcome <;> cases exit <;> simpa only [nativeType] using retainedBody

include sequential nativeType source rows extension faithful observations functionTypes valid reads lastReads missing unique wellFormed in
/-- Actual finish/discard/returnValue children select genuine native completions;
Source grades come independently from the two admitted expression producers. -/
theorem native_body_with_post (size : Nat) :
    NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  intro value finalStore bodyCompletion
  have nativeFinish : EvaluationSize size entry.actualBody entry.store
      (CompatibleStatements.finish lastLowered.type
        (LocalSequence.discard (LocalLoop.controlType lastLowered.type) (lowered.expression.rename entry.embedding)
          (LocalLoop.returnValue lastLowered.type (lastLowered.expression.rename entry.embedding)))
        fellThrough escaped) value finalStore := by
    rw [← emitted_rename sequential]
    exact bodyCompletion
  obtain ⟨flowSize, flowValue, flowStore, _flowStrict, flowCompletion⟩ := RecursiveNamedCallBounds.finish_flow nativeFinish
  obtain ⟨firstSize, middleStore, firstValue, _firstStrict, firstCompletion⟩ := flowCompletion.bind_computation
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached :=
    ⟨source.heapTyped, rows⟩
  obtain ⟨sourceSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, firstRepresented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects (poolBridge (headers := headers) (keys := keys))
      functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
      valid reads missing unique wellFormed source.runtime source.covers sequential.tree sequential.expressionFound sequential.expressionTyped
      entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted firstCompletion
  cases firstRepresented with
  | @fault reason oldToken matched =>
    cases firstTrace with | fault failed =>
      obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained firstCompletion.sound
      have tokenSame : oldToken = token := by simpa using sameValue
      subst token
      have bodyEvaluation := finished_head sequential firstCompletion.sound
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyCompletion.sound bodyEvaluation
      obtain ⟨bodySize, sourceTrace⟩ := trace_head sequential failed
      refine ⟨bodySize, .fault reason, middle, middleMap, middleWorld, sourceTrace, ?_, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, ⟨middleState, firstRelated⟩, ?_⟩
      · simpa only [nativeType] using (FunctionCalls.ResultRepresents.fault
          (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (mapping := middleMap) (world := middleWorld) (sourceType := header.function.resultType)
          (type := lastLowered.type) matched)
      · exact ⟨oldToken, by simp [nativeType],
          model_bodyPost.of_head sequential failed.sound origin firstCompletion.sound bodyEvaluation⟩
  | @value sourceValue payload representedFirst =>
    cases firstTrace with | value sourceFirst =>
      obtain ⟨_sourceTyped, middleAdmission⟩ := firstAdmission.at_value
      obtain ⟨suffixSize, _suffixStrict, suffixCompletion⟩ := flowCompletion.bind_success firstCompletion.sound
      have returnCompletion : EvaluationSize suffixSize (payload :: entry.actualBody) middleStore
          (LocalLoop.returnValue lastLowered.type
            (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) entry.embedding)))
          flowValue flowStore := by
        rw [← LoopRenaming.returnValue, GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
        exact suffixCompletion
      obtain ⟨lastSize, bodyStore, lastValue, _lastStrict, lastCompletion⟩ := returnCompletion.bind_computation
      obtain ⟨lastSourceSize, lastOutcome, after, finalMap, finalWorld, lastTrace, represented, finalHeaps,
          maps, worlds, frame, metadata, finalState, finalRelated, _postAdmission, retained⟩ :=
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects (poolBridge (headers := headers) (keys := keys))
          functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
          valid lastReads missing unique wellFormed source.runtime source.covers sequential.final.tree
          sequential.final.expressionFound sequential.final.expressionTyped
          (entry.environments.extend firstMaps firstWorlds) middleHeaps (source.locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix entry.lookups payload)
          (.cons representedFirst.runtime_hasType (entry.actualTyped.weaken firstWorlds)) middleState middleAdmission lastCompletion
      have retainedAt : ExpressionFailurePostContracts.OutcomePost
          (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
          program header.context header.function.evidence header.function.source entry.environment middle
          lastExpression lastLowered.type lastOutcome after lastValue finalMap finalWorld bodyStore := by
        cases lastOutcome with
        | value v => trivial
        | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained lastCompletion.sound
      obtain ⟨result, bodyEvaluation, finished, retainedBody⟩ := finish_tail sequential sourceFirst.sound firstCompletion.sound
        middleHeaps firstMaps firstWorlds firstFrame firstMetadata maps worlds frame metadata
        lastTrace.sound lastCompletion.sound represented retainedAt
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyCompletion.sound bodyEvaluation
      obtain ⟨bodySize, sourceTrace⟩ := trace_tail sequential sourceFirst lastTrace
      refine ⟨bodySize, lastOutcome, after, finalMap, finalWorld, sourceTrace, ?_, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        ⟨finalState, (protocol headers keys).trans firstRelated finalRelated⟩, ?_⟩
      · simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using finished
      · simpa only [nativeType] using retainedBody

include sequential nativeType source rows extension faithful observations functionTypes valid reads lastReads missing unique wellFormed in
/-- Every strict Source member is derived by the same concrete sequential theorem. -/
theorem source_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact source_body_with_post functions entry reached sequential nativeType source rows extension faithful
    observations functionTypes valid reads lastReads missing unique wellFormed child

include sequential nativeType source rows extension faithful observations functionTypes valid reads lastReads missing unique wellFormed in
/-- The native strict member uses its actual whole body completion. -/
theorem native_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact native_body_with_post functions entry reached sequential nativeType source rows extension faithful
    observations functionTypes valid reads lastReads missing unique wellFormed child

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSequentialNamedBodyFaultBounds
