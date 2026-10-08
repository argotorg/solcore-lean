import Solcore.SourceSemantics.CoreLowering.ReachedNamedConditionalBodyFaultPaths
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSequentialNamedBodyFaultBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeControlBounds

/-! The genuine condition and selected explicit return each run the admitted
builtin producer once. Their actual middle State retains admission and rows. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedConditionalNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts
open ReachedNamedConditionalBodyFaultPaths
open CompatibleExpressionPrimitives

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
  {statement : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
  {conditionFuel : Nat} {branch : Bool → StatementId} {branchNode : Bool → StatementNode}
  {expression : Bool → ExpressionId} {expressionNode : Bool → ExpressionNode} {fuel : Bool → Nat}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {conditionCode : Expr} {code : Bool → Expr}
  {type : Ty} {body : Expr} {fellThrough escaped : Word}
  (conditional : ConditionalAt (.initial checked) function context scope statement node condition conditionNode conditionFuel
    branch branchNode expression expressionNode fuel solved reasonAt conditionCode code type body fellThrough escaped)

include conditional in
private theorem emitted_rename (ξ : Renaming) :
    body.rename ξ = CompatibleStatements.finish type
      (LocalLoop.sequence type
        (LocalLoop.conditional type (conditionCode.rename ξ)
          (LocalLoop.returnValue type ((code true).rename ξ)) (LocalLoop.returnValue type ((code false).rename ξ)))
        (LocalLoop.fallthrough type)) fellThrough escaped := by
  rw [conditional.emitted, ImperativeFunctionFinish.rename, LoopRenaming.sequence,
    LoopRenaming.conditional, LoopRenaming.returnValue, LoopRenaming.returnValue, LoopRenaming.fallthrough]

include conditional in
private theorem finished_condition {actual : Environment} {initialStore bodyStore : Store} {ξ : Renaming} {token : Word}
    (first : Evaluates actual initialStore (conditionCode.rename ξ) (.inLeft .bool (.word token)) bodyStore) :
    Evaluates actual initialStore (body.rename ξ) (.inLeft type (.word token)) bodyStore := by
  rw [emitted_rename conditional]
  exact LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped
    (LocalLoop.sequence_failure _ (LocalControl.choose_failure _ first)))

include conditional in
private theorem selected_if {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique function.source)
    (trace : RecursiveNamedLoopContracts.ExecutesAt size true program context function.evidence function.source
      environment before function.body finalContext outcome after) :
    finalContext = context ∧ ∃ statementSize,
      RecursiveNamedStatementSourceBounds.IfTrace program context function.evidence function.source environment before
        condition [branch true] (some [branch false]) statementSize outcome after := by
  rw [conditional.statements] at trace
  have contains := lookupStatement?_sound conditional.found
  have shape : ∀ other, ContainsStatement function.source statement other →
      other.form = .ifThen condition [branch true] (some [branch false]) := by
    intro other present
    have same : other = node := Option.some.inj ((lookupStatement?_complete unique present).symm.trans conditional.found)
    exact same ▸ conditional.form
  cases trace with
  | control executed =>
    cases executed with
    | tailExpression actual same _ =>
      have actualForm := shape _ actual
      simp_all
    | singleton _ _ executed =>
      obtain ⟨same, selected⟩ := RecursiveNamedStatementSourceBounds.if_inv unique contains conditional.form (.control executed)
      exact ⟨same, _, selected⟩
  | fault failed =>
    cases failed with
    | tailExpression actual same _ =>
      have actualForm := shape _ actual
      simp_all
    | singleton failed =>
      obtain ⟨same, selected⟩ := RecursiveNamedStatementSourceBounds.if_inv unique contains conditional.form (.fault failed)
      exact ⟨same, _, selected⟩

include conditional in
private theorem finish_branch {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {initialStore middleStore bodyStore : Store} {actual : Environment} {ξ : Renaming} {boolean : Bool}
    {value : Value} {outcome : Dynamic.ExpressionOutcome}
    {initialMap middleMap finalMap : LocationMap} {initialWorld middleWorld finalWorld : StoreTyping}
    (sourceFirst : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before condition (.bool boolean) middle)
    (first : Evaluates actual initialStore (conditionCode.rename ξ) (.inRight .word (.bool boolean)) middleStore)
    (middleHeaps : CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore)
    (firstMaps : LocationMap.Extends initialMap middleMap) (firstWorlds : WorldExtends initialWorld middleWorld)
    (firstFrame : AdministrativePreserved initialMap initialStore middleMap middleStore) (firstMetadata : Dynamic.HeapMetadataExtend before middle)
    (maps : LocationMap.Extends middleMap finalMap) (worlds : WorldExtends middleWorld finalWorld)
    (frame : AdministrativePreserved middleMap middleStore finalMap bodyStore) (metadata : Dynamic.HeapMetadataExtend middle after)
    (sourceLast : Dynamic.ExpressionEvaluatesOutcome program context function.evidence function.source environment middle (expression boolean) outcome after)
    (second : Evaluates (.bool boolean :: actual) middleStore ((code boolean).rename (Renaming.comp (Renaming.insertion 0) ξ)) value bodyStore)
    (represented : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
      finalMap finalWorld (expressionNode boolean).type type faults outcome value)
    (retained : ExpressionFailurePostContracts.OutcomePost (ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry)
      program context function.evidence function.source environment middle (expression boolean) type outcome after value finalMap finalWorld bodyStore) :
    ∃ result, Evaluates actual initialStore (body.rename ξ) result bodyStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        finalMap finalWorld function.resultType type faults outcome result ∧
      OutcomePost (model_bodyPost checked functions registry) program function context environment before
        actual initialStore (body.rename ξ) type outcome after result finalMap finalWorld bodyStore := by
  have rawUnit : ∀ next, returnedControl outcome = Dynamic.ControlOutcome.fallthrough next → function.resultType = .unit := by
    cases outcome <;> intro next same <;> cases same
  have transfers : ImperativeFunctionFinish.TransferFaults faults escaped (returnedControl outcome) := by
    cases outcome <;> constructor <;> intro next same <;> cases same
  obtain ⟨flowValue, returnEvaluation, flowRelated⟩ : ∃ flowValue,
      Evaluates (.bool boolean :: actual) middleStore
        (LocalLoop.returnValue type ((code boolean).rename (Renaming.comp (Renaming.insertion 0) ξ))) flowValue bodyStore ∧
      TypedLexicalWhile.FlowRep (values := .initial checked) (ambient := ambient) (registry := registry)
        functions finalMap finalWorld faults function.resultType type (returnedControl outcome) flowValue := by
    cases represented with
    | value related => exact ⟨_, LocalLoop.returnValue_success _ second, .returned (conditional.resultType boolean ▸ related)⟩
    | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ second, .fault matched⟩
  have branchEvaluation : Evaluates (.bool boolean :: actual) middleStore
      ((LocalLoop.returnValue type ((code boolean).rename ξ)).weakenAt 0) flowValue bodyStore := by
    rw [← LoopRenaming.returnValue, ← GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
    exact returnEvaluation
  have choiceEvaluation : Evaluates actual initialStore
      (LocalLoop.conditional type (conditionCode.rename ξ)
        (LocalLoop.returnValue type ((code true).rename ξ)) (LocalLoop.returnValue type ((code false).rename ξ))) flowValue bodyStore := by
    cases boolean with
    | false => exact LocalControl.choose_false _ first branchEvaluation
    | true => exact LocalControl.choose_true _ first branchEvaluation
  have flowEvaluation : Evaluates actual initialStore
      (LocalLoop.sequence type
        (LocalLoop.conditional type (conditionCode.rename ξ)
          (LocalLoop.returnValue type ((code true).rename ξ)) (LocalLoop.returnValue type ((code false).rename ξ)))
        (LocalLoop.fallthrough type)) flowValue bodyStore := by
    cases outcome with
    | value v => cases flowRelated with | returned _ => exact LocalLoop.sequence_returned _ choiceEvaluation
    | fault r => cases flowRelated with | fault _ => exact LocalLoop.sequence_failure _ choiceEvaluation
  obtain ⟨result, completed, finished⟩ := ImperativeFunctionFinish.from_flow_with_transfers
    (values := .initial checked) (ambient := ambient) (mapping := finalMap) (world := finalWorld)
    (faults := faults) (outcome := returnedControl outcome)
    functions rawUnit conditional.projection fellThrough escaped transfers flowRelated flowEvaluation
  have bodyEvaluation : Evaluates actual initialStore (body.rename ξ) result bodyStore := by
    rw [emitted_rename conditional]
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
        have faultChild : Evaluates (.bool boolean :: actual) middleStore
            ((code boolean).rename (Renaming.comp (Renaming.insertion 0) ξ)) (.inLeft type (.word token)) bodyStore := sameValue ▸ second
        have faultBranch : Evaluates (.bool boolean :: actual) middleStore
            ((LocalLoop.returnValue type ((code boolean).rename ξ)).weakenAt 0)
            (.inLeft (LocalLoop.controlType type) (.word token)) bodyStore := by
          rw [← LoopRenaming.returnValue, ← GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
          exact LocalLoop.returnValue_failure _ faultChild
        have faultChoice : Evaluates actual initialStore
            (LocalLoop.conditional type (conditionCode.rename ξ)
              (LocalLoop.returnValue type ((code true).rename ξ)) (LocalLoop.returnValue type ((code false).rename ξ)))
            (.inLeft (LocalLoop.controlType type) (.word token)) bodyStore := by
          cases boolean with
          | false => exact LocalControl.choose_false _ first faultBranch
          | true => exact LocalControl.choose_true _ first faultBranch
        have faultBody : Evaluates actual initialStore (body.rename ξ) (.inLeft type (.word token)) bodyStore := by
          rw [emitted_rename conditional]
          exact LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped (LocalLoop.sequence_failure _ faultChoice))
        exact ⟨token, (evaluation_deterministic bodyEvaluation faultBody).1,
          model_bodyPost.of_branch conditional boolean sourceFirst first middleHeaps firstMaps firstWorlds firstFrame firstMetadata
            maps worlds frame metadata failed origin faultChild faultBody⟩

include conditional in
private theorem trace_condition {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {childSize : Nat} {reason : Dynamic.SemanticFault}
    (failed : SourceExecutionSize.ExpressionFaults program childSize context function.evidence function.source environment before condition reason after) :
    ∃ size, RecursiveNamedCallBounds.BodyTrace program size function context environment before (.fault reason) after := by
  refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [childSize]], .fault (finalContext := context) ?_⟩
  rw [conditional.statements]
  exact .singleton (.ifCondition (lookupStatement?_sound conditional.found) conditional.form failed)

include conditional in
private theorem trace_branch {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {boolean : Bool} {firstSize lastSize : Nat} {outcome : Dynamic.ExpressionOutcome}
    (first : SourceExecutionSize.ExpressionEvaluates program firstSize context function.evidence function.source environment before condition (.bool boolean) middle)
    (second : RecursiveNamedCallBounds.ExpressionOutcome program lastSize context function.evidence function.source environment middle (expression boolean) outcome after) :
    ∃ size, RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after := by
  cases outcome with
  | value value =>
    cases second with | value child =>
      have returning := SourceExecutionSize.StatementExecutes.returnValue
        (lookupStatement?_sound (conditional.branchFound boolean)) (conditional.branchForm boolean) child
      have selected := SourceExecutionSize.StatementsExecute.terminal (statements := []) returning (Dynamic.TerminalControl.returned value)
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize, SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [lastSize]]]],
        .returned (finalContext := context) ?_⟩
      rw [conditional.statements]
      apply SourceExecutionSize.FunctionStatementsExecute.singleton (lookupStatement?_sound conditional.found)
        (by intro expr; simp [conditional.form])
      cases boolean with
      | false => exact .ifFalseWithElse (lookupStatement?_sound conditional.found) conditional.form first selected
      | true => exact .ifTrue (lookupStatement?_sound conditional.found) conditional.form first selected
  | fault reason =>
    cases second with | fault child =>
      have returning := SourceExecutionSize.StatementFaults.returnValue
        (lookupStatement?_sound (conditional.branchFound boolean)) (conditional.branchForm boolean) child
      have selected := SourceExecutionSize.StatementsFault.head (statements := []) returning
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize, SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [lastSize]]]],
        .fault (finalContext := context) ?_⟩
      rw [conditional.statements]
      apply SourceExecutionSize.FunctionStatementsFault.singleton
      cases boolean with
      | false => exact .ifFalseBody (lookupStatement?_sound conditional.found) conditional.form first selected
      | true => exact .ifTrueBody (lookupStatement?_sound conditional.found) conditional.form first selected
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
  {statement : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
  {conditionFuel : Nat} {branch : Bool → StatementId} {branchNode : Bool → StatementNode}
  {expression : Bool → ExpressionId} {expressionNode : Bool → ExpressionNode} {fuel : Bool → Nat}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {conditionCode : Expr} {code : Bool → Expr}
  {type : Ty} {fellThrough escaped : Word}
  (conditional : ConditionalAt (.initial compiled.compatible.checked) header.function header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) statement node condition conditionNode conditionFuel
    branch branchNode expression expressionNode fuel solved reasonAt conditionCode code type header.body fellThrough escaped)
  (nativeType : type = header.output)
  (source : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (valid : CompatibleExpressionLiterals.ContextValid solved header.context header.function.evidence)
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies conditionFuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults)
  (branchReads : ∀ b, ReachedLoweredReadOutcomePorts.ReadPolicies (fuel b) (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
    header.function.source functions registry program header.context header.function.evidence reasonAt faults)
  (unique : NodeOccurrencesUnique header.function.source) (wellFormed : ProgramWellFormed program)

include conditional nativeType source rows extension faithful observations functionTypes valid reads branchReads missing unique wellFormed in
/-- Source inversion supplies the real condition and chosen return child. -/
theorem source_body_with_post (size : Nat) :
    SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry) (faults := faults) entry reached size := by
  intro outcome after bodyTrace
  obtain ⟨finalContext, control, flowTrace, exit⟩ := RecursiveNamedFunctionFinishBounds.trace_flow bodyTrace
  obtain ⟨rfl, statementSize, selected⟩ := selected_if conditional unique flowTrace
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached := ⟨source.heapTyped, rows⟩
  cases selected with
  | conditionFault failed _ =>
    cases exit
    obtain ⟨value, bodyStore, finalMap, finalWorld, first, represented, finalHeaps,
        maps, worlds, frame, metadata, finalState, related, _postAdmission, retained⟩ :=
      CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
        functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
        valid reads missing unique wellFormed source.runtime source.covers conditional.conditionTree conditional.conditionFound conditional.conditionTyped
        entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted (.fault failed)
    cases represented with | @fault _ oldToken matched =>
      obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained first
      have tokenSame : oldToken = token := by simpa using sameValue
      subst token
      have bodyEvaluation := finished_condition conditional first
      refine ⟨_, bodyStore, finalMap, finalWorld, bodyEvaluation, ?_, finalHeaps, maps, worlds, frame, metadata, ⟨finalState, related⟩, ?_⟩
      · simpa only [nativeType] using (FunctionCalls.ResultRepresents.fault
          (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (mapping := finalMap) (world := finalWorld) (sourceType := header.function.resultType) (type := type) matched)
      · exact ⟨oldToken, by simp [nativeType], model_bodyPost.of_route conditional origin first failed.sound bodyEvaluation⟩
  | conditionType firstTrace notBoolean _ _ =>
    obtain ⟨value, bodyStore, finalMap, finalWorld, _first, represented, _finalHeaps,
        _maps, _worlds, _frame, _metadata, _finalState, _related, _postAdmission, _retained⟩ :=
      CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
        functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
        valid reads missing unique wellFormed source.runtime source.covers conditional.conditionTree conditional.conditionFound conditional.conditionTyped
        entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted (.value firstTrace)
    cases represented with | value payload =>
      have boolPayload := conditional.conditionType ▸ payload
      obtain ⟨_boolean, rfl, _⟩ := bool_fields boolPayload
      exact False.elim (notBoolean trivial)
  | @branch conditionSize bodySize boolean middle innerContext innerOutcome _ firstTrace branchTrace _ _ =>
    have selectedReturn : innerContext = header.context ∧ ∃ lastSize lastOutcome,
        RecursiveNamedCallBounds.ExpressionOutcome program lastSize header.context header.function.evidence header.function.source
          entry.environment middle (expression boolean) lastOutcome after ∧ innerOutcome = returnedControl lastOutcome ∧ lastSize < bodySize := by
      apply RecursiveNamedLexicalTreeSourceBounds.returning (mode := false) unique (conditional.branchFound boolean) (conditional.branchForm boolean)
      cases boolean <;> simpa only [RecursiveNamedLoopContracts.ExecutesAt, Bool.false_eq_true, if_false, if_true, Option.getD_some] using branchTrace
    obtain ⟨rfl, lastSize, lastOutcome, lastTrace, rfl, _strict⟩ := selectedReturn
    obtain ⟨firstValue, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstAdmission, _retained⟩ :=
      CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
        functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
        valid reads missing unique wellFormed source.runtime source.covers conditional.conditionTree conditional.conditionFound conditional.conditionTyped
        entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted (.value firstTrace)
    cases represented with | @value _ payload representedFirst =>
      have boolPayload := conditional.conditionType ▸ representedFirst
      obtain ⟨actualBoolean, sourceEq, coreEq⟩ := bool_fields boolPayload
      have sameBoolean : actualBoolean = boolean := by simpa using sourceEq.symm
      subst actualBoolean
      subst payload
      obtain ⟨_sourceTyped, middleAdmission⟩ := firstAdmission.at_value
      obtain ⟨value, bodyStore, finalMap, finalWorld, second, represented, finalHeaps,
          maps, worlds, frame, metadata, finalState, finalRelated, _postAdmission, retained⟩ :=
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
          functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
          valid (branchReads boolean) missing unique wellFormed source.runtime source.covers (conditional.tree boolean)
          (conditional.expressionFound boolean) (conditional.expressionTyped boolean)
          (entry.environments.extend firstMaps firstWorlds) middleHeaps (source.locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix entry.lookups (.bool boolean))
          (.cons .bool (entry.actualTyped.weaken firstWorlds)) middleState middleAdmission lastTrace
      have retainedAt : ExpressionFailurePostContracts.OutcomePost
          (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
          program header.context header.function.evidence header.function.source entry.environment middle (expression boolean) type lastOutcome after value finalMap finalWorld bodyStore := by
        cases lastOutcome with
        | value v => trivial
        | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained second
      obtain ⟨result, bodyEvaluation, finished, retainedBody⟩ := finish_branch conditional firstTrace.sound first middleHeaps
        firstMaps firstWorlds firstFrame firstMetadata maps worlds frame metadata lastTrace.sound second represented retainedAt
      refine ⟨result, bodyStore, finalMap, finalWorld, bodyEvaluation, ?_, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        ⟨finalState, (protocol headers keys).trans firstRelated finalRelated⟩, ?_⟩
      · cases lastOutcome <;> cases exit <;> simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using finished
      · cases lastOutcome <;> cases exit <;> simpa only [nativeType] using retainedBody

include conditional nativeType source rows extension faithful observations functionTypes valid reads branchReads missing unique wellFormed in
/-- Native finish, sequence and conditional inversion retain the actual selected
branch. Source sizes are reconstructed independently from its true children. -/
theorem native_body_with_post (size : Nat) :
    NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry) (faults := faults) entry reached size := by
  intro value finalStore bodyCompletion
  have nativeFinish : EvaluationSize size entry.actualBody entry.store
      (CompatibleStatements.finish type
        (LocalLoop.sequence type
          (LocalLoop.conditional type (conditionCode.rename entry.embedding)
            (LocalLoop.returnValue type ((code true).rename entry.embedding)) (LocalLoop.returnValue type ((code false).rename entry.embedding)))
          (LocalLoop.fallthrough type)) fellThrough escaped) value finalStore := by
    rw [← emitted_rename conditional]
    exact bodyCompletion
  obtain ⟨flowSize, flowValue, flowStore, _flowStrict, flowCompletion⟩ := RecursiveNamedCallBounds.finish_flow nativeFinish
  obtain ⟨conditionalSize, conditionalStore, conditionalValue, _conditionalStrict, conditionalCompletion⟩ := flowCompletion.bind_computation
  obtain ⟨firstSize, middleStore, firstValue, _firstStrict, firstCompletion⟩ := conditionalCompletion.bind_computation
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached := ⟨source.heapTyped, rows⟩
  obtain ⟨sourceSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, firstRepresented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects (poolBridge (headers := headers) (keys := keys))
      functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
      valid reads missing unique wellFormed source.runtime source.covers conditional.conditionTree conditional.conditionFound conditional.conditionTyped
      entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted firstCompletion
  cases firstRepresented with
  | @fault reason oldToken matched =>
    cases firstTrace with | fault failed =>
      obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained firstCompletion.sound
      have tokenSame : oldToken = token := by simpa using sameValue
      subst token
      have bodyEvaluation := finished_condition conditional firstCompletion.sound
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyCompletion.sound bodyEvaluation
      obtain ⟨bodySize, sourceTrace⟩ := trace_condition conditional failed
      refine ⟨bodySize, .fault reason, middle, middleMap, middleWorld, sourceTrace, ?_, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, ⟨middleState, firstRelated⟩, ?_⟩
      · simpa only [nativeType] using (FunctionCalls.ResultRepresents.fault
          (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (mapping := middleMap) (world := middleWorld) (sourceType := header.function.resultType) (type := type) matched)
      · exact ⟨oldToken, by simp [nativeType], model_bodyPost.of_route conditional origin firstCompletion.sound failed.sound bodyEvaluation⟩
  | @value sourceValue payload representedFirst =>
    cases firstTrace with | value sourceFirst =>
      obtain ⟨boolean, sourceEq, coreEq⟩ := bool_fields representedFirst
      subst sourceValue
      subst payload
      obtain ⟨_sourceTyped, middleAdmission⟩ := firstAdmission.at_value
      obtain ⟨branchSize, _branchStrict, branchCompletion⟩ :
          ∃ branchSize, branchSize < conditionalSize ∧ EvaluationSize branchSize (.bool boolean :: entry.actualBody) middleStore
            ((LocalLoop.returnValue type ((code boolean).rename entry.embedding)).weakenAt 0) conditionalValue conditionalStore := by
        cases boolean with
        | false => exact conditionalCompletion.choose_false firstCompletion.sound
        | true => exact conditionalCompletion.choose_true firstCompletion.sound
      have returnCompletion : EvaluationSize branchSize (.bool boolean :: entry.actualBody) middleStore
          (LocalLoop.returnValue type ((code boolean).rename (Renaming.comp (Renaming.insertion 0) entry.embedding))) conditionalValue conditionalStore := by
        rw [← LoopRenaming.returnValue, GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
        exact branchCompletion
      obtain ⟨lastSize, bodyStore, lastValue, _lastStrict, lastCompletion⟩ := returnCompletion.bind_computation
      obtain ⟨lastSourceSize, lastOutcome, after, finalMap, finalWorld, lastTrace, represented, finalHeaps,
          maps, worlds, frame, metadata, finalState, finalRelated, _postAdmission, retained⟩ :=
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects (poolBridge (headers := headers) (keys := keys))
          functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
          valid (branchReads boolean) missing unique wellFormed source.runtime source.covers (conditional.tree boolean)
          (conditional.expressionFound boolean) (conditional.expressionTyped boolean)
          (entry.environments.extend firstMaps firstWorlds) middleHeaps (source.locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix entry.lookups (.bool boolean))
          (.cons .bool (entry.actualTyped.weaken firstWorlds)) middleState middleAdmission lastCompletion
      have retainedAt : ExpressionFailurePostContracts.OutcomePost
          (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
          program header.context header.function.evidence header.function.source entry.environment middle (expression boolean) type lastOutcome after lastValue finalMap finalWorld bodyStore := by
        cases lastOutcome with
        | value v => trivial
        | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained lastCompletion.sound
      obtain ⟨result, bodyEvaluation, finished, retainedBody⟩ := finish_branch conditional sourceFirst.sound firstCompletion.sound middleHeaps
        firstMaps firstWorlds firstFrame firstMetadata maps worlds frame metadata lastTrace.sound lastCompletion.sound represented retainedAt
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyCompletion.sound bodyEvaluation
      obtain ⟨bodySize, sourceTrace⟩ := trace_branch conditional sourceFirst lastTrace
      refine ⟨bodySize, lastOutcome, after, finalMap, finalWorld, sourceTrace, ?_, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        ⟨finalState, (protocol headers keys).trans firstRelated finalRelated⟩, ?_⟩
      · simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using finished
      · simpa only [nativeType] using retainedBody

include conditional nativeType source rows extension faithful observations functionTypes valid reads branchReads missing unique wellFormed in
/-- Every strict Source body member comes from the same concrete conditional producer. -/
theorem source_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry) (faults := faults) entry reached) := by
  intro child _strict
  exact source_body_with_post functions entry reached conditional nativeType source rows extension faithful observations functionTypes
    valid reads branchReads missing unique wellFormed child

include conditional nativeType source rows extension faithful observations functionTypes valid reads branchReads missing unique wellFormed in
/-- The native strict member consumes its own whole body completion. -/
theorem native_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry) (faults := faults) entry reached) := by
  intro child _strict
  exact native_body_with_post functions entry reached conditional nativeType source rows extension faithful observations functionTypes
    valid reads branchReads missing unique wellFormed child

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedConditionalNamedBodyFaultBounds
