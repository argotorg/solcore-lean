import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning

/-! Whole-body assembly for the literal recursive discard sequence. Original
full body typing fixes its declared raw result, then strict numeric Root IHs
construct the reached flow. The same accepted receipt supplies one finish
footer. No execution law or desired completed result is a static input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Sequence SequenceSupport parameterScope)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts (FlowReceipt Receipt)
open CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds (Tree)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)
open CallableIndexedOwnedPreparedStagedTerminalBodyMeaning (fallback)

/-- The retained accepted statement action fixes the complete renamed footer. -/
theorem emitted_rename {policy : SourceCoreLoops.Policy} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Receipt policy fuel source scope statements result reasonAt fellThrough escaped code)
    (ξ : Renaming) :
    code.rename ξ = CallableIndexedOwnedAdmittedStagedTerminalBody.code result
      (receipt.flow.rename ξ) escaped ((fallback result fellThrough).rename ξ) := by
  have footer := congrArg (fun generated : Expr => generated.rename ξ) receipt.emitted
  exact footer.trans (by
    simpa only [CompatibleStatements.finish,
      CallableIndexedOwnedAdmittedStagedTerminalBody.code, fallback] using
      (CallableIndexedOwnedAdmittedStagedTerminalBody.code_rename result receipt.flow
        escaped (fallback result fellThrough) ξ))

private theorem tree_of_roots {compiled : SourceCoreUnifiedCompilation.Compiled}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {scope : SourceCoreLocalCell.Scope} {semanticFaults : FunctionCalls.FaultRep}
    {policy : SourceCoreLoops.Policy} {view : TypedSource} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
    {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    (metadata : LambdaMetadataViews.MetadataView invocation.source view)
    (roots : ∀ expression child, receipt.Children expression child →
      Nonempty (RootAt compiled context invocation scope expression child semanticFaults)) :
    ∃ rawResult, Nonempty (Tree compiled context invocation scope semanticFaults result rawResult
      statements flow) := by
  revert roots
  induction receipt with
  | terminal terminal generated =>
    intro roots
    obtain ⟨root⟩ := roots _ _ ⟨rfl, rfl⟩
    exact ⟨root.support.node.type, ⟨.terminal root
      (CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head terminal metadata)
      terminal.sameType rfl⟩⟩
  | discard found form first generated tail accepted ih =>
    intro roots
    obtain ⟨root⟩ := roots _ _ (.inl ⟨rfl, rfl⟩)
    obtain ⟨rawResult, ⟨tailTree⟩⟩ := ih (fun expression child used =>
      roots expression child (.inr used))
    exact ⟨rawResult, ⟨.discard root (lookupStatement?_sound (metadata.statement found)) form tailTree⟩⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {capturedContext : Core.Context} {code : Code compiled.indexed function scope capturedContext}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
  (packet : Sequence code stages)
  (support : SequenceSupport code inputs stages packet semanticFaults)
  {child : Staging.Recursive.Scope} (selected : stages.Closure function child)

include support selected in
/-- The original frame and literal parameter extension derive the declared raw
result for the tree assembled from the actual receipt and original Roots. -/
theorem issued_tree :
    Nonempty (Tree compiled inputs.context child (parameterScope code) semanticFaults
      code.receipt.resultCore function.resultType function.body packet.receipt.flow) := by
  have source : child.source = function.source := stages.source selected
  have metadata : LambdaMetadataViews.MetadataView child.source code.view := by
    simpa only [source] using code.viewOfSource
  obtain ⟨rawResult, ⟨tree⟩⟩ := tree_of_roots packet.receipt.tree metadata
    (fun expression childCode used => support.roots child selected expression childCode used)
  obtain ⟨final, facts, typed, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters support.frame inputs.extended
  rw [← source] at typed
  have unique : NodeOccurrencesUnique child.source := by
    rw [source]
    exact support.frame.code.graph.nodeOccurrencesUnique
  have sameRaw : rawResult = function.resultType :=
    CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerSupport.raw_result
      unique tree typed completes
  subst rawResult
  exact ⟨tree⟩

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable {mapping : LocationMap} {world : StoreTyping}
  {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents
    (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative (parameterScope code) environment canonical
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before inputs.context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : State headers keys ⟨parameterScope code, mapping, world, before, store, canonical⟩)
  (admitted : Admission
    (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
    inputs.context initial)

include support selected environments heaps locals agrees actualTyped admitted in
/-- The exact original body trace manufactures its flow outcome and literal
footer evaluation at the same reached parameter state. -/
theorem preserves_body {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget)
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      stages size child inputs.context environment before function.body finalContext bodyOutcome after) :
    finalContext = inputs.context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧
      Staging.Recursive.BodyResult function.resultType bodyOutcome outcome ∧
      ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.receipt.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType code.receipt.resultCore callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
        ⟨parameterScope code, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          poolBridge inputs.context function.resultType outcome reached := by
  obtain ⟨tree⟩ := issued_tree packet support selected
  obtain ⟨sameContext, outcome, sameBody, value, finalStore, finalMap, finalWorld,
      flow, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds.preserves_flow
      (profile := profile) tree children environments heaps locals agrees actualTyped
      initial admitted within trace
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback code.receipt.resultCore packet.fellThrough).rename ξ)
      represented flow packet.escaped
  have evaluatedBody : Evaluates actual store (code.receipt.body.rename ξ) wholeValue finalStore := by
    rw [emitted_rename packet.receipt ξ]
    exact whole
  have bodyResult : Staging.Recursive.BodyResult function.resultType bodyOutcome outcome := by
    rw [sameBody]
    exact CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _
  exact ⟨sameContext, outcome, sameBody, bodyResult, wholeValue, finalStore, finalMap, finalWorld,
    evaluatedBody, resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

include support selected environments heaps locals agrees actualTyped admitted in
/-- The literal footer exposes a strict native flow child. Its Source grade
and nested fault remain independent of the original completed native grade. -/
theorem reflects_body {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.receipt.body.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        child inputs.context environment before function.body inputs.context (control outcome) after ∧
      Staging.Recursive.BodyResult function.resultType (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType code.receipt.resultCore callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
        ⟨parameterScope code, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          poolBridge inputs.context function.resultType outcome reached := by
  obtain ⟨tree⟩ := issued_tree packet support selected
  have original := completed
  rw [emitted_rename packet.receipt ξ] at original
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix original (Nat.le_refl size)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
      finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds.reflects_flow
      (profile := profile) tree children environments heaps locals agrees actualTyped
      initial admitted (Nat.le_trans (Nat.le_of_lt strict) within) flowTrace
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback code.receipt.resultCore packet.fellThrough).rename ξ)
      represented flowTrace.sound packet.escaped
  obtain ⟨same, stores⟩ := evaluation_deterministic original.sound whole
  cases same
  subst stores
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
    CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds
