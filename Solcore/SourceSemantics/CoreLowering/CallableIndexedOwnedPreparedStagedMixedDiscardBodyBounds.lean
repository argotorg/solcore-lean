import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerBodyBounds

/-! Internal whole-body assembly for the genuine selected discard packet.
The strict numeric Root IH produces both evaluated child meanings, and the
same accepted receipt supplies the actual finish footer. The completed body
result is derived from that flow; it is not a static support premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Discard DiscardSupport parameterScope)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)
open CallableIndexedOwnedPreparedStagedTerminalBodyMeaning (fallback)

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
  (packet : Discard code stages)
  (support : DiscardSupport code inputs stages packet semanticFaults)
  {child : Staging.Recursive.Scope} (selected : stages.Closure function child)

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
  obtain ⟨node, contains, form, terminal⟩ := support.heads child selected
  let roots := support.roots child selected
  rw [packet.body] at trace
  obtain ⟨sameContext, outcome, sameBody, value, finalStore, finalMap, finalWorld,
      flow, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedDiscardFlowBounds.preserves_flow
      (profile := profile) (firstRoot := roots.1) (terminalRoot := roots.2.val)
      (contains := contains) (form := form) (terminal := terminal)
      (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
      (actualTyped := actualTyped) (initial := initial) (admitted := admitted)
      children within trace
  have flowTyped : Evaluates actual store
      ((LocalSequence.discard (LocalLoop.controlType code.receipt.resultCore)
        packet.receipt.first.expression
        (LocalLoop.returnValue code.receipt.resultCore packet.receipt.tail.child.expression)).rename ξ)
      value finalStore := by
    simpa only [packet.receipt.tail.sameType] using flow
  have resultTyped : CallableIndexedOwnedAdmittedStagedTerminalStatements.ResultRepresents
      model finalMap finalWorld function.resultType code.receipt.resultCore callFaults outcome value := by
    simpa only [roots.2.val.support.rawResult, roots.2.property, packet.receipt.tail.sameType] using represented
  have finalPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      poolBridge inputs.context function.resultType outcome reached := by
    simpa only [roots.2.val.support.rawResult, roots.2.property] using post
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback code.receipt.resultCore packet.fellThrough).rename ξ)
      resultTyped flowTyped packet.escaped
  have evaluatedBody : Evaluates actual store (code.receipt.body.rename ξ) wholeValue finalStore := by
    rw [CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerBodyBounds.emitted_rename packet.receipt ξ]
    exact whole
  have bodyResult : Staging.Recursive.BodyResult function.resultType bodyOutcome outcome := by
    rw [sameBody]
    exact CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _
  exact ⟨sameContext, outcome, sameBody, bodyResult, wholeValue, finalStore, finalMap, finalWorld,
    evaluatedBody, resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related, finalPost⟩

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
  obtain ⟨node, contains, form, terminal⟩ := support.heads child selected
  let roots := support.roots child selected
  have original := completed
  rw [CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerBodyBounds.emitted_rename packet.receipt ξ] at original
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix original (Nat.le_refl size)
  have flowTyped : EvaluationSize flowSize actual store
      ((LocalSequence.discard (LocalLoop.controlType packet.receipt.tail.child.type)
        packet.receipt.first.expression
        (LocalLoop.returnValue packet.receipt.tail.child.type packet.receipt.tail.child.expression)).rename ξ)
      flowValue flowStore := by
    simpa only [packet.receipt.tail.sameType] using flowTrace
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
      finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedDiscardFlowBounds.reflects_flow
      (profile := profile) (firstRoot := roots.1) (terminalRoot := roots.2.val)
      (contains := contains) (form := form) (terminal := terminal)
      (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
      (actualTyped := actualTyped) (initial := initial) (admitted := admitted)
      children (Nat.le_trans (Nat.le_of_lt strict) within) flowTyped
  have resultTyped : CallableIndexedOwnedAdmittedStagedTerminalStatements.ResultRepresents
      model finalMap finalWorld function.resultType code.receipt.resultCore callFaults outcome flowValue := by
    simpa only [roots.2.val.support.rawResult, roots.2.property, packet.receipt.tail.sameType] using represented
  have finalPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      poolBridge inputs.context function.resultType outcome reached := by
    simpa only [roots.2.val.support.rawResult, roots.2.property] using post
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback code.receipt.resultCore packet.fellThrough).rename ξ)
      resultTyped flowTrace.sound packet.escaped
  obtain ⟨same, stores⟩ := evaluation_deterministic original.sound whole
  cases same
  subst stores
  have originalTrace : Staging.Recursive.Size.Statements
      (Program.ofChecked compiled.sourceProgram) stages sourceSize child inputs.context
      environment before function.body inputs.context (control outcome) after := by
    simpa only [packet.body] using trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, originalTrace,
    CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, finalPost⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardBodyBounds
