import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyExitReceipts

/-! Preservation and reflection of a supported recursive discard sequence
retain its original staged trace and reached admission. Ordinary returned values and
semantic faults additionally expose the exact lexical exit. A stage rejection
keeps its original scope, call, reason, context and prefix heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceBodyExitBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
  (Sequence SequenceSupport parameterScope PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)

/-- Ordinary exits and stage rejection retain distinct literal outcomes. -/
inductive ExitReceipt (checked : SourceCoreCompatibleCatalog.Checked)
    (definitions : DataEnvironment) (mapping : LocationMap) (world : StoreTyping)
    (administrative : Core.Context) (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (environment : Dynamic.Environment) (before after : Dynamic.Heap) :
    Staging.Recursive.Outcome → Prop where
  | returned {value : Dynamic.Value}
      (exit : TypedMixedNamedBody.ReachedExit checked definitions mapping world administrative
        program function context scope environment before after (.value value)) :
      ExitReceipt checked definitions mapping world administrative program stages invocation
        function context scope environment before after (.value value)
  | semanticFault {reason : Dynamic.SemanticFault}
      (exit : TypedMixedNamedBody.ReachedExit checked definitions mapping world administrative
        program function context scope environment before after (.fault reason)) :
      ExitReceipt checked definitions mapping world administrative program stages invocation
        function context scope environment before after (.fault (.semantic reason))
  | stageRejected {rejectionScope : Staging.Recursive.Scope} {call : ExpressionId}
      {reason : Staging.CallGuard.Fault}
      (trace : Staging.Recursive.Statements program stages invocation context environment before
        function.body context (.fault (.stage rejectionScope call reason)) after) :
      ExitReceipt checked definitions mapping world administrative program stages invocation
        function context scope environment before after (.fault (.stage rejectionScope call reason))

/-- Actual trace and extension receipts construct the appropriate exit branch. -/
theorem exit_receipt_of_trace
    {checked : SourceCoreCompatibleCatalog.Checked} {definitions : DataEnvironment}
    {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
    {administrative : Core.Context} {program : Program} {stages : Staging.Recursive.Registry}
    {invocation : Staging.Recursive.Scope} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment} {before after : Dynamic.Heap}
    (selected : stages.Closure function invocation)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog)
      mapping world administrative scope environment canonical definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (metadata : Dynamic.HeapMetadataExtend before after) {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Statements program stages invocation context environment before
      function.body context (control outcome) after) :
    ExitReceipt checked definitions finalMap finalWorld administrative program stages invocation
      function context scope environment before after outcome := by
  cases outcome with
  | value value =>
    exact .returned
      (CallableIndexedOwnedPreparedStagedBodyExitReceipts.reached_returned
        selected environments locals maps worlds metadata rfl trace)
  | fault failure =>
    cases failure with
    | semantic reason =>
      exact .semanticFault
        (CallableIndexedOwnedPreparedStagedBodyExitReceipts.reached_semanticFault
          selected environments locals maps worlds metadata rfl trace)
    | stage rejectionScope call reason => exact .stageRejected trace

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    NamedSupport header stages (namedTerminals header member) semanticFaults)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {capturedContext : Core.Context} {code : Code compiled.indexed function scope capturedContext}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
  (packet : Sequence code stages)
  (support : SequenceSupport code inputs stages packet semanticFaults)
  {child : Staging.Recursive.Scope} (selected : stages.Closure function child)

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

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry
  (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared
  observations extension semantic support selected environments heaps locals agrees actualTyped admitted in
/-- Closed strict child preservation supplies the literal body evaluation once.
The original trace retains its ordinary exit or exact stage rejection alongside
the full reached PostAdmission. -/
theorem preserves_body_with_exit {size : Nat}
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
      ExitReceipt compiled.compatible.checked
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
        finalMap finalWorld administrative (Program.ofChecked compiled.sourceProgram) stages child
        function inputs.context (parameterScope code) environment before after outcome ∧
      ∃ reached : State headers keys
        ⟨parameterScope code, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          poolBridge inputs.context function.resultType outcome reached := by
  have children : ∀ childSize, childSize < size →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize := by
    intro childSize _
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves
      profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared
      observations extension semantic childSize
  obtain ⟨sameContext, outcome, sameBody, bodyResult, value, finalStore, finalMap, finalWorld,
      evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds.preserves_body
      (profile := profile) packet support selected environments heaps locals agrees actualTyped
      initial admitted children (Nat.le_refl size) trace
  have original : Staging.Recursive.Statements (Program.ofChecked compiled.sourceProgram) stages
      child inputs.context environment before function.body inputs.context (control outcome) after := by
    simpa only [sameContext, sameBody] using trace.sound
  have exit := exit_receipt_of_trace selected environments locals maps worlds metadata original
  exact ⟨sameContext, outcome, sameBody, bodyResult, value, finalStore, finalMap, finalWorld,
    evaluated, represented, finalHeaps, maps, worlds, frame, metadata, exit, reached, related, post⟩

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared
  observations extension semantic stageEq support selected environments heaps locals agrees actualTyped admitted in
/-- Closed strict child reflection supplies the body trace once; every result
retains its nested fault representation and reached PostAdmission. -/
theorem reflects_body_with_exit {size : Nat} {value : Value} {finalStore : Store}
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
      ExitReceipt compiled.compatible.checked
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
        finalMap finalWorld administrative (Program.ofChecked compiled.sourceProgram) stages child
        function inputs.context (parameterScope code) environment before after outcome ∧
      ∃ reached : State headers keys
        ⟨parameterScope code, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          poolBridge inputs.context function.resultType outcome reached := by
  have children : ∀ childSize, childSize < size →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize := by
    intro childSize _
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects
      profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared
      observations extension semantic stageEq childSize
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, bodyResult, represented,
      finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds.reflects_body
      (profile := profile) packet support selected environments heaps locals agrees actualTyped
      initial admitted children (Nat.le_refl size) completed
  have exit := exit_receipt_of_trace selected environments locals maps worlds metadata trace.sound
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, bodyResult, represented,
    finalHeaps, maps, worlds, frame, metadata, exit, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceBodyExitBounds
