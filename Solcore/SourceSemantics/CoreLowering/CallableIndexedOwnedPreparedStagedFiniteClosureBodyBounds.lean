import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureCanonicalChildFactories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalLambdaApplicationBounds

/-! The fixed finite BodyWith family retains both compiler-view and original
Source trees from the same accepted Code. Its actual terminal child supplies
the finite staged evaluator directly. Original frame typing and selected
Source authority supply the raw child lookup at the real parameter context.
The application producers construct all child meanings internally; certified
read diagnostics and genuine compiler-view transport remain static inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedLambdaStaticBodySupport
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)

section FiniteChild

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- This literal certificate family is finite at both retained Sources. A
generic support family is not converted to it by an equality assumption. -/
def Family (code : Code compiled.indexed function scope administrative) :
    Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  fun readFuel source context => CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate
    readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    source context code.compilation.solvedRequirements code.reasonAt

/-- Compiler transport, flow, raw context and finite certificates all belong
to the same accepted BodyWith. LocalView/Avoids construction remains genuine. -/
abbrev FiniteBody (code : Code compiled.indexed function scope administrative)
    (registry : SourceCoreRawMetadata.Registry) (semanticFaults : FunctionCalls.FaultRep) :=
  BodyWith (values := .initial compiled.compatible.checked)
    CompatibleExpressionProducts.Syntax (Family code) code
    (Program.ofChecked compiled.sourceProgram) registry semanticFaults

private abbrev bodyScope (code : Code compiled.indexed function scope administrative) :
    SourceCoreLocalCell.Scope :=
  code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope

variable {code : Code compiled.indexed function scope administrative}
  {registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}
  (body : FiniteBody code registry semanticFaults)
  (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages)

/-- The canonical certificate is extracted from body.tree using the same
accepted finish equality. No second original-Source lowering is requested. -/
theorem canonical_child :
    CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate body.readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      function.source body.toContext.context code.compilation.solvedRequirements code.reasonAt
      (bodyScope code) packet.expression packet.receipt.child :=
  CallableIndexedOwnedPreparedTerminalClosureCanonicalChildFactories.canonical_child
    body packet.expression packet.receipt.terminal packet

/-- Genuine Registry.source and frame typing retain the original raw child,
including its result type, at this BodyWith's actual parameter context. -/
theorem raw_child (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ node, child.source.lookupExpression? packet.expression = some node ∧
      node.type = function.resultType ∧
      ExpressionHasType child.source body.toContext.context packet.expression node.type := by
  have view : LambdaMetadataViews.MetadataView child.source code.view := by
    rw [stages.source selected]
    exact code.viewOfSource
  exact CallableIndexedOwnedPreparedStagedTerminalBodyTyping.at_parameters body.frame body.extended
    (stages.source selected)
    (CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head packet.receipt view)

variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead body.readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      function.source body.toContext.context code.reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (code.reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include extension uninitialized semantic wellFormed in
/-- Every smaller Source child meaning is constructed by the actual finite
tree. The exact selected child is the sole singleton certificate member. -/
theorem child_preserves (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (budget : Nat) :
    PreservesBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      body.toContext.context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow packet).certificate
      faults budget := by
  have source := stages.source selected
  have certified := canonical_child body packet
  rw [← source] at certified
  have unique : NodeOccurrencesUnique child.source := by rw [source]; exact body.unique
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      body.toContext.context child.source := by
    rw [source]
    exact (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended).1
  have covers : child.evidence.Covers body.toContext.context := by
    rw [stages.evidence selected]
    exact body.valid.covers
  have certifiedFaults : ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead body.readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        child.source body.toContext.context code.reasonAt scope id lowered →
      ∀ location, semanticFaults (.uninitializedLocation location) (code.reasonAt id) := by
    simpa only [source] using uninitialized
  obtain ⟨node, found, _resultType, typed⟩ := raw_child body packet child selected
  intro size _smaller current id lowered point
  change current = bodyScope code ∧ id = packet.expression ∧ lowered = packet.receipt.child at point
  obtain ⟨rfl, rfl, rfl⟩ := point

  intro actualNode actualFound _actualTyped
  have same : actualNode = node := Option.some.inj (actualFound.symm.trans found)
  cases same
  intro mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.preserves (registry := stages) (invocation := child)
    (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
    functions extension body.valid.ledger body.valid.runtime faults certifiedFaults semantic unique
    wellFormed runtime covers size certified found typed environments heaps locals agrees actualTyped initial admitted trace

include extension uninitialized semantic wellFormed in
/-- Native reflection follows the original finite sites at each strict
budget and returns an independent Source grade with the full reached post. -/
theorem child_reflects (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (budget : Nat) :
    ReflectsBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      body.toContext.context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow packet).certificate
      faults budget := by
  have source := stages.source selected
  have certified := canonical_child body packet
  rw [← source] at certified
  have unique : NodeOccurrencesUnique child.source := by rw [source]; exact body.unique
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      body.toContext.context child.source := by
    rw [source]
    exact (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended).1
  have covers : child.evidence.Covers body.toContext.context := by
    rw [stages.evidence selected]
    exact body.valid.covers
  have certifiedFaults : ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead body.readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        child.source body.toContext.context code.reasonAt scope id lowered →
      ∀ location, semanticFaults (.uninitializedLocation location) (code.reasonAt id) := by
    simpa only [source] using uninitialized
  obtain ⟨node, found, _resultType, typed⟩ := raw_child body packet child selected
  intro size _smaller current id lowered point
  change current = bodyScope code ∧ id = packet.expression ∧ lowered = packet.receipt.child at point
  obtain ⟨rfl, rfl, rfl⟩ := point

  intro actualNode actualFound _actualTyped
  have same : actualNode = node := Option.some.inj (actualFound.symm.trans found)
  cases same
  intro mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted trace
  exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.reflects (registry := stages) (invocation := child)
    (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
    functions extension body.valid.ledger body.valid.runtime faults certifiedFaults semantic unique
    wellFormed runtime covers size certified found typed environments heaps locals agrees actualTyped initial admitted trace

end FiniteChild

section Application
open SourceCoreCallableIndexedFrames

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (body : FiniteBody code registry semanticFaults)
  {stages : Staging.Recursive.Registry}
  {faults : RecursiveStageMeaning.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments body.types)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead body.readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      function.source body.toContext.context code.reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (code.reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (expression : ExpressionId)
  (shape : Terminal code.view expression function.body)
  (reader : body.policy.readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked)



variable (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) callerContext callerSource)

include stable beforeTyped argumentsTyped extension uninitialized semantic wellFormed expression shape reader represented heaps locals reference currentCarried allowed callerRuntime in
/-- The strict body port is manufactured at the genuine parameter entry.
The Source application and both native prefixes run once. -/
theorem application_preserves (child : Staging.Recursive.Scope)
    (selected : stages.Closure function child) (budget : Nat)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size invocation callContext before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := registry) (faults := faults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  obtain ⟨packet, _sameCertificate, _sameChild, _sameExpression, _certified⟩ :=
    CallableIndexedOwnedPreparedTerminalClosureFactories.of_actual_body_exact
      body expression shape reader child selected
  let narrowed := CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow packet
  exact CallableIndexedOwnedPreparedStagedTerminalLambdaApplicationBounds.application_preserves
    captured code history body.toContext functions owner caller stable beforeTyped argumentsTyped
    narrowed.receipt narrowed.certifies represented heaps locals reference currentCarried allowed callerRuntime
    budget (fun actualChild actualSelected =>
      child_preserves body packet functions extension uninitialized semantic wellFormed
        actualChild actualSelected budget) trace within

include stable beforeTyped argumentsTyped extension uninitialized semantic wellFormed expression shape reader represented heaps locals reference currentCarried allowed callerRuntime in
/-- Reflection selects the authentic strict native body child and constructs
its independently graded Source body from the expression hypothesis. -/
theorem application_reflects (child : Staging.Recursive.Scope)
    (selected : stages.Closure function child) (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (budget : Nat)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize invocation callContext before
        (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := registry) (faults := faults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  obtain ⟨packet, _sameCertificate, _sameChild, _sameExpression, _certified⟩ :=
    CallableIndexedOwnedPreparedTerminalClosureFactories.of_actual_body_exact
      body expression shape reader child selected
  let narrowed := CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow packet
  exact CallableIndexedOwnedPreparedStagedTerminalLambdaApplicationBounds.application_reflects
    captured code history body.toContext functions owner caller stable beforeTyped argumentsTyped
    narrowed.receipt narrowed.certifies represented heaps locals reference currentCarried allowed callerRuntime
    child selected valid budget
    (child_reflects body packet functions extension uninitialized semantic wellFormed child selected budget)
    completed within

end Application

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureBodyBounds
