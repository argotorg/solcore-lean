import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedTerminalDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates

/-!
# Staged bounds: finite named and indirect calls

Named invocation, parent and global dispatch bounds of the finite family, and its indirect call bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedBodyBounds
/-! Actual finite named terminal bodies construct both staged directions
without an external expression meaning premise. The accepted child compiler
receipt retains its original raw typing and every literal/read/product site.
The actual issuer and receiver interpret read failures. Full reached caller
state, lazy mapping writes and independent Source/native grades are retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt Terminal)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {expression : ExpressionId}

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  (ordinary : CompatibleExpressionProducts.Ordinary header.function.source
    compiled.indexed.base.locals (CallableIndexedNamedGeneration.context compiled.indexed prepared.named).owner)
  (syntaxTree : CompatibleExpressionProducts.Syntax header.function.source expression)
  (sameLedger : header.context.solvedRequirements = header.solved)
  (runtimeLedger : RuntimeRequirementLedgerValid header.context)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context child.source)
  (covers : child.evidence.Covers header.context)

variable
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrative
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before header.context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge header.context initial)

include aligned diagnostic receiver selected wellFormed terminal ordinary syntaxTree sameLedger runtimeLedger runtime covers environments heaps locals agrees typed admitted
/-- The original named body Source typing and genuine selected child scope
construct preservation from the actual finite child tree. The body
trace and nested failure scope remain recursively staged. -/
theorem preserves_body (budget : Nat)
    {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages size child
      header.context environment before header.function.body finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (header.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) finalMap finalWorld
        header.function.resultType header.output (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge header.context header.function.resultType outcome reached := by
  have uniqueChild : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  have childTree : (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression terminal.child := by
    simpa only [stages.source selected] using
      CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.finite_child
        prepared aligned terminal selected wellFormed ordinary syntaxTree
  have certifies : ∀ lowered,
      header.policy.lowerExpression terminal.childFuel header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
      (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt) (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered := by
    intro lowered generated
    have same : terminal.child = lowered := Except.ok.inj (terminal.generated.symm.trans generated)
    exact same ▸ childTree
  have readFault : ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead compiled.indexed.fuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        child.source header.context header.reasonAt scope id lowered →
      ∀ location, CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
        (.uninitializedLocation location) (header.reasonAt id) := by
    intro scope id lowered receipt location
    exact CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized
      prepared diagnostic aligned receiver (by simpa only [stages.source selected] using receipt) location
  have children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow bridge header.context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
      stages child (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt) (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) budget := by
    intro childSize _smaller
    exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.preserves bridge functions
      completion.result.extension sameLedger runtimeLedger (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) readFault
      (fun reason token represented => CallableIndexedOwnedPublicDecodedStagedCallFaults.of_semantic represented)
      uniqueChild wellFormed runtime covers childSize
  have view : LambdaMetadataViews.MetadataView child.source header.function.source := by
    rw [stages.source selected]
    exact .refl _
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨staticFinal, facts, bodyTyped, complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  have scopedBodyTyped : StatementsHaveType child.source
      {returnType := header.function.resultType} header.context header.function.body staticFinal facts := by
    simpa only [stages.source selected] using bodyTyped
  exact CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.preserves_body
    (receipt := terminal) (view := view) (bridge := bridge) (bodyTyped := scopedBodyTyped) (complete := complete)
    (certifies := certifies) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    unique budget children (trace := trace) (matched := matched) (within := within)

include aligned diagnostic receiver selected wellFormed terminal ordinary syntaxTree sameLedger runtimeLedger runtime covers environments heaps locals agrees typed admitted
/-- Literal native body completion reflects to an independently graded staged
Source body, using the same accepted Header code and actual parameter state.
The complete returned pool and successful Source post are retained. -/
theorem reflects_body (budget : Nat)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (header.body.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize child
        header.context environment before header.function.body header.context
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) after ∧
      Staging.Recursive.BodyResult header.function.resultType
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) finalMap finalWorld
        header.function.resultType header.output (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge header.context header.function.resultType outcome reached := by
  have uniqueChild : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  have childTree : (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression terminal.child := by
    simpa only [stages.source selected] using
      CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.finite_child
        prepared aligned terminal selected wellFormed ordinary syntaxTree
  have certifies : ∀ lowered,
      header.policy.lowerExpression terminal.childFuel header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
      (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt) (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered := by
    intro lowered generated
    have same : terminal.child = lowered := Except.ok.inj (terminal.generated.symm.trans generated)
    exact same ▸ childTree
  have readFault : ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead compiled.indexed.fuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        child.source header.context header.reasonAt scope id lowered →
      ∀ location, CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
        (.uninitializedLocation location) (header.reasonAt id) := by
    intro scope id lowered receipt location
    exact CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized
      prepared diagnostic aligned receiver (by simpa only [stages.source selected] using receipt) location
  have children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow bridge header.context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
      stages child (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt) (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) budget := by
    intro childSize _smaller
    exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.reflects bridge functions
      completion.result.extension sameLedger runtimeLedger (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) readFault
      (fun reason token represented => CallableIndexedOwnedPublicDecodedStagedCallFaults.of_semantic represented)
      uniqueChild wellFormed runtime covers childSize
  have view : LambdaMetadataViews.MetadataView child.source header.function.source := by
    rw [stages.source selected]
    exact .refl _
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨staticFinal, facts, bodyTyped, complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  have scopedBodyTyped : StatementsHaveType child.source
      {returnType := header.function.resultType} header.context header.function.body staticFinal facts := by
    simpa only [stages.source selected] using bodyTyped
  exact CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.reflects_body
    (receipt := terminal) (view := view) (bridge := bridge) (bodyTyped := scopedBodyTyped) (complete := complete)
    (certifies := certifies) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    unique budget children (completed := completed) (within := within)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds
/-! Finite named invocation and application construct both directions from the
actual Header, Source parameter allocation and native parameter prefix. The
finite body producer discharges read/literal/group/pair execution internally.
The same returned pool restores the saved caller, retaining full admission
and separate Source/native grades, including nested staged failures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)


variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (index : Int) (actual : Environment) (store : Store) (saved : Value) :
    Evaluates (saved :: actual) store
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

private theorem related_cast_frame
    {initial : ProtectedStateTransition.Index} (saved : State headers keys initial)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {first second : Location} {next : Value} (same : first = second)
    (state : State headers keys ⟨scope, mapping, world, before, store.set first next, canonical⟩)
    (related : Relates saved state) :
    Relates saved (Eq.mp (congrArg (fun location => State headers keys
      ⟨scope, mapping, world, before, store.set location next, canonical⟩) same) state) := by
  cases same
  exact related

private theorem readyAt_cast
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {expression : ExpressionId}
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (ordinary : CompatibleExpressionProducts.Ordinary header.function.source
    compiled.indexed.base.locals (CallableIndexedNamedGeneration.context compiled.indexed prepared.named).owner)
  (syntaxTree : CompatibleExpressionProducts.Syntax header.function.source expression)
  (sameLedger : header.context.solvedRequirements = header.solved)
  (runtimeLedger : RuntimeRequirementLedgerValid header.context)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context header.function.source)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include functions owner caller header capture sourceAt terminal prepared aligned diagnostic receiver ordinary syntaxTree sameLedger runtimeLedger runtime in
/-- Authentic Source allocation and the strict staged body child construct the
native parameter/body continuation before literal caller restoration. The
returned state retains full representation, relates and caller PostAdmission. -/
theorem preserves_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions mapping world before store)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (budget : Nat)
    (covers : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      child.evidence.Covers header.context)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
      size invocation context before (.global function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  have liveLocals : Dynamic.EnvironmentAgrees before header.function.context.locals [] := by
    obtain ⟨original⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner member
    exact original.locals
  have liveReference : capture.canonical[header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using capture.reference
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨childSize, child, environment, bound, finalContext, bodyOutcome,
    selected, allocated, bodyTrace, converted, smaller⟩ := CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix sourceAt wellFormed arity trace
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
      (DataPatternValues.packValues payloads :: capture.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped capture.typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame model :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys model
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      model owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, before, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), capture.canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, before, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), capture.canonical⟩)
      physical.symm) installed
  obtain ⟨entry, parameterTransition, agreement⟩ := parameters_with_state installedAuthority
    capture.environments liveLocals liveReference capture.coherent represented installedHeaps
    layout actualTyped producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := completion.result.context.registry) functions owner caller header arguments :=
    ⟨origin, index, metadata, capture.administrative, _,
      .unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured,
      Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift),
      authority.frameLocation, (caller.rows owner.position).frame_eq, owned, history, emitted,
      entry, parameterState, installedRelated.trans parameterRelated, stable, heapTyped, argumentsTyped⟩
  have admitted : Admission poolBridge header.context parameterState := ⟨(receipt.source wellFormed).heapTyped, receipt.rows⟩
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    CallableIndexedOwnedPreparedStagedFiniteNamedBodyBounds.preserves_body
      (bridge := poolBridge) (selected := selected) (wellFormed := wellFormed)
      (prepared := prepared) (aligned := aligned) (functions := functions)
      (diagnostic := diagnostic) (receiver := receiver) (terminal := terminal)
      (ordinary := ordinary) (syntaxTree := syntaxTree) (sameLedger := sameLedger)
      (runtimeLedger := runtimeLedger) (runtime := by simpa only [stages.source selected] using runtime)
      (covers := covers selected)
      (environments := entry.environments) (heaps := entry.heaps) (locals := entry.locals)
      (agrees := entry.lookups) (typed := entry.actualTyped) (initial := parameterState) (admitted := admitted)
      budget bodyTrace converted (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
  have prefixEvaluation := agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ, physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using capture.capturedReference
  have evaluation := CallableContextFrames.withFrame_evaluates (.var reference) authority.frame.read
    (next_evaluates index (DataPatternValues.packValues payloads :: capture.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current)) prefixEvaluation
  have renamed : header.code.rename capture.embedding.lift = withFrame
      (.var (capture.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (header.parameterCode.rename capture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := installedRelated.trans (parameterRelated.trans bodyRelated)
  obtain ⟨restoredHeaps, restoredFrame, _cell, _fromBody, restoredRelated, _records, _transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using frame) related
  have restoredPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps, maps, worlds,
    restoredFrame, sourceMetadata, CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position,
    restoredRelated, restoredPost⟩
  simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using
    (renamed.symm ▸ evaluation)

/-- This is the literal carrier exposed by genuine positive named payloads.
No Source signature or code provenance is inferred from its native shape. -/
def carrier (identity descriptor : Word) : Value :=
  .pair (.pair (.inRight .unit (.word identity))
    (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor)

include functions owner caller header capture sourceAt terminal prepared aligned diagnostic receiver ordinary syntaxTree sameLedger runtimeLedger runtime in
/-- Source allocation and its selected body construct the exact invocation,
then the physical payload apply rule. No native grade is equated to Source. -/
theorem application_preserves
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions mapping world before store)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (identity descriptor : Word) (budget : Nat)
    (covers : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      child.evidence.Covers header.context)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
      size invocation context before (.global function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [carrier (owner := owner) header capture identity descriptor, DataPatternValues.packValues payloads]
        store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨value, finalStore, finalMap, finalWorld, result⟩ :=
    preserves_invocation (prepared := prepared) (aligned := aligned)
      (diagnostic := diagnostic) (receiver := receiver) (ordinary := ordinary) (syntaxTree := syntaxTree)
      (sameLedger := sameLedger) (runtimeLedger := runtimeLedger) (runtime := runtime)
      functions owner caller header capture sourceAt terminal sameLayouts member wellFormed
      stable heapTyped argumentsTyped represented heaps supports budget covers trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) result.1, result⟩

variable {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named header.named.signature.key))

include functions owner caller header capture sourceAt terminal prepared aligned diagnostic receiver ordinary syntaxTree sameLedger runtimeLedger runtime stagePrepared descriptor in
/-- The actual Header and its authenticated named sidecar construct the body
scope. The native prefix reaches its real allocation state, where strict child
reflection supplies the staged body. The original global application and the
literal restored caller are then constructed without an ordinary body law. -/
theorem reflects_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions mapping world before store)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (budget : Nat)
    (covers : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      child.evidence.Covers header.context)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt (registry := completion.result.context.registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedStagedNamedEntryBounds.native_prefix
    (functions := functions) (registry := completion.result.context.registry) owner caller header capture sameLayouts member represented heaps completed
  let receipt := CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.parameter_receipt functions owner caller header capture packet stable heapTyped argumentsTyped
  have source := receipt.source wellFormed
  obtain ⟨sidecar, _issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt prepared aligned stagePrepared descriptor
  have selected : (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function
      (RecursiveStageRegistry.scope sidecar [] header.function) := by
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected
  have admitted : Admission poolBridge header.context packet.reached :=
    ⟨source.heapTyped, receipt.rows⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, result,
    finalHeaps, bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    CallableIndexedOwnedPreparedStagedFiniteNamedBodyBounds.reflects_body
      (bridge := poolBridge) (selected := selected) (wellFormed := wellFormed)
      (prepared := prepared) (aligned := aligned) (functions := functions)
      (diagnostic := diagnostic) (receiver := receiver) (terminal := terminal)
      (ordinary := ordinary) (syntaxTree := syntaxTree) (sameLedger := sameLedger)
      (runtimeLedger := runtimeLedger)
      (runtime := by simpa only [(RecursiveNamedPreparedStageScopes.registry stagePrepared).source selected] using runtime)
      (covers := covers selected)
      (environments := packet.entry.environments) (heaps := packet.entry.heaps)
      (locals := packet.entry.locals) (agrees := packet.entry.lookups) (typed := packet.entry.actualTyped)
      (initial := packet.reached) (admitted := admitted)
      budget packet.completed (Nat.le_of_lt (Nat.lt_of_lt_of_le packet.strict within))
  have applied := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.applies
    (caller := invocation) (context := context) sourceAt stagePrepared selected
    header.extended packet.entry.allocation trace matched
  have maps := packet.entry.maps.trans bodyMaps
  have worlds := packet.entry.worlds.trans bodyWorlds
  have frame := packet.entry.frame.trans bodyFrame
  have metadata := packet.entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := packet.related.trans bodyRelated
  have physical : (caller.rows owner.position).authority.frameLocation = keys[owner.position.val].frameLocation :=
    (caller.rows owner.position).frame_eq
  obtain ⟨restoredHeaps, restoredFrame, _cell, _fromBody, restoredRelated, _records, _transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical] using frame) related
  have restoredPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  have storeEq : finalStore = (CallableIndexedOwnedBodyRestoration.finalIndex (body :=
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        finalMap, finalWorld, after, packet.bodyStore, packet.entry.canonical⟩) caller owner.position).store := by
    simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical] using packet.restored
  have whole := completed.sound
  rw [storeEq] at whole
  refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome, after, finalMap, finalWorld, applied, ?_⟩
  rw [storeEq]
  exact ⟨whole, result, restoredHeaps, maps, worlds, restoredFrame, metadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position, restoredRelated, restoredPost⟩

include functions owner caller header capture sourceAt terminal prepared aligned diagnostic receiver ordinary syntaxTree sameLedger runtimeLedger runtime stagePrepared descriptor in
/-- The actual complete native apply supplies a strict body invocation grade.
Its original Header and authenticated staged scope then construct the Source
application, with the exact full postcondition in the returned caller pool. -/
theorem application_reflects
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions mapping world before store)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (identity descriptorWord : Word) (budget : Nat)
    (covers : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      child.evidence.Covers header.context)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [carrier (owner := owner) header capture identity descriptorWord, DataPatternValues.packValues payloads]
      store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      Evaluates [carrier (owner := owner) header capture identity descriptorWord, DataPatternValues.packValues payloads]
        store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨bodySize, smaller, invoked⟩ := completed.apply_body
    (.second (.first (.var rfl))) (.var rfl)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    reflects_invocation (prepared := prepared) (aligned := aligned)
      (diagnostic := diagnostic) (receiver := receiver) (ordinary := ordinary) (syntaxTree := syntaxTree)
      (sameLedger := sameLedger) (runtimeLedger := runtimeLedger) (runtime := runtime)
      functions owner caller header capture sourceAt terminal stagePrepared descriptor
      sameLayouts member wellFormed stable heapTyped argumentsTyped represented heaps supports budget covers
      invoked (Nat.le_trans (Nat.le_of_lt smaller) within)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, completed.sound, result⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedParentBounds
/-! The actual named Header, original selected caller row and raw successful
argument trace feed the literal terminal application. Its returned pool is
restored around the original caller. The Source and native grades remain
independent, and nested stage failures retain their original scope and call.
The finite named invocation producer constructs the terminal body internally.
Authentic Header, diagnostic, receiver and finite compiler/runtime inputs remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {stages : Staging.Recursive.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
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
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {mapping argumentMap : LocationMap} {world argumentWorld : StoreTyping}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, argumentMap, argumentWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    argumentMap argumentWorld argumentsHeap argumentsStore)
  (maps : LocationMap.Extends mapping argumentMap) (worlds : WorldExtends world argumentWorld)
  (frame : AdministrativePreserved mapping store argumentMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)
  {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution} {function : Dynamic.GlobalFunction}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.global function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  (callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (count : dispatch.row.entry.parameterCount = ids.length)
  (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids (.global function))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
  (calleeHeapTyped : Dynamic.HeapWellTyped context calleeHeap)
  (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result))
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    argumentMap argumentWorld sourceTypes (compiler.codes.map (·.type)) sources values)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header argumentMap argumentWorld)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  (sourceAt : NamedSourceAt header rawD function)
  (identity descriptorWord : Word)
  (carrierEq : carrier = CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds.carrier
    (owner := owner) header capture identity descriptorWord)
  (nativeType : compiler.calleeCode.type =
    CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
  (sameLayouts : header.layouts = compiled.indexed.layouts)
  (member : header ∈ headers)
  {expression : ExpressionId}
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {row : SourceSpecialization.SpecializedFunction}
  (namedPrepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt namedPrepared instantiation header)
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt namedPrepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (ordinary : CompatibleExpressionProducts.Ordinary header.function.source
    compiled.indexed.base.locals (CallableIndexedNamedGeneration.context compiled.indexed namedPrepared.named).owner)
  (syntaxTree : CompatibleExpressionProducts.Syntax header.function.source expression)
  (sameLedger : header.context.solvedRequirements = header.solved)
  (runtimeLedger : RuntimeRequirementLedgerValid header.context)
  (headerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context header.function.source)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
  calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt nativeType in
private theorem arguments_at {argumentsSize : Nat}
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap) :
    CallableIndexedParameterMeaning.Arguments model argumentMap argumentWorld header.bindings sources values ∧
    Dynamic.HeapWellTyped header.function.context argumentsHeap ∧
    Dynamic.ValuesHaveTypes header.function.context argumentsHeap sources header.types ∧
    Dynamic.TypeContextSupports header.context context ∧
    compiler.original.type = header.function.resultType ∧ lowered.type = header.output := by
  have secondAccepted : CallableContract.decision prepared.site.gates .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none := by
    rw [prepared.site.decision_known .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract dispatch.row dispatch.found]
    exact SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication
      (dispatch.row.afterArguments_ok (count.trans selected.argument_count.symm))
  obtain ⟨parameters, physicalArity, rawResult⟩ :=
    CallableIndexedOwnedPreparedStagedNamedArgumentRows.accepted_rows sourceAt compiler wellFormed
      actualFunctionType callerPrepared dispatch selected secondAccepted calleeTyped nativeType represented bundle
  obtain ⟨headerHeap, headerArguments, supports⟩ :=
    CallableIndexedOwnedPreparedStagedNamedArgumentRows.at_successful_arguments sourceAt wellFormed
      runtime covers locals calleeHeapTyped typing calleeTyped bundle physicalArity argumentsTrace
  have callable := compiler.callableType
  rw [actualFunctionType] at callable
  have nativeSignature := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters (callable.trans nativeType)
  have sameCore : lowered.type = header.output :=
    (congrArg (fun output => output.type) compiler.output).trans
      (compiler.resultTypeEq.symm.trans (nativeSignature.2.trans header.resultType))
  exact ⟨parameters, headerHeap, headerArguments, supports, originalResult.trans rawResult, sameCore⟩

include bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture in
private theorem restored_result {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (sameSource : compiler.original.type = header.function.resultType)
    (sameCore : lowered.type = header.output)
    (resultAt : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
      (registry := completion.result.context.registry) (payloads := values) functions owner (bridge.pool reached) header capture
      context outcome after value finalStore finalMap finalWorld faults) :
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
      finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial returned ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome returned := by
  obtain ⟨_invoked, resultRep, finalHeaps, applicationMaps, applicationWorlds, applicationFrame,
    applicationMetadata, ownedReturned, ownedRelated, ownedPost⟩ := resultAt
  obtain ⟨returned, samePool, callerRelated⟩ := bridge.restore reached ownedReturned
    applicationMaps applicationWorlds applicationFrame applicationMetadata ownedRelated
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    cases outcome with
    | value sourceValue =>
      change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
      exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
        exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
      | stage failedScope failedCall reason =>
        change StableRows (bridge.pool returned)
        rw [samePool]
        exact ownedPost
  exact ⟨parentRep, finalHeaps, maps.trans applicationMaps, worlds.trans applicationWorlds,
    frame.trans applicationFrame, heapMetadata.trans applicationMetadata,
    returned, callerProtocol.trans related callerRelated, parentPost⟩

include bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers locals calleeHeapTyped
  typing calleeTyped actualFunctionType represented bundle originalResult owner header capture sourceAt
  identity descriptorWord carrierEq nativeType sameLayouts member terminal namedPrepared aligned diagnostic receiver ordinary syntaxTree sameLedger runtimeLedger headerRuntime in
/-- The original Source global application supplies allocation and its selected
terminal body once. The native suffix and all three original binds then join
the real callee and ordered argument effects into the whole caller result. -/
theorem preserves_parent (budget : Nat)
    (headerCovers : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      child.evidence.Covers header.context)
    {calleeSize argumentsSize applicationSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap (.global function) sources outcome after)
    (within : applicationSize ≤ budget)
    {calleeStore : Store}
    (calleeNative : Evaluates actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore)
    (firstGate : Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore)
    (argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
      invocation context environment before id outcome after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
      calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt
      nativeType argumentsTrace
  obtain ⟨value, finalStore, finalMap, finalWorld, application, resultAt⟩ :=
    CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds.application_preserves
      (prepared := namedPrepared) (aligned := aligned) (diagnostic := diagnostic) (receiver := receiver)
      (ordinary := ordinary) (syntaxTree := syntaxTree) (sameLedger := sameLedger)
      (runtimeLedger := runtimeLedger) (runtime := headerRuntime)
      functions owner (bridge.pool reached) header capture sourceAt terminal sameLayouts member wellFormed
      admitted.rows headerHeap headerArguments parameters heaps supports identity descriptorWord budget headerCovers called within
  change Evaluates [CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds.carrier
    (owner := owner) header capture identity descriptorWord, DataPatternValues.packValues values]
    argumentsStore CallableIndexedLambdaCalls.applyPayload value finalStore at application
  rw [← carrierEq] at application
  have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
    (actual := actual) (result := compiler.resultType)
    (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
    dispatch.shape selected dispatch.found count application
  have whole : Evaluates actual store
      (CallableContract.call prepared.site.gates
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
        (compiler.calleeCode.expression.rename ξ)
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore := by
    apply LanguageResult.bind_success compiler.resultType calleeNative
    apply LanguageResult.bind_success compiler.resultType firstGate
    apply LanguageResult.bind_success compiler.resultType
    · simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
    · exact suffix
  rw [← prepared.lowered_rename compiler ξ] at whole
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture
      sameSource sameCore resultAt
  exact ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    value, finalStore, finalMap, finalWorld, whole, parentRep, finalHeaps, finalMaps, finalWorlds,
    finalFrame, finalMetadata, returned, relatedFinal, post⟩

variable  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named header.named.signature.key))
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)

include bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers locals calleeHeapTyped
  typing calleeTyped actualFunctionType represented bundle originalResult owner header capture sourceAt
  identity descriptorWord carrierEq nativeType sameLayouts member terminal namedPrepared aligned diagnostic receiver ordinary syntaxTree sameLedger runtimeLedger headerRuntime
  stagePrepared descriptor stageEq in
/-- The real accepted suffix gives a strict measured application. Original
named registry authority then constructs the actual Source application, and
the returned pool supplies the full original parent's caller postcondition. -/
theorem reflects_suffix (budget : Nat)
    (headerCovers : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      child.evidence.Covers header.context)
    {calleeSize argumentsSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {suffixSize : Nat} {value : Value} {finalStore : Store}
    (suffix : EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : suffixSize ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
      calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt
      nativeType argumentsTrace
  obtain ⟨applicationSize, strict, application⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix dispatch.shape
      selected dispatch.found count suffix within
  rw [carrierEq] at application
  obtain ⟨applicationSourceSize, outcome, after, finalMap, finalWorld, applied, _wholeApplication, resultAt⟩ :=
    CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds.application_reflects
      (prepared := namedPrepared) (aligned := aligned) (diagnostic := diagnostic) (receiver := receiver)
      (ordinary := ordinary) (syntaxTree := syntaxTree) (sameLedger := sameLedger)
      (runtimeLedger := runtimeLedger) (runtime := headerRuntime)
      functions owner (bridge.pool reached) header capture sourceAt terminal stagePrepared descriptor
      sameLayouts member wellFormed admitted.rows headerHeap headerArguments
      parameters heaps supports identity descriptorWord budget headerCovers application (Nat.le_of_lt strict)
  have called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSourceSize
      invocation context argumentsHeap (.global function) sources outcome after := by
    simpa only [stageEq] using applied
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture
      sameSource sameCore resultAt
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSourceSize], outcome, after,
    finalMap, finalWorld,
    .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedParentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch
/-! A positive global payload retains its actual Header, Source instantiation,
dictionary and native captured code. The selected physical count is decided
at the real argument endpoint before this Header's terminal parent producer.
Finite per-Header compiler coverage constructs child execution internally.
Actual selected-scope evidence coverage remains an explicit runtime premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserDispatch (GlobalApplicationPrefix)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserPreservationDispatch (GlobalAppliedPrefix)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (ParentResult)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Each field describes this actual Header's compiler or original prepared
record. No completion, body law or desired application result is stored. -/
structure Terminal (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  row : SourceSpecialization.SpecializedFunction
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row
  instantiation : DeclarationInstantiation
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header
  layouts : header.layouts = compiled.indexed.layouts
  expression : ExpressionId
  receipt : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body
  diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared
  ordinary : CompatibleExpressionProducts.Ordinary header.function.source
    compiled.indexed.base.locals (CallableIndexedNamedGeneration.context compiled.indexed prepared.named).owner
  syntaxTree : CompatibleExpressionProducts.Syntax header.function.source expression
  sameLedger : header.context.solvedRequirements = header.solved
  runtimeLedger : RuntimeRequirementLedgerValid header.context
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    header.context header.function.source

variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
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
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry preparedStages)
  (callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = source)
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (calleeFound : source.lookupExpression? callee = some calleeNode)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bridge profile compiler prepared initial sourceParent occurrence preparedStages stageEq callerPrepared receiver
  wellFormed runtime covers locals sourceEq tree unique parentTyped calleeFound actualFunctionType in
/-- The actual global prefix exposes its original Header before any execution
law is used. Physical mismatch returns the original arity parent; equal count
runs the retained named terminal producer at the real reached argument state. -/
theorem reflects_global
    (terminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
    {budget size : Nat} {value : Value} {finalStore : Store}
    (bodyCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry preparedStages).Closure header.function child →
      child.evidence.Covers header.context)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (global : GlobalApplicationPrefix (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
      originalTree originalUnique originalTyping calleeFound
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  obtain ⟨function, rawParameter, rawResult, functionType, bundle, originalResult,
    calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    calleePost, calleeTyped, calleeTrace, accepted, argumentsTrace, represented, calleeRelated,
    _callView, boundary, heaps, maps, worlds, frame, heapMetadata, ⟨reached, related, admitted⟩,
    suffixSize, suffix, strict⟩ := global
  have origin : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry
      completion.result.context.registry semanticFaults profile finalMap finalWorld
      calleeNode.type (.global function) carrier compiler.calleeCode.type := by
    exact calleeRelated
  obtain ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt, _installed,
    _number, _projection, _nativeTyped, _runtimeType, nativeEq, nativeType⟩ :=
    CallableIndexedOwnedPreparedStagedNamedPayloadReceipts.named_payload profile origin function rfl
  have carrierEq : carrier = CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds.carrier
      (owner := owner) header capture identity descriptor.id := nativeEq
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · obtain ⟨terminal⟩ := terminals header member
      obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
        _calleeFrame, calleeMetadata, _calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
      have calleeHeapTyped := calleeAdmission.at_value.2.heap
      have rawCallee : Dynamic.ValueHasType context calleeHeap (.global function)
          (.function rawParameter rawResult) := by
        simpa only [functionType] using calleeTyped
      obtain ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, resultRep, returnedHeaps,
        returnedMaps, returnedWorlds, returnedFrame, returnedMetadata, returned, returnedRelated, returnedPost⟩ :=
        CallableIndexedOwnedPreparedStagedFiniteNamedParentBounds.reflects_suffix
          (namedPrepared := terminal.prepared) (aligned := terminal.aligned)
          (diagnostic := terminal.diagnostic) (receiver := receiver)
          (ordinary := terminal.ordinary) (syntaxTree := terminal.syntaxTree)
          (sameLedger := terminal.sameLedger) (runtimeLedger := terminal.runtimeLedger)
          (headerRuntime := terminal.runtime)
          bridge profile compiler prepared sourceParent occurrence initial reached related admitted
          heaps maps worlds frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers
          (locals.mono calleeMetadata) calleeHeapTyped typing rawCallee actualFunctionType represented bundle originalResult
          owner header capture sourceAt identity descriptor.id carrierEq nativeType terminal.layouts member
          terminal.receipt preparedStages descriptor stageEq budget (bodyCovers header member) calleeTrace argumentsTrace suffix (Nat.le_of_lt strict)
      exact ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, completed.sound,
        resultRep, returnedHeaps, returnedMaps, returnedWorlds, returnedFrame, returnedMetadata,
        returned, returnedRelated, returnedPost⟩
    · have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
        sourceAt callerPrepared dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have mismatch : header.function.parameters.length ≠ sources.length := by
        intro same
        exact count (physical.trans (same.trans valuesCount))
      have applied := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.arity_failure
        (actual := preparedStages) (caller := invocation) (context := context) (heap := argumentsHeap) sourceAt mismatch
      have called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
          (Staging.Recursive.Size.stepSize []) invocation context argumentsHeap (.global function) sources
          (.fault (.semantic (.argumentArityMismatch header.function.parameters.length sources.length))) argumentsHeap := by
        simpa only [stageEq] using applied
      have failedSource := Staging.Recursive.Size.Expression.applied occurrence compiler.argumentCoercions
        calleeTrace accepted argumentsTrace sourceParent.arity called
      have lowerType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      obtain ⟨sameValue, sameStore⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
          dispatch.shape selected dispatch.found count suffix
      cases sameStore
      obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
        CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
          compiler prepared preparedStages selected receiver initial functions reached related heaps
          (sourceResult := compiler.original.type) (resultCore := lowered.type) count
      cases sameState
      refine ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .fault (.semantic (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)),
        argumentsHeap, finalMap, finalWorld, ?_, completed.sound, ?_, keptHeaps, maps, worlds, frame,
        heapMetadata, reached, keptRelated, ?_⟩
      · simpa only [physical, valuesCount] using failedSource
      · have exactValue : value = .inLeft lowered.type
            (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
              .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))) := by
          simpa only [lowerType] using sameValue
        rw [exactValue]
        exact CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
      · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
        exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩

include bridge profile compiler prepared initial sourceParent occurrence preparedStages callerPrepared receiver
  wellFormed runtime covers locals sourceEq tree unique parentTyped calleeFound actualFunctionType in
/-- The genuine global Source suffix retains its original allocation and body
scope. The actual Header and physical row select terminal execution or arity
failure, and both branches preserve every reached caller effect. -/
theorem preserves_global
    (terminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
    (guardFrame : invocation.guards = CallableLedger.frame sidecar)
    (budget : Nat)
    (bodyCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
      stages.Closure header.function child → child.evidence.Covers header.context)
    {calleeSize argumentsSize applicationSize : Nat}
    {sourceValue : Dynamic.Value} {calleeHeap argumentsHeap : Dynamic.Heap}
    {sources : List Dynamic.Value} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (global : GlobalAppliedPrefix (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial
      calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap sources outcome after)
    (within : applicationSize ≤ budget) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize]) outcome after := by
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
      originalTree originalUnique originalTyping calleeFound
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  obtain ⟨function, selectedFunction, calleeTrace, accepted, argumentsTrace, called, prefixResult⟩ := global
  cases selectedFunction
  obtain ⟨rawParameter, rawResult, functionType, bundle, originalResult,
    calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
    originalNode, originalMetadata, calleePost, calleeTyped, firstGate, argumentsNative,
    represented, calleeRelated, _callView, boundary, heaps, maps, worlds,
    frame, heapMetadata, reached, related, admitted⟩ := prefixResult
  have origin : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry
      completion.result.context.registry semanticFaults profile finalMap finalWorld
      calleeNode.type (.global function) carrier compiler.calleeCode.type := by
    exact calleeRelated
  obtain ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt, _installed,
    _number, _projection, _nativeTyped, _runtimeType, nativeEq, nativeType⟩ :=
    CallableIndexedOwnedPreparedStagedNamedPayloadReceipts.named_payload profile origin function rfl
  have carrierEq : carrier = CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds.carrier
      (owner := owner) header capture identity descriptor.id := nativeEq
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · obtain ⟨terminal⟩ := terminals header member
      have calleeNative := calleePost.1
      obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
        _calleeFrame, calleeMetadata, _calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
      have calleeHeapTyped := calleeAdmission.at_value.2.heap
      have rawCallee : Dynamic.ValueHasType context calleeHeap (.global function)
          (.function rawParameter rawResult) := by
        simpa only [functionType] using calleeTyped
      exact CallableIndexedOwnedPreparedStagedFiniteNamedParentBounds.preserves_parent
          (namedPrepared := terminal.prepared) (aligned := terminal.aligned)
          (diagnostic := terminal.diagnostic) (receiver := receiver)
          (ordinary := terminal.ordinary) (syntaxTree := terminal.syntaxTree)
          (sameLedger := terminal.sameLedger) (runtimeLedger := terminal.runtimeLedger)
          (headerRuntime := terminal.runtime)
        bridge profile compiler prepared sourceParent occurrence initial reached related admitted
        heaps maps worlds frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers
        (locals.mono calleeMetadata) calleeHeapTyped typing rawCallee actualFunctionType represented bundle originalResult
        owner header capture sourceAt identity descriptor.id carrierEq nativeType terminal.layouts member
        terminal.receipt budget (bodyCovers header member)
        calleeTrace argumentsTrace called within calleeNative firstGate argumentsNative
    · have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
        sourceAt callerPrepared dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have different : header.function.parameters.length ≠ ids.length := by
        simpa only [physical] using count
      have bodyUnique : ∀ actualBody,
          Dynamic.FunctionInstantiates (Program.ofChecked compiled.sourceProgram) function.instantiation actualBody →
          RecursiveNamedCatalog.Header.sourceBody header = actualBody := by
        intro actualBody instantiated
        exact BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed sourceAt.frame.instantiated instantiated
      cases called with
      | global instantiated _covers _roots _selected _parameters allocate _body _converted =>
        have same := bodyUnique _ instantiated
        cases same
        have actualCount := (congrArg List.length sourceAt.frame.parameters).trans
          (allocate.length_eq.trans valuesCount)
        exact False.elim (different actualCount)
      | globalArity instantiated mismatch =>
        have same := bodyUnique _ instantiated
        cases same
        have actualAccepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar)
            prepared.site.call ids (.global function) := by
          simpa only [guardFrame, prepared.call] using accepted
        have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
            (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
            (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
          simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix]
            using argumentsNative
        have native := CallableIndexedOwnedPreparedSecondCallGateRejection.user_native_preserves
          (result := compiler.resultType) dispatch selected actualAccepted count
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown calleePost.1 argumentsWeaken
        change Evaluates actual store
          (CallableContract.call prepared.site.gates
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
            (compiler.calleeCode.expression.rename ξ)
            ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at native
        rw [← prepared.lowered_rename compiler ξ] at native
        obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
          CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
            compiler prepared preparedStages selected receiver initial functions reached related heaps
            (sourceResult := compiler.original.type) (resultCore := lowered.type) count
        cases sameState
        have loweredType : lowered.type = compiler.resultType :=
          (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
        have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
        have post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
            compiler.original.type
            (.fault (.semantic (.argumentArityMismatch
              (RecursiveNamedCatalog.Header.sourceBody header).source.inputs.length sources.length))) reached :=
          ⟨admitted.rows, by intro value impossible; cases impossible⟩
        refine ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity
          (.globalArity instantiated mismatch),
          .inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
            .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))),
          argumentsStore, finalMap, finalWorld, ?_, ?_, keptHeaps, maps, worlds, frame, heapMetadata,
          reached, keptRelated, post⟩
        · simpa only [loweredType] using native
        · simpa only [physical, sourceAt.frame.parameters, valuesCount] using faultRep

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteIndirectCallBounds
/-! Whole terminal indirect calls construct both directions of the original
parent meaning. Existing failure, builtin and closure producers retain their
actual traces; the authentic named producer consumes the global branch once.
Finite named and closure body meanings are constructed internally. Actual static
closure packets, named body Covers, registry/diagnostic authority and strict
caller callee/argument child meaning remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteIndirectCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds (FiniteFor)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (ParentResult)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch (Terminal)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {certificate : GenericExpressionMeaning.Certificate}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations extension semantic in
/-- One original native completion gives full staged Source parent meaning,
including the actual named global branch and restored caller post. -/
theorem reflects_parent
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      Nonempty (FiniteFor (registry := completion.result.context.registry) (stages := stages) association))
    (namedTerminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
    (namedCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      child.evidence.Covers header.context)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  rcases CallableIndexedOwnedPreparedStagedIndirectFiniteClosureReflectionDispatch.reflects_parent_or_global
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations
      extension semantic budget children closurePackets completed within with parent | global
  · exact parent
  · exact CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch.reflects_global
      bridge profile compiler prepared initial sourceParent occurrence stagePrepared stageEq caller receiver
      wellFormed runtime covers locals sourceEq tree unique parentTyped found actualFunctionType
      namedTerminals namedCovers completed global

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations extension semantic in
/-- One original staged Source parent constructs its native completion and
full caller post. The authentic named branch constructs its finite application
meaning internally; Source and native grades remain independent. -/
theorem preserves_parent (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate callFaults budget)
    (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      Nonempty (FiniteFor (registry := completion.result.context.registry) (stages := stages) association))
    (namedTerminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
    (namedCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
      stages.Closure header.function child → child.evidence.Covers header.context)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial size outcome after := by
  rcases CallableIndexedOwnedPreparedStagedIndirectFiniteClosurePreservationDispatch.preserves_parent_or_global
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations
      extension semantic budget children closurePackets trace within with parent | global
  · exact parent
  · obtain ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap, argumentsHeap,
      sources, sizeEq, strict, globalPrefix⟩ := global
    cases sizeEq
    exact CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch.preserves_global
      bridge profile compiler prepared initial sourceParent occurrence stagePrepared caller receiver
      wellFormed runtime covers locals sourceEq tree unique parentTyped found actualFunctionType
      namedTerminals guardFrame budget namedCovers globalPrefix (Nat.le_of_lt strict)

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteIndirectCallBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteCallHeadBounds
/-! Static call authority and admitted expression head ports. The actual
compiler receipt supplies the same callee and ordered argument vector. Source
typing is recovered from the original parent before applying the existing
whole-call proof. A recursive caller fold supplies the strict child laws; no
runtime state or completed execution is a field of the static Port. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteCallHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared SourceParent)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds (FiniteFor)
open CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

/-- Actual accepted compiler and sidecar authority. Every field is static.
The callee's raw typing is derived from the supplied original parent typing. -/
structure Port (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation
    source scope id callee ids metadata reasonAt lowered) where
  prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable
  sidecar : SourceCoreStageContracts.Sidecar
  caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar
  view : SourceView sidecar.source source
  guardFrame : invocation.guards = CallableLedger.frame sidecar
  originalUnique : NodeOccurrencesUnique sidecar.source
  sourceParent : SourceParent compiler
  calleeNode : ExpressionNode
  calleeFound : source.lookupExpression? callee = some calleeNode

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    Nonempty (FiniteFor (registry := completion.result.context.registry) (stages := stages) association))
  (namedTerminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
  (namedCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
    stages.Closure header.function child → child.evidence.Covers header.context)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include bridge receiver stagePrepared sourceEq profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers in
/-- Reuse the original whole-call producer at the supplied genuine Source
grade. The returned caller state and post are retained literally. -/
theorem preserves
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    {certificate : GenericExpressionMeaning.Certificate}
    (calleeCertified : certificate scope callee compiler.calleeCode)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (children : PreservesBelow bridge context model stages invocation certificate callFaults size) :
    PreservesAt bridge context model stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  exact (CallableIndexedOwnedPreparedStagedFiniteIndirectCallBounds.preserves_parent
    bridge receiver compiler port.prepared stagePrepared rfl occurrence initial port.view port.guardFrame
    profile calleeCertified port.calleeFound sourceTyped environments heaps locals agrees actualTyped
    admitted port.caller port.originalUnique port.sourceParent tree unique parentTyped
    wellFormed runtime covers actualFunctionType observations extension semantic
    size children closurePackets namedTerminals namedCovers trace (Nat.le_refl _)).2

include bridge receiver stagePrepared sourceEq profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers in
/-- The native completion keeps its independent Source grade and exact
staged fault scope. Only the duplicate native evaluation witness is omitted. -/
theorem reflects
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    {certificate : GenericExpressionMeaning.Certificate}
    (calleeCertified : certificate scope callee compiler.calleeCode)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (children : ReflectsBelow bridge context model stages invocation certificate callFaults size) :
    ReflectsAt bridge context model stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  have actualNamedCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
        child.evidence.Covers header.context := by
    simpa only [stageEq] using namedCovers
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated,
    represented, finalHeaps, maps, worlds, frame, metadataExtended, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedFiniteIndirectCallBounds.reflects_parent
      bridge receiver compiler port.prepared stagePrepared rfl occurrence initial port.view port.guardFrame
      profile calleeCertified port.calleeFound sourceTyped environments heaps locals agrees actualTyped
      admitted port.caller port.originalUnique port.sourceParent tree unique parentTyped
      wellFormed runtime covers actualFunctionType observations extension semantic
      stageEq size children closurePackets namedTerminals actualNamedCovers completed (Nat.le_refl _)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadataExtended, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteCallHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedIndirectCallBounds
/-! Whole terminal indirect calls construct both directions of the original
parent meaning. Existing failure, builtin and closure producers retain their
actual traces; the authentic named producer consumes the global branch once.
Finite named body meaning is constructed internally. Static terminal coverage,
actual named body Covers and strict caller/closure child meaning remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedIndirectCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor ReflectsBelowFor)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (ParentResult)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation (PreservesBelowFor)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch (Terminal)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {certificate : GenericExpressionMeaning.Certificate}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations in
/-- One original native completion gives full staged Source parent meaning,
including the actual named global branch and restored caller post. -/
theorem reflects_parent
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), Nonempty (TerminalFor association stages))
    (closureChildren : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore) (terminal : TerminalFor association stages),
      ReflectsBelowFor (registry := completion.result.context.registry) (faults := callFaults)
        association terminal functions budget)
    (namedTerminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
    (namedCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      child.evidence.Covers header.context)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  rcases CallableIndexedOwnedPreparedStagedIndirectTerminalReflectionDispatch.reflects_parent_or_global
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations
      budget children closureTerminals closureChildren completed within with parent | global
  · exact parent
  · exact CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch.reflects_global
      bridge profile compiler prepared initial sourceParent occurrence stagePrepared stageEq caller receiver
      wellFormed runtime covers locals sourceEq tree unique parentTyped found actualFunctionType
      namedTerminals namedCovers completed global

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations in
/-- One original staged Source parent constructs its native completion and
full caller post. The authentic named branch constructs its finite application
meaning internally; Source and native grades remain independent. -/
theorem preserves_parent (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate callFaults budget)
    (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), Nonempty (TerminalFor association stages))
    (closureChildren : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore) (terminal : TerminalFor association stages),
      PreservesBelowFor (registry := completion.result.context.registry) (faults := callFaults)
        association terminal functions budget)
    (namedTerminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
    (namedCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
      stages.Closure header.function child → child.evidence.Covers header.context)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial size outcome after := by
  rcases CallableIndexedOwnedPreparedStagedIndirectTerminalPreservationDispatch.preserves_parent_or_global
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations
      budget children closureTerminals closureChildren trace within with parent | global
  · exact parent
  · obtain ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap, argumentsHeap,
      sources, sizeEq, strict, globalPrefix⟩ := global
    cases sizeEq
    exact CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch.preserves_global
      bridge profile compiler prepared initial sourceParent occurrence stagePrepared caller receiver
      wellFormed runtime covers locals sourceEq tree unique parentTyped found actualFunctionType
      namedTerminals guardFrame budget namedCovers globalPrefix (Nat.le_of_lt strict)

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedIndirectCallBounds
end
