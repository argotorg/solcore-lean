import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedParameterReadyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds

/-! Real anonymous parameter entries retain complete captures, code, Source
frames and their own reached ordered pool. Genuine raw Source arguments and
actual hook/parameter effects supply admission before the strict shared child.
No arbitrary closure representation or completed body family is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) code inputs registry faults)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include beforeTyped argumentsTyped stable in
/-- Source admission and stable histories belong to the actual Source prefix
post, whose full captured canonical spine and nextHistory remain original. -/
def source_admitted_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) (keys := keys))
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin) (functions := functions) := by
  let original := CallableIndexedOwnedLambdaInvocationBounds.source_entry
    captured code history inputs functions owner caller body entry reached
  have source : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program body.origin.function
      body.origin.context original.environment original.heap := by
    change CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program body.origin.function
      body.origin.context entry.entry.environment entry.entry.heap
    simpa only [body.function_eq, body.context_eq] using
      CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt.of_lambda captured code history inputs functions entry
        body.frame beforeTyped argumentsTyped
  exact CallableIndexedOwnedAdmittedBodyEntries.Entry.of_parameters
    (bridge (headers := headers) (keys := keys)) original source caller stable owner.position entry.nextHistory entry.entry.frame

include beforeTyped argumentsTyped stable in
/-- The measured native prefix exposes the same actual Source allocation and
raw local agreement independently of the native body size. -/
def native_admitted_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) (keys := keys))
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin) (functions := functions) := by
  let original := CallableIndexedOwnedLambdaInvocationBounds.native_entry
    captured code history inputs functions owner caller body entry reached
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended] using argumentsTyped
  have allocated := entry.allocation.preservesHeapTyping beforeTyped rawArguments
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures body.frame.code.closed (fields.targetClosed body.frame.code.closed)
      body.frame.code.variables_closed (fields.targetResidualVariablesOpen body.frame.code.residual_variables_open)
  have runtime := CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame inputs.extended
  have bodyTyped := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters body.frame inputs.extended
  have source : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program body.origin.function
      body.origin.context original.environment original.heap := by
    change CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program body.origin.function
      body.origin.context entry.environment entry.heap
    simpa only [body.function_eq, body.context_eq] using
      (show CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program function inputs.context entry.environment entry.heap from
        ⟨runtime.1, runtime.2, heapTyped, entry.locals, bodyTyped⟩)
  exact CallableIndexedOwnedAdmittedBodyEntries.Entry.of_parameters
    (bridge (headers := headers) (keys := keys)) original source caller stable owner.position entry.nextHistory entry.frame

/-- Source packaging preserves the entire original entry definitionally. -/
theorem source_original
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached).original =
      CallableIndexedOwnedLambdaInvocationBounds.source_entry captured code history inputs functions owner caller body entry reached := rfl

/-- Native packaging retains the actual Prefix entry and initial pool. -/
theorem native_original
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached).original =
      CallableIndexedOwnedLambdaInvocationBounds.native_entry captured code history inputs functions owner caller body entry reached := rfl

variable (wellFormed : ProgramWellFormed program)
  (syntaxTree : GenericImperativeMatch.Syntax body.origin.function.source body.origin.expressionSyntax
    body.origin.context (.statements true body.origin.function.body) body.origin.function.resultType)
  {ι : Type} (origins : ι → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)

include wellFormed syntaxTree in
/-- Each actual Source-produced parameter packet selects its authentic family
origin. The callback consumes only the same strict child supplied by Mutual. -/
theorem source_continuation (budget : Nat)
    (selection : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
      (added : Environment) (_length : added.length = code.receipt.loweredParameters.length)
      (_spine : entry.entry.canonical = added ++ captured.canonical)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩),
      { i : ι // origins i = source_origin body.origin
        (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.PreservesAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i) child)) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length spine reached
  let selected := selection entry added length spine reached
  exact CallableIndexedOwnedParameterReadyContinuations.source_at
    (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached)
    wellFormed syntaxTree origins selected.val selected.property budget below

include wellFormed syntaxTree in
/-- The authentic measured Prefix and its full captured spine select the
same compiler family origin; reflected Source grades remain independent. -/
theorem native_continuation (budget : Nat)
    (selection : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
      { i : ι // origins i = source_origin body.origin
        (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i) child)) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached
  let selected := selection entry reached
  exact CallableIndexedOwnedParameterReadyContinuations.native_at
    (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached)
    wellFormed syntaxTree origins selected.val selected.property budget below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyContinuations
