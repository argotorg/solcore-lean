import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol

/-! Real anonymous parameter entries retain complete captures, code, Source
frames and their own reached ordered pool. Genuine raw Source arguments and
actual hook/parameter effects supply admission before the strict shared child.
Authentic captured slots, prefix and full Source seed add a nested packet to
the same real pool; no slots are inferred from base ownership. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
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
  (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) (program := program) principal)
  (sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named)

/-- The genuine nested packet carries full globals, bundle and Source seed;
its bridge projects and restores exactly the same actual pool. -/
def bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True)
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots (CallableIndexedOwnedNestedCallerProtocol.carrier owner principal)

include beforeTyped argumentsTyped stable observed prefixContext sourceSeed in
/-- Source admission and stable histories belong to the actual Source prefix
post, whose full captured canonical spine and nextHistory remain original. -/
def source_admitted_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner principal)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin) (functions := functions) := by
  let base := CallableIndexedOwnedLambdaReadyContinuations.source_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached
  exact ⟨CallableIndexedOwnedLambdaNestedEntries.source_entry captured code history inputs functions owner principal
    observed prefixContext sourceSeed caller body entry added length spine reached, base.source, base.rows⟩

include beforeTyped argumentsTyped stable observed prefixContext sourceSeed in
/-- The measured native prefix exposes the same actual Source allocation and
raw local agreement independently of the native body size. -/
def native_admitted_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner principal)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin) (functions := functions) := by
  let base := CallableIndexedOwnedLambdaReadyContinuations.native_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable entry reached
  exact ⟨CallableIndexedOwnedLambdaNestedEntries.native_entry captured code history inputs functions owner principal
    observed prefixContext sourceSeed caller body entry reached, base.source, base.rows⟩

/-- Source packaging preserves the entire original entry definitionally. -/
theorem source_original
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry added length spine reached).original =
      CallableIndexedOwnedLambdaNestedEntries.source_entry captured code history inputs functions owner principal
        observed prefixContext sourceSeed caller body entry added length spine reached := rfl

/-- Native packaging retains the actual Prefix entry and initial pool. -/
theorem native_original
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry reached).original =
      CallableIndexedOwnedLambdaNestedEntries.native_entry captured code history inputs functions owner principal
        observed prefixContext sourceSeed caller body entry reached := rfl

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
      (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
      (spine : entry.entry.canonical = added ++ captured.canonical)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩),
      { i : ι // origins i = source_origin body.origin
        (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry added length spine reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (readiness (bridge (headers := headers) owner principal)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i) child)) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length spine reached
  let selected := selection entry added length spine reached
  intro child strict outcome after trace
  have ready := below child strict selected.val
  rw [selected.property] at ready
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at (bridge (headers := headers) owner principal)
      (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry added length spine reached).source.runtime
      wellFormed syntaxTree ready
      (source_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry added length spine reached) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

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
        (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (readiness (bridge (headers := headers) owner principal)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i) child)) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached
  let selected := selection entry reached
  intro child strict value finalStore completed
  have ready := below child strict selected.val
  rw [selected.property] at ready
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at (bridge (headers := headers) owner principal)
      (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry reached).source.runtime
      wellFormed syntaxTree ready
      (native_admitted_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry reached) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedReadyContinuations
