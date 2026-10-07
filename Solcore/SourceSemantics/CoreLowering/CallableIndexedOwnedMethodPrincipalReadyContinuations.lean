import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodReadyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodNestedEntries

/-! The genuine selected method keeps its complete trait dictionary and
synthetic Source frame. Actual hook and parameter receipts establish admission
at the same reached pool before the shared family's strict body child. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments profile.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)

/-- Genuine globals and the complete principal seed accompany the same pool. -/
def bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True)
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedOriginCanonicalState.carrier owner principal.named)

include wellFormed beforeTyped argumentsTyped stable observed in
/-- Authentic Source method selection and the actual hook/parameter allocation
supply this complete admitted entry without inventing a top-level Header. -/
def source_admitted_entry {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) principal owner)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := origin principal.cached.compilation profile escaped extend runtimeOf) (functions := functions) := by
  let base := CallableIndexedOwnedMethodReadyContinuations.source_admitted_entry principal profile functions escaped extend runtimeOf owner caller
    wellFormed beforeTyped argumentsTyped stable selected history entry reached
  exact ⟨CallableIndexedOwnedMethodNestedEntries.source_entry principal profile functions escaped extend runtimeOf
    installed owner observed selected history entry added length spine reached, base.source, base.rows⟩

/-- Native Prefix receipts retain their actual Source allocation, independent
body grade and the same carried hook at the exact reached pool. -/
def native_admitted_entry {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {prefixSize : Nat} {value : Value} {bodyStore : Store}
    (entry : CallablePreparedMethodRuntimeMeaning.Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body prefixSize value bodyStore)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) principal owner)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := origin principal.cached.compilation profile escaped extend runtimeOf) (functions := functions) := by
  let base := CallableIndexedOwnedMethodReadyContinuations.native_admitted_entry principal profile functions escaped extend runtimeOf owner caller
    wellFormed beforeTyped argumentsTyped stable selected history entry reached
  exact ⟨CallableIndexedOwnedMethodNestedEntries.native_entry principal profile functions escaped extend runtimeOf
    installed owner observed selected history entry added length spine reached, base.source, base.rows⟩

/-- The complete original method parameter entry and its pool are unchanged. -/
theorem source_original {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (source_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
      beforeTyped argumentsTyped stable observed selected history entry added length spine reached).original =
      CallableIndexedOwnedMethodNestedEntries.source_entry principal profile functions escaped extend runtimeOf
        installed owner observed selected history entry added length spine reached := rfl

/-- The complete original method parameter entry and its pool are unchanged. -/
theorem native_original {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {prefixSize : Nat} {value : Value} {bodyStore : Store}
    (entry : CallablePreparedMethodRuntimeMeaning.Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body prefixSize value bodyStore)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (native_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
      beforeTyped argumentsTyped stable observed selected history entry added length spine reached).original =
      CallableIndexedOwnedMethodNestedEntries.native_entry principal profile functions escaped extend runtimeOf
        installed owner observed selected history entry added length spine reached := rfl

variable (syntaxTree : GenericImperativeMatch.Syntax principal.sourceFunction.source expressionSyntax profile.context
    (.statements true principal.sourceFunction.body) principal.sourceFunction.resultType)
  {ι : Type} (origins : ι → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
/-- The full actual hook/parameter packet selects its exact shared-family
origin; the callback uses only the strictly smaller body IH. -/
theorem source_continuation (budget : Nat)
    (selection : ∀ (hook : Word) (index : Int) (metadata : MetadataState)
      (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
        (.named principal.named.signature.key) = some hook)
      (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (.state index) (.named hook) (some metadata))
      (_emitted : principal.cached.compilation.output = SourceCoreCallableIndexedFrames.withFrame
        (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
        principal.cached.compilation.parameterCode)
      {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
      (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
      (added : Environment) (length : added.length = principal.named.inputs.length)
      (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
      (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (_related : Relates caller reached),
      { i : ι // origins i = source_origin (origin principal.cached.compilation profile escaped extend runtimeOf)
        (source_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
          beforeTyped argumentsTyped stable observed selected history entry added length spine reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.PreservesAt (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
        (readiness (bridge (headers := headers) principal owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions (Program.ofChecked compiled.sourceProgram) (origins i) child)) :
    SourceContinuationWithHistory (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro hook index metadata selected history emitted entry added length spine reached related
  let selectedOrigin := selection hook index metadata selected history emitted entry added length spine reached related
  intro child strict outcome after trace
  have ready := below child strict selectedOrigin.val
  rw [selectedOrigin.property] at ready
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, actualRelated, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at (bridge (headers := headers) principal owner)
      (source_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
        beforeTyped argumentsTyped stable observed selected history entry added length spine reached).source.runtime
      wellFormed syntaxTree ready
      (source_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
        beforeTyped argumentsTyped stable observed selected history entry added length spine reached) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, actualRelated⟩

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
/-- The full actual hook/parameter packet selects its exact shared-family
origin; the callback uses only the strictly smaller body IH. -/
theorem native_continuation (budget : Nat)
    (selection : ∀ (hook : Word) (index : Int) (metadata : MetadataState)
      (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
        (.named principal.named.signature.key) = some hook)
      (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (.state index) (.named hook) (some metadata))
      {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
      {prefixSize : Nat} {value : Value} {bodyStore : Store}
      (entry : CallablePreparedMethodRuntimeMeaning.Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body prefixSize value bodyStore)
      (added : Environment) (length : added.length = principal.named.inputs.length)
      (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
      (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (_related : Relates caller reached),
      { i : ι // origins i = source_origin (origin principal.cached.compilation profile escaped extend runtimeOf)
        (native_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
          beforeTyped argumentsTyped stable observed selected history entry added length spine reached).source.runtime })
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.ReflectsAt (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
        (readiness (bridge (headers := headers) principal owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions (Program.ofChecked compiled.sourceProgram) (origins i) child)) :
    NativeContinuationWithHistory (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro hook index metadata _prefixSize _bodyStore selected history _prefixWithin _value _finalStore
    _restored entry added length spine reached related
  let selectedOrigin := selection hook index metadata selected history entry added length spine reached related
  intro child strict value finalStore completed
  have ready := below child strict selectedOrigin.val
  rw [selectedOrigin.property] at ready
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, actualRelated, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at (bridge (headers := headers) principal owner)
      (native_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
        beforeTyped argumentsTyped stable observed selected history entry added length spine reached).source.runtime
      wellFormed syntaxTree ready
      (native_admitted_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
        beforeTyped argumentsTyped stable observed selected history entry added length spine reached) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, actualRelated⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalReadyContinuations
