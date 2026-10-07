import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalReadyContinuations

/-! An authentic selected method and its complete Source profile construct a
principal-protocol family index at the actual parameter entry. The original
pointwise continuation consumes only that index's strict shared child. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodReadyFamilyReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The real trait selector, full compiler profile, dictionary and original
Syntax remain independent Source/static receipts. No Header is invented. -/
structure Index where
  method : ExecutableImplMethods.CheckedMethod
  principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  administrative : Core.Context
  expressionSyntax : ExpressionId → Prop
  certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate
  validity : SourceSemantics.Context → Prop
  diagnosticPolicy : AssignmentDiagnosticPolicy
  profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy
  escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason
  extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next
  runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary
  syntaxTree : GenericImperativeMatch.Syntax principal.sourceFunction.source expressionSyntax profile.context
    (.statements true principal.sourceFunction.body) principal.sourceFunction.resultType
  sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    (CallableIndexedOwnedMethodInvocationBounds.origin principal.cached.compilation profile escaped extend runtimeOf).context
    (CallableIndexedOwnedMethodInvocationBounds.origin principal.cached.compilation profile escaped extend runtimeOf).function.source

/-- The exact complete method origin retains its genuine Source domain. -/
def origin (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  source_origin (CallableIndexedOwnedMethodInvocationBounds.origin index.principal.cached.compilation
    index.profile index.escaped index.extend index.runtimeOf) index.sourceRuntime

/-- The genuine trait principal and physical owner select the stronger protocol. -/
def body_protocol (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) index.owner index.principal.named

/-- Every packet accompanies the complete same actual ordered pool. -/
def bridge (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedMethodPrincipalReadyContinuations.bridge (headers := headers) index.principal index.owner

variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context}
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

variable (syntaxTree : GenericImperativeMatch.Syntax principal.sourceFunction.source expressionSyntax profile.context
    (.statements true principal.sourceFunction.body) principal.sourceFunction.resultType)

/-- The actual source parameter receipt constructs the index internally,
retaining the same original profile and its genuine Source runtime. -/
def of_source_entry {hook : Word} {index : Int} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named hook) (some metadata))
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : CallableIndexedOwnedMethodInvocationBounds.ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨method, principal, owner, administrative, expressionSyntax, certificates, validity, diagnosticPolicy,
    profile, escaped, extend, runtimeOf, syntaxTree,
    (CallableIndexedOwnedMethodPrincipalReadyContinuations.source_admitted_entry principal profile functions escaped extend runtimeOf
      installed owner caller wellFormed beforeTyped argumentsTyped stable observed selected history
      entry added length spine reached).source.runtime⟩

/-- The actual native parameter receipt constructs the index internally,
retaining the same original profile and its genuine Source runtime. -/
def of_native_entry {hook : Word} {index : Int} {metadata : MetadataState}
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
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨method, principal, owner, administrative, expressionSyntax, certificates, validity, diagnosticPolicy,
    profile, escaped, extend, runtimeOf, syntaxTree,
    (CallableIndexedOwnedMethodPrincipalReadyContinuations.native_admitted_entry principal profile functions escaped extend runtimeOf
      installed owner caller wellFormed beforeTyped argumentsTyped stable observed selected history
      entry added length spine reached).source.runtime⟩

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
/-- The genuine Source entry constructs its exact index and invokes only the
strict shared-family child at that principal protocol. -/
theorem source_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions (Program.ofChecked compiled.sourceProgram) (origin index))) :
    CallableIndexedOwnedMethodInvocationBounds.SourceContinuationWithHistory
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro hook current metadata selected history _emitted entry added length spine reached _related
  intro child strict outcome after trace
  let index := of_source_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed syntaxTree selected history entry added length spine reached
  let actualEntry := CallableIndexedOwnedMethodPrincipalReadyContinuations.source_admitted_entry
    principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed selected history entry added length spine reached
  have ready := below index child strict
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
      (CallableIndexedOwnedMethodPrincipalReadyContinuations.bridge (headers := headers) principal owner)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
/-- The original measured prefix constructs the index at its actual reached
pool; the resulting Source grade remains independent of native execution. -/
theorem native_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions (Program.ofChecked compiled.sourceProgram) (origin index))) :
    CallableIndexedOwnedMethodInvocationBounds.NativeContinuationWithHistory
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro hook current metadata _prefixSize _bodyStore selected history _prefixWithin _value _finalStore
    _restored entry added length spine reached _related
  intro child strict value finalStore completed
  let index := of_native_entry principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed syntaxTree selected history entry added length spine reached
  let actualEntry := CallableIndexedOwnedMethodPrincipalReadyContinuations.native_admitted_entry
    principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed selected history entry added length spine reached
  have ready := below index child strict
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
      (CallableIndexedOwnedMethodPrincipalReadyContinuations.bridge (headers := headers) principal owner)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodReadyFamilyReceipts
