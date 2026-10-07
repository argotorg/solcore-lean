import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodNestedEntries
/-! The actual selected hook history and ordered parameter post supply the
method principal packet before its strict body child. Both adapters consume the
same authentic method origin and forget only the returned packet proof; the
complete reached pool and relation remain intact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds
open RecursiveNamedCatalogInvocationBounds (Below)
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
  (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)

include observed in
/-- A strict Source body family receives the exact authentic parameter Entry
and reached pool produced by the selected method hook. -/
theorem source_continuation (budget : Nat)
    (meaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions (Program.ofChecked compiled.sourceProgram)
      (origin principal.cached.compilation profile escaped extend runtimeOf))) :
    SourceContinuationWithHistory (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro _origin _index _metadata selected history _emitted entry added length spine reached _related child strict _outcome _after trace
  let actual := CallableIndexedOwnedMethodNestedEntries.source_entry principal profile functions escaped extend runtimeOf
    installed owner observed selected history entry added length spine reached
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, exit, returned, related⟩ :=
    meaning child strict actual trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, exit, returned.val, related⟩

include observed in
/-- Native body reflection receives the actual measured Prefix and its same
reached pool, retaining an independently measured Source trace. -/
theorem native_continuation (budget : Nat)
    (meaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions (Program.ofChecked compiled.sourceProgram)
      (origin principal.cached.compilation profile escaped extend runtimeOf))) :
    NativeContinuationWithHistory (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  intro _origin _index _metadata _prefixSize _bodyStore selected history _prefixWithin _value _finalStore
    _restored entry added length spine reached _related child strict _bodyValue _bodyFinalStore completed
  let actual := CallableIndexedOwnedMethodNestedEntries.native_entry principal profile functions escaped extend runtimeOf
    installed owner observed selected history entry added length spine reached
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, exit, returned, related⟩ :=
    meaning child strict actual completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, exit, returned.val, related⟩
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalContinuations
