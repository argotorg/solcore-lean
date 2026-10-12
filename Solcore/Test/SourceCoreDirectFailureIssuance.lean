import Solcore.Test.SourceCoreDirectFailureSeed
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryIssuance
import Solcore.SourceSemantics.CoreLowering.RecursivePublicCallableArity
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers Inventory)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

def issuanceFuel : Nat := 1024

structure ObservedNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.NamedIssuedAt key issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamed session key) := do
  match ← session.namedWithReceipt key issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok result =>
    match returned : result.val.value with
    | .function handle => pure ⟨result.val, result.property, handle, returned⟩
    | _ => throw (IO.userError "named failure issuance did not return a function")

theorem failed_source_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.failedPacket.header.named.specialized.function.type = .function .unit .word := by
  obtain ⟨_facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
      support.failedPacket.sourceAt fixture.source_wellFormed
  have bindingTypes : support.failedHeader.header.types = [] := by
    have same := Dynamic.MonoBindersExtend.bodyTypes_eq support.failedHeader.header.extended
    rw [support.failedHeader.header.parameters] at same
    have raw := support.failedHeader.failed_inputs
    simpa only [List.map_map, Function.comp_def, raw] using same.symm
  have shape := certified.callable_type
  change support.failedPacket.header.named.specialized.function.type = _ at shape
  rw [← support.failedPacket.sourceAt.frame.result, ← support.failedEq,
    bindingTypes, support.failedHeader.failed_result_type] at shape
  rw [support.failedEq] at shape
  exact shape

theorem remember_named {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.failedRow.row.key) :
    ∃ (entry : Entry) (global : Dynamic.GlobalFunction),
      entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      entry.source = .global global ∧
      CallableIndexedOwnedFunctionValues.NamedSourceAt support.failedHeader.header support.failedInput.prepared.available global ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram) entry.source 0 ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  have member : Inventory.HasRow support.failedPacket support.rows := by
    rw [support.rowsEq]
    exact .here _
  have issued : publicSession.NamedIssuedAt support.failedPacket.header.named.signature.key issuanceFuel call.completion := by
    rw [← support.failedEq, support.failedHeader.key]
    exact call.issued
  obtain ⟨actual, native, actualAt, retained⟩ := RecursiveNamedPublicHistoryIssuance.named_remembered
    fixture.recipePrepared [support.failedInput, support.identityInput] support.rows support.failedPacket member
    receiver.completion.result.context.registry receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile state.history state.atRecipe state.atSession issued call.returned fixture.source_wellFormed
  have registry := (call.issued.same_runtime.indexed state.atSession actualAt.2.2.2).registry_at state.registry
  let global := CallableNamedReversal.global (CallableNamedMetadata.global
    support.failedPacket.header.named.specialized support.failedInput.prepared.available)
  let entry : Entry := ⟨support.failedPacket.header.named.specialized.function.type,
    .global global, call.handle, native,
    Core.CallableContract.functionType support.failedPacket.header.named.signature.parameterType
      support.failedPacket.header.named.signature.resultType, issuanceFuel⟩
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.failedHeader.header
      support.failedInput.prepared.available global := by
    rw [support.failedEq]
    exact support.failedPacket.sourceAt
  have noParameters : support.failedHeader.header.function.parameters = [] := by
    rw [support.failedHeader.header.parameters, ← support.failedHeader.header.inputs,
      support.failedHeader.source, observed.failedShape.inputs]
  have noInputs : support.failedHeader.header.sourceBody.source.inputs.length = 0 := by
    rw [← sourceAt.frame.parameters, noParameters]
    rfl
  refine ⟨entry, global, failed_source_type support, rfl, rfl, sourceAt,
    noInputs ▸ RecursivePublicCallableArity.Arity.global sourceAt.frame.instantiated,
    ⟨state.artifact, actual.session, state.mapping, state.world, state.heap, state.store, state.caller,
      actualAt.2.2.2, state.atRecipe, registry, retained⟩, rfl⟩

end Tests.SourceCoreDirectFailure
