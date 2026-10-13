import Solcore.Test.SourceCoreConstructorCallsCommon
import Solcore.Test.SourceCoreConstructorCallsSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionIssuance

/-! Real issuer receipts extend the retained history and authenticate exact raw
handle types. The Source heap remains the same across each issuance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers Inventory)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

theorem read_source_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.readPacket.header.named.specialized.function.type = .function (TypeSystem.Ty.productMany [makerType, .word, closureType, convertType]) (containerType fixture.dataType) := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
      support.readPacket.sourceAt fixture.source_wellFormed
  have shape := certified.callable_type
  change support.readPacket.header.named.specialized.function.type = _ at shape
  rw [← support.readPacket.sourceAt.frame.result, ← support.readEq,
    support.readHeader.read_types, support.readHeader.read_result_type] at shape
  rw [support.readEq] at shape
  exact shape

theorem ActualHeader.make_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).1
  rw [observed.makeShape.inputTypes, ← actual.source, actual.header.inputs] at raw
  simp only [List.map_map, Function.comp_def] at types raw
  exact types.symm.trans raw

theorem make_source_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.makePacket.header.named.specialized.function.type = makerType := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
      support.makePacket.sourceAt fixture.source_wellFormed
  have shape := certified.callable_type
  change support.makePacket.header.named.specialized.function.type = _ at shape
  rw [← support.makePacket.sourceAt.frame.result, ← support.makeEq,
    support.makeHeader.make_types, support.makeHeader.make_result_type] at shape
  rw [support.makeEq] at shape
  exact shape

section State
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
  {entries : List Entry}

/-- Named issuance appends the compiler-selected read global, preserving every
previous capture and the same actual heap. -/
theorem remember_named (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.readRow.row.key) :
    ∃ entry : Entry,
      entry.sourceType = .function (TypeSystem.Ty.productMany [makerType, .word, closureType, convertType]) (containerType fixture.dataType) ∧
      entry.handle = call.handle ∧ call.handle.sourceType = .function (TypeSystem.Ty.productMany [makerType, .word, closureType, convertType]) (containerType fixture.dataType) ∧
      entry.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.readPacket.header.named.specialized support.readInput.prepared.available)) ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  have member : Inventory.HasRow support.readPacket support.rows := by
    rw [support.rowsEq]
    exact .tail _ (.here _)
  have issued : publicSession.NamedIssuedAt support.readPacket.header.named.signature.key issuanceFuel call.completion := by
    rw [← support.readEq, support.readHeader.key]
    exact call.issued
  obtain ⟨entry, sourceType, source, handle, handleType, next, heap⟩ :=
    RecursiveNamedPublicPhysicalSessionIssuance.State.remember_named support.program
      fixture.recipePrepared state support.readPacket member issued call.returned
  exact ⟨entry, sourceType.trans (read_source_type support), handle,
    handleType.trans (read_source_type support), source, next, heap⟩

/-- Named issuance appends the compiler-selected read global, preserving every
previous capture and the same actual heap. -/
theorem remember_maker (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.makeRow.row.key) :
    ∃ entry : Entry,
      entry.sourceType = makerType ∧
      entry.handle = call.handle ∧ call.handle.sourceType = makerType ∧
      entry.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.makePacket.header.named.specialized support.makeInput.prepared.available)) ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  have member : Inventory.HasRow support.makePacket support.rows := by
    rw [support.rowsEq]
    exact .here _
  have issued : publicSession.NamedIssuedAt support.makePacket.header.named.signature.key issuanceFuel call.completion := by
    rw [← support.makeEq, support.makeHeader.key]
    exact call.issued
  obtain ⟨entry, sourceType, source, handle, handleType, next, heap⟩ :=
    RecursiveNamedPublicPhysicalSessionIssuance.State.remember_named support.program
      fixture.recipePrepared state support.makePacket member issued call.returned
  exact ⟨entry, sourceType.trans (make_source_type support), handle,
    handleType.trans (make_source_type support), source, next, heap⟩

/-- Builtin issuance appends the actual closed wordFromInteger payload. -/
theorem remember_builtin (state : RetainedState support publicSession entries)
    (call : ObservedBuiltin publicSession) :
    ∃ entry : Entry,
      entry.sourceType = .function .integer .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .integer .word ∧ entry.source = .builtin ⟨.wordFromInteger⟩ ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  obtain ⟨entry, sourceType, source, handle, handleType, next, heap⟩ :=
    RecursiveNamedPublicPhysicalSessionIssuance.State.remember_builtin fixture.recipePrepared
      state .wordFromInteger call.issued call.returned
  exact ⟨entry, sourceType, handle, handleType, source, next, heap⟩

end State
end Tests.SourceCoreConstructorCalls
