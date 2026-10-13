import Solcore.Test.SourceCoreDirectIssuedSequence
import Solcore.Test.SourceCoreCapturedReuseSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionIssuance

/-! Real issuer receipts extend the retained history and authenticate exact raw
handle types. The Source heap remains the same across each issuance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers Inventory)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

theorem read_source_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.readPacket.header.named.specialized.function.type = .function (.function .unit .word) .word := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
      support.readPacket.sourceAt fixture.source_wellFormed
  have shape := certified.callable_type
  change support.readPacket.header.named.specialized.function.type = _ at shape
  rw [← support.readPacket.sourceAt.frame.result, ← support.readEq,
    support.readHeader.read_types, support.readHeader.read_result_type] at shape
  rw [support.readEq] at shape
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
      entry.sourceType = .function (.function .unit .word) .word ∧
      entry.handle = call.handle ∧ call.handle.sourceType = .function (.function .unit .word) .word ∧
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
end Tests.SourceCoreDirectIssued
