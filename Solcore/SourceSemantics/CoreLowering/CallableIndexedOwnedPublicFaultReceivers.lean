import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceiverTables
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticCompleteness

/-! Diagnostic receivers retain the actual owning metadata registry and table.
Their construction requires no native execution or unrelated completion. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
open Core Frontend SourceInference
open CallableIndexedOwnedPublicFaultReceiverTables

/-- The metadata and diagnostics needed by public semantic bounds. -/
structure Result (checked : SourceCoreCompatibleCatalog.Checked) where
  context : SourceCoreCompatibleValues.Context
  contextOwner : context.checked = checked
  extension : SourceCoreRawMetadata.Extends checked.staticRegistry context.registry
  diagnostics : SourceCoreFaultSites.Table

/-- Metadata and a literal table, with issuance supplied separately by IssuedAt.
The carrier contains no native execution result. -/
structure Receiver {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) where
  entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts
  result : Result checked

namespace Receiver

/-- Existing actual runSource clients retain their literal context and table. -/
def of_completion {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    (completion : SourceCoreCallableIndexedPrograms.Completion prepared) : Receiver prepared where
  entry := completion.entry
  result := ⟨completion.result.context, completion.result.contextOwner,
    completion.result.extension, completion.result.diagnostics⟩

instance {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} :
    Coe (SourceCoreCallableIndexedPrograms.Completion prepared) (Receiver prepared) :=
  ⟨of_completion⟩

/-- Build the same static fallback or compatible table and callable suffix
that the public codec uses. Table completeness comes from real preparation. -/
theorem at_registry (compiled : SourceCoreUnifiedCompilation.Compiled)
    (entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry registry) :
    ∃ receiver : Receiver compiled.indexed,
      receiver.entry = entry ∧ receiver.result.context.registry = registry ∧
      IssuedAt compiled.indexed receiver.entry receiver.result.context.registry
        receiver.result.extension receiver.result.diagnostics := by
  let values : SourceCoreCompatibleValues.Context := ⟨compiled.compatible.checked, registry, extension⟩
  cases present : compiled.indexed.base.diagnostics with
  | none =>
    let base : SourceCoreFaultSites.Table := {
      owner := entry.key.declaration
      resultType := entry.sourceResultType
      reads := []
      escapedReason := Word.zero }
    exact ⟨⟨entry, ⟨values, rfl, extension, appendCallable compiled.indexed base⟩⟩,
      rfl, rfl, base, by rw [present], rfl⟩
  | some diagnostics =>
    obtain ⟨base, rebuilt⟩ := CompatibleRegistryDiagnosticCompleteness.compiled_table_complete
      compiled present registry extension
    exact ⟨⟨entry, ⟨values, rfl, extension, appendCallable compiled.indexed base⟩⟩,
      rfl, rfl, base, by rw [present]; exact rebuilt, rfl⟩

/-- An exact metadata context obtained from actual public input encoding is
kept verbatim, including its authenticated checked catalog. -/
theorem at_context (compiled : SourceCoreUnifiedCompilation.Compiled)
    (entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts)
    (values : SourceCoreCompatibleValues.Context)
    (owner : values.checked = compiled.compatible.checked) :
    ∃ receiver : Receiver compiled.indexed,
      receiver.entry = entry ∧ receiver.result.context = values ∧
      IssuedAt compiled.indexed receiver.entry receiver.result.context.registry
        receiver.result.extension receiver.result.diagnostics := by
  have extension : SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry values.registry := by
    rw [← owner]
    exact values.extension
  cases present : compiled.indexed.base.diagnostics with
  | none =>
    let base : SourceCoreFaultSites.Table := {
      owner := entry.key.declaration
      resultType := entry.sourceResultType
      reads := []
      escapedReason := Word.zero }
    exact ⟨⟨entry, ⟨values, owner, extension, appendCallable compiled.indexed base⟩⟩,
      rfl, rfl, base, by rw [present], rfl⟩
  | some diagnostics =>
    obtain ⟨base, rebuilt⟩ := CompatibleRegistryDiagnosticCompleteness.compiled_table_complete
      compiled present values.registry extension
    exact ⟨⟨entry, ⟨values, owner, extension, appendCallable compiled.indexed base⟩⟩,
      rfl, rfl, base, by rw [present]; exact rebuilt, rfl⟩

end Receiver
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
