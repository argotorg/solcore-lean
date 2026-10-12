import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState

/-! The immutable public global environment retains each finite inventory
Header's actual reserved reference at every session state. This lookup uses
the accepted catalog slot and fixed bootstrap owner, without replaying
initialization or claiming a value at that location in the current store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalReferences
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (owner)

/-- Inventory provenance fixes the literal global reference independently of
the current heap and store. The owned caller carries the separate store facts. -/
theorem global_reference
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers rows) :
    (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
        ((owner compiled).key.locations header)) := by
  obtain ⟨input, packet, _retained, same⟩ := rows.mem_headers header member
  subst header
  have selected : compiled.indexed.base.globals[packet.header.slot]? =
      some packet.header.named.signature := by
    rw [packet.aligned.slot, packet.aligned.named]
    exact input.slot.selected
  have reference := RecursiveNamedCatalogInitialization.global_reference
    compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame selected
  change (RecursiveNamedCatalogPreparedInitialization.environment compiled)[packet.header.slot]? =
    some (.cellRef (OptionalCell.cellType packet.header.named.signature.functionType)
      (RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals packet.header.slot)) at reference
  rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at reference
  exact reference

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalReferences
