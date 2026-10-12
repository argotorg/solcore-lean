import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.Test.SourceCoreOperatorCallsSyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport

/-! A complete static package is produced from the actual two issuer packets.
The Type-valued terminal dispatcher branches only on real physical slots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

private def selectTwo {compiled : SourceCoreUnifiedCompilation.Compiled}
    {left right : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (distinct : left.slot ≠ right.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (leftValue : property left) (rightValue : property right) :
    ∀ header, header ∈ [left, right] → property header := by
  intro header member
  if sameSlot : header.slot = left.slot then
    have same : header = left := by
      rcases List.mem_cons.mp member with same | rest
      · exact same
      · have same := List.mem_singleton.mp rest
        exact False.elim (distinct (sameSlot ▸ congrArg (·.slot) same))
    exact same.symm ▸ leftValue
  else
    have same : header = right := by
      rcases List.mem_cons.mp member with same | rest
      · exact False.elim (sameSlot (congrArg (·.slot) same))
      · exact List.mem_singleton.mp rest
    exact same.symm ▸ rightValue

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  identityInput : Input fixture.recipe.compiled
  selectInput : Input fixture.recipe.compiled
  identityRow : identityInput.row = observed.identityRow.row
  selectRow : selectInput.row = observed.selectRow.row
  identityPacket : Issued identityInput
  selectPacket : Issued selectInput
  identityHeader : ActualHeader fixture observed.identityRow.row
  selectHeader : ActualHeader fixture observed.selectRow.row
  identityEq : identityHeader.header = identityPacket.header
  selectEq : selectHeader.header = selectPacket.header
  rows : Inventory [identityInput, selectInput]
  rowsEq : rows = .cons identityPacket (.cons selectPacket .nil)
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([identityInput, selectInput].map (fun input => input.prepared.index)).Nodup
  slotsDistinct : identityHeader.header.slot ≠ selectHeader.header.slot
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  identityDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named identityHeader.header.named.signature.key)
  selectDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named selectHeader.header.named.signature.key)

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (identityStages : ObservedStages fixture observed.identityRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨identityInput, selectInput, identityRow, selectRow, identityPacket, selectPacket,
    identityHeader, selectHeader, identityEq, selectEq, complete⟩ := observed.inventory
  let rows : Inventory [identityInput, selectInput] := .cons identityPacket (.cons selectPacket .nil)
  have headerList : headers rows = [identityHeader.header, selectHeader.header] := by
    simp only [rows, headers, identityEq, selectEq]
  have identityIndex : identityHeader.header.slot = observed.identityRow.index :=
    identityHeader.aligned.slot.trans (observed.identityRow.prepared_slot identityHeader.prepared).2
  have selectIndex : selectHeader.header.slot = observed.selectRow.index :=
    selectHeader.aligned.slot.trans (observed.selectRow.prepared_slot selectHeader.prepared).2
  have slotsDistinct : identityHeader.header.slot ≠ selectHeader.header.slot := by
    rw [identityIndex, selectIndex]
    exact observed.distinctSlots
  have inputDistinct : identityInput.prepared.index ≠ selectInput.prepared.index := by
    have left : identityHeader.header.slot = identityInput.prepared.index := by
      rw [identityEq]; exact identityPacket.aligned.slot
    have right : selectHeader.header.slot = selectInput.prepared.index := by
      rw [selectEq]; exact selectPacket.aligned.slot
    rw [← left, ← right]
    exact slotsDistinct
  obtain ⟨identityTerminal, identityDiagnostic, identityExpression, identityPoint⟩ := identityHeader.terminal
    observed.identityShape.read.node.id observed.identityShape.statement observed.identityShape.roots
    observed.identityShape.statementFound observed.identityShape.statementForm
  obtain ⟨identitySupport⟩ := CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    identityTerminal identityDiagnostic receiver fixture.source_wellFormed
    (by rw [identityHeader.source]; exact observed.identity_metadata identityTerminal.prepared.named)
    (by rw [identityHeader.source, identityExpression]; exact observed.identity_syntax)
    (actualStagePrepared fixture) identityPoint
  obtain ⟨selectTerminal, selectDiagnostic, selectExpression, selectPoint⟩ := selectHeader.terminal
    observed.selectShape.expression.node.id observed.selectShape.statement observed.selectShape.roots
    observed.selectShape.statementFound observed.selectShape.statementForm
  obtain ⟨selectSupport⟩ := CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    selectTerminal selectDiagnostic receiver fixture.source_wellFormed
    (by rw [selectHeader.source]; exact observed.select_metadata selectTerminal.prepared.named)
    (by rw [selectHeader.source, selectExpression]; exact observed.select_syntax)
    (actualStagePrepared fixture) selectPoint
  let property := fun header => Σ terminal : Body header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectTwo slotsDistinct property
      ⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal identityTerminal, .recursive identitySupport⟩
      ⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal selectTerminal, .recursive selectSupport⟩ header (headerList ▸ member)
  exact ⟨{
    identityInput := identityInput
    selectInput := selectInput
    identityRow := identityRow
    selectRow := selectRow
    identityPacket := identityPacket
    selectPacket := selectPacket
    identityHeader := identityHeader
    selectHeader := selectHeader
    identityEq := identityEq
    selectEq := selectEq
    rows := rows
    rowsEq := rfl
    complete := complete
    distinct := by simp [inputDistinct]
    slotsDistinct := slotsDistinct
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := by
      intro mapping world function native bindings parameter result association
      cases association with
      | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
          apply False.elim
          have found := code.sourceFound
          rcases observed.cached_source identityHeader selectHeader support.caller.selected with original | original
          · rw [support.source.trans original] at found
            exact False.elim (observed.identity_no_lambda (lookupExpression?_sound found) code.sourceForm)
          · rw [support.source.trans original] at found
            exact False.elim (observed.select_no_lambda (lookupExpression?_sound found) code.sourceForm)
      | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
          exact False.elim (fixture.no_principal support.principal)
    identityDescriptor := identityHeader.descriptor identityStages
    selectDescriptor := selectHeader.descriptor selectStages }⟩

end Tests.SourceCoreOperatorCalls
