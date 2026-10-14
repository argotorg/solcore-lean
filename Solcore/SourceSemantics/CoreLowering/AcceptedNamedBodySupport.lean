import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodySyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission

/-! The actual named body action selects its structural branch. The supported
branch feeds the current physical scoped Support collector; the other branch
retains a concrete compiler frontier. There is no body-recognizer premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodySupport
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedFunctionValues (Header)

theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (table : TableAligned inputs directRows)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (children : ∀ receipt : Body header.policy header.fuel header.function.source
      (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.parameterScope header)
      header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body,
      ∀ child ∈ receipt.tree.children,
        GeneralSyntax header.function.source child.expression (DirectSite directRows))
    (bindings : ∀ receipt : Body header.policy header.fuel header.function.source
      (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.parameterScope header)
      header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body,
      ∀ binding ∈ receipt.tree.bindings,
        RecursiveNamedStatementSyntaxFacts.BinderReceipt header.function.source binding.binder)
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) ∨ Nonempty (Incomplete header.policy header.fuel header.function.source
      (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.parameterScope header)
      header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body) := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  cases closed : receipt.tree.closed with
  | false => exact .inr ⟨⟨receipt, closed⟩⟩
  | true =>
      obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
      have scan := receipt.tree.scan
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
        closed header.unique (by
          obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
          rw [header.frame.source]
          exact certificate.local_identity_ownership) (children receipt) (bindings receipt) typed
      exact .inl (CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual
        prepared aligned rows table ⟨metadata, scan⟩ ready diagnostic receiver wellFormed
        checked catalog methods member actual)


/-- Return selection uses the stored original head and the actual compiler receipt. -/
theorem of_returning {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (table : TableAligned inputs directRows)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {expression : ExpressionId}
    (statements : header.function.body = id :: rest)
    (found : header.function.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (child : GeneralSyntax header.function.source expression (DirectSite directRows))
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  have details := receipt.tree.at_return_list
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) statements found form
  obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  have scan := receipt.tree.scan
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    details.1 header.unique (by
      obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
      rw [header.frame.source]
      exact certificate.local_identity_ownership)
    (fun actual member => (details.2.2 actual member).symm ▸ child)
    (fun binding member => False.elim (by simp only [details.2.1, List.not_mem_nil] at member)) typed
  exact CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual
    prepared aligned rows table ⟨metadata, scan⟩ ready diagnostic receiver wellFormed
    checked catalog methods member actual

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodySupport
