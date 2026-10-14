import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyBindings
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceAdmissionTransport

/-! The accepted body action supplies statement structure. Original Source typing
supplies binding ownership; only expression certificates remain explicit.
Unsupported structure and generalized locals retain their actual compiled body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedScopedAdmission (SourceAdmission Admission)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

abbrev BodyAt (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :=
  Body header.policy header.fuel header.function.source
    (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.parameterScope header)
    header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body

/-- Each alternative retains the exact accepted body, including its actual
children, binding projections, statement roots and emitted code. -/
inductive Unsupported (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  | structure (receipt : BodyAt header) (openBranch : receipt.tree.closed = false)
  | generalized (receipt : BodyAt header) (binding : Binding header.policy header.function.source)
      (member : binding ∈ receipt.tree.bindings) (quantified : binding.binder.scheme.quantified ≠ [])

include aligned

/-- No statement-shape or binder callback is required by this producer. -/
theorem of_actual {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (children : ∀ receipt : BodyAt header, ∀ child ∈ receipt.tree.children,
      GeneralSyntax header.function.source child.expression (DirectSite directRows))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows ∨ Nonempty (Unsupported header) := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  cases closed : receipt.tree.closed with
  | false => exact .inr ⟨.structure receipt closed⟩
  | true =>
    rcases AcceptedNamedBodyBindings.of_header prepared aligned wellFormed receipt.tree with binders | generalized
    · obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
      exact .inl ⟨metadata, receipt.tree.scan
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
        closed header.unique (by
          obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
          rw [header.frame.source]
          exact certificate.local_identity_ownership) (children receipt) binders typed⟩
    · obtain ⟨binding, member, quantified⟩ := generalized
      exact .inr ⟨.generalized receipt binding member quantified⟩

/-- A stored return head selects the actual accepted return branch. The rest of
its Source statement list is preserved; the lowerer terminates at that head. -/
theorem of_returning {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = id :: rest)
    (found : header.function.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (child : GeneralSyntax header.function.source expression (DirectSite directRows))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  have details := receipt.tree.at_return_list
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
  obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  exact ⟨metadata, receipt.tree.scan
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    details.1 header.unique (by
      obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
      rw [header.frame.source]
      exact certificate.local_identity_ownership)
    (fun actual member => (details.2.2 actual member).symm ▸ child)
    (fun binding member => False.elim (by simp only [details.2.1, List.not_mem_nil] at member)) typed⟩

/-- Reverse transport uses the same cache identity and accepted root equation
as the existing source-to-Header adapter. -/
theorem source_of_header {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (admission : Admission prepared header directRows) :
    SourceAdmission compiled named named.specialized.function.typedBody
      (statements named.specialized.function.typedBody)
      named.specialized.function.inferredBodyType directRows := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  obtain ⟨source, body, result⟩ := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned
  change SourceAdmission compiled prepared.named header.function.source header.function.body
    header.function.resultType directRows at admission
  rw [source, body, result, namedEq] at admission
  exact admission

omit aligned

/-- The current physical scoped collector consumes the derived admission. -/
theorem support {compiled : SourceCoreUnifiedCompilation.Compiled}
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
        header body) ∨ Nonempty (Unsupported header) := by
  rcases of_actual prepared aligned metadata children wellFormed with admission | unsupported
  · exact .inl (CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual
      prepared aligned rows table admission ready diagnostic receiver wellFormed
      checked catalog methods member actual)
  · exact .inr unsupported

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission
