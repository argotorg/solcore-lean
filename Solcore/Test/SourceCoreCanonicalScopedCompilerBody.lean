import Solcore.Test.SourceCoreCanonicalScopedTypes
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open AcceptedNamedBodyFlow

theorem ActualHeader.relay_body {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    actual.header.function.body = [observed.relayShape.initialized.id, observed.relayShape.statement.id] := by
  rw [actual.aligned.function]
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.relayShape.roots] at accepted
  exact (Except.ok.inj accepted).symm

private theorem returned_child {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    {returned : StatementNode} {expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope [returned.id] code)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? returned.id = some returned)
    (form : returned.form = .returnStmt (some expression)) :
    tree.children.map (·.expression) = [expression] := by
  cases tree with
  | returning read actualForm =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
      rfl
  | initialized read actualForm | returnUnit read actualForm | absent read actualForm
  | assigning read actualForm | assigned read actualForm | whileLoop read actualForm
  | discard read actualForm | block read actualForm | conditional read actualForm
  | tailValue read actualForm | valueDiscard read actualForm
  | matching read actualForm | matched read actualForm
  | forLoop read actualForm | forBoundary read actualForm | breaking read actualForm | continuing read actualForm =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp only [form, expanded] at outside
      cases outside

private theorem let_return {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr} {statements : List StatementId}
    {initialized returned : StatementNode} {binder : TypedBinder} {initializer expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (roots : statements = [initialized.id, returned.id])
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (initialFound : source.lookupStatement? initialized.id = some initialized)
    (initialForm : initialized.form = .letDecl binder (some initializer))
    (returnFound : source.lookupStatement? returned.id = some returned)
    (returnForm : returned.form = .returnStmt (some expression)) :
    tree.closed = true ∧ tree.bindings.map (·.binder) = [binder] ∧
      tree.children.map (·.expression) = [initializer, expression] := by
  subst statements
  cases tree with
  | initialized read form _ projected child generated _ remaining allocated =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans initialFound)
      cases same
      rw [initialForm] at form
      cases form
      have tail := remaining.at_return reader returnFound returnForm
      have children := returned_child remaining reader returnFound returnForm
      simp only [Tree.closed, Tree.bindings, Tree.children, List.map_cons, tail.1, tail.2.1,
        List.map_nil, children, and_self]
  | returning read form | returnUnit read form | absent read form
  | assigning read form | assigned read form | whileLoop read form
  | discard read form | block read form | conditional read form
  | valueDiscard read form
  | matching read form | matched read form
  | forLoop read form | forBoundary read form | breaking read form | continuing read form =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans initialFound)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans initialFound)
      cases same
      simp only [initialForm, expanded] at outside
      cases outside

/-- Inversion of the actual accepted body preserves the ordered child actions
and original binder. No expression syntax is supplied to this theorem. -/
theorem ActualHeader.relay_compiler_details {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row)
    (receipt : AcceptedNamedBodyAdmission.BodyAt actual.header) :
    receipt.tree.closed = true ∧
      receipt.tree.bindings.map (·.binder) = [observed.relayShape.localBinder] ∧
      receipt.tree.children.map (·.expression) =
        [observed.relayShape.initial.value.node.id, observed.relayShape.finalRead.node.id] := by
  exact let_return receipt.tree actual.relay_body
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read actual.prepared actual.aligned)
    (by rw [actual.source]; exact observed.relayShape.initializedFound)
    observed.relayShape.initializedForm
    (by rw [actual.source]; exact observed.relayShape.statementFound)
    observed.relayShape.statementForm

theorem ActualHeader.relay_compiler_bindings {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row)
    (receipt : AcceptedNamedBodyAdmission.BodyAt actual.header) :
    ∀ binding ∈ receipt.tree.bindings,
      RecursiveNamedStatementSyntaxFacts.BinderReceipt actual.header.function.source binding.binder := by
  rcases AcceptedNamedBodyBindings.of_header actual.prepared actual.aligned fixture.source_wellFormed receipt.tree with binders | boundary
  · exact binders
  · obtain ⟨binding, member, quantified⟩ := boundary
    have present := List.mem_map.mpr (show ∃ actual ∈ receipt.tree.bindings, actual.binder = binding.binder from ⟨binding, member, rfl⟩)
    rw [actual.relay_compiler_details receipt |>.2.1] at present
    have same := List.mem_singleton.mp present
    exact False.elim (quantified (by rw [same, observed.relayShape.localScheme]; rfl))

theorem ActualHeader.relay_metadata {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite observed.relayAdmission.table.rows) := by
  rw [(CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data actual.prepared actual.aligned).1,
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named actual.prepared
      observed.relayAdmission.selected observed.relayAdmission.same]
  exact observed.relayAdmission.metadata

theorem ActualHeader.relay_direct_sites {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    RelayDirectSites actual.header.function.source observed.relayAdmission.table.rows := by
  rw [(CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data actual.prepared actual.aligned).1,
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named actual.prepared
      observed.relayAdmission.selected observed.relayAdmission.same]
  exact observed.relayAdmission.sites

theorem ObservedProgram.relay_direct_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ instantiation, CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite
      observed.relayAdmission.table.rows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation := by
  obtain ⟨identityInput, makeInput, relayInput, _identityRow, _makeRow, _relayRow,
    identityPacket, makePacket, relayPacket, _identityHeader, _makeHeader, _relayHeader,
    _identityEq, _makeEq, _relayEq, complete⟩ := observed.inventory
  let rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory
      [identityInput, makeInput, relayInput] :=
    .cons identityPacket (.cons makePacket (.cons relayPacket .nil))
  have table := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.table_aligned_of_complete
    rows complete observed.relayAdmission.table
  exact fun _ site => site.supported table

end Tests.SourceCoreCanonicalScoped
