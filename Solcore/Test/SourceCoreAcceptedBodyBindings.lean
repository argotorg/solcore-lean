import Solcore.Test.SourceCoreCanonicalScopedRelaySupport
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreAcceptedBodyBindings
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open AcceptedNamedBodyFlow
open Tests.SourceCoreCanonicalScoped

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
    tree.closed = true ∧ tree.bindings.map (·.binder) = [binder] := by
  subst statements
  cases tree with
  | initialized read form _ projected child generated _ remaining allocated =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans initialFound)
      cases same
      rw [initialForm] at form
      cases form
      have tail := remaining.at_return reader returnFound returnForm
      simp only [Tree.closed, Tree.bindings, List.map_cons, tail.1, tail.2.1, List.map_nil,
        and_self]
  | returning read form | returnUnit read form | absent read form
  | assigning read form | assigned read form | whileLoop read form
  | bitNotting read form | bitNotted read form
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

/-- The real cached H relay has one compiler-issued binding. Its declaration
receipt comes from original Header typing, without a supplied binder callback. -/
theorem relay_receipts {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    ∃ receipt : AcceptedNamedBodyAdmission.BodyAt actual.header,
      receipt.tree.closed = true ∧
      receipt.tree.bindings.map (·.binder) = [observed.relayShape.localBinder] ∧
      (∀ binding ∈ receipt.tree.bindings,
        RecursiveNamedStatementSyntaxFacts.BinderReceipt actual.header.function.source binding.binder) := by
  obtain ⟨receipt⟩ := body_of_accepted actual.aligned.accepted
  have roots := actual.relay_body (observed := observed)
  have source := actual.source
  have details : receipt.tree.closed = true ∧
      receipt.tree.bindings.map (·.binder) = [observed.relayShape.localBinder] := by
    exact let_return receipt.tree roots (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read actual.prepared actual.aligned)
      (by rw [source]; exact observed.relayShape.initializedFound)
      observed.relayShape.initializedForm
      (by rw [source]; exact observed.relayShape.statementFound)
      observed.relayShape.statementForm
  have mono : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = [] := by
    intro binding member
    have present : binding.binder ∈ receipt.tree.bindings.map (·.binder) :=
      List.mem_map.mpr ⟨binding, member, rfl⟩
    rw [details.2] at present
    have same := List.mem_singleton.mp present
    rw [same, observed.relayShape.localScheme]
    rfl
  rcases AcceptedNamedBodyBindings.of_header actual.prepared actual.aligned fixture.source_wellFormed receipt.tree with receipts | boundary
  · exact ⟨receipt, details.1, details.2, receipts⟩
  · obtain ⟨binding, member, quantified⟩ := boundary
    exact False.elim (quantified (mono binding member))

theorem observed_receipts (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    ∃ actual : ActualHeader fixture observed.relayRow.row,
      ∃ receipt : AcceptedNamedBodyAdmission.BodyAt actual.header,
        receipt.tree.closed = true ∧
        receipt.tree.bindings.map (·.binder) = [observed.relayShape.localBinder] ∧
        (∀ binding ∈ receipt.tree.bindings,
          RecursiveNamedStatementSyntaxFacts.BinderReceipt actual.header.function.source binding.binder) := by
  obtain ⟨input, row, packet, actual, rest⟩ := observed.relayRow.issue
  exact ⟨actual, relay_receipts actual⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  have _receipts := observed_receipts fixture observed
  IO.println "ACCEPTED_BODY_BINDINGS_PASS: actual H let/direct/return, one original monomorphic local, exact compiler flow and Header-derived declaration"

end Tests.SourceCoreAcceptedBodyBindings
