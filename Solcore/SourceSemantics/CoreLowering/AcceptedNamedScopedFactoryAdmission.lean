import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyResultTyping
import Solcore.SourceSemantics.CoreLowering.AcceptedScopedLambdaBodyReceipts
import Solcore.SourceSemantics.CoreLowering.AcceptedCompilerExpressionProfile
import Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodySubsetProfile
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedClosureAdmission

/-! Flat original profiles close the actual scoped lambda body and its ordered
expression actions. The same derived scan issues both formation and closure
certificates without a caller-provided grammar or body completion premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedScopedFactoryAdmission
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (context)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open AcceptedScopedLambdaBodyReceipts (Produced)
open CallableIndexedOwnedPreparedScopedFactoryAdmission (SourceCertificate Certificate)
open CallableIndexedOwnedPreparedScopedClosureAdmission (SourceBodyCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {directRows : List SourceSpecialization.SpecializedFunction} {directOnly allowIndices allowConstructors : Bool}

/-- Every expression proof comes from an actual child compiler action at its
minimum root budget and original lexical scope. -/
theorem Produced.scan (produced : Produced prepared header parameters result statements)
    (expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source directRows directOnly allowIndices allowConstructors)
    (bodyProfile : AcceptedCompilerBodySubsetProfile.Profile header.function.source expressions.ids statements result)
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ScopedSourceBodyAdmission.Scan header.function.source
      (fun id => GeneralSyntax header.function.source id (DirectSite directRows)) result true statements := by
  have readPolicy : (AcceptedContextualLambdaReceipt.bodyPolicy produced.action.root produced.action.fuel).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := rfl
  obtain ⟨closed, monomorphic, members⟩ := bodyProfile.facts produced.inner.tree readPolicy produced.ready
  have children : ∀ child ∈ produced.inner.tree.children,
      GeneralSyntax header.function.source child.expression (DirectSite directRows) := by
    intro child member
    obtain ⟨trace⟩ := AcceptedNamedExpressionFlow.Trace.of_accepted
      (root := produced.action.root) expressions.metadata supported expressions.covered child.accepted
    cases trace.syntax_or_boundary expressions.covered with
    | inl grammar => exact grammar
    | inr residual =>
      obtain ⟨boundary⟩ := residual
      exact False.elim (boundary.impossible_ordinary expressions.metadata expressions.compositeForms expressions.noInitializer
        expressions.ordinaryArguments expressions.ordinaryMetadata expressions.indexOperands expressions.constructorRanges (members child member))
  obtain ⟨inner, final, facts, typed⟩ := AcceptedScopedLambdaBodyReceipts.inner_typing
    produced.actual.roots produced.actual.found produced.actual.form produced.action.head.found produced.form wellFormed
  obtain ⟨_facts, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have ownership : LocalIdentityOwnership header.function.source := by
    rw [header.frame.source]
    exact certified.local_identity_ownership
  have binders := AcceptedNamedBodyBindings.of_monomorphic produced.inner.tree readPolicy
    header.unique ownership typed monomorphic
  exact produced.inner.tree.scan_complete readPolicy closed header.unique ownership children binders typed

private theorem origin_owner : ∃ signature ∈ compiled.sourceProgram.signatures.functions,
    prepared.named.specialized.function.typedBody.owner = signature.id := by
  obtain ⟨request, signature, generic, member, _genericMember, _resolved, accepted⟩ := prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have fields := CallableCoercionBodyProvenance.specialization_fields accepted
  refine ⟨signature, member, ?_⟩
  rw [prepared.same, fields.1, SourceSpecialization.applyCheckedFunction_bodyOwner,
    identities.2.1, identities.1]

include aligned in
/-- Formation and later body admission share the same derived original scan. -/
theorem of_produced (produced : Produced prepared header parameters result statements)
    (expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source directRows directOnly allowIndices allowConstructors)
    (bodyProfile : AcceptedCompilerBodySubsetProfile.Profile header.function.source expressions.ids statements result)
    (bareUnary : PreparedBranchingBareUnarySyntax.Body header.function.source statements)
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (SourceCertificate compiled prepared.named header.function.source header.function.body) ∧
      Nonempty (SourceBodyCertificate compiled prepared.named directRows statements) := by
  have scan := Produced.scan prepared produced expressions bodyProfile supported wellFormed
  let factory : SourceCertificate compiled prepared.named header.function.source header.function.body := {
    expression := produced.actual.expression
    terminal := produced.actual.terminal.terminal
    node := produced.action.head.node
    parameters := parameters
    result := result
    statements := statements
    reported := produced.reported
    found := produced.action.head.found
    form := produced.form
    owner := produced.action.head.owner
    requirements := produced.requirements
    coercions := produced.coercions
    ordinary := produced.ordinary
    read := produced.read
    scan := scan.map (fun _ _ => True.intro)
    bareUnary := bareUnary }
  obtain ⟨signature, member, owner⟩ := origin_owner prepared
  have source := (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned).1
  have typedScan := scan
  have metadata := expressions.metadata
  rw [source] at typedScan metadata
  exact ⟨⟨factory⟩, ⟨⟨result, typedScan, metadata, signature, member, owner⟩⟩⟩

include aligned in
/-- The accepted outer return identifies the literal lambda. Its actual scoped
body and expression receipts derive both certificate lanes internally. -/
theorem of_returning {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧ binding.initializer = id)) = none)
    (expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source directRows directOnly allowIndices allowConstructors)
    (bodyProfile : AcceptedCompilerBodySubsetProfile.Profile header.function.source expressions.ids statements result)
    (bareUnary : PreparedBranchingBareUnarySyntax.Body header.function.source statements)
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (SourceCertificate compiled prepared.named header.function.source header.function.body) ∧
      Nonempty (SourceBodyCertificate compiled prepared.named directRows statements) := by
  obtain ⟨produced⟩ := AcceptedScopedLambdaBodyReceipts.of_returning prepared aligned roots outerFound outerForm
    found form requirements coercions ordinary
  exact of_produced prepared aligned produced expressions bodyProfile bareUnary supported wellFormed

include aligned in
/-- Full cache identity transports the factory certificate to its original row. -/
theorem source_of_header {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    (certificate : SourceCertificate compiled prepared.named header.function.source header.function.body) :
    Nonempty (Certificate compiled named) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  obtain ⟨source, body, _result⟩ :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned
  rw [source, body, namedEq] at certificate
  exact ⟨certificate⟩

/-- Full cache identity transports the inner certificate without replacing its source. -/
theorem closure_of_header {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    (certificate : SourceBodyCertificate compiled prepared.named directRows statements) :
    Nonempty (SourceBodyCertificate compiled named directRows statements) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  rw [namedEq] at certificate
  exact ⟨certificate⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedScopedFactoryAdmission
