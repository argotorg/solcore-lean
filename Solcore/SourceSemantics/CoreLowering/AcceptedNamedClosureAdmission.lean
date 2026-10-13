import Solcore.SourceSemantics.CoreLowering.AcceptedNamedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionBoundaryExclusion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosureAdmission

/-! The actual returned lambda retains its inner expression compiler action.
That same action supplies the ordinary closure certificate; no separate body
or expression traversal is evaluated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedClosureAdmission
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (context)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported Child)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedClosureAdmission (OrdinaryBodyCertificate)
open AcceptedNamedFactoryAdmission (Produced ReturningAt ExpressionAt)
open AcceptedNamedExpressionFlow (Trace Boundary ReachedForms ReachedArguments)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {directRows : List SourceSpecialization.SpecializedFunction}

/-- The minimum budget and captured scope are those in the same lambda action. -/
theorem Produced.trace (produced : Produced prepared header)
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation) :
    Nonempty (Trace produced.action.root header.function.source produced.compiler.bodyScope header.reasonAt
      (min produced.inner.childFuel produced.action.fuel) produced.certificate.returnExpression produced.inner.child) := by
  apply Trace.of_accepted metadata supported covered
  exact produced.inner.generated

private theorem origin_owner : ∃ signature ∈ compiled.sourceProgram.signatures.functions,
    prepared.named.specialized.function.typedBody.owner = signature.id := by
  obtain ⟨request, signature, generic, member, _genericMember, _resolved, accepted⟩ := prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have fields := CallableCoercionBodyProvenance.specialization_fields accepted
  refine ⟨signature, member, ?_⟩
  rw [prepared.same, fields.1, SourceSpecialization.applyCheckedFunction_bodyOwner,
    identities.2.1, identities.1]

/-- A remaining boundary records the actual inner trace and its exact path. -/
structure Unsupported (produced : Produced prepared header)
    (directRows : List SourceSpecialization.SpecializedFunction) where
  trace : Trace produced.action.root header.function.source produced.compiler.bodyScope header.reasonAt
    (min produced.inner.childFuel produced.action.fuel) produced.certificate.returnExpression produced.inner.child
  boundary : Boundary trace

include aligned in
/-- The compiler traversal supplies syntax or the indexed unexpanded action. -/
theorem of_produced_or_boundary (produced : Produced prepared header)
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation) :
    Nonempty (OrdinaryBodyCertificate compiled prepared.named directRows [produced.certificate.returnStatement]) ∨
      Nonempty (Unsupported prepared produced directRows) := by
  obtain ⟨trace⟩ := Produced.trace prepared produced metadata supported covered
  cases trace.syntax_or_boundary covered with
  | inl grammar =>
    obtain ⟨signature, member, owner⟩ := origin_owner prepared
    have terminal := produced.inner.terminal
    have source := (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned).1
    have actualGrammar := Eq.mp (congrArg (fun source =>
      GeneralSyntax source produced.certificate.returnExpression (DirectSite directRows)) source) grammar
    have actualTerminal := Eq.mp (congrArg (fun source =>
      CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal source
        produced.certificate.returnExpression [produced.certificate.returnStatement]) source) terminal
    rw [source] at metadata
    exact .inl ⟨⟨produced.certificate.returnExpression, actualTerminal, actualGrammar,
      metadata, signature, member, owner⟩⟩
  | inr residual =>
    obtain ⟨boundary⟩ := residual
    exact .inr ⟨⟨trace, boundary⟩⟩

include aligned in
/-- Finite original direct/read reachability closes only the actual inner path. -/
theorem of_produced (produced : Produced prepared header)
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    {reached : ExpressionId → Prop}
    (forms : ReachedForms header.function.source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedArguments header.function.source reached)
    (present : reached produced.certificate.returnExpression) :
    Nonempty (OrdinaryBodyCertificate compiled prepared.named directRows [produced.certificate.returnStatement]) := by
  cases of_produced_or_boundary prepared aligned produced metadata supported covered with
  | inl result => exact result
  | inr residual =>
    obtain ⟨residual⟩ := residual
    exact False.elim (residual.boundary.impossible metadata forms initializers arguments present)

include aligned in
/-- Original finite return facts identify the produced lambda and inner action.
The compiler supplies the native read, captured scope, allocation and body. -/
theorem produced_of_returning {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧ binding.initializer = id)) = none)
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ produced : Produced prepared header,
      produced.certificate.returnStatement = statement ∧ produced.certificate.returnExpression = expression := by
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      header.function.source id header.function.body := by
    rw [roots]
    exact .returning rest outerFound outerForm
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) terminal aligned.accepted
  let actual : ReturningAt header := ⟨outer, rest, outerNode, id, roots, outerFound, outerForm, receipt⟩
  obtain ⟨fuel, predecessor, root, ⟨head⟩⟩ := AcceptedNamedExpressionFlow.of_header prepared aligned receipt.generated
  let action : ExpressionAt prepared actual := ⟨fuel, predecessor, root, head⟩
  have same : action.head.node = node := Option.some.inj (action.head.found.symm.trans found)
  have actualForm : action.head.node.form = .lambda parameters result [statement] := same ▸ form
  have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.lambda_policy action.root
    (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (reasonAt := header.reasonAt) action.head.found actualForm (same ▸ requirements) (same ▸ coercions) ordinary
  have plain : action.head.special = none := by
    have noSpecial := profile.special
      (Child action.root.selected.policy action.root.selected.lowerBody action.fuel
        (context compiled.indexed prepared.named)) (action.fuel + 1)
    exact Except.ok.inj (action.head.selected.symm.trans noSpecial)
  obtain ⟨reported, read, actualRequirements, actualCoercions, actualOrdinary, ⟨compiler⟩⟩ :=
    AcceptedContextualLambdaReceipt.of_head action.root action.head plain actualForm
  have returnType := AcceptedNamedFactoryAdmission.return_type roots outerFound outerForm
    action.head.found actualForm returnFound returnForm wellFormed
  let certificate : CallableIndexedOwnedPreparedNamedFactoryAdmission.SourceCertificate
      compiled prepared.named header.function.source header.function.body :=
    ⟨id, terminal, action.head.node, parameters, result, statement, returnNode, expression, reported,
      action.head.found, actualForm, action.head.owner, actualRequirements, actualCoercions, actualOrdinary,
      read, returnFound, returnForm, returnType⟩
  obtain ⟨inner⟩ := AcceptedContextualLambdaReceipt.inner_returning action.root compiler
    (CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal.returning [] returnFound returnForm)
  exact ⟨⟨certificate, actual, action, rfl, rfl, compiler, inner⟩, rfl, rfl⟩

include aligned in
/-- The same accepted inner body closes its direct/read certificate. Original
typing supplies its declared result; reached facts close actual trace boundaries. -/
theorem of_returning {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧ binding.initializer = id)) = none)
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    {reached : ExpressionId → Prop}
    (forms : ReachedForms header.function.source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedArguments header.function.source reached)
    (present : reached expression) :
    Nonempty (OrdinaryBodyCertificate compiled prepared.named directRows [statement]) := by
  obtain ⟨produced, statementEq, expressionEq⟩ := produced_of_returning prepared aligned roots outerFound outerForm
    found form requirements coercions ordinary returnFound returnForm wellFormed
  have reachedInner : reached produced.certificate.returnExpression := expressionEq ▸ present
  have result := of_produced prepared aligned produced metadata supported covered forms initializers arguments reachedInner
  simpa only [statementEq] using result

/-- Full cache identity transports the closure certificate without replacing its source. -/
theorem source_of_header {index : Nat} {named : SourceCoreGeneralFunctions.Function} {body : List StatementId}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    (certificate : OrdinaryBodyCertificate compiled prepared.named directRows body) :
    Nonempty (OrdinaryBodyCertificate compiled named directRows body) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  rw [namedEq] at certificate
  exact ⟨certificate⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedClosureAdmission
