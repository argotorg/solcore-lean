import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyCompilerFactory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerCertificates

/-! Actual body callback acceptances construct the selected raw certificate
factory. The original compiler induction interprets that same factory later. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodySiteInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport CallableIndexedOwnedPreparedOrdinaryLambdaFormation
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericImperativeMatch
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open RecursiveNamedExpressionCompilerCertificates
open CallableIndexedOwnedPreparedMixedCompilerHeads (extraForm extraChildren)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)

section Chosen
variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

/-- The actual named representation passes this literal expression callback. -/
theorem body_expression : (bodyPolicy produced.compilation produced.site.code).lowerExpression =
    FunctionCode.children produced.site.code.policy produced.site.code.lowerBody produced.site.code.fuel
      produced.site.code.compilation := by
  rfl

/-- The collector's accepted child action carries its original minimum fuel. -/
theorem accepted_child
    (policyEq : produced.site.code.policy = root.selected.policy)
    (bodyEq : produced.site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : produced.site.code.reasonAt = rootReasonAt)
    {context : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {residualMode : Bool}
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (signatures : context.signatures = compiled.compatible.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations produced.site.code.view childScope context)
    (allowed : expressionSyntax produced.site.code.view id)
    (found : produced.site.code.view.lookupExpression? id = some node)
    (typed : ExpressionHasType produced.site.code.view context id node.type)
    (accepted : (bodyPolicy produced.compilation produced.site.code).lowerExpression fuel
      produced.site.code.view childScope id produced.site.code.reasonAt = .ok lowered)
    (readFuel : Nat) :
    AcceptedAt root expressionSyntax readFuel produced.site.code.view context childScope id lowered := by
  rw [body_expression, FunctionCode.children, policyEq, bodyEq, reasonEq, produced.site.compilation] at accepted
  exact .intro found typed allowed declarations closed residual signatures accepted

/-- Only the two expression fields are built; every remaining static field is
passed from its authentic shell at this same Produced. -/
def SiteShell.to_inputs (shell : SiteShell expressionSyntax produced)
    (policyEq : produced.site.code.policy = root.selected.policy)
    (bodyEq : produced.site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : produced.site.code.reasonAt = rootReasonAt) :
    CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.SiteInputs caller produced where
  expressionSyntax := expressionSyntax
  certificates := certificates root expressionSyntax
  issued := shell.issued
  diagnosticPolicy := shell.diagnosticPolicy
  entry := shell.entry
  frame := shell.frame
  readFuel := shell.readFuel
  changed := []
  edited := shell.canonical.symm ▸ LocalView.refl (source caller.named)
  avoids := by intro id member; cases member
  unique := shell.unique
  sameLedger := shell.sameLedger
  syntaxTransport := by intro id reached allowed; simpa only [shell.canonical] using allowed
  expressions := by intro context childScope id lowered reached given; simpa only [shell.canonical] using given
  syntaxTree := shell.syntaxTree
  viewSyntax := shell.canonical.symm ▸ shell.syntaxTree
  projection := shell.projection
  residualMode := shell.residualMode
  static := {
    matchCompilation := shell.static.matchCompilation
    matchPolicy := shell.static.matchPolicy
    matchValues := shell.static.matchValues
    matchDefinitions := shell.static.matchDefinitions
    matchAllocator := shell.static.matchAllocator
    matchChildStatic := MatchChildStatic.of_hidden shell.static.hidden
    readPolicy := shell.static.readPolicy
    binderPolicy := shell.static.binderPolicy
    allocationPolicy := shell.static.allocationPolicy
    expressions := by
      intro context closed residual signatures childScope fuel id node lowered declarations allowed found typed accepted
      exact accepted_child root expressionSyntax produced policyEq bodyEq reasonEq closed residual signatures
        declarations allowed found typed accepted shell.readFuel
    assignments := shell.static.assignments
    unaries := shell.static.unaries
    assignmentExpressions := by
      intro context childScope fuel id lowered closed residual signatures declarations allowed node found typed accepted
      exact ⟨accepted_child root expressionSyntax produced policyEq bodyEq reasonEq closed residual signatures
        declarations allowed found typed accepted shell.readFuel,
        shell.static.assignmentNative context childScope fuel id lowered closed residual signatures declarations allowed
          node found typed accepted⟩
    closed := shell.static.closed
    residual := shell.static.residual
    sourceSignatures := shell.static.sourceSignatures
    declarations := shell.static.declarations
    ledger := shell.static.ledger }
  nativeTyped := shell.nativeTyped

/-- This property attaches the raw factory to the actual input entry. -/
def InputProperty
    (inputs : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.SiteInputs caller produced) : Prop :=
  inputs.expressionSyntax = expressionSyntax ∧ inputs.certificates = certificates root expressionSyntax

 theorem SiteShell.input_property (shell : SiteShell expressionSyntax produced)
    (policyEq : produced.site.code.policy = root.selected.policy)
    (bodyEq : produced.site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : produced.site.code.reasonAt = rootReasonAt) :
    InputProperty root expressionSyntax produced (SiteShell.to_inputs root expressionSyntax produced shell policyEq bodyEq reasonEq) := ⟨rfl, rfl⟩

end Chosen
section Coverage
open RecursiveNamedCallSelectionCertificates CallableAncestryPairedLookup
open CallableIndexedOwnedPreparedMixedCompilerCertificates (ExtraMetadata baseAdmitted)
variable {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {readFuel : Nat}
  (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
    (source caller.named) sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    (certificates root expressionSyntax))
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))

/-- The finite leaf sum is indexed by the actual current body scope. Lambda
leaves also retain their selected raw certificate factory and entry receipts. -/
inductive BodyCalls
    (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
      rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
      (source caller.named) sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (certificates root expressionSyntax))
    (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | named {childScope id lowered}
      (head : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
        (context compiled.indexed caller.named) (source caller.named) sourceContext children childScope id lowered) :
      BodyCalls root expressionSyntax factory headers children childScope id lowered
  | prepared_lambda {childFuel id lowered node parameters result statements reported}
      (found : (source caller.named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed caller.named) (source caller.named) scope id node parameters result statements reported rootReasonAt lowered)
      (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
        sourceContext evidence scope id lowered)
      (samePolicy : receipt.formation.produced.site.code.policy = root.selected.policy)
      (sameBody : receipt.formation.produced.site.code.lowerBody = root.selected.lowerBody)
      (sameFuel : receipt.formation.produced.site.code.fuel = childFuel)
      (sameView : receipt.formation.produced.site.code.view = source caller.named)
      (sameReason : receipt.formation.produced.site.code.reasonAt = rootReasonAt)
      (sameCertificate : HEq receipt.formation.produced.site.code.receipt certificate)
      (chosen : ∃ inputs : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.SiteInputs caller receipt.formation.produced,
        InputProperty root expressionSyntax receipt.formation.produced inputs ∧
        receipt.formation.expressionSyntax = inputs.expressionSyntax ∧
        receipt.formation.certificates = inputs.certificates ∧
        receipt.formation.body.readFuel = inputs.readFuel ∧ HEq receipt.formation.body.toContext inputs.entry)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type) :
      BodyCalls root expressionSyntax factory headers children scope id lowered
  | prepared_indirect {childFuel id lowered node callee ids metadata}
      (found : (source caller.named).lookupExpression? id = some node)
      (form : node.form = .call callee ids (.indirect metadata))
      (receipt : CallableIndexedOwnedIndirectCompilerReceipts.Receipt compiled.indexed.ancestry.graph.inputs.callable [] factory
        (policy := root.selected.policy) (body := root.selected.lowerBody) (fuel := childFuel)
        (id := id) (callee := callee) (ids := ids) (metadata := metadata) (reasonAt := rootReasonAt) (lowered := lowered))
      (ordered : ∀ child code, (child, code) ∈ receipt.compiler.entries → children scope child code) :
      BodyCalls root expressionSyntax factory headers children scope id lowered

theorem include_named {children childScope id lowered}
    (head : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
      (context compiled.indexed caller.named) (source caller.named) sourceContext children childScope id lowered) :
    BodyCalls root expressionSyntax factory headers children childScope id lowered := .named head

theorem projected {children childScope id lowered node}
    (head : BodyCalls root expressionSyntax factory headers children childScope id lowered)
    (found : (source caller.named).lookupExpression? id = some node) :
    compiled.compatible.checked.catalog.project node.type = .ok lowered.type := by
  cases head with
  | named actual => exact RecursiveNamedCallEvidenceHeads.projected actual found
  | prepared_lambda actualFound _ _ _ _ _ _ _ _ _ _ metadata =>
    have same := Option.some.inj (actualFound.symm.trans found)
    exact same ▸ metadata.projected
  | prepared_indirect _ _ receipt _ =>
    have same := Option.some.inj (receipt.compiler.found.symm.trans found)
    have emitted := congrArg SourceCoreBasic.LoweredExpr.type receipt.compiler.output
    simpa only [same, emitted] using receipt.parentMetadata.projected

/-- A real Source occurrence is known to be non-indirect. -/
def AbsentAt (source : TypedSource) (id : ExpressionId) : Prop :=
  ∀ {node callee ids metadata}, source.lookupExpression? id = some node →
    node.form ≠ .call callee ids (.indirect metadata)

/-- The exact named receipt rules out only the indirect form at this id. -/
theorem named_absent {children childScope id lowered}
    (head : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
      (context compiled.indexed caller.named) (source caller.named) sourceContext children childScope id lowered) :
    AbsentAt (source caller.named) id := by
  intro node callee ids metadata found form
  cases head with
  | ordinary actual =>
    cases actual with
    | named _ metadata _ actualForm _ _ _ _ _ _ _ _ _ _ _ _ =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      simp only [← same, actualForm] at form
      cases form
  | direct receipt _ _ =>
    have same := Option.some.inj (receipt.found.symm.trans found)
    simp only [← same, receipt.form] at form
    cases form

/-- Extra leaves retain the compiler's approved occurrence; named leaves
retain their actual declaration form. The original head stays literal. -/
def ScopedBodyCalls (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun childScope id lowered => BodyCalls root expressionSyntax factory headers children childScope id lowered ∧
    (expressionSyntax (source caller.named) id ∨ AbsentAt (source caller.named) id)

/-- The internal mode preserves the legacy certificate as its false case. -/
def CallsFor (supported : Bool) (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  if supported then ScopedBodyCalls root expressionSyntax factory headers children
  else BodyCalls root expressionSyntax factory headers children

theorem named_for (supported : Bool) {children childScope id lowered}
    (head : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
      (context compiled.indexed caller.named) (source caller.named) sourceContext children childScope id lowered) :
    CallsFor root expressionSyntax factory headers supported children childScope id lowered := by
  cases supported
  · exact .named head
  · exact ⟨.named head, .inr (named_absent headers head)⟩

theorem projected_for (supported : Bool) {children childScope id lowered node}
    (head : CallsFor root expressionSyntax factory headers supported children childScope id lowered)
    (found : (source caller.named).lookupExpression? id = some node) :
    compiled.compatible.checked.catalog.project node.type = .ok lowered.type := by
  cases supported
  · exact projected root expressionSyntax factory headers head found
  · obtain ⟨actual, _⟩ := head
    exact projected root expressionSyntax factory headers actual found

private theorem extra_cases {form : ExpressionForm} (extra : extraForm form) :
    (∃ parameters result statements, form = .lambda parameters result statements) ∨
      ∃ callee ids metadata, form = .call callee ids (.indirect metadata) := by
  cases form <;> simp only [extraForm] at extra
  case lambda parameters result statements => exact .inl ⟨parameters, result, statements, rfl⟩
  case call callee ids resolution =>
    cases resolution <;> simp only [extraForm] at extra
    case indirect metadata => exact .inr ⟨callee, ids, metadata, rfl⟩

private theorem pointwise_extra (domain : DomainAt root expressionSyntax readFuel sourceContext evidence scope headers)
    {id : ExpressionId} {node : ExpressionNode} (allowed : expressionSyntax (source caller.named) id)
    (found : (source caller.named).lookupExpression? id = some node) (extra : extraForm node.form) :
    PointwiseFor root (source caller.named) scope id rootReasonAt := by
  obtain ⟨requirements, coercions⟩ := domain.metadata.empty id node allowed found extra
  have ordinary := domain.metadata.ordinary id node allowed found extra
  rcases extra_cases extra with ⟨parameters, result, statements, form⟩ | ⟨callee, ids, resolution, form⟩
  · exact lambda_policy root found form requirements coercions ordinary
  · exact indirect_policy root found form requirements coercions
      (domain.metadata.arguments id node callee ids resolution allowed found form) ordinary

/-- Route and read profiles are extended before any acceptance assumption. -/
theorem policy_for_all (domain : DomainAt root expressionSyntax readFuel sourceContext evidence scope headers) :
    PolicyForWith (headers := headers) (some evidence) root.selected.policy
      (context compiled.indexed caller.named) readFuel (.initial compiled.compatible.checked)
      (source caller.named) sourceContext scope rootReasonAt (expressionSyntax (source caller.named)) where
  fragment := domain.basePolicy.fragment
  route := by
    intro id node allowed found
    by_cases extra : extraForm node.form
    · exact .inl (pointwise_extra root expressionSyntax headers domain allowed found extra).special
    · exact domain.basePolicy.route id node ⟨allowed, node, found, extra⟩ found
  read := by
    intro id allowed
    obtain ⟨node, found⟩ := domain.admission.base.found id allowed
    by_cases extra : extraForm node.form
    · exact (pointwise_extra root expressionSyntax headers domain allowed found extra).read
    · exact domain.basePolicy.read id ⟨allowed, node, found, extra⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Invert only the actual lambda read prefix, leaving its compiler receipt to
the existing finite lambda certificate producer. -/
theorem lambda_read {childFuel : Nat} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (found : (source caller.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (pointwise : PointwiseFor root (source caller.named) scope id rootReasonAt)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered) :
    ∃ reported, SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      (source caller.named) id = .ok (node, reported) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = (source caller.named).owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := pointwise.special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
        (min budget childFuel) (context compiled.indexed caller.named) childSource childScope childId childReasonAt) (childFuel + 1)
    cases hook : root.selected.policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals simp only [form, bind, Except.bind, pure, Except.pure] at accepted
    all_goals
      obtain ⟨pair, read, _⟩ := bind_ok accepted
      have metadata := CompatibleExpressionReads.metadata_of_read (pointwise.read ▸ read)
      have same := Option.some.inj (metadata.found.symm.trans found)
      exact ⟨pair.2, same ▸ (pointwise.read ▸ read)⟩
  · simp [owner, bind, Except.bind] at accepted

/-- Raw shells build the lambda leaf's chosen inputs internally; indirect
leaves preserve the original physical child entries for the existing IH. -/
theorem extra_receipts
    (domain : DomainAt root expressionSyntax readFuel sourceContext evidence scope headers)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (covers : evidence.Covers sourceContext)
    (childFuel : Nat) (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr)
    (allowed : expressionSyntax (source caller.named) id) (found : (source caller.named).lookupExpression? id = some node)
    (extra : extraForm node.form) (typed : ExpressionHasType (source caller.named) sourceContext id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered) :
    ∃ entries : List (ExpressionId × SourceCoreBasic.LoweredExpr),
      BodyCalls root expressionSyntax factory headers (CompatibleExpressionCalls.Entries scope entries) scope id lowered ∧
      entries.map Prod.fst = extraChildren node.form ∧
      ∀ child code, (child, code) ∈ entries → ∃ childNode,
        (source caller.named).lookupExpression? child = some childNode ∧
        ExpressionHasType (source caller.named) sourceContext child childNode.type ∧
        SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody childFuel
          (context compiled.indexed caller.named) (source caller.named) scope child rootReasonAt = .ok code := by
  obtain ⟨requirements, coercions⟩ := domain.metadata.empty id node allowed found extra
  have ordinary := domain.metadata.ordinary id node allowed found extra
  rcases extra_cases extra with ⟨parameters, result, statements, form⟩ | ⟨callee, ids, resolution, form⟩
  · have pointwise := pointwise_extra root expressionSyntax headers domain allowed found extra
    obtain ⟨reported, read⟩ := lambda_read root found form pointwise accepted
    have parentMetadata := CompatibleExpressionReads.metadata_of_read read
    have facts := CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (function := closure caller.named parameters result statements sourceContext evidence [])
      runtime.graph.nodeOccurrencesUnique found form typed coercions
    obtain ⟨certificate, receipt, samePolicy, sameBody, sameFuel, sameView, sameReason, sameCertificate, chosen⟩ :=
      CallableIndexedOwnedSamePolicyCompilerLeafReceipts.lambda_of_accepted_with_inputs root sourceContext evidence domain.profile
        (LambdaMetadataViews.MetadataView.refl _) found form facts.sourceType facts.ordinary coercions found rfl
        parentMetadata.owner requirements coercions ordinary read accepted
        (domain.native childFuel id node parameters result statements lowered allowed found form typed accepted)
        (fun produced inputs => InputProperty root expressionSyntax produced inputs)
        (fun produced sameDiagnostics sameCode sameCompilation samePolicy sameBody sameFuel sameView sameReason => by
          obtain ⟨shell⟩ := domain.shells childFuel id node parameters result statements lowered allowed found form typed accepted
            produced sameDiagnostics sameCode sameCompilation samePolicy sameBody sameFuel sameView sameReason
            (facts.frame runtime covers)
          exact ⟨SiteShell.to_inputs root expressionSyntax produced shell samePolicy sameBody sameReason, rfl, rfl⟩)
    have annotation := congrArg SourceCoreBasic.LoweredExpr.type certificate.emitted
    have outputMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type :=
      annotation.symm ▸ parentMetadata
    refine ⟨[], .prepared_lambda found form certificate receipt samePolicy sameBody sameFuel sameView sameReason sameCertificate chosen outputMetadata, ?_, ?_⟩
    · simp only [List.map_nil, form, extraChildren]
    · intro child code member; cases member
  · obtain ⟨receipt⟩ := CallableIndexedOwnedSamePolicyCompilerLeafReceipts.indirect_of_accepted root factory found form
      requirements coercions (domain.metadata.arguments id node callee ids resolution allowed found form) ordinary
      typed runtime.graph.nodeOccurrencesUnique accepted
    exact ⟨receipt.compiler.entries, .prepared_indirect found form receipt (fun _ _ member => ⟨rfl, member⟩),
      by simpa only [form, extraChildren] using receipt.positions, receipt.generated⟩

theorem extra_for (supported : Bool)
    (domain : DomainAt root expressionSyntax readFuel sourceContext evidence scope headers)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (covers : evidence.Covers sourceContext)
    (childFuel : Nat) (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr)
    (allowed : expressionSyntax (source caller.named) id) (found : (source caller.named).lookupExpression? id = some node)
    (extra : extraForm node.form) (typed : ExpressionHasType (source caller.named) sourceContext id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered) :
    ∃ entries : List (ExpressionId × SourceCoreBasic.LoweredExpr),
      CallsFor root expressionSyntax factory headers supported (CompatibleExpressionCalls.Entries scope entries) scope id lowered ∧
      entries.map Prod.fst = extraChildren node.form ∧
      ∀ child code, (child, code) ∈ entries → ∃ childNode,
        (source caller.named).lookupExpression? child = some childNode ∧
        ExpressionHasType (source caller.named) sourceContext child childNode.type ∧
        SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody childFuel
          (context compiled.indexed caller.named) (source caller.named) scope child rootReasonAt = .ok code := by
  obtain ⟨entries, actual, positions, generated⟩ :=
    extra_receipts root expressionSyntax factory headers domain runtime covers childFuel id node lowered allowed found extra typed accepted
  cases supported
  · exact ⟨entries, actual, positions, generated⟩
  · exact ⟨entries, ⟨actual, .inl allowed⟩, positions, generated⟩

/-- The full current ledger creates the indirect factory at this exact scope. -/
theorem indirect_factory (domain : DomainAt root expressionSyntax readFuel sourceContext evidence scope headers)
    (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed caller.named).solvedRequirements sourceContext evidence) :
    CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
      (source caller.named) sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (certificates root expressionSyntax) where
  sourceView := .refl _
  namedLedger := domain.namedLedger
  sourceLedger := valid.ledger
  valid := domain.namedLedger ▸ valid

/-- Consume the actual AcceptedAt action once through the original compiler
induction. No body or expression tree is supplied by DomainAt. -/
theorem cover_for (supported : Bool) (domain : DomainAt root expressionSyntax readFuel sourceContext evidence scope headers)
    (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed caller.named).solvedRequirements sourceContext evidence)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : AcceptedAt root expressionSyntax readFuel (source caller.named) sourceContext scope id lowered) :
    RuntimeExpressionsFor (CallsFor root expressionSyntax (indirect_factory root expressionSyntax headers domain valid) headers supported)
      readFuel (.initial compiled.compatible.checked) (source caller.named) sourceContext
      (context compiled.indexed caller.named).solvedRequirements rootReasonAt scope id lowered := by
  cases receipt with
  | intro found typed allowed declarations closed residual signatures accepted =>
    let factory := indirect_factory root expressionSyntax headers domain valid
    exact tree_of_functions_at_runtime_with_children (headers := headers)
      (values := .initial compiled.compatible.checked) (compilation := context compiled.indexed caller.named)
      (some evidence) (CallsFor root expressionSyntax factory headers supported)
      (named_for root expressionSyntax factory headers supported) (projected_for root expressionSyntax factory headers supported) extraForm extraChildren
      domain.admission domain.coverage domain.sourceTypes domain.emptyEvidence domain.order
      runtime.graph.nodeOccurrencesUnique declarations signatures domain.constructorValid domain.fragmentValid domain.selectedValid
      (policy_for_all root expressionSyntax headers domain) compiled.indexed.ancestry.graph.inputs.callable [] root.callables
      domain.fragmentCoercions domain.coercions
      (extra_for root expressionSyntax factory headers supported domain runtime valid.covers) allowed found typed accepted

theorem coverage (domain : DomainAt root expressionSyntax readFuel sourceContext evidence scope headers)
    (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed caller.named).solvedRequirements sourceContext evidence)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : AcceptedAt root expressionSyntax readFuel (source caller.named) sourceContext scope id lowered) :
    RuntimeExpressionsFor (BodyCalls root expressionSyntax (indirect_factory root expressionSyntax headers domain valid) headers)
      readFuel (.initial compiled.compatible.checked) (source caller.named) sourceContext
      (context compiled.indexed caller.named).solvedRequirements rootReasonAt scope id lowered :=
  cover_for root expressionSyntax headers false domain valid runtime receipt

end Coverage

section RetainedFactory
variable {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)

/-- The selected factory, readFuel and actual entry stay beside one Formation. -/
def ChosenFactory : Prop :=
  ∃ inputs : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.SiteInputs caller receipt.formation.produced,
    InputProperty root expressionSyntax receipt.formation.produced inputs ∧
    receipt.formation.expressionSyntax = inputs.expressionSyntax ∧
    receipt.formation.certificates = inputs.certificates ∧
    receipt.formation.body.readFuel = inputs.readFuel ∧ HEq receipt.formation.body.toContext inputs.entry

theorem formation_factories (chosen : ChosenFactory root expressionSyntax receipt) :
    receipt.formation.expressionSyntax = expressionSyntax ∧
    receipt.formation.certificates = certificates root expressionSyntax := by
  obtain ⟨inputs, property, sameSyntax, sameCertificates, _⟩ := chosen
  exact ⟨sameSyntax.trans property.1, sameCertificates.trans property.2⟩

/-- Recapture changes the captured environment while copying these literals. -/
theorem recaptured_factory (chosen : ChosenFactory root expressionSyntax receipt)
    (environment : Dynamic.Environment) :
    (receipt.formation.support environment).expressionSyntax = expressionSyntax ∧
    (receipt.formation.support environment).certificates = certificates root expressionSyntax ∧
    (receipt.formation.support environment).body.readFuel = receipt.formation.body.readFuel := by
  have factories := formation_factories root expressionSyntax receipt chosen
  exact ⟨factories.1, factories.2, rfl⟩

/-- Coverage consumes a real child certificate from the SAME recaptured
Support, at its current lexical context and its own semantic readFuel. -/
theorem support_cover_for (supported : Bool) (chosen : ChosenFactory root expressionSyntax receipt)
    (environment : Dynamic.Environment)
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
    (domain : DomainAt root expressionSyntax receipt.formation.body.readFuel currentContext evidence childScope headers)
    (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed caller.named).solvedRequirements currentContext evidence)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) currentContext (source caller.named))
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : (receipt.formation.support environment).certificates
      (receipt.formation.support environment).body.readFuel (receipt.formation.function environment).source
      currentContext childScope child output) :
    RuntimeExpressionsFor
      (CallsFor root expressionSyntax (indirect_factory root expressionSyntax headers domain valid) headers supported)
      receipt.formation.body.readFuel (.initial compiled.compatible.checked) (source caller.named) currentContext
      (context compiled.indexed caller.named).solvedRequirements rootReasonAt childScope child output := by
  change receipt.formation.certificates receipt.formation.body.readFuel (source caller.named)
    currentContext childScope child output at actual
  have same := congrArg (fun family => family receipt.formation.body.readFuel (source caller.named)
    currentContext childScope child output) (formation_factories root expressionSyntax receipt chosen).2
  exact cover_for root expressionSyntax headers supported domain valid runtime (same.mp actual)

theorem coverage_at_support (chosen : ChosenFactory root expressionSyntax receipt)
    (environment : Dynamic.Environment)
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
    (domain : DomainAt root expressionSyntax receipt.formation.body.readFuel currentContext evidence childScope headers)
    (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed caller.named).solvedRequirements currentContext evidence)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) currentContext (source caller.named))
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : (receipt.formation.support environment).certificates
      (receipt.formation.support environment).body.readFuel (receipt.formation.function environment).source
      currentContext childScope child output) :
    RuntimeExpressionsFor
      (BodyCalls root expressionSyntax (indirect_factory root expressionSyntax headers domain valid) headers)
      receipt.formation.body.readFuel (.initial compiled.compatible.checked) (source caller.named) currentContext
      (context compiled.indexed caller.named).solvedRequirements rootReasonAt childScope child output :=
  support_cover_for root expressionSyntax receipt false chosen environment headers domain valid runtime actual

end RetainedFactory
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodySiteInputs
