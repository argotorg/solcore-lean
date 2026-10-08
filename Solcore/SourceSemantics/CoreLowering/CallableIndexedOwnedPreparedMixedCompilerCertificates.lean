import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerHeads

/-! Actual extra leaves populate the existing compiler tree from one root
policy. Static metadata covers admitted nodes before any successful child call. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerCertificates
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedMixedCompilerHeads
open RecursiveNamedExpressionCompilerCertificates
open RecursiveNamedCallSelectionCertificates CallableAncestryPairedLookup

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
  {reasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel (source caller.named) scope rootId reasonAt rootLowered)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
    (source caller.named) sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) certificates)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  {admitted : ExpressionId → Prop}

/-- These facts hold at admitted actual lookups without an acceptance premise. -/
structure ExtraMetadata (admitted : ExpressionId → Prop) : Prop where
  empty : ∀ id node, admitted id → (source caller.named).lookupExpression? id = some node →
    extraForm node.form → node.requirements = [] ∧ node.coercions = []
  ordinary : ∀ id node, admitted id → (source caller.named).lookupExpression? id = some node →
    extraForm node.form → compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id node callee ids metadata, admitted id →
    (source caller.named).lookupExpression? id = some node → node.form = .call callee ids (.indirect metadata) →
    metadata.argumentCoercions = []

def baseAdmitted (source : TypedSource) (admitted : ExpressionId → Prop) (id : ExpressionId) : Prop :=
  admitted id ∧ ∃ node, source.lookupExpression? id = some node ∧ ¬ extraForm node.form

private theorem extra_cases {form : ExpressionForm} (extra : extraForm form) :
    (∃ parameters result statements, form = .lambda parameters result statements) ∨
      ∃ callee ids metadata, form = .call callee ids (.indirect metadata) := by
  cases form <;> simp only [extraForm] at extra
  case lambda parameters result statements => exact .inl ⟨parameters, result, statements, rfl⟩
  case call callee ids resolution =>
    cases resolution <;> simp only [extraForm] at extra
    case indirect metadata => exact .inr ⟨callee, ids, metadata, rfl⟩

private theorem pointwise_extra (metadata : ExtraMetadata (caller := caller) admitted)
    {id : ExpressionId} {node : ExpressionNode} (allowed : admitted id)
    (found : (source caller.named).lookupExpression? id = some node) (extra : extraForm node.form) :
    PointwiseFor root (source caller.named) scope id reasonAt := by
  obtain ⟨requirements, coercions⟩ := metadata.empty id node allowed found extra
  have ordinary := metadata.ordinary id node allowed found extra
  rcases extra_cases extra with ⟨parameters, result, statements, form⟩ | ⟨callee, ids, resolution, form⟩
  ·
    exact lambda_policy root found form requirements coercions ordinary
  ·
    exact indirect_policy root found form requirements coercions
      (metadata.arguments id node callee ids resolution allowed found form) ordinary

/-- Extend the original static route only at genuine extra lookup forms. -/
theorem policy_for_all {readFuel : Nat}
    (admission : AdmissionWith extraForm extraChildren (source caller.named) admitted)
    (metadata : ExtraMetadata (caller := caller) admitted)
    (basePolicy : PolicyForWith (headers := headers) (some evidence) root.selected.policy
      (context compiled.indexed caller.named) readFuel (.initial compiled.compatible.checked)
      (source caller.named) sourceContext scope reasonAt (baseAdmitted (source caller.named) admitted)) :
    PolicyForWith (headers := headers) (some evidence) root.selected.policy
      (context compiled.indexed caller.named) readFuel (.initial compiled.compatible.checked)
      (source caller.named) sourceContext scope reasonAt admitted where
  fragment := basePolicy.fragment
  route := by
    intro id node allowed found
    by_cases extra : extraForm node.form
    · exact .inl (pointwise_extra root metadata allowed found extra).special
    · exact basePolicy.route id node ⟨allowed, node, found, extra⟩ found
  read := by
    intro id allowed
    obtain ⟨node, found⟩ := admission.base.found id allowed
    by_cases extra : extraForm node.form
    · exact (pointwise_extra root metadata allowed found extra).read
    · exact basePolicy.read id ⟨allowed, node, found, extra⟩

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
    (pointwise : PointwiseFor root (source caller.named) scope id reasonAt)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) (source caller.named) scope id reasonAt = .ok lowered) :
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

/-- Native typing and collector inputs apply only to actual accepted lambda
children. The genuine Source frame is supplied to the collector internally. -/
structure LambdaStatic (admitted : ExpressionId → Prop) : Prop where
  native : ∀ childFuel id node parameters result statements lowered, admitted id →
    (source caller.named).lookupExpression? id = some node → node.form = .lambda parameters result statements →
    ExpressionHasType (source caller.named) sourceContext id node.type →
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) (source caller.named) scope id reasonAt = .ok lowered →
    HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      lowered.expression (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions
  inputs : ∀ childFuel id node parameters result statements lowered, admitted id →
    (source caller.named).lookupExpression? id = some node → node.form = .lambda parameters result statements →
    ExpressionHasType (source caller.named) sourceContext id node.type →
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) (source caller.named) scope id reasonAt = .ok lowered →
    ∀ produced : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Produced (compiled := compiled)
      caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered,
      produced.diagnostics = diagnostics → produced.namedCode = namedCode → HEq produced.compilation compilation →
      produced.site.code.policy = root.selected.policy → produced.site.code.lowerBody = root.selected.lowerBody →
      produced.site.code.fuel = childFuel → produced.site.code.view = source caller.named →
      produced.site.code.reasonAt = reasonAt →
      Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
        (closure caller.named parameters result statements sourceContext evidence []) →
      Nonempty (CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.SiteInputs caller produced)

/-- Populate one extra parent from its actual accepted compiler branch. Its
physical indirect entries are returned verbatim for the original compiler IH. -/
theorem extra_receipts
    (metadata : ExtraMetadata (caller := caller) admitted)
    (static : LambdaStatic root (sourceContext := sourceContext) (evidence := evidence) admitted)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (covers : evidence.Covers sourceContext)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (childFuel : Nat) (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr)
    (allowed : admitted id) (found : (source caller.named).lookupExpression? id = some node)
    (extra : extraForm node.form) (typed : ExpressionHasType (source caller.named) sourceContext id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) (source caller.named) scope id reasonAt = .ok lowered) :
    ∃ entries : List (ExpressionId × SourceCoreBasic.LoweredExpr),
      Head root factory headers (CompatibleExpressionCalls.Entries scope entries) scope id lowered ∧
      entries.map Prod.fst = extraChildren node.form ∧
      ∀ child code, (child, code) ∈ entries → ∃ childNode,
        (source caller.named).lookupExpression? child = some childNode ∧
        ExpressionHasType (source caller.named) sourceContext child childNode.type ∧
        SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody childFuel
          (context compiled.indexed caller.named) (source caller.named) scope child reasonAt = .ok code := by
  obtain ⟨requirements, coercions⟩ := metadata.empty id node allowed found extra
  have ordinary := metadata.ordinary id node allowed found extra
  rcases extra_cases extra with ⟨parameters, result, statements, form⟩ | ⟨callee, ids, resolution, form⟩
  ·
    have pointwise := pointwise_extra root metadata allowed found extra
    obtain ⟨reported, read⟩ := lambda_read root found form pointwise accepted
    have parentMetadata := CompatibleExpressionReads.metadata_of_read read
    have facts := CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (function := closure caller.named parameters result statements sourceContext evidence [])
      runtime.graph.nodeOccurrencesUnique found form typed coercions
    obtain ⟨certificate, receipt, samePolicy, sameBody, sameFuel, sameView, sameReason, sameCertificate⟩ :=
      CallableIndexedOwnedSamePolicyCompilerLeafReceipts.lambda_of_accepted root sourceContext evidence profile
        (LambdaMetadataViews.MetadataView.refl _) found form facts.sourceType facts.ordinary coercions found rfl
        parentMetadata.owner requirements coercions ordinary read accepted
        (static.native childFuel id node parameters result statements lowered allowed found form typed accepted)
        (fun produced sameDiagnostics sameCode sameCompilation samePolicy sameBody sameFuel sameView sameReason =>
          static.inputs childFuel id node parameters result statements lowered allowed found form typed accepted
            produced sameDiagnostics sameCode sameCompilation samePolicy sameBody sameFuel sameView sameReason
            (facts.frame runtime covers))
    have annotation := congrArg SourceCoreBasic.LoweredExpr.type certificate.emitted
    have outputMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type :=
      annotation.symm ▸ parentMetadata
    refine ⟨[], .prepared_lambda found form certificate receipt samePolicy sameBody sameFuel sameView sameReason sameCertificate outputMetadata, ?_, ?_⟩
    · simp only [List.map_nil, form, extraChildren]
    · intro child code member; cases member
  ·
    obtain ⟨receipt⟩ := CallableIndexedOwnedSamePolicyCompilerLeafReceipts.indirect_of_accepted root factory found form
      requirements coercions (metadata.arguments id node callee ids resolution allowed found form) ordinary
      typed runtime.graph.nodeOccurrencesUnique accepted
    exact ⟨receipt.compiler.entries, .prepared_indirect found form receipt (fun _ _ member => ⟨rfl, member⟩),
      by simpa only [form, extraChildren] using receipt.positions, receipt.generated⟩

/-- The actual accepted root uses the original compiler induction once. All
ordinary and named static cuts retain their original Source and scope. -/
theorem tree_of_functions {readFuel : Nat}
    (admission : AdmissionWith extraForm extraChildren (source caller.named) admitted)
    (coverage : ReachedCoverage headers (context compiled.indexed caller.named) (source caller.named) admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers sourceContext)
    (emptyEvidence : SelectedEmptyEvidence headers (context compiled.indexed caller.named) (source caller.named) admitted)
    (order : ∀ id callee arguments instantiation node, admitted id →
      (source caller.named).lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) →
      Ordered (context compiled.indexed caller.named).plan instantiation)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (covers : evidence.Covers sourceContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext)
    (signatures : sourceContext.signatures = compiled.compatible.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw (source caller.named) sourceContext admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw (source caller.named) sourceContext
      (CompatibleExpressionBuiltins.Syntax (source caller.named)))
    (selectedValid : SelectedDeclarationLaw headers (context compiled.indexed caller.named)
      (source caller.named) sourceContext admitted)
    (basePolicy : PolicyForWith (headers := headers) (some evidence) root.selected.policy
      (context compiled.indexed caller.named) readFuel (.initial compiled.compatible.checked)
      (source caller.named) sourceContext scope reasonAt (baseAdmitted (source caller.named) admitted))
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax (source caller.named) id →
      (source caller.named).lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → (source caller.named).lookupExpression? id = some node → node.coercions = [])
    (metadata : ExtraMetadata (caller := caller) admitted)
    (static : LambdaStatic root (sourceContext := sourceContext) (evidence := evidence) admitted)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {node : ExpressionNode} (allowed : admitted rootId)
    (found : (source caller.named).lookupExpression? rootId = some node)
    (typed : ExpressionHasType (source caller.named) sourceContext rootId node.type) :
    RuntimeExpressionsFor (Head root factory headers) readFuel (.initial compiled.compatible.checked)
      (source caller.named) sourceContext (context compiled.indexed caller.named).solvedRequirements reasonAt
      scope rootId rootLowered := by
  exact tree_of_functions_at_runtime_with_children (headers := headers)
    (values := .initial compiled.compatible.checked) (compilation := context compiled.indexed caller.named)
    (some evidence) (Head root factory headers)
    (include_named root factory headers) (projected root factory headers) extraForm extraChildren
    admission coverage sourceTypes emptyEvidence order runtime.graph.nodeOccurrencesUnique declarations signatures
    constructorValid fragmentValid selectedValid (policy_for_all root headers admission metadata basePolicy)
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables fragmentCoercions coercions
    (extra_receipts root factory headers metadata static runtime covers profile) allowed found typed root.selected.accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerCertificates
