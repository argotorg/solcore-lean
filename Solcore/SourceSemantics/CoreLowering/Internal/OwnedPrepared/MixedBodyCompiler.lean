import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSamePolicyCompilerLeafReceipts
import Solcore.SourceSemantics.CoreLowering.FunctionCodeCertificates
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeInversion
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.Dynamic.Preservation

/-!
# Prepared callables: mixed body compiler

Compiler certificates, factory and site inputs of mixed bodies, and terminal body receipts.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerCertificates
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
  issued : ∀ id node parameters result statements, (admitted) id →
    (source caller.named).lookupExpression? id = some node → node.form = .lambda parameters result statements →
    CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics
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
      CallableIndexedOwnedSamePolicyCompilerLeafReceipts.lambda_of_accepted root (static.issued id node parameters result statements allowed found form) sourceContext evidence profile
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyCompilerFactory
/-! Raw body child certificates retain the actual accepted root compiler action.
The static shell excludes expression trees and completed joint bodies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport CallableIndexedOwnedPreparedOrdinaryLambdaFormation
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericImperativeMatch

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- The compiler fuel belongs to this actual child action; readFuel is its
separate certificate index. Lexical and Source facts belong to this context. -/
inductive AcceptedAt (expressionSyntax : TypedSource → ExpressionId → Prop) (readFuel : Nat)
    (source : TypedSource) (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate where
  | intro {scope id node lowered compilerFuel residualMode}
      (found : source.lookupExpression? id = some node)
      (typed : ExpressionHasType source sourceContext id node.type)
      (allowed : expressionSyntax source id)
      (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
      (closed : sourceContext.typeVariables = [])
      (residual : sourceContext.residualTypeVariables = residualMode)
      (signatures : sourceContext.signatures = compiled.compatible.checked.signatures)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
        compilerFuel (context compiled.indexed caller.named) source scope id rootReasonAt = .ok lowered) :
      AcceptedAt expressionSyntax readFuel source sourceContext scope id lowered

/-- This factory is chosen before any body collector runs. -/
def certificates (expressionSyntax : TypedSource → ExpressionId → Prop) :
    Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  AcceptedAt root expressionSyntax

section Extraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
    {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Static policy and child evidence is for the actual supplied body lowerer.
The residual factory contains no required legacy error interpretation. -/
structure StaticInputs (residualMode : Bool) (policy : SourceCoreLoops.Policy)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) where
  matchCompilation : SourceCoreCompatibleDataMatches.Context
  matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation
  matchValues : matchCompilation.values = values
  matchDefinitions : matchCompilation.definitions = definitions
  matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  hidden : MatchHiddenFresh source
  readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder
  allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault
  unaries : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault
  assignmentNative : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
    sourceContext.signatures = values.checked.signatures → CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
    expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
    ExpressionHasType source sourceContext id node.type →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions
  closed : context.typeVariables = []
  residual : context.residualTypeVariables = residualMode
  sourceSignatures : context.signatures = values.checked.signatures
  declarations : CompatibleExpressionReads.ScopeDeclarations source scope context
  ledger : context.solvedRequirements = matchCompilation.solvedRequirements

end Extraction

section Chosen
variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- Non-expression collector inputs are supplied at the actual chosen Site.
Raw child acceptance will construct its certificate fields internally. -/
structure SiteShell (expressionSyntax : TypedSource → ExpressionId → Prop)
    (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered) where
  issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  entry : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) produced.site.code
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
    (closure caller.named parameters result statements sourceContext evidence [])
  readFuel : Nat
  canonical : produced.site.code.view = source caller.named
  bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named
  declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext
  unique : NodeOccurrencesUnique (source caller.named)
  sameLedger : sourceContext.solvedRequirements = produced.site.code.compilation.solvedRequirements
  syntaxTree : Syntax (source caller.named) (expressionSyntax (source caller.named))
    entry.context (.statements true statements) result
  projection : compiled.compatible.checked.catalog.project result = .ok produced.site.code.receipt.resultCore
  residualMode : Bool
  static : StaticInputs (layouts := compiled.indexed.layouts) (owner := produced.site.code.compilation.owner)
    (active := produced.site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := compiled.indexed.base.globals.length) (onError := produced.site.code.allocationError)
    (values := .initial compiled.compatible.checked) (source := produced.site.code.view)
    (expressionSyntax := expressionSyntax produced.site.code.view) (reasonAt := produced.site.code.reasonAt)
    (definitions := compiled.indexed.layouts.definitions)
    (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    (invalidOperand := issued.invalidOperand) (invalidUnary := issued.invalidUnary)
    (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
    residualMode (bodyPolicy produced.compilation produced.site.code) entry.context
    (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
  nativeTyped : HasType (SourceCoreLocalCell.coreContext
      (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    produced.site.code.receipt.body (LanguageResult.resultType produced.site.code.receipt.resultCore)
    compiled.indexed.layouts.definitions

end Chosen
section Domain
open RecursiveNamedExpressionCompilerCertificates
open RecursiveNamedCallSelectionCertificates CallableAncestryPairedLookup
open CallableIndexedOwnedPreparedMixedCompilerHeads (extraForm extraChildren)
open CallableIndexedOwnedPreparedMixedCompilerCertificates (ExtraMetadata baseAdmitted)

/-- These are the original compiler's static premises at the current lexical
context and scope. Accepted lambda inputs are raw shells, with no final tree. -/
structure DomainAt (expressionSyntax : TypedSource → ExpressionId → Prop)
    (readFuel : Nat) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope)
    (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram)) : Prop where
  issued : ∀ id node parameters result statements, (expressionSyntax (source caller.named)) id →
    (source caller.named).lookupExpression? id = some node → node.form = .lambda parameters result statements →
    CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics
  namedLedger : (context compiled.indexed caller.named).solvedRequirements = caller.solved
  admission : AdmissionWith extraForm extraChildren (source caller.named) (expressionSyntax (source caller.named))
  coverage : ReachedCoverage headers (context compiled.indexed caller.named) (source caller.named)
    (expressionSyntax (source caller.named))
  sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers sourceContext
  emptyEvidence : SelectedEmptyEvidence headers (context compiled.indexed caller.named) (source caller.named)
    (expressionSyntax (source caller.named))
  order : ∀ id callee arguments instantiation node, expressionSyntax (source caller.named) id →
    (source caller.named).lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) → Ordered (context compiled.indexed caller.named).plan instantiation
  constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw (source caller.named) sourceContext
    (expressionSyntax (source caller.named))
  fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw (source caller.named) sourceContext
    (CompatibleExpressionBuiltins.Syntax (source caller.named))
  selectedValid : SelectedDeclarationLaw headers (context compiled.indexed caller.named) (source caller.named) sourceContext
    (expressionSyntax (source caller.named))
  basePolicy : PolicyForWith (headers := headers) (some evidence) root.selected.policy
    (context compiled.indexed caller.named) readFuel (.initial compiled.compatible.checked)
    (source caller.named) sourceContext scope rootReasonAt (baseAdmitted (source caller.named) (expressionSyntax (source caller.named)))
  fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax (source caller.named) id →
    (source caller.named).lookupExpression? id = some node → node.coercions = []
  coercions : ∀ id node, expressionSyntax (source caller.named) id → (source caller.named).lookupExpression? id = some node → node.coercions = []
  metadata : ExtraMetadata (caller := caller) (expressionSyntax (source caller.named))
  profile : compiled.compatible.checked.catalog.callableContracts = true
  native : ∀ childFuel id node parameters result statements lowered, expressionSyntax (source caller.named) id →
    (source caller.named).lookupExpression? id = some node → node.form = .lambda parameters result statements →
    ExpressionHasType (source caller.named) sourceContext id node.type →
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered →
    HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      lowered.expression (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions
  shells : ∀ childFuel id node parameters result statements lowered, expressionSyntax (source caller.named) id →
    (source caller.named).lookupExpression? id = some node → node.form = .lambda parameters result statements →
    ExpressionHasType (source caller.named) sourceContext id node.type →
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered →
    ∀ produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered,
      produced.diagnostics = diagnostics → produced.namedCode = namedCode → HEq produced.compilation compilation →
      produced.site.code.policy = root.selected.policy → produced.site.code.lowerBody = root.selected.lowerBody →
      produced.site.code.fuel = childFuel → produced.site.code.view = source caller.named →
      produced.site.code.reasonAt = rootReasonAt →
      Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
        (closure caller.named parameters result statements sourceContext evidence []) →
      Nonempty (SiteShell expressionSyntax produced)

end Domain
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyCompilerFactory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodySiteInputs
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
  bodyReasons := shell.bodyReasons
  declarations := shell.declarations
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
      CallableIndexedOwnedSamePolicyCompilerLeafReceipts.lambda_of_accepted_with_inputs root (domain.issued id node parameters result statements allowed found form) sourceContext evidence domain.profile
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts
/-! Accepted terminal body compilation retains the exact used expression
action and original footer. This first bridge stays at the same Source as the
compiler. It supplies no expression execution or completed body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

inductive Terminal (source : TypedSource) (expression : ExpressionId) : List StatementId → Prop where
  | returning {id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression)) : Terminal source expression (id :: rest)
  | tail {id node} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression false) : Terminal source expression [id]

/-- Static fields extracted from the actual accepted terminal branch. -/
structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (statements : List StatementId) (result : Ty)
    (reasonAt : ExpressionId → Word) (fellThrough escaped : Word) (code : Expr) where
  childFuel : Nat
  child : SourceCoreBasic.LoweredExpr
  predecessor : fuel = childFuel + 1
  generated : policy.lowerExpression childFuel source scope expression reasonAt = .ok child
  sameType : child.type = result
  terminal : Terminal source expression statements
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
    result reasonAt fellThrough escaped = .ok code
  emitted : code = CompatibleStatements.finish result
    (LocalLoop.returnValue result child.expression) fellThrough escaped

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem return_flow {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : StatementId} {node : StatementNode}
    {expression : ExpressionId} {rest : List StatementId} {result : Ty}
    {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word} {flow : Expr}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      (id :: rest) result reasonAt mode escaped = .ok flow) :
    ∃ childFuel child, fuel = childFuel + 1 ∧
      policy.lowerExpression childFuel source scope expression reasonAt = .ok child ∧
      child.type = result ∧ flow = LocalLoop.returnValue result child.expression := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
    obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
    have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
    subst actual
    simp only [form] at accepted
    obtain ⟨checked, _, accepted⟩ := bind_ok accepted
    cases checked
    obtain ⟨child, generated, accepted⟩ := bind_ok accepted
    obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
    cases checked
    have same := ensure_same checkedType
    subst result
    cases accepted
    exact ⟨fuel, child, rfl, generated, rfl, rfl⟩

private theorem tail_flow {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : StatementId} {node : StatementNode}
    {expression : ExpressionId} {result : Ty} {reasonAt : ExpressionId → Word}
    {escaped : Word} {flow : Expr}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression false)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      [id] result reasonAt true escaped = .ok flow) :
    ∃ childFuel child, fuel = childFuel + 1 ∧
      policy.lowerExpression childFuel source scope expression reasonAt = .ok child ∧
      child.type = result ∧ flow = LocalLoop.returnValue result child.expression := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
    obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
    have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
    subst actual
    simp only [form] at accepted
    obtain ⟨child, generated, accepted⟩ := bind_ok accepted
    simp only [Bool.not_false, Bool.and_self, List.isEmpty_nil, ↓reduceIte] at accepted
    obtain ⟨checked, _, accepted⟩ := bind_ok accepted
    cases checked
    obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
    cases checked
    have same := ensure_same checkedType
    subst result
    cases accepted
    exact ⟨fuel, child, rfl, generated, rfl, rfl⟩

/-- The source lookup and actual compiler output construct the receipt. -/
theorem of_accepted {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (terminal : Terminal source expression statements)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
      result reasonAt fellThrough escaped = .ok code) :
    Nonempty (Receipt policy fuel source scope expression statements result reasonAt fellThrough escaped code) := by
  have whole := accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  have footer : code = CompatibleStatements.finish result flow fellThrough escaped :=
    Except.ok.inj returned.symm
  have used : ∃ childFuel child, fuel = childFuel + 1 ∧
      policy.lowerExpression childFuel source scope expression reasonAt = .ok child ∧
      child.type = result ∧ flow = LocalLoop.returnValue result child.expression := by
    cases terminal with
    | returning rest found form => exact return_flow readPolicy found form generated
    | tail found form => exact tail_flow readPolicy found form generated
  obtain ⟨childFuel, child, predecessor, childGenerated, sameType, flowEq⟩ := used
  exact ⟨⟨childFuel, child, predecessor, childGenerated, sameType, terminal, whole, flowEq ▸ footer⟩⟩

/-- The exact original source relation supplies the genuine staged Head. -/
theorem Receipt.head {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Receipt policy fuel source scope expression statements result reasonAt fellThrough escaped code)
    (invocation : Staging.Recursive.Scope) (sameSource : invocation.source = source) :
    CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation expression statements := by
  cases sameSource
  cases receipt.terminal with
  | returning rest found form => exact .returning rest (lookupStatement?_sound found) form
  | tail found form => exact .tail (lookupStatement?_sound found) form

/-- Enclosing native checking supplies typing of the same used child. -/
theorem Receipt.native_child {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Receipt policy fuel source scope expression statements result reasonAt fellThrough escaped code)
    {context : Core.Context} {nativeType : Ty} {definitions : DataEnvironment}
    (typed : HasType context code nativeType definitions) :
    ∃ childType, HasType context receipt.child.expression childType definitions := by
  rw [receipt.emitted] at typed
  obtain ⟨flowType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow typed
  cases flowTyped with
  | caseE computation failure next => exact ⟨_, computation⟩

/-- Enclosing checked code determines the exact language-result type of
the used terminal child, including both error and success payloads. -/
theorem Receipt.native_child_exact {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Receipt policy fuel source scope expression statements result reasonAt fellThrough escaped code)
    {context : Core.Context} {nativeType : Ty} {definitions : DataEnvironment}
    (typed : HasType context code nativeType definitions) :
    HasType context receipt.child.expression (LanguageResult.resultType receipt.child.type) definitions := by
  rw [receipt.emitted] at typed
  obtain ⟨flowType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow typed
  cases flowTyped with
  | caseE computation failure success =>
    cases failure with
    | inLeft wellFormed error =>
      cases error with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        cases success with
        | inRight wordValid returned =>
          cases returned with
          | inLeft transferValid returned =>
            cases returned with
            | inRight unitValid returned =>
              cases returned with
              | var found =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                cases found
                simpa only [receipt.sameType, LanguageResult.resultType] using computation

/-- A chosen static body certificate stores only accepted compiler receipts. -/
def certificate (policy : SourceCoreLoops.Policy) (reasonAt : ExpressionId → Word)
    (fellThrough escaped : Word) : FunctionCode.BodyCertificate :=
  fun source scope statements result code =>
    ∃ fuel expression, Nonempty (Receipt policy fuel source scope expression statements result
      reasonAt fellThrough escaped code)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalContextCertificates
/-! Actual lexical binder receipts transport nonlocal context fields to each
expression certificate. This is a static map over the genuine compiler tree. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalContextCertificates
open Core Frontend SourceInference GenericLexicalStatements

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {initial context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

/-- The same accepted allocations and emitted code are preserved. -/
theorem Tree.discharge_context
    (tree : Tree layouts owner active frame globals onError values source
      (fun context scope id lowered => Dynamic.RuntimeContextFields initial context → certificates context scope id lowered)
      context scope mode statements expected type code)
    (fields : Dynamic.RuntimeContextFields initial context) :
    Tree layouts owner active frame globals onError values source certificates
      context scope mode statements expected type code := by
  induction tree with
  | nil allowed => exact .nil allowed
  | returnUnit rest found form => exact .returnUnit rest found form
  | returnValue rest found form expressionFound valueType value =>
      exact .returnValue rest found form expressionFound valueType (value fields)
  | tail found form expressionFound valueType value =>
      exact .tail found form expressionFound valueType (value fields)
  | uninitialized found form mono extended ordinary projected allocation annotation same _remaining ih =>
      exact .uninitialized found form mono extended ordinary projected allocation annotation same
        (ih (fields.trans (.ofBinderExtends extended)))
  | initialized found form mono extended ordinary initializerFound sourceType initialValue allocation annotation same _remaining ih =>
      exact .initialized found form mono extended ordinary initializerFound sourceType (initialValue fields)
        allocation annotation same (ih (fields.trans (.ofBinderExtends extended)))
  | discard found form notTail expressionFound value _remaining ih =>
      exact .discard found form notTail expressionFound (value fields) (ih fields)
  | block found form _inner _remaining innerIH remainingIH =>
      exact .block found form (innerIH fields) (remainingIH fields)
  | ifThen found form conditionFound conditionType conditionTree _then _else _remaining thenIH elseIH remainingIH =>
      exact .ifThen found form conditionFound conditionType (conditionTree fields)
        (thenIH fields) (elseIH fields) (remainingIH fields)
  | terminalBlock unique found form _inner stops issued ih =>
      exact .terminalBlock unique found form (ih fields) stops issued
  | terminalIf unique found form conditionFound conditionType conditionTree _then _else thenStops elseStops issued thenIH elseIH =>
      exact .terminalIf unique found form conditionFound conditionType (conditionTree fields)
        (thenIH fields) (elseIH fields) thenStops elseStops issued

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalContextCertificates
end
