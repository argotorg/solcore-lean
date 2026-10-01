import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchReadyFactory

/-! The fixed loop policy supplies actual match ledger provenance. Independent
source validity reaches distinct same-body arms, the default, and lexical
bindings without a second ledger-validity assumption. The ready factory leaves
all existing diagnostic laws explicit. This file has no runtime evaluator. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreGenericImperativeMatchReadyFactory
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchArmScopes GenericMatchChildren
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"match_scoped_contexts", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "match_scoped_contexts.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 2⟩
private def binder (index : Nat) : TypedBinder :=
  ⟨⟨owner, index⟩, toString index, .mono .unit, [], false, none⟩
private def pattern (index : Nat) : TypedMatchPattern := {
  source := .group span (.binder span (toString index)), type := .unit, resolution := .binder (binder index) }
private def arm (index : Nat) : TypedMatchCase := ⟨span, pattern index, []⟩
private def resolution : MatchResolution := ⟨⟨⟨owner, 1⟩⟩, hidden, [arm 0, arm 1], some [], []⟩
private def node : StatementNode := ⟨site, span, .unit, .matchWith resolution⟩
private def source : TypedSource := {owner, inputs := [], roots := [.statement site], nodes := [.statement node]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private theorem admitted : TypeAdmissible context .unit := .unit (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures])
private theorem patternTyped (index : Nat) : TypedMatchPatternHasType context (pattern index) .unit [binder index] 0 := {
  type_eq := rfl, source_represents := .group (.binder rfl)
  resolution_type := .binder {
    scheme_eq := rfl, runtime := rfl
    wellFormed := by intro declaration installed; cases installed }
  binders_distinct := ⟨by simp, by simp⟩ }
private def armContext (index : Nat) : SourceSemantics.Context :=
  context.withLocal (binder index).id (binder index).scheme []
private theorem extended (index : Nat) : BindersExtend source.owner context [binder index] (armContext index) := by
  apply BindersExtend.cons (middle := armContext index)
  · apply BinderExtends.intro
    · exact {
        owned := rfl, scheme := SchemeWellFormed.monoAdmissible admitted
        quantified_fresh := by intro metavariable member; cases member
        monomorphic_requirements_empty := by intro mono; rfl }
    · simp [LocalFresh, context, Context.ofSignatures]
  · exact .nil _
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.get catalogExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some checked.catalog.definitions⟩
private def hiddenScope : Scope := [(hidden, .unit)]
private def fallback : CertifiedPattern compilation.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit) }
private def compiled (index : Nat) : CertifiedPattern compilation.definitions :=
  match compilePattern compilation 20 source hiddenScope site span .unit (pattern index) with
  | .ok result => result | .error _ => fallback
private theorem firstAccepted : compilePattern compilation 20 source hiddenScope site span .unit (pattern 0) = .ok (compiled 0) := by rfl
private theorem secondAccepted : compilePattern compilation 20 source hiddenScope site span .unit (pattern 1) = .ok (compiled 1) := by rfl
private theorem emptyScope : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index type selected authentic
  cases selected
private theorem hiddenAbsent : hidden ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id) := by
  simp [SourceCoreDataPlaces.declaredBinders, SourceCoreDataPlaces.patternBinders,
    source, node, resolution, arm, pattern, binder, hidden]

private def request (index : Nat) : Request :=
  ⟨armScope hiddenScope (compiled index).pattern, [], LocalLoop.fallthrough .unit⟩
private def defaultRequest : Request := ⟨hiddenScope, [], LocalLoop.fallthrough .unit⟩

theorem first_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    (request 0) (armContext 0) :=
  ScopedContextFor.compiled_arm (scope := hiddenScope) (arm := arm 0)
    (cases := resolution.cases) (fallback := resolution.defaultBody)
    (LocalLoop.fallthrough .unit) (List.mem_cons_self)
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 0) (compiled 0) firstAccepted) rfl (patternTyped 0) (extended 0)

theorem second_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    (request 1) (armContext 1) :=
  ScopedContextFor.compiled_arm (scope := hiddenScope) (arm := arm 1)
    (cases := resolution.cases) (fallback := resolution.defaultBody)
    (LocalLoop.fallthrough .unit) (List.mem_cons_of_mem _ List.mem_cons_self)
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 1) (compiled 1) secondAccepted) rfl (patternTyped 1) (extended 1)

theorem default_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    defaultRequest context := .default rfl rfl


private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member
    simp [context, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [context, SourceSemantics.Context.ofSignatures] at member

theorem first_arm_context : CompatiblePatternLeaves.ContextValid compilation (armContext 0) :=
  CompatibleMatchContextFactory.of_context
    (CompatibleMatchContextFactory.scoped_context first_scoped valid)
    first_scoped.closed_fields.1 rfl rfl

theorem second_arm_context : CompatiblePatternLeaves.ContextValid compilation (armContext 1) :=
  CompatibleMatchContextFactory.of_context
    (CompatibleMatchContextFactory.scoped_context second_scoped valid)
    second_scoped.closed_fields.1 rfl rfl

theorem default_context : CompatiblePatternLeaves.ContextValid compilation context :=
  CompatibleMatchContextFactory.of_context
    (CompatibleMatchContextFactory.scoped_context default_scoped valid) rfl rfl rfl

/-- Both ordinary declarations and for initializers use this same independent
binder extension. Its local table differs while the ledger stays fixed. -/
theorem after_let_or_for_initializer (index : Nat) :
    CompatibleExpressionLiterals.ContextValid [] (armContext index) [] ∧
      CompatiblePatternLeaves.ContextValid compilation (armContext index) := by
  have extendedValid := CompatibleMatchMeaning.valid_binders [] valid (extended index)
  exact ⟨extendedValid, CompatibleMatchContextFactory.of_context extendedValid
    (extended index).signatures_eq rfl rfl⟩

/-- Equal value catalogs do not authenticate an unrelated, unused ledger. -/
theorem different_ledger_not_authenticated (entry : SolvedRequirement) :
    ¬ CompatiblePatternLeaves.ContextValid { compilation with solvedRequirements := [entry] } context := by
  intro wrong
  have ledger := wrong.ledger
  cases ledger

end Tests.SourceCoreGenericImperativeMatchReadyFactory

namespace Tests.SourceCoreGenericImperativeMatchReadyFactory.ActualPolicy
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GenericImperativeMatch GenericImperativeMatch.Tree
open TypedLexicalWhile (absentRequest initializedRequest)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : GenericImperativeMatch.ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {solved : List SolvedRequirement} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The concrete compatible loop policy fixes the compilation ledger; the
actual match receipt, ordered child scopes and existing errors feed Ready.
There is no caller-supplied pattern context or runtime child contract. -/
theorem actual_fixed_match_ready
      {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
      {found : source.lookupStatement? id = some node}
      (form : node.form = .matchWith resolution)
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values}
      (sameDefinitions : compilation.definitions = definitions)
      {allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError))}
      {requests : List GenericMatchChildren.Request}
      {receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched}
      {ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt}
      {children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      {childErrors : ∀ request member childContext valid, Errors registry faults (children request member childContext valid)}
      {remainingErrors : Errors registry faults remaining}
      (childLedgers : ∀ request member childContext related, SiteLedgers solved registry faults (childErrors request member childContext related))
      (remainingErrorsLedger : SiteLedgers solved registry faults remainingErrors)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreCompatibleDataMatches.ExpressionLowerer)
    (fixed : compilation = ⟨values, solved,
      some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)),
      some definitions⟩)
    {evidence : Dynamic.EvidenceEnvironment}
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures) :
    (SourceCoreCompatibleDataMatches.loopPolicy values solved assignments diagnostics owner expression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions)).lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons compilation) ∧
    Ready registry faults (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
      sameValues sameDefinitions allocator requests receipt ordinary children remaining) := by
  have policy := CompatibleMatchContextFactory.fixed_policy contextValid signatures assignments diagnostics owner expression
    (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
    (some definitions)
  have sameLedger : compilation.solvedRequirements = solved := by rw [fixed]
  refine ⟨by simpa only [fixed] using policy.1, ?_⟩
  exact (@SiteLedgers.matchWith layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved registry faults context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining childErrors remainingErrors sameLedger childLedgers remainingErrorsLedger).ready contextValid signatures

end Tests.SourceCoreGenericImperativeMatchReadyFactory.ActualPolicy
