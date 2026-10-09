import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnSiteShells
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts

/-! Literal shells retain the original issued diagnostic preparation while
using its unchanged place and assignment providers in the actual compiler table. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralPlaceDiagnosticShells
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedLiteralReturnSiteShells

/-- These are the literal place providers; root-table receivers are independent. -/
def PlaceReasonsEq (first second : SourceCoreDataPlaceFaultSites.Program) : Prop :=
  ∀ owner site binder missingType,
    first.placeReason owner site binder missingType = second.placeReason owner site binder missingType

theorem PlaceReasonsEq.function_eq {first second : SourceCoreDataPlaceFaultSites.Program}
    (same : PlaceReasonsEq first second) : first.placeReason = second.placeReason := by
  funext owner site binder missingType
  exact same owner site binder missingType

/-- Changing the receiving table preserves every original place token. -/
theorem placeReasons_rootTable (program : SourceCoreDataPlaceFaultSites.Program)
    (table : SourceCoreFaultSites.Table) : PlaceReasonsEq program {program with rootTable := table} := by
  intro owner site binder missingType
  rfl

/-- Equality of the retained place inventory is enough for the exact provider. -/
theorem placeReasons_of_places {first second : SourceCoreDataPlaceFaultSites.Program}
    (same : first.places = second.places) : PlaceReasonsEq first second := by
  intro owner site binder missingType
  simp only [SourceCoreDataPlaceFaultSites.Program.placeReason, same]

/-- The sealed compiler's actual optional callable replacement preserves the provider. -/
theorem placeReasons_of_lowered {compiled : SourceCoreUnifiedCompilation.Compiled}
    (diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked))
    {lowered : SourceCoreDataPlaceFaultSites.Program}
    (actual : lowered = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}) :
    PlaceReasonsEq diagnostics.program lowered := by
  rw [actual]
  cases compiled.indexed.base.callableContext
  · intro owner site binder missingType; rfl
  · exact placeReasons_rootTable _ _

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

section Diagnostics
variable (issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named))

private theorem missing_policy
    (samePlaces : PlaceReasonsEq issued.diagnostics.program produced.diagnostics) :
    issued.missingDefault = fun site root type =>
      produced.diagnostics.placeReason (context compiled.indexed caller.named).owner site root (some type) := by
  funext site root type
  change issued.diagnostics.program.placeReason produced.site.code.compilation.owner site root (some type) = _
  rw [samePlaces.function_eq, produced.site.compilation]

/-- The diagnostic rows are the literal rows used by the selected body callback. -/
theorem assignment_policy
    (sameAssignments : issued.assignments = produced.compilation.own.assignments)
    (samePlaces : PlaceReasonsEq issued.diagnostics.program produced.diagnostics) :
    CompatibleAssignmentStatements.AssignmentPolicy (bodyPolicy produced.compilation produced.site.code)
      (.initial compiled.compatible.checked) issued.invalidProjection issued.invalidOperand issued.missingDefault := by
  have missing := missing_policy produced issued samePlaces
  refine ⟨read_policy produced, ?_, ?_⟩
  · rw [missing]
    dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidOperand]
    simp only [sameAssignments, samePlaces.function_eq, produced.site.compilation]
    rfl
  · rw [missing]
    dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidOperand]
    simp only [sameAssignments, samePlaces.function_eq, produced.site.compilation]
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl

/-- The original unary callback uses those same genuine issued tokens. -/
theorem unary_policy
    (sameAssignments : issued.assignments = produced.compilation.own.assignments)
    (samePlaces : PlaceReasonsEq issued.diagnostics.program produced.diagnostics) :
    CompatibleBitNotStatements.Policy (bodyPolicy produced.compilation produced.site.code)
      (.initial compiled.compatible.checked) issued.invalidProjection issued.invalidUnary issued.missingDefault := by
  have missing := missing_policy produced issued samePlaces
  unfold CompatibleBitNotStatements.Policy
  rw [missing]
  dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidUnary]
  simp only [sameAssignments, samePlaces.function_eq, produced.site.compilation]
  rfl
end Diagnostics

section Shell
variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : LiteralRootReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- These are actual Source rows, initial frame fields and compiler identities.
The original issued preparation remains intact across receiving root-table changes. -/
structure PlaceDiagnosticBodyInputs where
  issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named)
  sameAssignments : issued.assignments = produced.compilation.own.assignments
  placeReasons : PlaceReasonsEq issued.diagnostics.program produced.diagnostics
  samePolicy : produced.site.code.policy = root.root.selected.policy
  canonical : produced.site.code.view = source caller.named
  typed : ExpressionHasType (source caller.named) sourceContext id produced.site.code.sourceNode.type
  lambdaCoercions : produced.site.code.sourceNode.coercions = []
  signatures : sourceContext.signatures = compiled.compatible.checked.signatures
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named)
  covers : evidence.Covers sourceContext
  kinds : ∀ binder ∈ parameters,
    (source caller.named).inputs.any (fun input => decide (input.id = binder.id)) = false
  declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext
  ledger : sourceContext.solvedRequirements = (context compiled.indexed caller.named).solvedRequirements
  statement : StatementId
  statementNode : StatementNode
  expression : ExpressionId
  expressionNode : ExpressionNode
  singleton : statements = [statement]
  statementFound : (source caller.named).lookupStatement? statement = some statementNode
  statementForm : statementNode.form = .returnStmt (some expression)
  statementOwner : statement.occurrence.owner = (source caller.named).owner
  statementCore : Ty
  statementProjected : SourceCoreCompatibleDataExpressions.projectType compiled.compatible.checked
    (.occurrence statement.occurrence) statementNode.type = .ok statementCore
  expressionFound : (source caller.named).lookupExpression? expression = some expressionNode
  atomic : CompatibleExpressionLiterals.Atomic expressionNode.form
  unitType : expressionNode.form = .tuple [] → expressionNode.type = .unit
  owned : List RequirementId
  ordinaryRequirements : SourceCompilationPlan.ordinaryOwnedRequirements? expressionNode = some owned
  literalCoercions : expressionNode.coercions = []
  literalRequirements : expressionNode.requirements = [] ∨
    ∃ literal resolution, expressionNode.form = .integerLiteral literal resolution
  initializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = expression)) = none
  noMatches : ∀ statement node, (source caller.named).lookupStatement? statement = some node →
    ∀ resolution, node.form ≠ .matchWith resolution

variable (inputs : PlaceDiagnosticBodyInputs produced root)

/-- The selected literal occurrence is the exact approved static domain. -/
def approved : TypedSource → ExpressionId → Prop := fun _ candidate => candidate = inputs.expression

/-- Genuine Source typing and the same accepted compiler recipe populate one literal-return shell. -/
theorem literal_shell (readFuel : Nat) : Nonempty (SiteShell (approved produced root inputs) produced) := by
  let code := produced.site.code
  have literalFound : code.view.lookupExpression? inputs.expression = some inputs.expressionNode := inputs.canonical.symm ▸ inputs.expressionFound
  have canonical : code.view = source caller.named := inputs.canonical
  have unique := inputs.runtime.graph.nodeOccurrencesUnique
  have facts := CallableIndexedOwnedOrdinaryLambdaSourceFacts.Produced.source_facts caller produced unique
    inputs.typed inputs.lambdaCoercions
  have frame := facts.frame inputs.runtime inputs.covers
  have kinds : ∀ binding ∈ code.receipt.loweredParameters,
      (source caller.named).inputs.any (fun input => decide (input.id = binding.1.id)) = false := by
    intro binding member
    apply inputs.kinds binding.1
    change binding.1 ∈ (closure caller.named parameters result statements sourceContext evidence []).parameters
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code]
    exact List.mem_map.mpr ⟨binding, member, rfl⟩
  obtain ⟨entry, finalContext, bodyFacts, bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts (values := .initial compiled.compatible.checked) code facts kinds (reference_index produced)
  have fields := (CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_runtime (values := .initial compiled.compatible.checked) entry frame).1
  have declarations := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_declarations (values := .initial compiled.compatible.checked) code entry facts inputs.declarations
  change CompatibleExpressionReads.ScopeDeclarations (source caller.named)
    (code.receipt.loweredParameters.reverse.map (fun binding : TypedBinder × Ty => (binding.1.id, binding.2)) ++ scope) entry.context at declarations
  have bodyTyped : StatementsHaveType (source caller.named) {returnType := result}
      entry.context [inputs.statement] finalContext bodyFacts := by
    change StatementsHaveType (source caller.named) {returnType := result} entry.context statements finalContext bodyFacts at bodyTyped
    simpa only [inputs.singleton] using bodyTyped
  have syntaxTree := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.return_syntax unique inputs.statementFound
    inputs.statementForm bodyTyped (show approved produced root inputs (source caller.named) inputs.expression from rfl)
  have syntaxTree : GenericImperativeMatch.Syntax (source caller.named) (approved produced root inputs (source caller.named))
      entry.context (.statements true statements) result := by simpa only [inputs.singleton] using syntaxTree
  have projected := code.receipt.resultProjected
  rw (occs := .pos [1]) [inputs.samePolicy] at projected
  rw (occs := .pos [1]) [root.root.projectType] at projected
  have projection := CompatibleExpressionReads.projectType_of_accepted projected
  have referenceRead : (bodyPolicy produced.compilation code).readStatement code.view inputs.statement =
      .ok (inputs.statementNode, inputs.statementCore) := by
    rw [read_policy produced, canonical]
    simp [SourceCoreCompatibleDataExpressions.readStatement, inputs.statementOwner, inputs.statementFound, inputs.statementProjected]
    rfl
  have accepted := body_accepted produced
  conv at accepted => lhs; arg 5; rw [inputs.singleton]
  have policyAt := literal_policy root.root (childSource := code.view)
    (childScope := code.receipt.loweredParameters.reverse.map (fun binding : TypedBinder × Ty => (binding.1.id, binding.2)) ++ scope)
    (reasonAt := code.reasonAt) literalFound
    inputs.atomic inputs.ordinaryRequirements inputs.literalCoercions inputs.literalRequirements inputs.initializer
  have special : ∀ child budget, (match code.policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower code.compilation child budget code.view
        (code.receipt.loweredParameters.reverse.map (fun binding : TypedBinder × Ty => (binding.1.id, binding.2)) ++ scope)
        inputs.expression code.reasonAt) = .ok none := by
    rw (occs := .pos [1]) [inputs.samePolicy]
    rw (occs := .pos [1]) [produced.site.compilation]
    exact policyAt.special
  have actualRead : code.policy.readExpression code.view inputs.expression =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked code.view inputs.expression :=
    inputs.samePolicy.symm ▸ policyAt.read
  have actualLeaf : code.policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer (.initial compiled.compatible.checked) :=
    (congrArg SourceCoreFunctions.Policy.leafLowerer inputs.samePolicy).trans root.leaf
  have nativeTyped := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.literal_body_native
    (show (bodyPolicy produced.compilation code).lowerExpression = FunctionCode.children code.policy code.lowerBody code.fuel code.compilation from rfl)
    referenceRead inputs.statementForm accepted literalFound
    inputs.atomic inputs.unitType special actualRead actualLeaf compiled.indexed.layouts.definitions
    (SourceCoreLocalCell.coreContext (code.receipt.loweredParameters.reverse.map (fun binding : TypedBinder × Ty => (binding.1.id, binding.2)) ++ scope) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
  refine ⟨{
    issued := inputs.issued
    diagnosticPolicy := .reachable
    entry := entry
    frame := frame
    readFuel := readFuel
    canonical := canonical
    unique := unique
    sameLedger := ?_
    syntaxTree := syntaxTree
    projection := projection
    residualMode := true
    nativeTyped := nativeTyped
    static := {
      matchCompilation := ambientMatch produced
      matchPolicy := match_policy produced
      matchValues := rfl
      matchDefinitions := ?_
      matchAllocator := ?_
      hidden := ?_
      readPolicy := read_policy produced
      binderPolicy := ?_
      allocationPolicy := allocation_policy produced root.root inputs.samePolicy
      assignments := assignment_policy produced inputs.issued inputs.sameAssignments inputs.placeReasons
      unaries := unary_policy produced inputs.issued inputs.sameAssignments inputs.placeReasons
      assignmentNative := ?_
      closed := ?_
      residual := ?_
      sourceSignatures := ?_
      declarations := ?_
      ledger := ?_ } }⟩
  · rw [produced.site.compilation]
    exact inputs.ledger
  · rfl
  · exact allocation_policy produced root.root inputs.samePolicy
  · intro statement node resolution found form
    rw [canonical] at found
    exact (inputs.noMatches statement node found resolution form).elim
  · intro currentScope binder monomorphic
    exact binder_policy produced binder currentScope monomorphic
  · intro currentContext currentScope fuel candidate lowered _closed _residual _signatures _declarations allowed node found _typed generated
    change candidate = inputs.expression at allowed
    subst candidate
    have sameNode : node = inputs.expressionNode := Option.some.inj (found.symm.trans literalFound)
    subst node
    have currentPolicy := literal_policy root.root (childSource := code.view) (childScope := currentScope) (reasonAt := code.reasonAt)
      literalFound inputs.atomic inputs.ordinaryRequirements
      inputs.literalCoercions inputs.literalRequirements inputs.initializer
    have currentSpecial : ∀ child budget, (match code.policy.lowerSpecial? with
        | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
        | some lower => lower code.compilation child budget code.view currentScope inputs.expression code.reasonAt) = .ok none := by
      rw (occs := .pos [1]) [inputs.samePolicy]
      rw (occs := .pos [1]) [produced.site.compilation]
      exact currentPolicy.special
    exact (CallableIndexedOwnedLiteralReturnLambdaStaticFacts.literal_expression_native
      found inputs.atomic inputs.unitType currentSpecial (inputs.samePolicy.symm ▸ currentPolicy.read) actualLeaf generated
      compiled.indexed.layouts.definitions (SourceCoreLocalCell.coreContext currentScope ++
        RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)).2
  · exact fields.typeVariables.trans frame.code.variables_closed
  · exact fields.residualTypeVariables.trans frame.code.residual_variables_open
  · exact fields.signatures.trans inputs.signatures
  · change CompatibleExpressionReads.ScopeDeclarations code.view
      (code.receipt.loweredParameters.reverse.map (fun binding : TypedBinder × Ty => (binding.1.id, binding.2)) ++ scope) entry.context
    rw (occs := .pos [1]) [canonical]
    exact declarations
  · exact fields.solvedRequirements.trans inputs.ledger

section Domain
open RecursiveNamedExpressionCompilerCertificates
open RecursiveNamedCallSelectionCertificates CallableAncestryPairedLookup
open CallableIndexedOwnedPreparedMixedCompilerHeads (extraForm extraChildren)
open CallableIndexedOwnedPreparedMixedCompilerCertificates (ExtraMetadata baseAdmitted)

private theorem literal_node {candidate : ExpressionId} {node : ExpressionNode}
    (allowed : approved produced root inputs (source caller.named) candidate)
    (found : (source caller.named).lookupExpression? candidate = some node) :
    node = inputs.expressionNode := by
  change candidate = inputs.expression at allowed
  subst candidate
  exact Option.some.inj (found.symm.trans inputs.expressionFound)

private theorem atomic_children {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form) :
    evaluationChildren form = [] := by
  cases atomic <;> rfl

private theorem atomic_not_extra {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form) :
    ¬ extraForm form := by
  cases atomic <;> simp only [extraForm, not_false_eq_true]

/-- The actual literal row is admitted without selecting any unrelated Source node. -/
theorem literal_admission : AdmissionWith extraForm extraChildren (source caller.named)
    (approved produced root inputs (source caller.named)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro candidate allowed
    change candidate = inputs.expression at allowed
    subst candidate
    exact ⟨inputs.expressionNode, inputs.expressionFound⟩
  · intro candidate node allowed found
    have same := literal_node produced root inputs allowed found
    subst node
    change candidate = inputs.expression at allowed
    subst candidate
    exact .inl (.fragment (.fragment (.fragment (.fragment (.fragment
      (.primitive (.product (.literal inputs.expressionFound inputs.atomic))))))))
  · intro candidate node allowed found child member
    have same := literal_node produced root inputs allowed found
    subst node
    rw [atomic_children inputs.atomic] at member
    cases member
  · intro candidate node allowed found extra child member
    have same := literal_node produced root inputs allowed found
    subst node
    exact (atomic_not_extra inputs.atomic extra).elim

/-- The bounded compiler domain is built from the literal's actual fields.
Its read budget is the fixed original representation budget. -/
theorem literal_domain {currentContext : SourceSemantics.Context}
    {currentScope : SourceCoreLocalCell.Scope}
    {headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram)}
    (globals : LiteralDomainGlobals root currentContext currentScope headers) :
    DomainAt root.root (approved produced root inputs) compiled.indexed.fuel currentContext evidence currentScope headers := by
  have pointwise := literal_policy root.root (childSource := source caller.named)
    (childScope := currentScope) (reasonAt := rootReasonAt) inputs.expressionFound
    inputs.atomic inputs.ordinaryRequirements inputs.literalCoercions inputs.literalRequirements inputs.initializer
  refine {
    namedLedger := globals.namedLedger
    admission := literal_admission produced root inputs
    coverage := {plan := rfl, ordered := globals.headerOrder, slots := ?_}
    sourceTypes := globals.sourceTypes
    emptyEvidence := ?_
    order := ?_
    constructorValid := ?_
    fragmentValid := globals.fragmentValid
    selectedValid := ?_
    basePolicy := {
      fragment := ⟨globals.fragmentSpecial, globals.fragmentRead, root.lowerRead, root.leaf⟩
      route := ?_
      read := ?_ }
    fragmentCoercions := globals.fragmentCoercions
    coercions := ?_
    metadata := {empty := ?_, ordinary := ?_, arguments := ?_}
    profile := globals.profile
    native := ?_
    shells := ?_ }
  · intro policy candidate node callee arguments instantiation index signature specialized allowed found form _selected _exactRecord
    have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
    rw [form] at atomic
    cases atomic
  · intro candidate node callee arguments instantiation header policy index signature allowed found form
    have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
    rw [form] at atomic
    cases atomic
  · intro candidate callee arguments instantiation node allowed found form
    have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
    rw [form] at atomic
    cases atomic
  · intro candidate node instantiation arguments allowed found form
    have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
    rw [form] at atomic
    cases atomic
  · intro candidate node callee arguments instantiation header policy index signature allowed found form
    have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
    rw [form] at atomic
    cases atomic
  · intro candidate node allowed _found
    have same : candidate = inputs.expression := allowed.1
    subst candidate
    exact .inl pointwise.special
  · intro candidate allowed
    have same : candidate = inputs.expression := allowed.1
    subst candidate
    exact pointwise.read
  · intro candidate node allowed found
    exact (literal_node produced root inputs allowed found).symm ▸ inputs.literalCoercions
  · intro candidate node allowed found extra
    have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
    exact (atomic_not_extra atomic extra).elim
  · intro candidate node allowed found extra
    have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
    exact (atomic_not_extra atomic extra).elim
  · intro candidate node callee arguments metadata allowed found form
    have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
    rw [form] at atomic
    cases atomic
  · intro childFuel candidate node parameters result statements lowered allowed found form
    have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
    rw [form] at atomic
    cases atomic
  · intro childFuel candidate node parameters result statements lowered allowed found form
    have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
    rw [form] at atomic
    cases atomic

end Domain

end Shell

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralPlaceDiagnosticShells
