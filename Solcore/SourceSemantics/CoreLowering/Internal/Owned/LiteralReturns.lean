import Solcore.SourceSemantics.CoreLowering.Internal.Owned.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.TerminalStatementOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.PublicExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.SourceDiagnosticTyping
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.ScalarReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedOperators
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StatementAdmission
import Solcore.SourceSemantics.Staging.RecursiveProfile
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.ExpressionTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies

/-!
# Owned callables: literal returns and principal lambdas

Static facts and site shells of literal returns, issued diagnostics, and expression heads of principal lambdas.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnLambdaStaticFacts
/-! Finite static facts for an actual ordinary lambda with a literal return.
The existing Source typing and accepted compiler actions supply entry, syntax,
and native typing independently of body execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnLambdaStaticFacts
open Core Frontend SourceInference

/-- The original lambda typing exposes its genuine parameter context. -/
theorem entry_of_source_facts
    {values : SourceCoreCompatibleValues.Context} {prepared : CallableIndexedLambdaValues.Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code prepared function scope administrative)
    {id : ExpressionId} {node : ExpressionNode}
    (facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function id node)
    (kinds : ∀ binding ∈ code.receipt.loweredParameters,
      function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (referenceIndex : code.referenceIndex = scope.length + 1 + prepared.base.globals.length) :
    ∃ entry : CallableIndexedLambdaEntryPrefix.Context code, ∃ finalContext bodyFacts,
      StatementsHaveType function.source {returnType := function.resultType}
        entry.context function.body finalContext bodyFacts ∧
      BodyCompletes function.resultType bodyFacts := by
  have typing := facts.typing
  rw [facts.form] at typing
  generalize rawTypeEq : FunctionValues.sourceType function = raw at typing
  cases typing with
  | lambda namesUnique extended bodyTyped completes =>
    exact ⟨⟨_, _, extended, kinds, referenceIndex⟩, _, _, bodyTyped, completes⟩

/-- Lambda binders are declarations at this actual Source occurrence. -/
theorem parameter_declared {function : Dynamic.Closure} {id : ExpressionId} {node : ExpressionNode}
    (facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function id node)
    {binder : TypedBinder} (member : binder ∈ function.parameters) :
    binder ∈ SourceCoreDataPlaces.declaredBinders function.source := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨.expression node, facts.contains.1, ?_⟩
  simpa only [facts.form] using member

/-- Parameter installation uses the existing Source declaration producer. -/
theorem entry_declarations
    {values : SourceCoreCompatibleValues.Context} {prepared : CallableIndexedLambdaValues.Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code prepared function scope administrative)
    (entry : CallableIndexedLambdaEntryPrefix.Context code)
    {id : ExpressionId} {node : ExpressionNode}
    (facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function id node)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context) :
    CompatibleExpressionReads.ScopeDeclarations function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      entry.context := by
  have extended := entry.extended
  rw [CallableIndexedLambdaEntryPrefix.parameters code] at extended
  have declared : ∀ binding, binding ∈ code.receipt.loweredParameters →
      binding.1 ∈ SourceCoreDataPlaces.declaredBinders function.source := by
    intro binding member
    apply parameter_declared facts
    rw [CallableIndexedLambdaEntryPrefix.parameters code]
    exact List.mem_map.mpr ⟨binding, member, rfl⟩
  have installed := RecursiveNamedHeaderScopeDeclarations.parameters declared extended declarations
  simpa only [List.foldl_flip_cons_eq_append, List.map_reverse] using installed

/-- Entry extension retains the full nonlocal context and covering evidence. -/
theorem entry_runtime
    {values : SourceCoreCompatibleValues.Context} {prepared : CallableIndexedLambdaValues.Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : CallableIndexedLambdaValues.Code prepared function scope administrative}
    (entry : CallableIndexedLambdaEntryPrefix.Context code) {program : Program}
    (frame : Dynamic.ClosureFrame program function) :
    Dynamic.RuntimeContextFields function.context entry.context ∧
      Dynamic.SourceRuntimeValid program entry.context function.source ∧
      function.evidence.Covers entry.context := by
  exact ⟨Dynamic.MonoBindersExtend.runtimeContextFields entry.extended,
    CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame entry.extended⟩

private theorem statement_reported {source : TypedSource} {control : ControlContext}
    {context finalContext : SourceSemantics.Context} {statement : StatementId} {facts : StatementFacts}
    (typed : StatementHasType source control context statement finalContext facts) :
    ∃ node, ContainsStatement source statement node ∧ node.type = facts.type := by
  cases typed <;> exact ⟨_, by assumption, by assumption⟩

/-- Singleton return syntax is derived from the original statement judgment. -/
theorem return_syntax {source : TypedSource} {context finalContext : SourceSemantics.Context}
    {statement : StatementId} {node : StatementNode} {expression : ExpressionId}
    {result : TypeSystem.Ty} {bodyFacts : BodyFacts} {approved : ExpressionId → Prop}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression))
    (typed : StatementsHaveType source {returnType := result} context [statement] finalContext bodyFacts)
    (allowed : approved expression) :
    GenericImperativeMatch.Syntax source approved context (.statements true [statement]) result := by
  cases typed with
  | singleton head =>
    obtain ⟨reported, reportedContains, reportedType⟩ := statement_reported head
    have sameReported : reported = node := Option.some.inj
      ((lookupStatement?_complete unique reportedContains).symm.trans found)
    subst reported
    obtain ⟨controlNode, controlContains, controlTyped⟩ := Dynamic.StatementHasType.controlFormTyping head
    have sameControl : controlNode = node := Option.some.inj
      ((lookupStatement?_complete unique controlContains).symm.trans found)
    subst controlNode
    rw [form] at controlTyped
    cases controlTyped
    obtain ⟨actual, actualContains, actualTyped⟩ := Dynamic.StatementHasType.formTyping head
    have sameActual : actual = node := Option.some.inj
      ((lookupStatement?_complete unique actualContains).symm.trans found)
    subst actual
    rw [form] at actualTyped
    cases actualTyped with
    | returnValue expressionTyped =>
      obtain ⟨expressionNode, expressionContains, expressionType⟩ := expressionTyped.stored_type
      exact .body (.returnValue [] found form reportedType
        (lookupExpression?_complete unique expressionContains) expressionType
        (expressionType.symm ▸ expressionTyped) allowed)

/-- Literal-only approval excludes indirect calls at the same lookup row. -/
theorem literal_not_indirect {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (atomic : CompatibleExpressionLiterals.Atomic node.form) :
    CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn source (fun candidate => candidate = id) := by
  intro candidate actual callee ids metadata allowed selected
  subst candidate
  have same : actual = node := Option.some.inj (selected.symm.trans found)
  subst actual
  generalize nodeForm : node.form = shape at atomic
  cases atomic <;> intro impossible <;> cases impossible

/-- A real accepted literal child is typed at every administrative context.
The numeric validator and ordinary compiler fields remain authentic inputs. -/
theorem literal_expression_native
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {expressionBudget childBudget : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (atomic : CompatibleExpressionLiterals.Atomic node.form)
    (unitType : node.form = .tuple [] → node.type = .unit)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : FunctionCode.children policy lowerBody expressionBudget compilation
      childBudget source scope id reasonAt = .ok lowered)
    (definitions : DataEnvironment) (context : Core.Context) :
    lowered.type.WellFormed definitions ∧
      HasType context lowered.expression (LanguageResult.resultType lowered.type) definitions := by
  obtain ⟨_, _, literal⟩ := CompatibleExpressionLiterals.of_functions
    found atomic unitType special readPolicy leafPolicy accepted
  exact CompatibleExpressionScalarNativeTyping.literal_native literal definitions context

/-- The accepted literal callback supplies native body typing under any actual
administrative context. No scope typing or completed body law is needed. -/
theorem literal_body_native
    {policy : SourceCoreLoops.Policy} {expressions : SourceCoreFunctions.Policy}
    {lowerBody : SourceCoreFunctions.BodyLowerer} {expressionBudget : Nat}
    {compilation : SourceCoreFunctions.Context} {fuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statement : StatementId} {node : StatementNode}
    {type : Ty} {expression : ExpressionId} {expressionNode : ExpressionNode} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (callback : policy.lowerExpression = FunctionCode.children expressions lowerBody expressionBudget compilation)
    (read : policy.readStatement source statement = .ok (node, type))
    (form : node.form = .returnStmt (some expression))
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope [statement] result reasonAt fellThrough escaped = .ok code)
    (found : source.lookupExpression? expression = some expressionNode)
    (atomic : CompatibleExpressionLiterals.Atomic expressionNode.form)
    (unitType : expressionNode.form = .tuple [] → expressionNode.type = .unit)
    (special : ∀ child budget, (match expressions.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope expression reasonAt) = .ok none)
    (readPolicy : expressions.readExpression source expression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source expression)
    (leafPolicy : expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (definitions : DataEnvironment) (context : Core.Context) :
    HasType context code (LanguageResult.resultType result) definitions := by
  obtain ⟨budget, lowered, generated, same, emitted⟩ :=
    CallableIndexedLambdaScalarNativeTyping.scalar_body_receipt read (.inl form) accepted
  rw [callback] at generated
  obtain ⟨wellFormed, typed⟩ := literal_expression_native
    found atomic unitType special readPolicy leafPolicy generated definitions context
  rw [same] at wellFormed typed
  rw [emitted]
  apply LocalControl.finish_hasType wellFormed
    (LocalLoop.toControl_hasType escaped wellFormed (LocalLoop.returnValue_hasType wellFormed typed))
  split
  · rename_i unitResult
    simpa only [unitResult] using
      (LanguageResult.success_hasType (HasType.unit (definitions := definitions) (context := context)))
  · exact LanguageResult.failure_hasType wellFormed .word

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnLambdaStaticFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnSiteShells
/-! Literal return bodies populate the static shell at one actual selected Site.
The contextual policy fields come from that Site's original body recipe. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnSiteShells
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedContextualCompilerPolicyProfiles

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

/-- This is the actual match callback context, before extending only definitions. -/
def baseMatch : SourceCoreCompatibleDataMatches.Context :=
  ⟨.initial compiled.compatible.checked,
    (context compiled.indexed caller.named).solvedRequirements,
    (bodyPolicy produced.compilation produced.site.code).sourceCells, none⟩

/-- The original callback is kept under the final indexed definition table. -/
def ambientMatch : SourceCoreCompatibleDataMatches.Context :=
  CompatibleMatchAmbientLowering.withDefinitions (baseMatch produced) compiled.indexed.layouts.definitions

theorem match_policy : CompatibleMatchAmbientLowering.PolicySuccess
    (bodyPolicy produced.compilation produced.site.code) (ambientMatch produced) := by
  apply CompatibleMatchAmbientLowering.PolicySuccess.extend
    (compilation := baseMatch produced)
  · rfl
  · exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

theorem read_policy : (bodyPolicy produced.compilation produced.site.code).readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := rfl

theorem binder_policy (binder : TypedBinder) (childScope : SourceCoreLocalCell.Scope)
    (monomorphic : binder.scheme.quantified = []) :
    (bodyPolicy produced.compilation produced.site.code).lowerBinder
      produced.site.code.view childScope binder =
    SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked
      produced.site.code.view childScope binder := by
  change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
  simp only [SourceCoreGeneralFunctions.contextualBinder, monomorphic, List.isEmpty_nil, ↓reduceIte]
  rfl

/-- One actual contextual compiler bind keeps the root policy and its literal leaf callback together. -/
structure LiteralRootReceipt (named : Named)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    fuel source scope id reasonAt lowered
  leaf : root.selected.policy.leafLowerer =
    SourceCoreCompatibleDataExpressions.leafLowerer (.initial compiled.compatible.checked)
  lowerRead : root.selected.policy.lowerRead =
    SourceCoreCompatibleDataExpressions.lowerRead compiled.indexed.fuel (.initial compiled.compatible.checked)

/-- The literal root companion is selected once from the original accepted action. -/
def LiteralRootReceipt.of_accepted
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) source scope id reasonAt = .ok lowered) :
    LiteralRootReceipt (compiled := compiled) named diagnostics namedCode compilation
      fuel source scope id reasonAt lowered := by
  rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  dsimp only at accepted
  change (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key
    |>.mapError SourceCoreBasic.Error.callPreparation) >>= _ = .ok lowered at accepted
  rw [record] at accepted
  simp only [Except.mapError, bind, Except.bind] at accepted
  exact ⟨⟨⟨_, _, accepted, rfl, rfl, _, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, by funext lambda; simp⟩⟩, rfl, rfl⟩

section Root
variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- The real selected policy and the Site's allocator profile identify one allocator. -/
theorem allocation_policy (samePolicy : produced.site.code.policy = root.selected.policy) :
    (bodyPolicy produced.compilation produced.site.code).sourceCells = some
      (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
        compiled.indexed.base.globals.length
        (compiled.indexed.layouts.allocatorAt produced.site.code.compilation.owner produced.site.code.active
          produced.site.code.allocationError)) := by
  have actual : (bodyPolicy produced.compilation produced.site.code).sourceCells = root.selected.policy.sourceCells := by
    rw [root.sourceCells]
    rfl
  exact actual.trans ((congrArg SourceCoreFunctions.Policy.sourceCells samePolicy).symm.trans
    produced.site.code.allocationProfile)
/-- The literal's authentic raw metadata closes the original evidence and initializer gates. -/
theorem literal_policy
    {childSource : TypedSource} {childScope : SourceCoreLocalCell.Scope} {childId : ExpressionId}
    {reasonAt : ExpressionId → Word} {node : ExpressionNode} {owned : List RequirementId}
    (found : childSource.lookupExpression? childId = some node)
    (atomic : CompatibleExpressionLiterals.Atomic node.form)
    (ordinaryRequirements : SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned)
    (coercions : node.coercions = [])
    (requirements : node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution)
    (initializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = childId)) = none) :
    PointwiseFor root childSource childScope childId reasonAt := by
  have actualSource : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed caller.named).plan compiled.indexed.base.locals
      (context compiled.indexed caller.named).owner none childSource childId = .ok childSource := by
    generalize shape : node.form = form at atomic
    cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, found, shape]
  constructor
  · rw [root.selected.readExpression]
    simp only [actualSource, bind, Except.bind]
    rw [CallableIndexedOwnedIndirectCompilerPolicyInputs.representation_read]
  · intro child budget
    rw [root.selected.special_eq, root.selected.special_body]
    have evidenceNone : SourceCoreEvidence.lowerWithProjector compiled.indexed.base.sourceProgram
        ((representation compiled.indexed).atContext caller.named.signature.key []).expressions.projectType
        caller.named.specialized (context compiled.indexed caller.named) child budget childSource childScope
        childId reasonAt (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []) = .ok none := by
      rcases requirements with empty | ⟨literal, resolution, native⟩
      · generalize shape : node.form = form at atomic
        cases atomic <;> simp [SourceCoreEvidence.lowerWithProjector, found, shape, ordinaryRequirements, coercions, empty]
      · simp [SourceCoreEvidence.lowerWithProjector, found, native, ordinaryRequirements, coercions]
    simp only [actualSource, bind, Except.bind, found, pure, Except.pure, initializer,
      Option.filter_none, evidenceNone]
    generalize shape : node.form = form at atomic
    cases atomic <;> rfl

end Root


/-- The selected parameter compiler supplies the actual extended body scope. -/
theorem body_scope : produced.site.code.receipt.bodyScope =
    produced.site.code.receipt.loweredParameters.reverse.map (fun binding : TypedBinder × Ty => (binding.1.id, binding.2)) ++ scope := by
  simpa only [List.map_reverse] using
    (FunctionCode.Parameters.of_accepted produced.site.code.receipt.parametersCompiled).scope

/-- Body acceptance comes from the same chosen certificate and retained recipe. -/
theorem body_accepted : SourceCoreLoops.lowerStatementsWithPolicy
    (bodyPolicy produced.compilation produced.site.code) produced.site.code.fuel produced.site.code.view
    (produced.site.code.receipt.loweredParameters.reverse.map (fun binding : TypedBinder × Ty => (binding.1.id, binding.2)) ++ scope)
    statements produced.site.code.receipt.resultCore produced.site.code.reasonAt
    produced.site.code.compilation.internalReason produced.site.code.compilation.internalReason =
    .ok produced.site.code.receipt.body := by
  have actual := produced.site.code.receipt.bodyCompiled
  rw [callback_of_recipe produced.compilation produced.recipe, body_scope produced] at actual
  exact actual

/-- The administrative reference keeps the original named compiler layout. -/
theorem reference_index : produced.site.code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  unfold Code.referenceIndex
  rw [produced.site.compilation]
  rfl


section Diagnostics
variable (issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named))

private theorem missing_policy
    (sameDiagnostics : issued.diagnostics.program = produced.diagnostics) :
    issued.missingDefault = fun site root type =>
      produced.diagnostics.placeReason (context compiled.indexed caller.named).owner site root (some type) := by
  funext site root type
  change issued.diagnostics.program.placeReason produced.site.code.compilation.owner site root (some type) = _
  rw [sameDiagnostics, produced.site.compilation]

/-- The diagnostic rows are the literal rows used by the selected body callback. -/
theorem assignment_policy
    (sameAssignments : issued.assignments = produced.compilation.own.assignments)
    (sameDiagnostics : issued.diagnostics.program = produced.diagnostics) :
    CompatibleAssignmentStatements.AssignmentPolicy (bodyPolicy produced.compilation produced.site.code)
      (.initial compiled.compatible.checked) issued.invalidProjection issued.invalidOperand issued.missingDefault := by
  have missing := missing_policy produced issued sameDiagnostics
  refine ⟨read_policy produced, ?_, ?_⟩
  · rw [missing]
    dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidOperand]
    simp only [sameAssignments, sameDiagnostics, produced.site.compilation]
    rfl
  · rw [missing]
    dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidOperand]
    simp only [sameAssignments, sameDiagnostics, produced.site.compilation]
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl

/-- The original unary callback uses those same genuine issued tokens. -/
theorem unary_policy
    (sameAssignments : issued.assignments = produced.compilation.own.assignments)
    (sameDiagnostics : issued.diagnostics.program = produced.diagnostics) :
    CompatibleBitNotStatements.Policy (bodyPolicy produced.compilation produced.site.code)
      (.initial compiled.compatible.checked) issued.invalidProjection issued.invalidUnary issued.missingDefault := by
  have missing := missing_policy produced issued sameDiagnostics
  unfold CompatibleBitNotStatements.Policy
  rw [missing]
  dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidUnary]
  simp only [sameAssignments, sameDiagnostics, produced.site.compilation]
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
There is no body tree, native body typing or finished SiteShell premise. -/
structure LiteralBodyInputs where
  issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named)
  sameAssignments : issued.assignments = produced.compilation.own.assignments
  sameDiagnostics : issued.diagnostics.program = produced.diagnostics
  samePolicy : produced.site.code.policy = root.root.selected.policy
  canonical : produced.site.code.view = source caller.named
  bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named
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

variable (inputs : LiteralBodyInputs produced root)

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
    bodyReasons := inputs.bodyReasons
    declarations := inputs.declarations
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
      assignments := assignment_policy produced inputs.issued inputs.sameAssignments inputs.sameDiagnostics
      unaries := unary_policy produced inputs.issued inputs.sameAssignments inputs.sameDiagnostics
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

/-- These whole-Source static facts are independent of the approved literal.
The builtin fragment excludes the unrelated lambda and indirect parent forms. -/
structure LiteralDomainGlobals (currentContext : SourceSemantics.Context)
    (currentScope : SourceCoreLocalCell.Scope)
    (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram)) : Prop where
  namedLedger : (context compiled.indexed caller.named).solvedRequirements = caller.solved
  headerOrder : ∀ header, header ∈ headers →
    header.instantiation.parameterSubstitution.map Prod.fst =
      (header.named.specialized.parameterSubstitution.map Prod.fst).reverse
  sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers currentContext
  fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw (source caller.named) currentContext
    (CompatibleExpressionBuiltins.Syntax (source caller.named))
  fragmentCoercions : ∀ candidate node, CompatibleExpressionBuiltins.Syntax (source caller.named) candidate →
    (source caller.named).lookupExpression? candidate = some node → node.coercions = []
  fragmentSpecial : ∀ candidate, CompatibleExpressionBuiltins.Syntax (source caller.named) candidate →
    ∀ child budget, (match root.root.selected.policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context compiled.indexed caller.named) child budget
        (source caller.named) currentScope candidate rootReasonAt) = .ok none
  fragmentRead : ∀ candidate, CompatibleExpressionBuiltins.Syntax (source caller.named) candidate →
    root.root.selected.policy.readExpression (source caller.named) candidate =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked (source caller.named) candidate
  profile : compiled.compatible.checked.catalog.callableContracts = true

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
    issued := by
      intro candidate node parameters result statements allowed found form
      have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
      rw [form] at atomic
      cases atomic
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnSiteShells
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralPlaceDiagnosticShells
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
  bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named
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
    bodyReasons := inputs.bodyReasons
    declarations := inputs.declarations
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
    issued := by
      intro candidate node parameters result statements allowed found form
      have atomic := (literal_node produced root inputs allowed found).symm ▸ inputs.atomic
      rw [form] at atomic
      cases atomic
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralIssuedSourceReceipts
/-! The selected compiler receipt supplies its original diagnostic issuer.
Only genuine full-Source unary and operand typing remain separate inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralIssuedSourceReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

/-- The actual cached Source and selected assignment row belong to the same
original compatible diagnostic preparation. The receiving root table may change. -/
theorem of_compilation
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    {lowered : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed caller.named lowered namedCode)
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (actual : lowered = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable})
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named)) :
    ∃ issued : IssuedSource compiled caller.named.signature.key (source caller.named),
      issued.assignments = compilation.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program lowered := by
  obtain ⟨root, extra, prepared, collected⟩ :=
    CallableIndexedOwnedPublicPlaceMissingDiagnostics.inventory_at_header caller found
  have basePrepared := CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base prepared
  have sameBase : lowered.base = diagnostics.program.base := by
    rw [actual]
    cases compiled.indexed.base.callableContext <;> rfl
  have selected := compilation.diagnostic
  rw [sameBase] at selected
  obtain ⟨first, assignmentsPrepared⟩ := SourceCoreProgramFaultSites.prepare_assignments_at
    basePrepared (CallableIndexedActualNamedSourceReceipts.header_record compiled caller) selected
  change SourceCoreAssignmentFaultSites.prepare (source caller.named) first =
    .ok compilation.own.assignments at assignmentsPrepared
  rw [caller.agreement.source] at collected
  let issued : IssuedSource compiled caller.named.signature.key (source caller.named) := {
    first := first
    assignments := compilation.own.assignments
    assignmentsPrepared := assignmentsPrepared
    typing := typing
    plan := compiled.indexed.base.plan
    root := root
    extra := extra
    diagnostics := diagnostics
    prepared := prepared
    collected := collected }
  exact ⟨issued, rfl, placeReasons_of_lowered diagnostics actual⟩

variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

/-- This is the exact issuer owner stored by the already selected lambda Site. -/
theorem at_produced
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (actual : produced.diagnostics = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable})
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named)) :
    ∃ issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named),
      issued.assignments = produced.compilation.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program produced.diagnostics := by
  have owner : produced.site.code.compilation.owner = caller.named.signature.key := by
    rw [produced.site.compilation]
    rfl
  rw [owner]
  exact of_compilation caller produced.compilation found actual typing

/-- The existing same-root callback retains these literal compiler identities.
It transports the receipt to that original compilation without selecting again. -/
theorem at_callback
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    {actualDiagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed caller.named actualDiagnostics namedCode)
    (diagnosticsEq : produced.diagnostics = actualDiagnostics)
    (namedCodeEq : produced.namedCode = namedCode)
    (compilationEq : HEq produced.compilation compilation)
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (actual : actualDiagnostics = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable})
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named)) :
    ∃ issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named),
      issued.assignments = compilation.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program actualDiagnostics := by
  have ownEq : produced.compilation.own = compilation.own := by
    cases diagnosticsEq
    cases namedCodeEq
    exact congrArg (fun retained => retained.own) (eq_of_heq compilationEq)
  obtain ⟨issued, assignments, places⟩ := at_produced caller produced found (diagnosticsEq.trans actual) typing
  exact ⟨issued, assignments.trans (congrArg (fun own => own.assignments) ownEq), diagnosticsEq ▸ places⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralIssuedSourceReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
/-! A positive issuer packet comes from the exact sealed second-pass slot.
The original compatible diagnostics, named compiler action, selected assignment
row and complete Source are retained together. Ordinary and selected-method
packets use the same genuine factory; a synthetic method has no ordinary Header.

An arbitrary older IssuedSource may have been prepared at another first token.
This producer does not upgrade that packet or infer diagnostic identity from
equal native code. Prospective collectors must retain the issued packet and
Compilation produced here. Transfer of an actual operand/unary occurrence to
the receiving diagnostic table still needs the real program/fixed-prefix
priority producer and successful receiving-registry rebuild.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

/-- Only the actual callable receiver replacement changes the lowered table. -/
def lowered (compiled : SourceCoreUnifiedCompilation.Compiled)
    (diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)) :
    SourceCoreDataPlaceFaultSites.Program :=
  match compiled.indexed.base.callableContext with
  | none => diagnostics.program
  | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}

/-- The full-key selector retains the original complete Source in the plan. -/
theorem selected_collected {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      named.signature.key = .ok named.specialized) :
    (named.signature.key, source named) ∈ compiled.indexed.base.plan.specializations.map
      (fun specialized => (specialized.key, specialized.function.typedBody)) := by
  have member : named.specialized ∈ compiled.indexed.base.plan.specializations.filter
      (fun actual => decide (actual.key = named.signature.key)) := by
    rw [CallableIndexedOwnedContextualDiagnosticSources.selected_filter record]
    exact List.mem_singleton_self _
  exact List.mem_map.mpr ⟨named.specialized, (List.mem_filter.mp member).1, by
    rw [CallableIndexedOwnedContextualDiagnosticSources.selected_key record]
    rfl⟩

/-- These are actual compiler records. The issuer's table equality is an output
of the factory, alongside the genuine cache slot and diagnostic identity. -/
structure SelectedReceipt (compiled : SourceCoreUnifiedCompilation.Compiled) (named : Named) (index : Nat) where
  selected : compiled.indexed.base.functions[index]? = some named
  diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)
  found : compiled.indexed.base.diagnostics = some diagnostics
  code : Expr
  cached : compiled.indexed.secondPass.closures[index]? = some code
  compilation : Compilation compiled.indexed named (lowered compiled diagnostics) code
  record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
    named.signature.key = .ok named.specialized
  functionFirst : Nat
  functionPositive : 0 < functionFirst
  functionIssued : SourceCoreProgramFaultSites.FunctionIssuance functionFirst named.specialized compilation.own
  issued : IssuedSource compiled named.signature.key (source named)
  issuedDiagnostics : issued.diagnostics = diagnostics
  issuedPlan : issued.plan = compiled.indexed.base.plan
  issuedFirst : issued.first = functionFirst + compilation.own.table.reads.length
  assignments : issued.assignments = compilation.own.assignments
  places : PlaceReasonsEq issued.diagnostics.program (lowered compiled diagnostics)

/-- A real selected second-pass action manufactures the first token, inventory
and assignment row internally. No chosen issuer or equality is an input. -/
theorem at_selected {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named} {index : Nat}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source named)) :
    Nonempty (SelectedReceipt compiled named index) := by
  obtain ⟨diagnostics, code, found, cached, accepted⟩ := NamedCalls.compiled_at compiled.indexed selected
  obtain ⟨compilation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed accepted
  have record := CallableIndexedActualNamedSourceReceipts.cached_record compiled selected compilation.hook
  obtain ⟨root, extra, prepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled found
  have basePrepared := CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base prepared
  have sameBase : (lowered compiled diagnostics).base = diagnostics.program.base := by
    unfold lowered
    cases compiled.indexed.base.callableContext <;> rfl
  have own := compilation.diagnostic
  change (lowered compiled diagnostics).base.find? named.signature.key = some compilation.own at own
  rw [sameBase] at own
  obtain ⟨first, positive, functionIssued⟩ := SourceCoreProgramFaultSites.prepare_function_issuance basePrepared record own
  have assignmentsPrepared : SourceCoreAssignmentFaultSites.prepare (source named)
      (first + compilation.own.table.reads.length) = .ok compilation.own.assignments := by
    cases functionIssued with
    | intro _ _ _ _ assignments _ _ _ _ _ => exact assignments
  let issued : IssuedSource compiled named.signature.key (source named) := {
    first := first + compilation.own.table.reads.length
    assignments := compilation.own.assignments
    assignmentsPrepared := assignmentsPrepared
    typing := typing
    plan := compiled.indexed.base.plan
    root := root
    extra := extra
    diagnostics := diagnostics
    prepared := prepared
    collected := List.mem_append_left _ (selected_collected record) }
  exact ⟨{
    selected := selected
    diagnostics := diagnostics
    found := found
    code := code
    cached := cached
    compilation := compilation
    record := record
    functionFirst := first
    functionPositive := positive
    functionIssued := functionIssued
    issued := issued
    issuedDiagnostics := rfl
    issuedPlan := rfl
    issuedFirst := rfl
    assignments := rfl
    places := placeReasons_of_lowered (compiled := compiled) diagnostics rfl }⟩

/-- The actual method selector supplies diagnostic typing. The old cached slot
and newly retained real slot agree on code; their diagnostic certificates are
not equated or recovered from this equality. -/
theorem at_principal {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ receipt : SelectedReceipt compiled principal.named principal.cached.index,
      receipt.code = principal.cached.code := by
  obtain ⟨receipt⟩ := at_selected principal.cached.selected (SourceDiagnosticTypingOrigins.principal principal wellFormed)
  exact ⟨receipt, Option.some.inj (receipt.cached.symm.trans principal.cached.cached)⟩

/-- A prospective method collector retains this actual compilation and issuer
at formation. The original complete selector and dictionary remain literal. -/
def SelectedReceipt.principal {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (receipt : SelectedReceipt compiled principal.named principal.cached.index) :
    CallableIndexedOwnedMethodPrincipal.Principal compiled method where
  cached := {
    index := principal.cached.index
    named := principal.named
    diagnostics := lowered compiled receipt.diagnostics
    code := receipt.code
    selected := receipt.selected
    same := principal.cached.same
    cached := receipt.cached
    compilation := receipt.compilation }
  callerContext := principal.callerContext
  callerEvidence := principal.callerEvidence
  traitName := principal.traitName
  methodName := principal.methodName
  requirements := principal.requirements
  dictionary := principal.dictionary
  selected := principal.selected

/-- All Source selector fields are unchanged by positive compiler issuance. -/
theorem SelectedReceipt.principal_source {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (receipt : SelectedReceipt compiled principal.named principal.cached.index) :
    (SelectedReceipt.principal principal receipt).named = principal.named ∧
      (SelectedReceipt.principal principal receipt).dictionary = principal.dictionary ∧
      (SelectedReceipt.principal principal receipt).sourceBody = principal.sourceBody :=
  ⟨rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies
/-! Actual selected compilation and the literal receiving table construct the
read and mapping-index policies. Each read uses its real Source binder. Each
unavailable index uses the raw mapping metadata and runtime views retained by
its own missing witness. No unrelated token or registered mapping type is
required to decode as this occurrence's error. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedNamedGeneration
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
open CallableIndexedOwnedPublicDecodedAssignmentFaults
open CallableIndexedOwnedPublicFaultReceiverTables

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named} {index : Nat}
  (selected : SelectedReceipt compiled named index)

/-- The actual selected compiler uses this issuer for its expression tokens. -/
def reasonAt : ExpressionId → Word :=
  (lowered compiled selected.diagnostics).reasonAt named.signature.key

/-- Replacing the callable receiver's root table retains expression issuance. -/
theorem reason_eq (id : ExpressionId) :
    reasonAt selected id = selected.diagnostics.program.reasonAt named.signature.key id := by
  unfold reasonAt lowered
  cases compiled.indexed.base.callableContext <;> rfl

/-- The lookup follows from the retained named compilation itself. -/
theorem own_found : selected.diagnostics.program.base.find? named.signature.key =
    some selected.compilation.own := by
  have found := selected.compilation.diagnostic
  change (lowered compiled selected.diagnostics).base.find? named.signature.key =
    some selected.compilation.own at found
  have sameBase : (lowered compiled selected.diagnostics).base =
      selected.diagnostics.program.base := by
    unfold lowered
    cases compiled.indexed.base.callableContext <;> rfl
  rw [sameBase] at found
  exact found

/-- The real public read row constructs inclusion only at a certified local
read and its actual current uninitialized cell. -/
theorem reads {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique (source named))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics) :
    ReachedLoweredReadOutcomePorts.ReadPolicies fuel values (source named) context
      (reasonAt selected) (faults completion.result.diagnostics) := by
  intro scope id code certificate binding environment heap location cell witness
  obtain ⟨read, _expression, _binder, _span, token, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver
      selected.found selected.record unique witness.contains witness.localReference (own_found selected)
  apply of_decoded (diagnostic := {
    error := .uninitializedLocal certificate.binder
    site := .occurrence id.occurrence
    span := some certificate.node.span })
  · simpa only [reason_eq selected id, ← token] using decoded
  · exact .readUninitialized location certificate.binder

/-- The exact unavailable mapping supplies its real canonical raw view and
receiving metadata, so the first matching public row is derived internally. -/
theorem missing {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (unique : NodeOccurrencesUnique (source named))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics) :
    IndexFaultPostContracts.MissingPolicies values (source named) functions
      completion.result.context.registry program context evidence (reasonAt selected)
      (faults completion.result.diagnostics) := by
  intro id base key node baseNode keyNode layout comparison first second header
    mapping world baseSource keySource baseValue environment before middle heap
    keyFound form baseTrace keyTrace rawKey rawValue sources tag entries fallback witness
  have contains : ContainsExpression (source named) node.id node := by
    rw [witness.contains.2]
    exact witness.contains
  have view : CompatiblePublicContextualMissingDiagnosticObservations.CanonicalMappingView
      (source named) base rawKey rawValue := by
    refine ⟨baseNode, lookupExpression?_complete unique witness.baseContains, ?_⟩
    rw [witness.sourceType, SourceCoreRawMetadata.runtimeType, witness.keyView, witness.valueView]
  have decoded :=
    CompatiblePublicContextualMissingDiagnosticObservations.receiver_index_missing_diagnostic
      compiled receiver selected.found selected.record unique contains form view witness.fields.metadata
  apply of_decoded (diagnostic := {
    error := .typeMismatch rawValue none
    site := .occurrence id.occurrence
    span := some node.span })
  · simpa only [witness.contains.2, reason_eq selected id] using decoded
  · exact .missing rawValue

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalClosureAssociation
/-! Positive closure receipts retain every actual captured physical slot together
with the original Source association. Map/world growth leaves that captured
canonical environment unchanged. Only forward erasure to the old association
is provided. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalClosureAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

private def slotsFor {scope : SourceCoreLocalCell.Scope} {actual : Environment}
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world scope function.captured actual) : Prop :=
  CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope captured.canonical

/-- This predicate refers to the canonical capture retained by the authentic
ordinary or principal association, including physical method slots. -/
def CapturedSlots
    (original : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys registry faults mapping world function native bindings parameter result) : Prop := by
  cases original with
  | ordinary _ captured _ _ _ _ _ _ _ _ _ => exact slotsFor captured
  | principal _ captured _ _ _ _ _ _ _ _ _ => exact slotsFor captured

structure Association
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping)
    (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) where
  original : CallableIndexedOwnedContextualTypedClosureReceipts.Association
    headers keys registry faults mapping world function native bindings parameter result
  slots : CapturedSlots original

theorem CapturedSlots.extend
    {original : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys registry faults mapping world function native bindings parameter result}
    (slots : CapturedSlots original)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    CapturedSlots (original.extend maps worlds) := by
  cases original <;> exact slots

def Association.extend
    (association : Association headers keys registry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association headers keys registry faults futureMapping futureWorld function native bindings parameter result :=
  ⟨association.original.extend maps worlds, association.slots.extend maps worlds⟩

abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping)
    (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  Nonempty (Association headers keys registry faults mapping world function native bindings parameter result)

theorem StaticMember.forget
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    CallableIndexedOwnedContextualTypedClosureReceipts.StaticMember
      headers keys registry faults mapping world function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨association.original⟩

theorem StaticMember.represents
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) := member.forget.represents

theorem StaticMember.extend
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember headers keys registry faults futureMapping futureWorld function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨association.extend maps worlds⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalClosureAssociation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOperatorSourceAdmission
/-! Prepared operators retain the independently selected Source dictionary.
These finite static views preserve the same accepted method code, tree and
parameter receipts. Genuine operator typing supplies raw callee heap/argument
admission; no native projection or body execution law is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOperatorSourceAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogHookMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)

/-- Actual dictionary coverage strengthens only the static validity domain. -/
def EvidenceValidity (dictionary : Dynamic.EvidenceEnvironment) (context : SourceSemantics.Context) : Prop :=
  validity context ∧ dictionary.Covers context

/-- Reindex the genuine same-code compiler receipt at its actual Source selector. -/
def with_dictionary (dictionary : Dynamic.EvidenceEnvironment)
    (covers : dictionary.Covers principal.sourceBody.context) :
    ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody dictionary administrative registry faults
      expressionSyntax certificates (EvidenceValidity (validity := validity) dictionary) diagnosticPolicy := {
  sameSource := profile.sameSource, parameters := profile.parameters
  sourceFrame := { profile.sourceFrame with covers := covers }
  context := profile.context, types := profile.types, extended := profile.extended
  body := { profile.body with
    initialValid := ⟨profile.body.initialValid, (Dynamic.MonoBindersExtend.runtimeContextFields profile.extended).covers covers⟩ }
  definitions := profile.definitions, registered := profile.registered, parameterType := profile.parameterType }

/-- A real binder extension transports only genuine static fields and coverage. -/
theorem evidence_extend (dictionary : Dynamic.EvidenceEnvironment)
    (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
    {context next : SourceSemantics.Context} {binder : TypedBinder}
    (valid : EvidenceValidity (validity := validity) dictionary context)
    (extended : BinderExtends principal.sourceBody.source.owner context binder next) :
    EvidenceValidity (validity := validity) dictionary next :=
  ⟨extend valid.1 extended, (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers valid.2⟩

/-- Original ledger/runtime fields and the actual dictionary remain separate. -/
theorem evidence_runtime (dictionary : Dynamic.EvidenceEnvironment)
    (runtimeOf : ∀ {context}, validity context →
      CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
    {context : SourceSemantics.Context} (valid : EvidenceValidity (validity := validity) dictionary context) :
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context dictionary :=
  ⟨(runtimeOf valid.1).ledger, (runtimeOf valid.1).runtime, valid.2⟩

/-- The actual trait profile and selector authenticate the raw parameter vector
and Source context at the successful operand heap, before Core erasure. -/
theorem at_selected_arguments
    {context : SourceSemantics.Context} {source : TypedSource}
    {callerEvidence dictionary : Dynamic.EvidenceEnvironment} {traitName methodName : String}
    {operand : TypeSystem.Ty} {parameterTypes returnTypes : List TypeSystem.Ty}
    {predicates : List ProgramPredicate} {requirements : List RequirementId}
    {heap : Dynamic.Heap} {arguments : List Dynamic.Value}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (operatorProfile : OperatorProfileInstantiates context traitName methodName operand parameterTypes returnTypes predicates)
    (requirementsProve : RequirementSequenceProves context requirements predicates)
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      traitName methodName requirements principal.sourceBody dictionary)
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context heap arguments parameterTypes) :
    Dynamic.HeapWellTyped principal.sourceFunction.context heap ∧
      Dynamic.ValuesHaveTypes principal.sourceFunction.context heap arguments profile.types ∧
      principal.sourceBody.resultType = TypeSystem.Ty.productMany returnTypes := by
  obtain ⟨lexicalContext, facts, certificate, resultEq⟩ := selected.certificateOfProfile wellFormed
    runtime.signatures runtime.requirements.idsUnique operatorProfile requirementsProve
  have signatures := certificate.signatures_eq.trans runtime.signatures.symm
  have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyArguments := argumentsTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have typesEq : parameterTypes = profile.types :=
    (Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend).symm.trans
      (Dynamic.MonoBindersExtend.bodyTypes_eq profile.extended)
  exact ⟨principal.source_frame.context.symm ▸ bodyHeap,
    principal.source_frame.context.symm ▸ (typesEq ▸ bodyArguments), resultEq⟩

section ParentFacts
open CallablePreparedMethodSelection CallableCoercionExpressionCertificates
open CallablePreparedOperatorSourceBounds
variable {checkedProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  {receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output}
  (selected : OperatorSource receipt)
  {context : SourceSemantics.Context}

/-- Genuine parent typing exposes its original operands, operator profile and
raw result. These facts concern the complete original Source judgment. -/
theorem source_facts (unique : NodeOccurrencesUnique source)
    (coercions : node.coercions = []) (typed : ExpressionHasType source context id node.type) :
    ∃ operand parameterTypes returnTypes predicates,
      ExpressionsHaveTypes source context receipt.arguments parameterTypes ∧
      OperatorProfileInstantiates context selected.traitName selected.methodName operand parameterTypes returnTypes predicates ∧
      RequirementSequenceProves context receipt.requirements predicates ∧
      node.type = TypeSystem.Ty.productMany returnTypes := by
  generalize _typeEq : node.type = annotation at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw rawEq _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.found)
    subst actualNode
    have layout := CallableCallRequirementLayouts.ordinary_owned receipt.ordinary
    have dispatch := selected.dispatch
    rcases receipt.form with ⟨operator, operandId, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
    · simp only [form] at dispatch
      rw [form] at raw
      cases raw with
      | unary child operatorTyped =>
        cases valid with
        | ordinary _ path requirements =>
          have ownedEq := List.append_cancel_right (layout.symm.trans requirements)
          rw [coercions] at path
          generalize targetEq : node.type = target at path
          cases path
          cases operatorTyped with
          | logicalNot | wordBitNot | integerBitNot => exact False.elim (receipt.nonempty ownedEq)
          | trait staticDispatch operatorProfile proves =>
            obtain ⟨rfl, rfl⟩ := unary_dispatch_unique dispatch staticDispatch
            exact ⟨_, _, _, _, arguments ▸ .cons child (.nil context), operatorProfile, ownedEq.symm ▸ proves, rfl⟩
    · simp only [form] at dispatch
      rw [form] at raw
      cases raw with
      | binary first second operatorTyped =>
        cases valid with
        | ordinary _ path requirements =>
          have ownedEq := List.append_cancel_right (layout.symm.trans requirements)
          rw [coercions] at path
          generalize targetEq : node.type = target at path
          cases path
          cases operatorTyped with
          | wordArithmetic _ | integerArithmetic _ | wordShift _ | wordUnchecked _ | wordComparison _ | integerComparison _ | fixedComparison _ | fixedBitwise _ | booleanAnd | booleanOr =>
            exact False.elim (receipt.nonempty ownedEq)
          | trait staticDispatch operatorProfile proves =>
            obtain ⟨rfl, rfl⟩ := binary_dispatch_unique dispatch staticDispatch
            exact ⟨_, _, _, _, arguments ▸ .cons first (.cons second (.nil context)), operatorProfile, ownedEq.symm ▸ proves, rfl⟩
end ParentFacts

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOperatorSourceAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBareAssignmentAdmission
/-! A plain bare write needs only the successful RHS admission and the
original writable lexical target. It does not rerun whole-program preservation.
The real write retains the captured cell type even if the RHS changed its value. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBareAssignmentAdmission
open Frontend SourceInference Staging.Recursive

/-- The actual current-cell write preserves deep heap typing at the exact RHS
endpoint. Both raw type identities come from the accepted Source assignment. -/
theorem heap_after_equal
    {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {rhs : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? rhs = some node)
    (typed : SourceAssignmentHasType source context assignment .equal rhs)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (snapshot : BareTarget environment before assignment.target target)
    (heapTyped : Dynamic.HeapWellTyped context middle)
    (rightTyped : Dynamic.ValueHasType context middle right node.type)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies .equal target.selected right replacement)
      middle target updated after) :
    Dynamic.HeapWellTyped context after := by
  cases typed with
  | wordCompound operator _ _ _ => cases operator
  | equal targetTyped rhsTyped _ =>
    obtain ⟨actual, contains, storedType⟩ := rhsTyped.stored_type
    have sameNode : actual = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst actual
    cases snapshot with
    | intro bare lookup read initial =>
      cases targetTyped with
      | intro writable projections _ =>
        rw [bare] at projections
        cases projections
        obtain ⟨scheme, staticLookup, _schemeTyped, _mono, bodyType⟩ := writable.scheme
        obtain ⟨location, cell, typedLookup, typedRead, cellType, _storage⟩ := locals.lookup staticLookup
        cases lookup.functional typedLookup
        cases read.functional typedRead
        cases write with
        | intro currentRead currentType _ update written =>
          cases update with
          | leaf modified =>
            cases modified
            refine Dynamic.HeapWellTyped.write heapTyped currentRead (.some ?_) written
            rw [currentType, cellType, bodyType, ← storedType]
            exact rightTyped

theorem heap_after_assignment
    {source : TypedSource} {context : SourceSemantics.Context}
    {operator : Syntax.ValueAssignOp}
    {assignment : AssignmentResolution} {rhs : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? rhs = some node)
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (snapshot : BareTarget environment before assignment.target target)
    (heapTyped : Dynamic.HeapWellTyped context middle)
    (rightTyped : Dynamic.ValueHasType context middle right node.type)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated after) :
    Dynamic.HeapWellTyped context after := by
  cases typed with
  | equal targetTyped rhsTyped same =>
      exact heap_after_equal unique found (.equal targetTyped rhsTyped same) locals snapshot heapTyped rightTyped write
  | wordCompound kind targetTyped rhsTyped same =>
      obtain ⟨actual, contains, storedType⟩ := rhsTyped.stored_type
      have sameNode : actual = node := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst actual
      have rightWord : Dynamic.ValueHasType context middle right .word := by
        rw [← storedType]
        exact rightTyped
      cases snapshot with
      | intro bare lookup read initial =>
        cases targetTyped with
        | intro writable projections _ =>
          rw [bare] at projections
          cases projections
          obtain ⟨scheme, staticLookup, _schemeTyped, _mono, bodyType⟩ := writable.scheme
          obtain ⟨location, cell, typedLookup, typedRead, cellType, _storage⟩ := locals.lookup staticLookup
          cases lookup.functional typedLookup
          cases read.functional typedRead
          cases write with
          | intro currentRead currentType _ update written =>
            cases update with
            | leaf modified =>
              have updatedWord : Dynamic.ValueHasType context middle updated .word := by
                cases kind <;> cases modified <;> rename_i primitive <;>
                  cases primitive <;> cases rightWord <;> exact .word _
              refine Dynamic.HeapWellTyped.write heapTyped currentRead (.some ?_) written
              rw [currentType, cellType, bodyType]
              exact updatedWord

theorem source_profile
    {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    {rhs : ExpressionId} {node : ExpressionNode} {leaf : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? rhs = some node)
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (view : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type) :
    operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word := by
  cases typed with
  | equal _ _ _ => exact .inl rfl
  | wordCompound _ _ rhsTyped _ =>
      obtain ⟨actual, contains, storedType⟩ := rhsTyped.stored_type
      have sameNode : actual = node := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst actual
      exact .inr (view.trans (congrArg SourceCoreRawMetadata.runtimeType storedType))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBareAssignmentAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaFormation
/-! Actual formation attaches the full captured slot receipt to the same Code,
history and original Source origin. The capture proof is supplied by the real
input environment before the freshly formed value enters the positive model.
The formation copies the captured cells, and the copies keep every global slot. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedOrdinaryLambdaSupport (Support SourceOrigin)
open CallableIndexedOwnedContextualLambdaProvenance (OrdinaryAt)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}

section Formation
variable {scope : SourceCoreLocalCell.Scope} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults) (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : OrdinaryAt code support)
  (allSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope captured.canonical)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

include packet profile prefixContext observed provenance allSlots in
/-- One original contextual formation retains its complete traces and
represented value, plus the same static member for later initialized reads.
The factory is used once, without an escaped-token hypothesis. The member is
the formed closure over the copies of its captured cells. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code (history_at captured code support owner initial packet) heap store
        owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      CallableIndexedOwnedPhysicalClosureAssociation.StaticMember headers keys registry faults formed.finalMap formed.finalWorld
        formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  let history := history_at captured code support owner initial packet
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [reference_index captured code support]
    exact observed.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history copied
    (reference_index captured code support) heaps reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formed.represents heaps.runtime_hasTypes)
  exact ⟨formed, formed.source _ ordinary coercions, formed.evaluated,
    fun _ _ completed => Core.evaluation_deterministic completed formed.evaluated,
    ⟨⟨.ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨(source_origin captured code support owner initial packet).metadata⟩
      prefixContext (observed.of_slots formed.slots) (reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.provenance_recapture provenance formed.captured),
      allSlots.of_slots formed.slots⟩⟩⟩

end Formation

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrincipalLambdaExpressionHeads
/-! Authentic method lambda certificates construct principal closures whose
shared representation retains the actual globals and leading bundle. Ordered
arguments and invocation keep the caller's function model and exact restored
pool; call bodies use only the original strict joint family hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrincipalLambdaExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)
open CallableIndexedOwnedMethodLambdaExpressionHeads (Formation Call Head bridge)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context)

/-- Every child and returned heap retains the caller's same function model. -/
def model (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) :=
  CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  {certificate : GenericExpressionMeaning.Certificate}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include inclusion complete slots wellFormed runtime covers in
/-- Each authentic finite branch constructs captures, Code and Support at
its actual input. Strict arguments and the joint body's own strict IH remain. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (registry := registry) (faults := faults) principal context certificate) faults size := by
  intro scope id lowered head node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  let captured := CallableIndexedOwnedMethodPrincipalCaptures.captures principal owner initial.val initial.property
    complete environments agrees nativeTyped
  have packet := CallableIndexedOwnedMethodPrincipalCaptures.captured_packet principal owner initial.val initial.property
    complete environments agrees nativeTyped slots
  let capturedInitial : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
      ⟨scope, mapping, world, before, store, captured.canonical⟩ := ⟨initial.val, packet⟩
  have capturedAdmission : Admission (bridge (headers := headers) principal owner) context capturedInitial :=
    ⟨admitted.heap, admitted.rows⟩
  cases head with
  | formation head =>
    let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
    let support : Support code registry faults := head.support environment
    have sourceFound : (CallableIndexedNamedGeneration.source principal.named).lookupExpression? id = some code.sourceNode := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, CallableIndexedLambdaGeneration.closure, head.identifier] using
        head.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have nativeTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
        (head.function environment).context (head.function environment).evidence (head.function environment).source
        (head.function environment).captured before code.id outcome after := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using trace
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context code.id code.sourceNode.type := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using typed
    obtain ⟨result, finalStore, evaluated, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedPrincipalLambdaFormation.preserves_at
        (function := head.function environment) (scope := scope) (actual := actual) captured code support owner initial.val packet profile functions inclusion
        wellFormed runtime covers locals actualTyped head.sourceType head.site.snapshots head.ordinary head.coercions heaps
        capturedAdmission nativeTrace
    have evaluated : Evaluates actual store (lowered.expression.rename ξ) result finalStore := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        head.emitted, captured, CallableIndexedOwnedMethodPrincipalCaptures.captures] using evaluated
    have represented : GenericExpressionMeaning.ResultRepresents
        (model (registry := registry) functions)
        finalMap finalWorld code.sourceNode.type lowered.type faults outcome result := by
      simpa only [model, code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, head.emitted] using represented
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩
  | call head =>
    let code : Code compiled.indexed (head.formation.function environment) scope captured.administrative := head.formation.code environment
    let support : Support code registry faults := head.formation.support environment
    have same := Option.some.inj (found.symm.trans head.compiler.found)
    subst node
    let issued : CallableIndexedOwnedMethodLambdaSelectedCall.Receipt
        (function := head.formation.function environment) captured code support head.compiler certificate := {
      native := head.native, prepared := head.prepared, parent := head.parent,
      selection := ⟨head.selection.children, head.selection.nativeTypes, head.selection.escaped,
        head.selection.rawResult, head.selection.nativeResult, head.selection.stageAccepted, head.selection.arityAccepted⟩,
      sameCallee := head.sameCallee, ordinary := head.formation.ordinary, coercions := head.formation.coercions,
      copied := head.formation.site.snapshots, sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
      syntaxTree := head.formation.syntaxTree, parentTyped := typed }
    obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedMethodLambdaSelectedCallWithFunctions.preserves_at_receipt
        (function := head.formation.function environment) (scope := scope) (actual := actual)
        (captured := captured) (code := code) (support := support) (owner := owner) (initial := initial.val) (packet := packet)
        (profile := profile) (functions := functions) (inclusion := fun represented => inclusion
          (CallableIndexedOwnedGeneralLambdaValues.includes_method keys registry faults profile represented)) (compiler := head.compiler) (wellFormed := wellFormed) (runtime := runtime)
        (covers := covers) (locals := locals) (heaps := heaps)
        (admitted := capturedAdmission) issued budget children below trace within
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩

include inclusion complete slots wellFormed runtime covers in
/-- Native child bounds are measured independently. The same static branch
producer reconstructs the authentic Source trace and restores its exact pool. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (registry := registry) (faults := faults) principal context certificate) faults size := by
  intro scope id lowered head node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  let captured := CallableIndexedOwnedMethodPrincipalCaptures.captures principal owner initial.val initial.property
    complete environments agrees nativeTyped
  have packet := CallableIndexedOwnedMethodPrincipalCaptures.captured_packet principal owner initial.val initial.property
    complete environments agrees nativeTyped slots
  let capturedInitial : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
      ⟨scope, mapping, world, before, store, captured.canonical⟩ := ⟨initial.val, packet⟩
  have capturedAdmission : Admission (bridge (headers := headers) principal owner) context capturedInitial :=
    ⟨admitted.heap, admitted.rows⟩
  cases head with
  | formation head =>
    let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
    let support : Support code registry faults := head.support environment
    have sourceFound : (CallableIndexedNamedGeneration.source principal.named).lookupExpression? id = some code.sourceNode := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        CallableIndexedLambdaGeneration.closure, head.identifier] using head.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context code.id code.sourceNode.type := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using typed
    have actualCompleted : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) value finalStore := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        head.emitted, captured, CallableIndexedOwnedMethodPrincipalCaptures.captures] using completed
    obtain ⟨sourceSize, outcome, after, trace, _native, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame,
        metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedPrincipalLambdaFormation.reflects_at
        (function := head.function environment) (scope := scope) (actual := actual) captured code support owner initial.val packet profile functions inclusion
        wellFormed runtime covers locals actualTyped head.sourceType head.site.snapshots head.ordinary head.coercions heaps
        capturedAdmission actualCompleted
    have sourceTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) environment before id outcome after := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using trace
    have represented : GenericExpressionMeaning.ResultRepresents
        (model (registry := registry) functions)
        finalMap finalWorld code.sourceNode.type lowered.type faults outcome value := by
      simpa only [model, code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, head.emitted] using represented
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed sourceTrace frame⟩
  | call head =>
    let code : Code compiled.indexed (head.formation.function environment) scope captured.administrative := head.formation.code environment
    let support : Support code registry faults := head.formation.support environment
    have same := Option.some.inj (found.symm.trans head.compiler.found)
    subst node
    let issued : CallableIndexedOwnedMethodLambdaSelectedCall.Receipt
        (function := head.formation.function environment) captured code support head.compiler certificate := {
      native := head.native, prepared := head.prepared, parent := head.parent,
      selection := ⟨head.selection.children, head.selection.nativeTypes, head.selection.escaped,
        head.selection.rawResult, head.selection.nativeResult, head.selection.stageAccepted, head.selection.arityAccepted⟩,
      sameCallee := head.sameCallee, ordinary := head.formation.ordinary, coercions := head.formation.coercions,
      copied := head.formation.site.snapshots, sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
      syntaxTree := head.formation.syntaxTree, parentTyped := typed }
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedMethodLambdaSelectedCallWithFunctions.reflects_at_receipt
        (function := head.formation.function environment) (scope := scope) (actual := actual)
        (captured := captured) (code := code) (support := support) (owner := owner) (initial := initial.val) (packet := packet)
        (profile := profile) (functions := functions) (inclusion := fun represented => inclusion
          (CallableIndexedOwnedGeneralLambdaValues.includes_method keys registry faults profile represented)) (compiler := head.compiler) (wellFormed := wellFormed) (runtime := runtime)
        (covers := covers) (locals := locals) (heaps := heaps)
        (admitted := capturedAdmission) issued budget children below completed within
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrincipalLambdaExpressionHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrincipalLambdaExpressionRuntimeBounds
/-! The original expression support fold consumes authentic principal-lambda
formation and selected-call heads. Formed closures retain their actual globals
and leading bundle in the shared model. Runtime literal meaning is internal;
all heaps use the caller's function model and body children use its strict IH. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrincipalLambdaExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaExpressionHeads (bridge Head)
open CallableIndexedOwnedPrincipalLambdaExpressionHeads (model)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

/-- Certificate identity is the original static compiler Tree. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodLambdaExpressionRuntimeBounds.Tree (registry := registry) (faults := faults)
    (solved := solved) (reasonAt := reasonAt) (fuel := fuel) principal context

/-- Runtime literal receipts remain the original static certificate family. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodLambdaExpressionRuntimeBounds.RuntimeTree (registry := registry) (faults := faults)
    (solved := solved) (reasonAt := reasonAt) (fuel := fuel) principal context

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named))
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
theorem preserves_at_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (registry := registry) (faults := faults) principal context) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions
    (Head (registry := registry) (faults := faults) principal context) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      functions
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (registry := registry) (faults := faults) principal context) budget child childWithin children
    exact CallableIndexedOwnedPrincipalLambdaExpressionHeads.preserves_at
      principal context owner profile functions inclusion complete slots wellFormed runtime covers budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
theorem reflects_at_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (registry := registry) (faults := faults) principal context) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions
    (Head (registry := registry) (faults := faults) principal context) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      functions
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (registry := registry) (faults := faults) principal context) budget child childWithin children
    exact CallableIndexedOwnedPrincipalLambdaExpressionHeads.reflects_at
      principal context owner profile functions inclusion complete slots wellFormed runtime covers budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem preserves_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context) faults size := by
  exact preserves_at_with_literals principal context owner profile functions inclusion complete slots extension faithful observations
    functionTypes wellFormed runtime covers unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger unique faults)
    budget size within below

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem reflects_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context) faults size := by
  exact reflects_at_with_literals principal context owner profile functions inclusion complete slots extension faithful observations
    functionTypes wellFormed runtime covers unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger (CallableIndexedNamedGeneration.source principal.named) faults)
    budget size within below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrincipalLambdaExpressionRuntimeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyOperatorSourceBounds
/-! Prepared unary and binary method operators with an empty output coercion
suffix retain their original compiler selection and Source operand/body grades.
Actual admitted operand posts feed the selected method invocation; broader
coercion suffixes and stored callees are outside this finite branch. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyOperatorSourceBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open DataExpressionSequence CallablePreparedOperatorSourceBounds
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u,0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes originalTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}

/-- The source receipt keeps each original operand's strict grade. -/
def OperandOutcomeAt (budget : Nat) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (outcome : Outcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .ok values => ArgumentsAt (Program.ofChecked compiled.sourceProgram) budget context evidence source environment before ids values after
  | .error reason => ArgumentsFaultAt (Program.ofChecked compiled.sourceProgram) budget context evidence source environment before ids reason after

/-- Unary/binary packaging uses the existing single child and two-child adapter.
Every successful first post supplies admission for the actual next child. -/
theorem preserves_operands (budget : Nat)
    (shape : (∃ id, ids = [id]) ∨ (∃ left right, ids = [left,right]))
    (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids originalTypes)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope,mapping,world,before,store,canonical⟩)
    (admitted : Admission bridge context initial)
    (trace : OperandOutcomeAt (compiled := compiled) (context := context) (evidence := evidence) (source := source) (ids := ids) budget environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedExpressionSequence.PostSequenceAdmission bridge (context := context) outcome reached := by
  rcases shape with ⟨id,rfl⟩ | ⟨left,right,rfl⟩
  · cases tree with
    | single found certified =>
      have sourceTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing (by simp) found
      cases outcome with
      | ok values =>
        dsimp only [OperandOutcomeAt] at trace
        cases trace with
        | cons head strict tail =>
          cases tail
          obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,post⟩ :=
            meaning _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted (.value head)
          cases represented with
          | @value sourceValue nativeValue payload =>
            exact ⟨_,finalStore,finalMap,finalWorld,evaluated,.values (values := [nativeValue]) (.cons payload .nil),finalHeaps,maps,worlds,frame,metadata,
              reached,related,⟨post.rows,fun _ _ => post.at_value.2⟩⟩
      | error reason =>
        dsimp only [OperandOutcomeAt] at trace
        cases trace with
        | head failed strict =>
          obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,post⟩ :=
            meaning _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted (.fault failed)
          cases represented with
          | fault matched =>
            exact ⟨_,finalStore,finalMap,finalWorld,evaluated,.fault matched,finalHeaps,maps,worlds,frame,metadata,
              reached,related,⟨post.rows,by intro _ impossible; cases impossible⟩⟩
        | tail _ _ tail => cases tail
  · cases tree with
    | cons firstFound firstCertified tail =>
      cases tail with
      | single secondFound secondCertified =>
        have firstTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing (by simp) firstFound
        have secondTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing (by simp) secondFound
        cases outcome with
        | ok values =>
          dsimp only [OperandOutcomeAt] at trace
          cases trace with
          | cons head strict tail =>
            cases tail with
            | cons second secondStrict nil =>
              cases nil
              obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,post⟩ :=
                CallableIndexedOwnedAdmittedExpressionBounds.preserves_pair_after_value (bridge := bridge)
                  (meaning _ strict) (meaning _ secondStrict) firstCertified secondCertified firstFound secondFound firstTyped secondTyped
                  environments heaps locals agrees typed initial admitted (.value head) (.value second)
              exact ⟨_,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,
                reached,related,⟨post.rows,fun _ _ => post.at_value.2⟩⟩
        | error reason =>
          dsimp only [OperandOutcomeAt] at trace
          cases trace with
          | head failed strict =>
            obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,post⟩ :=
              meaning _ strict firstCertified firstFound firstTyped environments heaps locals agrees typed initial admitted (.fault failed)
            cases represented with
            | fault matched =>
              refine ⟨_,finalStore,finalMap,finalWorld,?_,.fault matched,finalHeaps,maps,worlds,frame,metadata,
                reached,related,⟨post.rows,by intro _ impossible; cases impossible⟩⟩
              simpa [SourceCoreCalls.packArguments, DataExpressionSequence.pair_rename] using
                LocalSequence.pair_left_failure _ _ evaluated
          | tail first strict failed =>
            cases failed with
            | head failed secondStrict =>
              obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,post⟩ :=
                CallableIndexedOwnedAdmittedExpressionBounds.preserves_pair_after_value (bridge := bridge)
                  (meaning _ strict) (meaning _ secondStrict) firstCertified secondCertified firstFound secondFound firstTyped secondTyped
                  environments heaps locals agrees typed initial admitted (.value first) (.fault failed)
              exact ⟨_,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,
                reached,related,⟨post.rows,by intro _ impossible; cases impossible⟩⟩
            | tail _ _ failed => cases failed


section MethodCall
open CallablePreparedMethodRuntimeMeaning CallableIndexedParameterMeaning
open CallableIndexedOwnedExtendedJointReadyContinuations
variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {methodAdministrative : Core.Context}
  {bodySyntax : ExpressionId → Prop} {bodyCertificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary methodAdministrative registry faults
    bodySyntax bodyCertificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
  {headerCertificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {headerSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (syntaxTree : GenericImperativeMatch.Syntax principal.sourceFunction.source bodySyntax profile.context
    (.statements true principal.sourceFunction.body) principal.sourceFunction.resultType)

/-- This static row conversion retains the original binder schemes and native
binder types together. It performs no evaluation recursion. -/
private theorem arguments_of_values {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List CallableIndexedParameterCertificates.Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : Values model mapping world (bindings.map (fun binding => binding.1.scheme.body))
      (bindings.map Prod.snd) sources payloads) : Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding rest ih => cases represented with
    | cons head tail => exact .cons head (ih tail)

include runtime covers wellFormed in
/-- The real successful operand trace authenticates the raw Source heap and
values at its actual post. The original typing row is independent of Core. -/
theorem after_operands {environment : Dynamic.Environment} {before middle : Dynamic.Heap}
    {arguments : List Dynamic.Value} {parameterTypes : List TypeSystem.Ty}
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (typedHeap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes source context ids parameterTypes)
    (evaluated : Dynamic.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) context evidence source environment
      before ids arguments middle) :
    Dynamic.ValuesHaveTypes context middle arguments parameterTypes ∧ Dynamic.HeapWellTyped context middle := by
  have preserves : Dynamic.ExpressionExecutionPreserves (Program.ofChecked compiled.sourceProgram) context evidence source environment := by
    intro before after id value type covers locals typedHeap typing evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment before after id value type
      runtime covers locals typedHeap typing evaluated
  have actual := Dynamic.ExpressionsEvaluate.preserves preserves covers locals typedHeap typing evaluated
  exact ⟨actual.1, actual.2.1⟩

include syntaxTree wellFormed runtime covers escaped extend runtimeOf in
/-- Original operand grades feed the actual selected parameter/body entry.
The same base body post restores the stronger caller at its original spine. -/
theorem preserves_raw_at (budget rawBudget : Nat) (bounded : rawBudget ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    (shape : (∃ id, ids = [id]) ∨ (∃ left right, ids = [left,right]))
    (tree : Tree source certificate scope ids (principal.named.inputs.map (fun binding => binding.1.scheme.body)) codes)
    (nativeTypes : codes.map (·.type) = principal.named.inputs.map Prod.snd)
    (packedType : principal.named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)
    (unique : NodeOccurrencesUnique source)
    {operand : TypeSystem.Ty} {parameterTypes returnTypes : List TypeSystem.Ty} {predicates : List ProgramPredicate}
    {traitName methodName : String} {requirements : List RequirementId}
    (typing : ExpressionsHaveTypes source context ids parameterTypes)
    (operatorProfile : OperatorProfileInstantiates context traitName methodName operand parameterTypes returnTypes predicates)
    (proves : RequirementSequenceProves context requirements predicates)
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence
      traitName methodName requirements principal.sourceBody principal.dictionary)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {callerAdministrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome} {reason : Word}
    (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
      (administrative := methodAdministrative) functions mapping world before store actual)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameFrame : installed.frameLocation = owner.key.frameLocation)
    (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
      callerAdministrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope,mapping,world,before,store,canonical⟩)
    (admitted : Admission bridge context initial)
    (trace : RawTraceAt (Program.ofChecked compiled.sourceProgram) rawBudget context evidence principal.dictionary source environment
      before ids principal.sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (SourceCoreCalls.call principal.named.signature installed.globalIndex
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩ := by
  cases trace with
  | @argumentFault sourceReason after failed =>
    obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,frame,metadata,reached,related,_post⟩ :=
      preserves_operands bridge (outcome := .error sourceReason) rawBudget shape tree unique typing
        (fun size strict => children size (Nat.lt_of_lt_of_le strict bounded))
        environments heaps locals agrees typed initial admitted failed
    cases represented with
    | fault matched =>
      exact ⟨_,finalStore,finalMap,finalWorld,SourceCoreCalls.call_argument_failure
        (signature := principal.named.signature) (index := installed.globalIndex) (internalReason := reason)
        (packedType.symm ▸ evaluated),.fault matched,finalHeaps,maps,worlds,frame,metadata,reached,related⟩
  | @apply bodySize arguments middle outcome after argumentsEvaluated called bodyStrict =>
    obtain ⟨value,middleStore,middleMap,middleWorld,argumentsEvaluation,argumentRep,middleHeaps,
        argumentMaps,argumentWorlds,argumentFrame,argumentMetadata,argumentState,argumentRelated,argumentPost⟩ :=
      preserves_operands bridge (outcome := .ok arguments) rawBudget shape tree unique typing
        (fun size strict => children size (Nat.lt_of_lt_of_le strict bounded))
        environments heaps locals agrees typed initial admitted argumentsEvaluated
    cases argumentRep with
    | @values arguments payloads represented =>
      rw [nativeTypes] at represented
      have nativeArguments := arguments_of_values principal.named.inputs represented
      let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
      have raw := after_operands wellFormed runtime covers locals admitted.heap typing argumentsEvaluated.sound
      have callee := CallableIndexedOwnedOperatorSourceAdmission.at_selected_arguments principal profile wellFormed runtime
        operatorProfile proves selected raw.2 raw.1
      obtain ⟨result,finalStore,finalMap,finalWorld,bodyEvaluation,resultRep,finalHeaps,
          bodyMaps,bodyWorlds,bodyFrame,bodyMetadata,bodyState,bodyRelated⟩ :=
        CallableIndexedOwnedExtendedReadyMethodInvocationBounds.invocation_preserves_at
          principal profile functions escaped extend runtimeOf next owner (bridge.pool argumentState)
          wellFormed callee.1 callee.2.1 (argumentPost.successful arguments rfl).rows observed syntaxTree
          nativeArguments sameFrame middleHeaps budget below called
          (Nat.le_of_lt (Nat.lt_of_lt_of_le bodyStrict bounded))
      obtain ⟨returned,_same,related⟩ := bridge.restore initial bodyState (argumentMaps.trans bodyMaps)
        (argumentWorlds.trans bodyWorlds) (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
        ((bridge.related argumentRelated).trans bodyRelated)
      have read := OptionalCell.read_success reason
        (show Evaluates (DataPatternValues.packValues payloads :: actual) middleStore
          (.var (installed.globalIndex + 1)) (.cellRef (OptionalCell.cellType principal.named.signature.functionType) installed.globalLocation)
          middleStore from .var installed.globalReference) next.globalRead
      exact ⟨result,finalStore,finalMap,finalWorld,SourceCoreCalls.call_success argumentsEvaluation read bodyEvaluation,
        resultRep,finalHeaps,argumentMaps.trans bodyMaps,argumentWorlds.trans bodyWorlds,
        argumentFrame.trans bodyFrame,argumentMetadata.trans bodyMetadata,returned,related⟩

/-- Actual failed operand completion fixes both the parent fault and post store.
This is the finite original call prefix inversion. -/
private theorem call_fault {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {environment : Environment} {before middle after : Store} {token : Word} {value : Value} {size : Nat}
    (argument : Evaluates environment before arguments (.inLeft signature.parameterType (.word token)) middle)
    (completed : EvaluationSize size environment before (SourceCoreCalls.call signature index arguments reason) value after) :
    value = .inLeft signature.resultType (.word token) ∧ after = middle := by
  cases completed with
  | caseLeft actual branch =>
    obtain ⟨same,rfl⟩ := evaluation_deterministic actual.sound argument
    cases same
    cases branch with
    | inLeft payload =>
      cases payload with
      | var found =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at found
        cases found
        exact ⟨rfl,rfl⟩
  | caseRight actual _ => cases (evaluation_deterministic actual.sound argument).1

include syntaxTree wellFormed runtime covers escaped extend runtimeOf in
/-- Native operand/body prefixes retain their original strict sizes. The Source
trace is reconstructed independently at the same reached argument and body pools. -/
theorem reflects_raw_at (budget : Nat)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    (tree : Tree source certificate scope ids (principal.named.inputs.map (fun binding => binding.1.scheme.body)) codes)
    (nativeTypes : codes.map (·.type) = principal.named.inputs.map Prod.snd)
    (packedType : principal.named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)
    (unique : NodeOccurrencesUnique source)
    {operand : TypeSystem.Ty} {parameterTypes returnTypes : List TypeSystem.Ty} {predicates : List ProgramPredicate}
    {traitName methodName : String} {requirements : List RequirementId}
    (typing : ExpressionsHaveTypes source context ids parameterTypes)
    (operatorProfile : OperatorProfileInstantiates context traitName methodName operand parameterTypes returnTypes predicates)
    (proves : RequirementSequenceProves context requirements predicates)
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence
      traitName methodName requirements principal.sourceBody principal.dictionary)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {callerAdministrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value} {size : Nat} {reason : Word}
    (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
      (administrative := methodAdministrative) functions mapping world before store actual)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameFrame : installed.frameLocation = owner.key.frameLocation)
    (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
      callerAdministrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope,mapping,world,before,store,canonical⟩)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store (SourceCoreCalls.call principal.named.signature installed.globalIndex
      ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore)
    (within : size ≤ budget) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.Arguments.Trace (Program.ofChecked compiled.sourceProgram) context evidence principal.dictionary source environment
        before ids principal.sourceBody outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩ := by
  obtain ⟨argumentSize,argumentValue,middleStore,argumentStrict,argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨_sourceSize,argumentOutcome,middle,middleMap,middleWorld,argumentTrace,argumentRep,middleHeaps,
      argumentMaps,argumentWorlds,argumentFrame,argumentMetadata,argumentState,argumentRelated,argumentPost⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique typing children
      environments heaps locals agrees typed initial admitted argumentEvaluation (Nat.lt_of_lt_of_le argumentStrict within)
  cases argumentRep with
  | fault matched =>
    cases argumentTrace with
    | fault failed =>
      obtain ⟨rfl,rfl⟩ := call_fault (packedType.symm ▸ argumentEvaluation.sound) completed
      exact ⟨.fault _,middle,middleMap,middleWorld,.argumentFault failed.sound,.fault matched,middleHeaps,
        argumentMaps,argumentWorlds,argumentFrame,argumentMetadata,argumentState,argumentRelated⟩
  | @values arguments payloads represented =>
    cases argumentTrace with
    | values evaluatedArguments =>
      rw [nativeTypes] at represented
      have nativeArguments := arguments_of_values principal.named.inputs represented
      let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
      have raw := after_operands wellFormed runtime covers locals admitted.heap typing evaluatedArguments.sound
      have callee := CallableIndexedOwnedOperatorSourceAdmission.at_selected_arguments principal profile wellFormed runtime
        operatorProfile proves selected raw.2 raw.1
      obtain ⟨bodySize,bodyStrict,bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
        argumentEvaluation.sound installed.globalReference next.globalRead completed
      obtain ⟨sourceSize,outcome,after,finalMap,finalWorld,bodyTrace,resultRep,finalHeaps,
          bodyMaps,bodyWorlds,bodyFrame,bodyMetadata,bodyState,bodyRelated⟩ :=
        CallableIndexedOwnedExtendedReadyMethodInvocationBounds.invocation_reflects_at
          principal profile functions escaped extend runtimeOf next owner (bridge.pool argumentState)
          wellFormed callee.1 callee.2.1 (argumentPost.successful arguments rfl).rows observed syntaxTree
          nativeArguments sameFrame middleHeaps budget below bodyEvaluation
          (Nat.le_of_lt (Nat.lt_of_lt_of_le bodyStrict within))
      obtain ⟨returned,_same,related⟩ := bridge.restore initial bodyState (argumentMaps.trans bodyMaps)
        (argumentWorlds.trans bodyWorlds) (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
        ((bridge.related argumentRelated).trans bodyRelated)
      refine ⟨outcome,after,finalMap,finalWorld,?_,resultRep,finalHeaps,argumentMaps.trans bodyMaps,
        argumentWorlds.trans bodyWorlds,argumentFrame.trans bodyFrame,argumentMetadata.trans bodyMetadata,returned,related⟩
      cases bodyTrace with
      | value invoked => exact .apply evaluatedArguments.sound (.value invoked.sound)
      | fault failed => exact .apply evaluatedArguments.sound (.fault failed.sound)

section Parent
open CallablePreparedMethodSelection CallableCoercionExpressionCertificates
variable {project : Projector} {callerFunction : Specialized} {compilation : SourceCoreFunctions.Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {id : ExpressionId} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : Lowered}
  (receipt : Operator compiled.sourceProgram project callerFunction compilation child fuel source scope id reasonAt policy node output)
  (alignment : OperatorAlignment (named := principal.named) (sourceBody := principal.sourceBody) (dictionary := principal.dictionary) receipt)
  (operatorSource : OperatorSource receipt)
  (anchor : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence
    operatorSource.traitName operatorSource.methodName receipt.requirements principal.sourceBody principal.dictionary)
  (catalogIdentity : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)

include alignment in
private theorem output_type (coercions : node.coercions = []) :
    output.type = principal.named.signature.resultType := by
  have suffix := receipt.suffix.accepted
  rw [coercions] at suffix
  have same : receipt.operand = output := Except.ok.inj suffix
  rw [← same,receipt.native.emitted,alignment.signature]

include syntaxTree wellFormed runtime covers escaped extend runtimeOf alignment operatorSource anchor catalogIdentity ledger in
/-- The complete original prepared parent keeps its actual Source dictionary.
Empty coercions expose the raw call, whose real reached pool supplies admission. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    (coercions : node.coercions = [])
    (tree : Tree source certificate scope receipt.arguments (principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (nativeTypes : receipt.loweredArguments.map (·.type) = principal.named.inputs.map Prod.snd)
    (unique : NodeOccurrencesUnique source) (parentTyped : ExpressionHasType source context id node.type)
    (children : ∀ childSize, childSize < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults childSize)
    {mapping : LocationMap} {world : StoreTyping} {callerAdministrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
      (administrative := methodAdministrative) functions mapping world before store actual)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameFrame : installed.frameLocation = owner.key.frameLocation)
    (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
      callerAdministrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope,mapping,world,before,store,canonical⟩)
    (admitted : Admission bridge context initial)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size context evidence source environment
      before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached := by
  obtain ⟨operand,parameterTypes,returnTypes,predicates,sourceTyping,operatorProfile,proves,resultType⟩ :=
    CallableIndexedOwnedOperatorSourceAdmission.source_facts operatorSource unique coercions parentTyped
  obtain ⟨_,_,_,bodyResult⟩ := anchor.certificateOfProfile wellFormed runtime.signatures runtime.requirements.idsUnique operatorProfile proves
  have sameResult : principal.sourceBody.resultType = node.type := bodyResult.trans resultType.symm
  have packedType : principal.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    simpa only [alignment.signature] using receipt.native.inputType
  have emitted := alignment.emitted receipt coercions ξ
  rw [← located] at emitted
  have shape : (∃ id, receipt.arguments = [id]) ∨ (∃ left right, receipt.arguments = [left,right]) := by
    rcases receipt.form with ⟨_,operand,_,arguments⟩ | ⟨_,left,right,_,arguments⟩
    · exact .inl ⟨operand,arguments⟩
    · exact .inr ⟨left,right,arguments⟩
  have run : ∀ {rawSize rawOutcome rawAfter dictionary},
      Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence
        operatorSource.traitName operatorSource.methodName receipt.requirements principal.sourceBody dictionary →
      RawTraceAt (Program.ofChecked compiled.sourceProgram) rawSize context evidence dictionary source environment
        before receipt.arguments principal.sourceBody rawOutcome rawAfter → rawSize < size →
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store (output.expression.rename ξ) value finalStore ∧
        GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          finalMap finalWorld node.type output.type faults rawOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld rawAfter finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rawAfter ∧
        ProtectedStateTransition.Transition callerProtocol initial ⟨scope,finalMap,finalWorld,rawAfter,finalStore,canonical⟩ := by
    intro rawSize rawOutcome rawAfter dictionary actualSelected rawTrace rawStrict
    let actualPrincipal := CallableIndexedOwnedMethodPrincipal.of_selected principal.cached actualSelected
    let actualProfile := CallableIndexedOwnedOperatorSourceAdmission.with_dictionary principal profile dictionary actualPrincipal.dictionary_covers
    have actualExtend : ∀ {context next binder},
        CallableIndexedOwnedOperatorSourceAdmission.EvidenceValidity (validity := validity) dictionary context →
        BinderExtends principal.sourceBody.source.owner context binder next →
        CallableIndexedOwnedOperatorSourceAdmission.EvidenceValidity (validity := validity) dictionary next :=
      fun valid extended => CallableIndexedOwnedOperatorSourceAdmission.evidence_extend (principal := principal) dictionary extend valid extended
    have actualRuntime : ∀ {context},
        CallableIndexedOwnedOperatorSourceAdmission.EvidenceValidity (validity := validity) dictionary context →
        CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context dictionary :=
      fun valid => CallableIndexedOwnedOperatorSourceAdmission.evidence_runtime (principal := principal) dictionary runtimeOf valid
    obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,resultRep,finalHeaps,maps,worlds,frame,metadata,transition⟩ :=
      preserves_raw_at bridge actualPrincipal actualProfile functions escaped actualExtend actualRuntime wellFormed runtime covers syntaxTree
        budget rawSize (Nat.le_of_lt (Nat.lt_of_lt_of_le rawStrict within)) below shape tree nativeTypes packedType unique
        sourceTyping operatorProfile proves actualSelected children installed owner sameFrame observed environments heaps locals agrees typed initial admitted rawTrace
    change FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults rawOutcome value at resultRep
    rw [sameResult,← output_type principal receipt alignment coercions] at resultRep
    exact ⟨value,finalStore,finalMap,finalWorld,emitted.symm ▸ evaluated,resultRep,finalHeaps,maps,worlds,frame,metadata,transition⟩
  have raw := CallablePreparedOperatorSourceBounds.OperatorSource.source_inv_sized operatorSource catalogIdentity ledger anchor unique trace
  have finished : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩ := by
    cases raw with
    | @rawFault rawSize sourceReason sourceAfter raw strict =>
      obtain ⟨dictionary,actualSelected,rawTrace⟩ := raw
      exact run (rawOutcome := .fault sourceReason) (rawAfter := after) actualSelected rawTrace strict
    | path raw path rawStrict _ =>
      obtain ⟨dictionary,actualSelected,rawTrace⟩ := raw
      cases outcome with
      | value value =>
        dsimp only [PathAt] at path
        rw [coercions] at path
        cases path
        exact run actualSelected rawTrace rawStrict
      | fault reason =>
        dsimp only [PathAt] at path
        rw [coercions] at path
        cases path
  obtain ⟨value,finalStore,finalMap,finalWorld,evaluated,resultRep,finalHeaps,maps,worlds,frame,metadata,reached,related⟩ := finished
  exact ⟨value,finalStore,finalMap,finalWorld,evaluated,resultRep,finalHeaps,maps,worlds,frame,metadata,reached,related,
    after_expression_sized (bridge := bridge) initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

include syntaxTree wellFormed runtime covers escaped extend runtimeOf alignment operatorSource anchor in
/-- The measured native parent reflects its own strict operand/body prefixes.
A genuine Source parent is independently reconstructed, then authenticates the
successful raw heap at that identical returned caller state. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    (coercions : node.coercions = [])
    (tree : Tree source certificate scope receipt.arguments (principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (nativeTypes : receipt.loweredArguments.map (·.type) = principal.named.inputs.map Prod.snd)
    (unique : NodeOccurrencesUnique source) (parentTyped : ExpressionHasType source context id node.type)
    (children : ∀ childSize, childSize < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults childSize)
    {mapping : LocationMap} {world : StoreTyping} {callerAdministrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
      (administrative := methodAdministrative) functions mapping world before store actual)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameFrame : installed.frameLocation = owner.key.frameLocation)
    (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
      callerAdministrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope,mapping,world,before,store,canonical⟩)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store (output.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source environment
        before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope,finalMap,finalWorld,after,finalStore,canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached := by
  obtain ⟨operand,parameterTypes,returnTypes,predicates,sourceTyping,operatorProfile,proves,resultType⟩ :=
    CallableIndexedOwnedOperatorSourceAdmission.source_facts operatorSource unique coercions parentTyped
  obtain ⟨_,_,_,bodyResult⟩ := anchor.certificateOfProfile wellFormed runtime.signatures runtime.requirements.idsUnique operatorProfile proves
  have sameResult : principal.sourceBody.resultType = node.type := bodyResult.trans resultType.symm
  have packedType : principal.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    simpa only [alignment.signature] using receipt.native.inputType
  have emitted := alignment.emitted receipt coercions ξ
  rw [← located] at emitted
  rw [emitted] at completed
  obtain ⟨outcome,after,finalMap,finalWorld,rawTrace,resultRep,finalHeaps,maps,worlds,frame,metadata,reached,related⟩ :=
    reflects_raw_at bridge principal profile functions escaped extend runtimeOf wellFormed runtime covers syntaxTree
      budget below tree nativeTypes packedType unique sourceTyping operatorProfile proves anchor children installed
      owner sameFrame observed environments heaps locals agrees typed initial admitted completed within
  rw [sameResult,← output_type principal receipt alignment coercions] at resultRep
  have sourceTrace := operatorSource.expression anchor coercions rawTrace
  obtain ⟨sourceSize,sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size sourceTrace
  exact ⟨sourceSize,outcome,after,finalMap,finalWorld,sized,resultRep,finalHeaps,maps,worlds,frame,metadata,reached,related,
    after_expression_sized (bridge := bridge) initial reached admitted wellFormed runtime covers locals parentTyped sized frame⟩
end Parent
end MethodCall

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyOperatorSourceBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSingletonReturnCompilerReceipts
/-! The same selected lambda certificate supplies the actual singleton-return
child callback and finish expression. The original minimum compiler budget is
retained separately from any semantic read or execution index. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSingletonReturnCompilerReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedLiteralReturnSiteShells

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

/-- This receipt contains successful compiler equations and the exact emitted
finish wrapper. It contains no child evaluation or body execution law. -/
structure Receipt (expression : ExpressionId) where
  budget : Nat
  child : SourceCoreBasic.LoweredExpr
  accepted : (bodyPolicy produced.compilation produced.site.code).lowerExpression budget
    produced.site.code.view
    (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    expression produced.site.code.reasonAt = .ok child
  resultType : child.type = produced.site.code.receipt.resultCore
  emitted : produced.site.code.receipt.body =
    LocalControl.finish produced.site.code.receipt.resultCore
      (LocalLoop.toControl produced.site.code.receipt.resultCore
        (LocalLoop.returnValue produced.site.code.receipt.resultCore child.expression)
        produced.site.code.compilation.internalReason)
      (if produced.site.code.receipt.resultCore = .unit then LanguageResult.success .unit
       else LanguageResult.failure produced.site.code.receipt.resultCore
         (.word produced.site.code.compilation.internalReason))

/-- Inversion uses the original accepted body once, at its actual chosen Site. -/
theorem of_return {statement : StatementId} {node : StatementNode} {statementType : Ty}
    {expression : ExpressionId}
    (singleton : statements = [statement])
    (read : (bodyPolicy produced.compilation produced.site.code).readStatement produced.site.code.view statement =
      .ok (node, statementType))
    (form : node.form = .returnStmt (some expression)) :
    Nonempty (Receipt produced expression) := by
  have accepted := body_accepted produced
  conv at accepted => lhs; arg 5; rw [singleton]
  obtain ⟨budget, child, generated, sameType, emitted⟩ :=
    CallableIndexedLambdaScalarNativeTyping.scalar_body_receipt read (Or.inl form) accepted
  exact ⟨⟨budget, child, generated, sameType, emitted⟩⟩

variable {expression : ExpressionId} (receipt : Receipt produced expression)

/-- The real body callback keeps its own minimum fuel and selected policy. -/
theorem Receipt.functions_child :
    SourceCoreFunctions.lowerExpressionWithPolicy produced.site.code.policy produced.site.code.lowerBody
      (min receipt.budget produced.site.code.fuel) produced.site.code.compilation produced.site.code.view
      (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression produced.site.code.reasonAt = .ok receipt.child := by
  exact receipt.accepted

section Root
variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := compiled) caller.named diagnostics namedCode compilation
      rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- Genuine callback identities place the same child action under its original
root. No compiler callback, Source row or selected Site is reconstructed. -/
theorem Receipt.at_root
    (policy : produced.site.code.policy = root.selected.policy)
    (body : produced.site.code.lowerBody = root.selected.lowerBody)
    (canonical : produced.site.code.view = source caller.named)
    (reason : produced.site.code.reasonAt = rootReasonAt) :
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (min receipt.budget produced.site.code.fuel) (context compiled.indexed caller.named) (source caller.named)
      (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression rootReasonAt = .ok receipt.child := by
  have actual := receipt.functions_child produced
  conv at actual => lhs; arg 1; rw [policy]
  conv at actual => lhs; arg 2; rw [body]
  conv at actual => lhs; arg 4; rw [produced.site.compilation]
  conv at actual => lhs; arg 5; rw [canonical]
  conv at actual => lhs; arg 8; rw [reason]
  exact actual

end Root
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSingletonReturnCompilerReceipts
end
