import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableMethodResolverTable
import Solcore.SourceSemantics.CoreLowering.CachedMethodEvidenceCoherence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DiscardSequences
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Coercions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticProducers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentProvenance
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedScopedPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedImperative
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical

/-!
# Staged bounds: scoped method roots

Scoped method bodies: selection issuance, caller evidence, static support, collectors and bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionIssuer
/-! One issuer dispatches the existing empty-method catalog and the validated
full-evidence and actual-origin catalogs. Named and closure collectors share the same proof bodies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionIssuer
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableNamedMetadata (environment)

inductive Catalog (compiled : SourceCoreUnifiedCompilation.Compiled) where
  | generic (catalog : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)
  | evidence (catalog : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog compiled)
  | origins (catalog : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog compiled)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  (actual : Operator compiled.sourceProgram project caller compilation
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation) (fuel+1)
    source scope id reasonAt policy.callables receipt.node lowered)
  (special : (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation
        (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation)
        (fuel+1) source scope id reasonAt) = .ok (some lowered))

include receipt actual special in
/-- Complete static evidence is recovered from the actual compiler table.
The public body family supplies no method execution or dictionary equality. -/
theorem of_actual
    (selected : OperatorSource actual)
    (methods : Catalog compiled)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (sourceUnique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
      receipt context callerEvidence (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  cases methods with
  | generic methods =>
      let authentic := CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.authentic receipt actual special
      have support := CallableIndexedOwnedPreparedStagedGenericMethodSelection.selection_support
        authentic checked wellFormed methods selected signatures ledger assumptions sourceUnique unique typed
      exact CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.of_actual receipt actual special
        selected support checked wellFormed catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary actualStages
  | evidence methods =>
      exact CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.of_actual receipt actual special
        selected methods checked wellFormed catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary sourceUnique typed actualStages
  | origins methods =>
      exact CallableIndexedOwnedPreparedStagedOriginsMethodSelection.of_actual receipt actual special
        selected methods checked wellFormed catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary sourceUnique typed actualStages

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionIssuer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyViewTransport
/-! Selected method and direct actions cross the same unchanged body occurrences.
The actual callee check and ordered child actions agree before the retained
compiler hook is compared; dictionaries are never replaced or assumed equal. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyViewTransport
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax OperatorForm)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open CallableIndexedOwnedPreparedStagedOrdinaryMethodPolicy

/-- Equal original operator nodes and ordered operand actions retain exactly
    the same authenticated method selection, including errors. -/
theorem operator_evidence_eq
    (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (compilation : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    {source view : TypedSource} (scope : SourceCoreLocalCell.Scope)
    {id : ExpressionId} (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (viewFound : view.lookupExpression? id = some node)
    (form : (∃ operator operand, node.form = .unary operator operand) ∨
      (∃ operator left right, node.form = .binary left operator right))
    (coercions : node.coercions = [])
    (children : ∀ argument, RuntimeChild node.form argument →
      child budget source scope argument reasonAt = child budget view scope argument reasonAt) :
    SourceCoreEvidence.lowerWithProjector program projector caller compilation child budget source scope id reasonAt callables =
      SourceCoreEvidence.lowerWithProjector program projector caller compilation child budget view scope id reasonAt callables := by
  have ordinary := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.ordinary_requirements coercions
  rcases form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
  · have operandSame := children operand (by simp [RuntimeChild, form, ExpressionForm.references])
    by_cases empty : node.requirements = []
    · simp [SourceCoreEvidence.lowerWithProjector, found, viewFound, form, ordinary, coercions, empty]
    · have nonempty : node.requirements.isEmpty = false := by cases h : node.requirements <;> simp_all
      simp [SourceCoreEvidence.lowerWithProjector, found, viewFound, form, ordinary,
        coercions, nonempty, bind, Except.bind, pure, Except.pure, operandSame]
  · have leftSame := children left (by simp [RuntimeChild, form, ExpressionForm.references])
    have rightSame := children right (by simp [RuntimeChild, form, ExpressionForm.references])
    by_cases empty : node.requirements = []
    · simp [SourceCoreEvidence.lowerWithProjector, found, viewFound, form, ordinary, coercions, empty]
    · have nonempty : node.requirements.isEmpty = false := by cases h : node.requirements <;> simp_all
      simp [SourceCoreEvidence.lowerWithProjector, found, viewFound, form, ordinary,
        coercions, nonempty, bind, Except.bind, pure, Except.pure, List.mapM_cons, List.mapM_nil,
        leftSame, rightSame]

section Recipe
variable {directSites : DeclarationInstantiation → Prop}
  {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation prepared named diagnostics namedCode}
  {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
  (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
  {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  (metadata : MetadataFor prepared named source directSites)

include recipe edited avoids metadata in
theorem recipe_read_view (id : ExpressionId) (reached : Reaches source roots (.expression id)) :
    policy.readExpression source id = policy.readExpression view id := by
  have same := expression_lookup edited avoids reached
  rw [recipe.readExpression]
  cases found : source.lookupExpression? id with
  | none =>
    have viewed := same.symm.trans found
    simp only [SourceCoreGeneralFunctions.contextualSource, found, viewed]
    rfl
  | some node =>
    have viewed := same.symm.trans found
    have contextual (current : TypedSource) (lookup : current.lookupExpression? id = some node) :
        SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
          (context prepared named).plan prepared.base.locals (context prepared named).owner none current id = .ok current := by
      simp only [SourceCoreGeneralFunctions.contextualSource, lookup, bind, Except.bind, pure, Except.pure]
      split
      · next name binder form =>
        have noLocal := metadata.localRead id (.leaf (.read found form)) node found name binder form
        simp only [noLocal, Bool.false_eq_true, ↓reduceIte]
      · rfl
    simp only [contextual source found, contextual view viewed, bind, Except.bind]
    change SourceCoreCompatibleDataExpressions.readExpression checked source id =
      SourceCoreCompatibleDataExpressions.readExpression checked view id
    exact CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.compatible_read_eq edited.metadata same

include recipe edited avoids metadata in
theorem compiler_eq_on
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [])
    (body : SourceCoreFunctions.BodyLowerer) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) (fuel : Nat)
    {id : ExpressionId} (tree : GeneralSyntax source id directSites)
    (reached : Reaches source roots (.expression id)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel (context prepared named) source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel (context prepared named) view scope id reasonAt := by
  have sourceMetadata := CallableIndexedOwnedPreparedStagedOrdinaryMethodPolicy.MetadataFor.on metadata
    (fun id => Reaches source roots (.expression id))
  have viewMetadata := viewed_metadata edited avoids metadata
  have sourceProfile := reads_on recipe sourceMetadata
  have viewProfile := reads_on recipe viewMetadata
  induction fuel generalizing id with
  | zero => simp only [SourceCoreFunctions.lowerExpressionWithPolicy]
  | succ fuel ih =>
    obtain ⟨node, found⟩ := syntax_found tree
    have lookup := expression_lookup edited avoids reached
    have viewFound := lookup.symm.trans found
    have viewTree := syntax_view edited avoids tree reached
    have children : ∀ child, RuntimeChild node.form child →
        SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel (context prepared named) source scope child reasonAt =
          SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel (context prepared named) view scope child reasonAt := by
      intro child edge
      exact ih (syntax_child tree found edge) (.expression reached found (runtime_child_references edge))
    apply CallableIndexedOwnedPreparedStagedGeneralBodyViewTransport.compiler_step_eq_of_hook
      edited avoids sourceProfile viewProfile callables
      (recipe_read_view recipe edited avoids metadata) fuel tree reached found children
    by_cases direct : ∃ callee ids instantiation, node.form = .call callee ids (.declaration instantiation)
    · obtain ⟨callee, ids, instantiation, form⟩ := direct
      let child : SourceCoreFunctions.ExpressionLowerer :=
        fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
            (context prepared named) childSource childScope childId childReasonAt
      refine (direct_hook_on recipe sourceMetadata reached tree found form child (fuel + 1) scope reasonAt).trans ?_
      refine Eq.trans ?_ (direct_hook_on recipe viewMetadata (reached.metadata edited.metadata)
        viewTree viewFound form child (fuel + 1) scope reasonAt).symm
      apply CallableIndexedOwnedPreparedStagedEvidenceBodyViewTransport.direct_evidence_eq _ _ _ _ _ _ _ _ _ found viewFound form
      · exact expression_lookup edited avoids (.expression reached found (by simp [form, ExpressionForm.references]))
      · intro argument member
        have same := children argument (by simp [RuntimeChild, form, member])
        simpa only [child, Nat.min_eq_right (Nat.le_succ fuel)] using same
    · by_cases operator : OperatorForm node.form
      · have form : (∃ op operand, node.form = .unary op operand) ∨
            (∃ op left right, node.form = .binary left op right) := by
          cases formEq : node.form <;> simp [formEq, OperatorForm] at operator
          · exact .inl ⟨_, _, rfl⟩
          · exact .inr ⟨_, _, _, rfl⟩
        let child : SourceCoreFunctions.ExpressionLowerer :=
          fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
              (context prepared named) childSource childScope childId childReasonAt
        refine (operator_hook_on recipe sourceMetadata reached tree found form child (fuel + 1) scope reasonAt).trans ?_
        refine Eq.trans ?_ (operator_hook_on recipe viewMetadata (reached.metadata edited.metadata)
          viewTree viewFound form child (fuel + 1) scope reasonAt).symm
        apply operator_evidence_eq _ _ _ _ _ _ _ _ _ found viewFound form (metadata.coercions id tree node found)
        intro argument edge
        simpa only [child, Nat.min_eq_right (Nat.le_succ fuel)] using children argument edge
      · have ordinary : tree.NonDirect := by
          intro actual selected callee ids instantiation form
          have same := Option.some.inj (selected.symm.trans found)
          subst actual
          exact direct ⟨callee, ids, instantiation, form⟩
        have primitive : tree.NonOperator := by
          intro actual selected form
          have same := Option.some.inj (selected.symm.trans found)
          exact operator (same ▸ form)
        have viewedOrdinary : viewTree.NonDirect := by
          intro actual selected callee ids instantiation form
          exact ordinary actual (lookup.trans selected) callee ids instantiation form
        have viewedPrimitive : viewTree.NonOperator := by
          intro actual selected form
          exact primitive actual (lookup.trans selected) form
        rw [recipe.lowerSpecial]
        exact (special_none_on compilation rootFuel sourceMetadata reached tree ordinary primitive _ _ scope reasonAt).trans
          (special_none_on compilation rootFuel viewMetadata (reached.metadata edited.metadata)
            viewTree viewedOrdinary viewedPrimitive _ _ scope reasonAt).symm

end Recipe

/-- Transfer the actual ordinary body compiler action using its retained named
recipe and the original body's reached metadata. -/
theorem accepted_original
    {directSites : DeclarationInstantiation → Prop}
    {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function parameterScope administrative)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
    (metadata : MetadataFor compiled.indexed named function.source directSites)
    {scope : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralSyntax function.source id directSites)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation code.view scope id code.reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation function.source scope id code.reasonAt = .ok lowered := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation] at accepted ⊢
  exact (compiler_eq_on recipe (CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource)
    (CallableIndexedLambdaBodyViewEdits.avoids bodyView) metadata callables code.lowerBody scope code.reasonAt fuel tree reached).trans accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyViewTransport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerEvidence
/-! The genuine method selector and implementation catalog determine
its complete caller dictionary. Parameter and lexical contexts preserve the
actual ledger and requirement identities used by later direct calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerEvidence
open Frontend SourceInference
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (ResolvedCaller)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method)

structure CallerAt (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) where
  resolved : ResolvedCaller compiled.sourceProgram principal.named.specialized evidence
  signatures : context.signatures = compiled.sourceProgram.signatures
  ledger : context.solvedRequirements = principal.named.specialized.function.solvedRequirements
  assumptions : ∀ goal, goal ∈ principal.named.specialized.assumptions → goal ∈ context.assumptions
  unique : RequirementIdsUnique context

/-- The selected method's complete assumption list follows from its real
trait, implementation and method catalog entries. -/
theorem assumptions_empty_generic
    (catalog : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram) :
    principal.sourceBody.context.assumptions = [] := by
  obtain ⟨implementation, declaration, trait, definition, substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro implementationMember methodMember traitMember _owner _member _id _bodyOwner _exact _range _source _result context =>
    have empty := catalog.assumptions implementation implementationMember declaration methodMember trait traitMember
    rw [context]
    change List.map _ (implementation.methodAssumptions trait declaration) = []
    rw [empty]
    rfl

/-- Actual selection assembles precisely the empty method dictionary; no
statement about resolver agreement is inferred from coverage alone. -/
def of_selected_generic
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (catalog : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context}
    (fields : Dynamic.RuntimeContextFields sourceAt.context context) :
    CallerAt principal context child.evidence := by
  have empty := assumptions_empty_generic principal catalog
  have dictionary := RecursiveMethodSelectionIdentity.dictionary_empty principal.selected empty
  have callerEmpty : principal.named.specialized.assumptions = [] := by
    rw [principal.cached.same]
    exact empty
  have parameters := RecursiveNamedInitialContextValidity.mono_fields sourceAt.extended
  refine ⟨⟨[], ?_, ?_⟩, ?_, fields.solvedRequirements.trans sourceAt.valid.ledger, ?_, ?_⟩
  · rw [callerEmpty]
    rfl
  · rw [stages.evidence selected]
    exact dictionary
  · exact fields.signatures.trans (parameters.signatures.trans rfl)
  · intro goal member
    rw [callerEmpty] at member
    cases member
  · exact (fields.runtimeRequirementLedger sourceAt.valid.runtime).idsUnique

/-- The closed-catalog entry point retains its original signature. -/
theorem assumptions_empty
    (catalog : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram) :
    principal.sourceBody.context.assumptions = [] :=
  assumptions_empty_generic principal (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed catalog)

/-- Existing callers use the same authentic selected frame and dictionary. -/
def of_selected
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (catalog : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context}
    (fields : Dynamic.RuntimeContextFields sourceAt.context context) :
    CallerAt principal context child.evidence :=
  of_selected_generic principal sourceAt
    (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed catalog) selected fields

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerEvidence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerResolvedEvidence
/-! An authentic complete method resolver receipt survives parameter entry
and lexical context changes. The method's own assumptions remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerResolvedEvidence
open Frontend SourceInference
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (ResolvedCaller)
open CallableIndexedOwnedPreparedStagedMethodCallerEvidence (CallerAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}

def of_selected (principal : Principal compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (resolved : ResolvedCaller compiled.sourceProgram principal.named.specialized principal.dictionary)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context}
    (fields : Dynamic.RuntimeContextFields sourceAt.context context) :
    CallerAt principal context child.evidence := by
  have parameters := RecursiveNamedInitialContextValidity.mono_fields sourceAt.extended
  refine ⟨?_, fields.signatures.trans (parameters.signatures.trans rfl),
    fields.solvedRequirements.trans sourceAt.valid.ledger, ?_,
    (fields.runtimeRequirementLedger sourceAt.valid.runtime).idsUnique⟩
  · rw [stages.evidence selected]
    exact resolved
  · intro goal member
    rw [fields.assumptions, parameters.assumptions]
    change goal ∈ method.specialized.assumptions
    simpa only [principal.cached.same] using member

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerResolvedEvidence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport
/-! Scoped method packets retain the actual selected implementation, complete
Source dictionary, parameter context and accepted flow. Reached children keep
their original lexical fields and mixed expression roots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallablePreparedMethodRuntimeProfileFactory (SourceAt policy scope)
open CompatibleEncoding (bind_ok)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method)

abbrev parameterScope : SourceCoreLocalCell.Scope := scope (named := principal.named)

def nativePrefix : Core.Context :=
  principal.named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
    [.cell compiled.indexed.ancestry.layout.frame.type]

structure Packet where
  sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
    principal.sourceBody principal.dictionary
  flow : Expr
  accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy principal.cached.compilation)
    compiled.indexed.fuel principal.sourceBody.source (parameterScope principal)
    principal.cached.compilation.statements principal.named.signature.resultType
    (principal.cached.diagnostics.reasonAt principal.named.signature.key) true
    principal.cached.compilation.own.table.escapedReason = .ok flow
  emitted : principal.cached.compilation.body = CompatibleStatements.finish
    principal.named.signature.resultType flow principal.cached.compilation.own.fellThroughReason
    principal.cached.compilation.own.table.escapedReason
  shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape principal.sourceBody.source true
    principal.cached.compilation.statements

/-- The real accepted method body determines its flow without any execution premise. -/
theorem of_accepted
    (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
      principal.sourceBody principal.dictionary)
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape principal.sourceBody.source true
      principal.cached.compilation.statements) : Nonempty (Packet principal) := by
  have accepted := sourceAt.accepted principal.cached.compilation
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  exact ⟨⟨sourceAt, flow, generated, (Except.ok.inj returned).symm, shape⟩⟩

theorem statements (packet : Packet principal)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ final facts, StatementsHaveType principal.sourceBody.source {returnType := principal.sourceBody.resultType}
      packet.sourceAt.context principal.cached.compilation.statements final facts ∧
      BodyCompletes principal.sourceBody.resultType facts := by
  obtain ⟨facts, typed⟩ := CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.source_typing
    principal packet.sourceAt wellFormed
  obtain ⟨final, body, _roots, complete⟩ := typed.typing.body_typed
  refine ⟨final, facts, ?_, complete⟩
  have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
      | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
    principal.source_frame.roots.filterMap_eq
  exact roots ▸ body

theorem runtime (packet : Packet principal)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      packet.sourceAt.context principal.sourceBody.source := by
  obtain ⟨_facts, typed⟩ := CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.source_typing
    principal packet.sourceAt wellFormed
  exact typed.sourceRuntimeValid.transport (RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended)

abbrev Certificate
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ root : CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt compiled headers stages
      context invocation scope id lowered semanticFaults,
    root.compilation.administrativePrefix = 1

structure Support (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep) : Prop where
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    principal.sourceBody.source (fun site root => principal.cached.diagnostics.placeReason principal.named.signature.key site root none) (fun site root raw => principal.cached.diagnostics.placeReason principal.named.signature.key site root (some raw)))
  tree : ∀ child, stages.Closure principal.sourceFunction child →
    ∃ expressionSyntax : ExpressionId → Prop,
      CallableIndexedOwnedPreparedBranchingCatalogSites.Collected (fun site root => principal.cached.diagnostics.placeReason principal.named.signature.key site root none)
        (fun site root raw => principal.cached.diagnostics.placeReason principal.named.signature.key site root (some raw)) (faults := semanticFaults) compiled.indexed.layouts
        principal.named.signature.key [] compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
        (fun error => .sourceAllocation (reprStr error)) (.initial compiled.compatible.checked)
        child.source expressionSyntax
        (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate child.source
          (fun context => Certificate headers stages semanticFaults context child))
        compiled.indexed.layouts.definitions (nativePrefix principal)
        packet.sourceAt.context (parameterScope principal) (.statements true principal.cached.compilation.statements)
        principal.sourceBody.resultType principal.named.signature.resultType packet.flow

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedCollectors
/-! The actual cached implementation and its accepted flow provide native child
typing. The one compiler traversal preserves every reached lexical context and
the selected method's original Source ledger and full dictionary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport
open CallablePreparedMethodRuntimeProfileFactory (policy)
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {recipe : SourceCoreIndexedSession.Recipe}
  (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (member : entry ∈ compiled.indexed.entries)

include ready member in
/-- The complete physical cache bounds the actual method closure's native slots. -/
theorem body_typed :
    HasType (SourceCoreLocalCell.coreContext (parameterScope principal) ++ nativePrefix principal)
      principal.cached.compilation.body (LanguageResult.resultType principal.named.signature.resultType)
      compiled.indexed.layouts.definitions := by
  have cached := CallableIndexedCachedNativeTyping.prepared_native_closure compiled.indexedPrepared member
    principal.cached.cached (CallableIndexedPreparedInventories.cached_global_at compiled principal.cached.selected)
  have supported := RecursiveNamedCatalogPreparedInitialization.supported_cached ready principal.cached.cached
  rw [principal.cached.compilation.emitted] at cached supported
  have original : HasType ((compiled.indexed.base.globals.map (·.referenceType) ++
      [.cell compiled.indexed.ancestry.layout.frame.type]) ++
        SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (.lambda principal.named.signature.parameterType (LanguageResult.resultType principal.named.signature.resultType)
        principal.cached.compilation.output)
      principal.named.signature.functionType compiled.indexed.layouts.definitions := by
    simpa only [List.append_assoc, List.singleton_append] using cached
  have minimal := NativeExpressionContextSupport.prefix_typing (targetSuffix := []) original
    (by simpa only [List.length_append, List.length_map, List.length_singleton] using supported)
  cases minimal with
  | lambda _ _ body =>
    simpa only [parameterScope, CallablePreparedMethodRuntimeProfileFactory.scope,
      nativePrefix, List.append_nil, List.append_assoc, List.cons_append] using
      CallableIndexedParameterNativeInversion.body_native principal.cached.compilation body

private def matchContext : SourceCoreCompatibleDataMatches.Context :=
  CompatibleMatchAmbientLowering.withDefinitions
    ⟨.initial compiled.compatible.checked, principal.named.specialized.function.solvedRequirements,
      some (CallableIndexedNamedGeneration.allocator compiled.indexed principal.named), none⟩
    compiled.indexed.layouts.definitions

private theorem match_policy : CompatibleMatchAmbientLowering.PolicySuccess
    (policy principal.cached.compilation) (matchContext principal) := by
  apply CompatibleMatchAmbientLowering.PolicySuccess.extend (by rfl)
  exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

private def invalidProjection (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  principal.cached.diagnostics.placeReason principal.named.signature.key site root none

private def invalidOperand (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (operator : Solcore.Syntax.ValueAssignOp) : Word :=
  if operator = .equal then Word.zero else principal.cached.compilation.own.assignments.reasonAt site root (.value operator)

private def invalidUnary (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  principal.cached.compilation.own.assignments.reasonAt site root .bitNot

private def missingDefault (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) (type : TypeSystem.Ty) : Word :=
  principal.cached.diagnostics.placeReason principal.named.signature.key site root (some type)

private theorem assignments : CompatibleAssignmentStatements.AssignmentPolicy
    (policy principal.cached.compilation) (.initial compiled.compatible.checked)
    (invalidProjection principal) (invalidOperand principal) (missingDefault principal) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

private theorem unaryPolicy : CompatibleBitNotStatements.Policy
    (policy principal.cached.compilation) (.initial compiled.compatible.checked)
    (invalidProjection principal) (invalidUnary principal) (missingDefault principal) := rfl

/-- The exact cached method preparation and public issuer supply its operand tokens. -/
theorem operands_of_diagnostic
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {site assignment operator rhs}
    (origin : AssignmentDiagnosticOrigins.Occurs principal.sourceBody.source site assignment operator rhs)
    (profile : operator = .equal ∨ assignment.target.type = .word) :
    AssignmentOperandDiagnostics.OperandsLaw
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) operator
      (invalidOperand principal site assignment.target.root operator) := by
  obtain ⟨first, prepared⟩ := CallableIndexedOwnedAssignmentProvenance.method_assignments principal diagnostic
  exact PreparedBranchingAssignmentDiagnostics.operands prepared
    (fun _ _ represented => CallableIndexedOwnedAssignmentProvenance.cached_operands
      principal.cached diagnostic receiver represented) origin profile

/-- Cached method provenance includes the actual unary entries in its full source. -/
theorem unary_of_diagnostic
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {site assignment}
    (origin : GenericAssignmentUnaryDiagnostics.UnaryOccurs principal.sourceBody.source site assignment)
    (rawWord : assignment.target.type = .word) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.invalidUnaryOperand .bitNot) (invalidUnary principal site assignment.target.root) := by
  obtain ⟨first, prepared⟩ := CallableIndexedOwnedAssignmentProvenance.method_assignments principal diagnostic
  exact GenericAssignmentUnaryDiagnostics.prepared_unary_included prepared
    (fun _ _ represented => CallableIndexedOwnedPublicUnaryAssignmentDiagnostics.cached_unary
      principal.cached diagnostic receiver represented) origin rawWord

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include ready member wellFormed in
/-- Children retain the complete runtime context fields along actual binders. -/
theorem collected
    {faults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs principal.sourceBody.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator
        (invalidOperand principal site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs principal.sourceBody.source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot)
        (invalidUnary principal site assignment.target.root))
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax principal.sourceBody.source expressionSyntax
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields packet.sourceAt.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context →
      expressionSyntax id → principal.sourceBody.source.lookupExpression? id = some node →
      ExpressionHasType principal.sourceBody.source context id node.type →
      (policy principal.cached.compilation).lowerExpression fuel principal.sourceBody.source scope id
        (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ nativePrefix principal)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      certificates context scope id lowered) :
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected (invalidProjection principal) (missingDefault principal) (faults := faults) compiled.indexed.layouts
      principal.named.signature.key [] compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      (fun error => .sourceAllocation (reprStr error)) (.initial compiled.compatible.checked)
      principal.sourceBody.source expressionSyntax
      (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate principal.sourceBody.source certificates)
      compiled.indexed.layouts.definitions (nativePrefix principal)
      packet.sourceAt.context (parameterScope principal) (.statements true principal.cached.compilation.statements)
      principal.sourceBody.resultType principal.named.signature.resultType packet.flow := by
  have body := body_typed principal ready member
  rw [packet.emitted] at body
  obtain ⟨nativeType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow body
  obtain ⟨_, typed⟩ := CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.source_typing
    principal packet.sourceAt wellFormed
  have ownership := typed.local_identity_ownership
  have current := runtime principal packet wellFormed
  exact CallableIndexedOwnedPreparedNativeBranchingCollectors.collected
    (expressionSyntax := expressionSyntax) (certificates := certificates) (LocalView.refl _)
    (by intro id member; cases member) packet.sourceAt.unique rfl
    (by
      intro scope binder monomorphic
      change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
      simp only [SourceCoreGeneralFunctions.contextualBinder, monomorphic, List.isEmpty_nil, ↓reduceIte]
      rfl)
    rfl (assignments principal) (unaryPolicy principal) operands unary (match_policy principal) rfl rfl rfl
    (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    (CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed)
    packet.sourceAt.valid.ledger
    (fun context fields scope fuel id node lowered declarations approved _reached found typed accepted nativeType native =>
      children context fields (scope := scope) (fuel := fuel) (id := id) (node := node)
        (lowered := lowered) declarations approved found typed accepted (nativeType := nativeType) native)
    syntaxTree rfl packet.shape (.refl _) current.variables_closed current.residual_variables_open
    packet.sourceAt.signatures (packet.sourceAt.declarations principal.cached.compilation)
    (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
    packet.sourceAt.projection packet.accepted flowTyped

include ready member wellFormed in
/-- The static family is issued from the original compiler callback at each
actual method stage. It contains no execution or body correspondence premise. -/
theorem of_compiler
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs principal.sourceBody.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw semanticFaults operator
        (invalidOperand principal site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs principal.sourceBody.source site assignment →
      assignment.target.type = .word → semanticFaults (.invalidUnaryOperand .bitNot)
        (invalidUnary principal site assignment.target.root))
    {expressionSyntax : ExpressionId → Prop}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax principal.sourceBody.source expressionSyntax
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType)
    (children : ∀ child, stages.Closure principal.sourceFunction child →
      ∀ context, Dynamic.RuntimeContextFields packet.sourceAt.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context →
      expressionSyntax id → principal.sourceBody.source.lookupExpression? id = some node →
      ExpressionHasType principal.sourceBody.source context id node.type →
      (policy principal.cached.compilation).lowerExpression fuel principal.sourceBody.source scope id
        (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ nativePrefix principal)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      Certificate headers stages semanticFaults context child scope id lowered) :
    Support principal packet headers stages semanticFaults := by
  refine ⟨PreparedAssignmentDiagnosticProducers.cached principal.cached diagnostic
    principal.source_eq.symm packet.sourceAt.unique, ?_⟩
  intro child selected
  rw [stages.source selected]
  exact ⟨expressionSyntax, collected principal packet ready member wellFormed operands unary syntaxTree (children child selected)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots
/-! Authentic direct evidence calls inside selected implementation methods
retain the real caller dictionary and reached lexical ledger. The accepted
method compiler and shared scoped collector supply every child root. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

/-- The initial method profile contains actual references and declaration calls.
The full original node table excludes indirect, indexed and operator-method sites. -/
def DirectSource (source : TypedSource) : Prop :=
  ∀ id node, source.lookupExpression? id = some node →
    (∃ name resolution, node.form = .reference name resolution) ∨
    (∃ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation))

section Resolved
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceForms : DirectSource principal.sourceBody.source)
  {directSites : DeclarationInstantiation → Prop}
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
    compiled.sourceProgram principal.named.specialized principal.dictionary)

local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

private theorem policy_receipt {scope : SourceCoreLocalCell.Scope} {fuel : Nat}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    ∃ predecessor, Nonempty (CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      principal.named principal.cached.diagnostics principal.cached.code principal.cached.compilation
      predecessor principal.sourceBody.source scope id
      (principal.cached.diagnostics.reasonAt principal.named.signature.key) lowered) := by
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext principal.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    principal.cached.compilation.parents principal.cached.compilation.own.assignments principal.cached.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
    compiled.indexed.base.callableContext none none fuel principal.sourceBody.source scope id
    (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered at accepted
  cases fuel with
  | zero => rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted; cases accepted
  | succ predecessor =>
    exact ⟨predecessor, CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
      principal.cached.compilation principal.record accepted⟩

include diagnostic receiver wellFormed sourceForms supported metadata rows covered resolved in
/-- The actual compiler action and selected scope supply a mixed root with all
readiness obligations derived from original Source forms and full context fields. -/
theorem of_child_with_evidence
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields packet.sourceAt.context context)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    (declarations : CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context)
    (tree : GeneralSyntax principal.sourceBody.source id directSites)
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (typed : ExpressionHasType principal.sourceBody.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    Certificate headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨predecessor, ⟨root⟩⟩ := policy_receipt principal accepted
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables supported
    metadata scope (principal.cached.diagnostics.reasonAt principal.named.signature.key)
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    packet.sourceAt.unique declarations profile (fun id node tree found => metadata.coercions id tree node found) tree found typed root.selected.accepted
  let result : RootAt compiled headers stages context child scope id lowered
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := RootAt.ofRoot {
    compilerFuel := predecessor + 1
    accepted := by simpa only [sourceEq] using root.selected.accepted
    certificate := by simpa only [sourceEq] using certificate
    node := node
    found := by simpa only [sourceEq] using found
    rawResult := rfl
    typed := by simpa only [sourceEq] using typed
    sameLedger := fields.solvedRequirements.trans packet.sourceAt.valid.ledger
    runtimeLedger := fields.runtimeRequirementLedger packet.sourceAt.valid.runtime
    unique := sourceEq ▸ packet.sourceAt.unique
    wellFormed := wellFormed
    runtime := by simpa only [sourceEq] using (runtime principal packet wellFormed).transport fields
    covers := by rw [stages.evidence selected]; exact fields.covers packet.sourceAt.valid.covers
    actualFunctionType := by rw [root.callables]; rfl
    uninitialized := by
      intro current id code read _reached location
      exact CallableIndexedOwnedPreparedStagedMethodTerminalSupport.uninitialized principal diagnostic receiver
        packet.sourceAt.unique (by simpa only [sourceEq] using read) location
    callsReady := by
      intro callFuel callScope callId callee ids callMetadata code compiler _path
      rcases sourceForms callId compiler.original (by simpa only [sourceEq] using compiler.found) with
        ⟨name, resolution, form⟩ | ⟨actualCallee, arguments, instantiation, form⟩ <;>
        have impossible := compiler.originalForm <;> simp [form] at impossible
    directReady := by
      intro callFuel callScope callId callee ids instantiation code compiler path
      have originalTree : GeneralSyntax child.source id directSites := by simpa only [sourceEq] using tree
      have childMetadata : MetadataFor compiled.indexed principal.named child.source directSites := by
        simpa only [sourceEq] using metadata
      have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path originalTree
      have site := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax.direct_site
        actualTree compiler.metadata.found compiler.form
      obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory_at compiler rows
        (covered instantiation site compiler.index compiler.signature compiler.target compiler.global) rfl
      rcases CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.accepted_direct_action
        root.compilerPolicy childMetadata actualTree compiler.metadata.found compiler.form compiler.accepted with bypass | authentic
      · obtain ⟨requirements, assumptions⟩ :=
          CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct
            compiler.metadata.found compiler.form bypass
        have special := fun callback budget =>
          (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.direct_hook root.compilerPolicy
            childMetadata actualTree compiler.metadata.found compiler.form callback budget callScope
            (principal.cached.diagnostics.reasonAt principal.named.signature.key)).trans
            (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
              compiler.metadata.coercions assumptions)
        have ordinary := compiler.ordinary special
          (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy root.compilerPolicy childMetadata actualTree)
        exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
          compiler port ordinary requirements context child.evidence⟩⟩
      · obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
          compiler.metadata.found compiler.form authentic
        rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
        let caller := CallableIndexedOwnedPreparedStagedMethodCallerResolvedEvidence.of_selected
          principal packet.sourceAt resolved selected fields
        exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence_of_resolved
          compiler port actual caller.resolved caller.signatures caller.ledger caller.assumptions caller.unique⟩⟩
    indexReady := by
      intro indexScope indexId base key actual baseNode keyNode layout comparison first second indexed _keyFound form _sourceType _path
      rcases sourceForms indexId actual (by simpa only [sourceEq] using indexed.metadata.found) with
        ⟨name, resolution, nodeForm⟩ | ⟨callee, arguments, instantiation, nodeForm⟩ <;> simp [nodeForm] at form
    methodReady := by
      intro callFuel callScope callId code compiler _path
      rcases sourceForms callId compiler.node (by simpa only [sourceEq] using compiler.metadata.found) with
        ⟨name, resolution, nodeForm⟩ | ⟨callee, arguments, instantiation, nodeForm⟩
      all_goals
        rcases compiler.operator.form with ⟨op, operand, form, _arguments⟩ | ⟨op, left, right, form, _arguments⟩ <;>
          simp [nodeForm] at form }
  exact ⟨result, rfl⟩

include diagnostic receiver wellFormed sourceForms supported metadata rows covered resolved in
/-- The original scoped grammar and actual method compiler provide every child. -/
theorem of_actual_with_evidence
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {stages : Staging.Recursive.Registry}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax principal.sourceBody.source
      (fun id => GeneralSyntax principal.sourceBody.source id directSites)
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType) :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  apply CallableIndexedOwnedPreparedStagedMethodScopedCollectors.of_compiler principal packet ready member wellFormed diagnostic
    (CallableIndexedOwnedPreparedStagedMethodScopedCollectors.operands_of_diagnostic principal diagnostic receiver)
    (CallableIndexedOwnedPreparedStagedMethodScopedCollectors.unary_of_diagnostic principal diagnostic receiver) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations tree found typed accepted _nativeType _native
  exact of_child_with_evidence principal packet diagnostic receiver wellFormed sourceForms supported metadata rows covered resolved selected fields
    declarations tree found typed accepted

end Resolved

section Generic
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceForms : DirectSource principal.sourceBody.source)
  {directSites : DeclarationInstantiation → Prop}
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (catalog : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)

local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

private def resolved_generic :
    CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
      compiled.sourceProgram principal.named.specialized principal.dictionary := by
  have empty := CallableIndexedOwnedPreparedStagedMethodCallerEvidence.assumptions_empty_generic principal catalog
  have dictionary := RecursiveMethodSelectionIdentity.dictionary_empty principal.selected empty
  have callerEmpty : principal.named.specialized.assumptions = [] := by
    rw [principal.cached.same]
    exact empty
  refine ⟨[], ?_, dictionary⟩
  rw [callerEmpty]
  rfl

include diagnostic receiver wellFormed sourceForms supported metadata rows covered catalog in
theorem of_child_generic
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields packet.sourceAt.context context)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    (declarations : CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context)
    (tree : GeneralSyntax principal.sourceBody.source id directSites)
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (typed : ExpressionHasType principal.sourceBody.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    Certificate headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  exact of_child_with_evidence principal packet diagnostic receiver wellFormed sourceForms supported metadata rows covered
    (resolved_generic principal catalog) selected fields declarations tree found typed accepted

include diagnostic receiver wellFormed sourceForms supported metadata rows covered catalog in
theorem of_actual_generic
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {stages : Staging.Recursive.Registry}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax principal.sourceBody.source
      (fun id => GeneralSyntax principal.sourceBody.source id directSites)
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType) :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  exact of_actual_with_evidence principal packet diagnostic receiver wellFormed sourceForms supported metadata rows covered
    (resolved_generic principal catalog) ready member syntaxTree

end Generic


section Legacy
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceForms : DirectSource principal.sourceBody.source)
  {directSites : DeclarationInstantiation → Prop}
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (catalog : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)

local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

include diagnostic receiver wellFormed sourceForms supported metadata rows covered catalog in
theorem of_child
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields packet.sourceAt.context context)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    (declarations : CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context)
    (tree : GeneralSyntax principal.sourceBody.source id directSites)
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (typed : ExpressionHasType principal.sourceBody.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    Certificate headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  exact of_child_generic principal packet diagnostic receiver wellFormed sourceForms supported metadata rows covered
    (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed catalog) selected fields
    declarations tree found typed accepted

include diagnostic receiver wellFormed sourceForms supported metadata rows covered catalog in
theorem of_actual
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {stages : Staging.Recursive.Registry}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax principal.sourceBody.source
      (fun id => GeneralSyntax principal.sourceBody.source id directSites)
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType) :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  exact of_actual_generic principal packet diagnostic receiver wellFormed sourceForms supported metadata rows covered
    (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed catalog) ready member syntaxTree

end Legacy

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodies
/-! Both method body forms retain their actual compiler packet and SourceAt.
The alternatives contain static receipts only. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedMethodPrincipal (Principal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}

inductive Packet (principal : Principal compiled method) where
  | terminal : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal → Packet principal
  | scoped : CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.Packet principal → Packet principal

def Packet.sourceAt {principal : Principal compiled method} (packet : Packet principal) :
    CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary :=
  match packet with
  | .terminal packet => packet.sourceAt
  | .scoped packet => packet.sourceAt

def Support (principal : Principal compiled method) (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep) : Prop :=
  match packet with
  | .terminal packet => CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Support
      principal packet headers stages semanticFaults
  | .scoped packet => CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.Support
      principal packet headers stages semanticFaults

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedBounds
/-! The actual installed method and marked parameter entry supply admission,
physical cache slots and the frame used by the existing scoped flow engine.
Every reached expression is discharged by the strict mixed root family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport (Packet Support parameterScope nativePrefix)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedMethodInvocationBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (support : Support principal packet headers stages semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {registry : SourceCoreRawMetadata.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure principal.sourceFunction child)
  {administrative : Core.Context} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : CallablePreparedMethodRuntimeMeaning.Installed principal.cached.compilation
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := principal.sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments packet.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "bodyBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)

include wellFormed beforeTyped argumentsTyped in
private theorem heap_at_parameters {environment : Dynamic.Environment} {after : Dynamic.Heap}
    (allocation : Dynamic.BindersAllocate [] before principal.sourceFunction.parameters arguments environment after) :
    Dynamic.HeapWellTyped packet.sourceAt.context after := by
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq packet.sourceAt.extended
  have rawArguments : Dynamic.ValuesHaveTypes principal.sourceBody.context before arguments
      (principal.sourceBody.source.inputs.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes, principal.source_frame.context] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping
    (principal.source_frame.context ▸ beforeTyped) rawArguments (principal.source_frame.parameters ▸ allocation)
  obtain ⟨_, typed⟩ := CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.source_typing principal packet.sourceAt wellFormed
  have runtime := typed.sourceRuntimeValid
  have fields := RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended
  exact allocated.transportClosed fields.signatures runtime.closed (fields.targetClosed runtime.closed)
    runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)

include packet in
private theorem prefix_agrees
    {localScope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {map : LocationMap} {typing : StoreTyping} {environment : Dynamic.Environment}
    {administrative : Core.Context} {location : Location}
    (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 localScope canonical)
    (reference : canonical[localScope.length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      map typing (SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative)
      localScope environment canonical compiled.indexed.layouts.definitions) :
    NativeExpressionContextSupport.Agrees (nativePrefix principal).length (nativePrefix principal)
      (SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative) := by
  have typed := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext localScope ++
        SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative)[index]? = some value.type := by
    rw [← typed]
    simp [found]
  intro index smaller
  cases index with
  | zero => simp [nativePrefix, packet.sourceAt.parameterType]
  | succ slot =>
    have bound : slot < compiled.indexed.base.globals.length + 1 := by
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil] at smaller
      omega
    by_cases globalSlot : slot < compiled.indexed.base.globals.length
    · let signature := compiled.indexed.base.globals[slot]
      have selected : compiled.indexed.base.globals[slot]? = some signature :=
        List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
      have atType := tag (slots slot signature selected)
      have outside : ¬ localScope.length + 1 + slot < localScope.length := by omega
      have offset : localScope.length + 1 + slot - localScope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        globalSlot, selected, signature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = compiled.indexed.base.globals.length := by omega
      have atType := tag reference
      have outside : ¬ localScope.length + 1 + compiled.indexed.base.globals.length < localScope.length := by omega
      have offset : localScope.length + 1 + compiled.indexed.base.globals.length - localScope.length =
          compiled.indexed.base.globals.length + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        last, Value.type] using atType

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled registry
    (fun reason token => faults (.semantic reason) token))

include support wellFormed selected keyPhysical beforeTyped argumentsTyped stable semantic faithful observations assignmentInterpretation in
/-- Actual parameter allocation supplies the entire Source body entry. -/
theorem source_continuation
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    SourceContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata _owned history _emitted entry _added _length _spine reached _related physical slots
  intro size finalContext bodyOutcome outcome after trace matched within
  have prefixAgreement := prefix_agrees principal packet slots entry.reference entry.environments
  have environments := RecursiveNamedLambdaFormationHeads.environments_prefix entry.environments (nativePrefix principal) prefixAgreement
  have agrees : EnvironmentsAgree entry.embedding
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) entry.actualBody :=
    RecursiveNamedLambdaFormationHeads.agrees_prefix entry.lookups
    ((parameterScope principal).length + (nativePrefix principal).length)
  have retainedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 (parameterScope principal)
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) := by
    intro slot signature found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [List.getElem?_take, if_pos]
    · exact slots slot signature found
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  have reference : (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length))[
      (parameterScope principal).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [List.getElem?_take, if_pos]
    · exact entry.reference
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨parameterScope principal, entry.mapping, entry.world, entry.heap, entry.store,
        entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)⟩ :=
    ⟨⟨reached, retainedSlots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet wellFormed beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨staticFinal, facts, bodyTyped, _completes⟩ :=
    CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.statements principal packet wellFormed
  rw [← sourceEq] at bodyTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source packet.sourceAt.context
      principal.cached.compilation.statements := ⟨_, _, _, bodyTyped⟩
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true
      principal.cached.compilation.statements := sourceEq ▸ packet.shape
  obtain ⟨expressionSyntax, collected⟩ := support.tree child selected
  obtain ⟨assignmentAuthority⟩ := support.assignmentAuthority
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready
      (values := .initial compiled.compatible.checked) functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
      principal.sourceBody.source (fun site root => principal.cached.diagnostics.placeReason principal.named.signature.key site root none)
      (fun site root raw => principal.cached.diagnostics.placeReason principal.named.signature.key site root (some raw)) registry
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
  rw [← sourceEq] at assignmentDiagnostics
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history
  obtain ⟨flowValue, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_at (compiled := compiled)
      bodyBridge (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1)
      functions faithful observations extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model 1)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner (headers := headers) model 1 stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages child
            (Point scope id lowered) faults size := children size smaller root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      unique collected.tree (collected.sites registry) semantic assignmentDiagnostics rfl shape originalTyping packet.sourceAt.projection
      (Nat.le_of_lt within) environments entry.heaps entry.locals agrees entry.actualTyped reference entry.read entry.unmapped
      initial conditioned admitted trace
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    unique bodyTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function packet.sourceAt.projection represented controlClosed
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated
      principal.cached.compilation.own.fellThroughReason principal.cached.compilation.own.table.escapedReason entry.embedding
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, bodyStore, finalMap, finalWorld, ?_, representedBody, heaps,
    maps, worlds, frame, metadata, returned.base.val, related⟩
  simpa only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody

include support wellFormed selected keyPhysical beforeTyped argumentsTyped stable semantic functionTypes faithful observations assignmentInterpretation in
/-- Native completion is inverted through the same real flow and footer. -/
theorem native_continuation
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    NativeContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata prefixSize bodyStore _owned history _prefixWithin value finalStore _restored
    entry _added _length _spine reached _related physical slots within
  have prefixAgreement := prefix_agrees principal packet slots entry.reference entry.environments
  have environments := RecursiveNamedLambdaFormationHeads.environments_prefix entry.environments (nativePrefix principal) prefixAgreement
  have agrees : EnvironmentsAgree entry.embedding
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) entry.actualBody :=
    RecursiveNamedLambdaFormationHeads.agrees_prefix entry.lookups
    ((parameterScope principal).length + (nativePrefix principal).length)
  have retainedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 (parameterScope principal)
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) := by
    intro slot signature found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [List.getElem?_take, if_pos]
    · exact slots slot signature found
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  have reference : (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length))[
      (parameterScope principal).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [List.getElem?_take, if_pos]
    · exact entry.reference
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨parameterScope principal, entry.mapping, entry.world, entry.heap, entry.store,
        entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)⟩ :=
    ⟨⟨reached, retainedSlots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet wellFormed beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨staticFinal, facts, bodyTyped, _completes⟩ :=
    CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.statements principal packet wellFormed
  rw [← sourceEq] at bodyTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source packet.sourceAt.context
      principal.cached.compilation.statements := ⟨_, _, _, bodyTyped⟩
  have graph : OccurrenceGraphWellFormed child.source :=
    sourceEq ▸ (CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.runtime principal packet wellFormed).graph
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true
      principal.cached.compilation.statements := sourceEq ▸ packet.shape
  obtain ⟨expressionSyntax, collected⟩ := support.tree child selected
  obtain ⟨assignmentAuthority⟩ := support.assignmentAuthority
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready
      (values := .initial compiled.compatible.checked) functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
      principal.sourceBody.source (fun site root => principal.cached.diagnostics.placeReason principal.named.signature.key site root none)
      (fun site root raw => principal.cached.diagnostics.placeReason principal.named.signature.key site root (some raw)) registry
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
  rw [← sourceEq] at assignmentDiagnostics
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history
  have bodyTrace := entry.completed
  simp only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace (Nat.le_of_lt within)
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativeFlow.reflects_at (compiled := compiled)
      bodyBridge (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1)
      functions functionTypes faithful observations extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model 1)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner (headers := headers) model 1 stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages child
            (Point scope id lowered) faults size := children size smaller root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      graph collected.tree (collected.sites registry) semantic assignmentDiagnostics rfl shape originalTyping packet.sourceAt.projection
      (Nat.le_of_lt strict) environments entry.heaps entry.locals agrees entry.actualTyped reference entry.read entry.unmapped
      initial conditioned admitted flowTrace
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    graph.nodeOccurrencesUnique bodyTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function packet.sourceAt.projection represented controlClosed
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound
      principal.cached.compilation.own.fellThroughReason principal.cached.compilation.own.table.escapedReason entry.embedding
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  exact ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld, trace,
    represented.body_result, representedBody, heaps, maps, worlds, frame, metadata, returned.base.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyBounds
/-! Static method packet dispatch preserves the same genuine parameter entry
and current physical authority in either body form. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedStagedMethodBodies (Packet Support)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds
open CallableIndexedOwnedPreparedStagedMethodInvocationBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (support : Support principal packet headers stages semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {registry : SourceCoreRawMetadata.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure principal.sourceFunction child)
  {administrative : Core.Context} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : CallablePreparedMethodRuntimeMeaning.Installed principal.cached.compilation
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := principal.sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments packet.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled registry
    (fun reason token => faults (.semantic reason) token))

include support wellFormed selected keyPhysical beforeTyped argumentsTyped stable semantic faithful observations assignmentInterpretation in
theorem source_continuation
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    SourceContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  cases packet with
  | terminal packet =>
    exact CallableIndexedOwnedPreparedStagedMethodTerminalBounds.source_continuation
      principal packet support wellFormed functions selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable budget
      (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
        children size smaller
          (CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt.ofMethod root) owner physical)
  | «scoped» packet =>
    exact CallableIndexedOwnedPreparedStagedMethodScopedBounds.source_continuation (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      principal packet support wellFormed functions faithful observations selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable extension budget children

include support wellFormed selected keyPhysical beforeTyped argumentsTyped stable semantic functionTypes faithful observations assignmentInterpretation in
theorem native_continuation
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    NativeContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  cases packet with
  | terminal packet =>
    exact CallableIndexedOwnedPreparedStagedMethodTerminalBounds.native_continuation
      principal packet support wellFormed functions selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable budget
      (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
        children size smaller
          (CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt.ofMethod root) owner physical)
  | «scoped» packet =>
    exact CallableIndexedOwnedPreparedStagedMethodScopedBounds.native_continuation (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      principal packet support wellFormed functions functionTypes faithful observations selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable extension budget children

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedRoots
/-! Actual read and Boolean occurrences in selected implementation methods are
issued at each reached lexical context. The static support remains indexed by
general mixed roots, while the initial concrete profile excludes calls from its
original node forms rather than from an execution observation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

/-- A factual property of the full original node table, including unused nodes. -/
def LeafSource (source : TypedSource) : Prop :=
  ∀ id node, source.lookupExpression? id = some node →
    (∃ name binder, node.form = .reference name (.local binder)) ∨
    (∃ name value, node.form = .reference name (.builtinBoolean value))

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (leaves : LeafSource principal.sourceBody.source)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source (fun _ => False))

private theorem policy_receipt {scope : SourceCoreLocalCell.Scope} {fuel : Nat}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    ∃ predecessor, Nonempty (CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      principal.named principal.cached.diagnostics principal.cached.code principal.cached.compilation
      predecessor principal.sourceBody.source scope id
      (principal.cached.diagnostics.reasonAt principal.named.signature.key) lowered) := by
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext principal.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    principal.cached.compilation.parents principal.cached.compilation.own.assignments principal.cached.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
    compiled.indexed.base.callableContext none none fuel principal.sourceBody.source scope id
    (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered at accepted
  cases fuel with
  | zero => rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted; cases accepted
  | succ predecessor =>
    exact ⟨predecessor, CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
      principal.cached.compilation principal.record accepted⟩

include diagnostic receiver wellFormed leaves metadata in
/-- The actual compiler action and selected scope supply a mixed root with all
readiness obligations derived from original Source forms and full context fields. -/
theorem of_child
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields packet.sourceAt.context context)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    (declarations : CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context)
    (tree : GeneralSyntax principal.sourceBody.source id (fun _ => False))
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (typed : ExpressionHasType principal.sourceBody.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    Certificate headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨predecessor, ⟨root⟩⟩ := policy_receipt principal accepted
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables (fun _ impossible => False.elim impossible)
    metadata scope (principal.cached.diagnostics.reasonAt principal.named.signature.key)
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    packet.sourceAt.unique declarations profile (fun id node tree found => metadata.coercions id tree node found) tree found typed root.selected.accepted
  let result : RootAt compiled headers stages context child scope id lowered
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := RootAt.ofRoot {
    compilerFuel := predecessor + 1
    accepted := by simpa only [sourceEq] using root.selected.accepted
    certificate := by simpa only [sourceEq] using certificate
    node := node
    found := by simpa only [sourceEq] using found
    rawResult := rfl
    typed := by simpa only [sourceEq] using typed
    sameLedger := fields.solvedRequirements.trans packet.sourceAt.valid.ledger
    runtimeLedger := fields.runtimeRequirementLedger packet.sourceAt.valid.runtime
    unique := sourceEq ▸ packet.sourceAt.unique
    wellFormed := wellFormed
    runtime := by simpa only [sourceEq] using (runtime principal packet wellFormed).transport fields
    covers := by rw [stages.evidence selected]; exact fields.covers packet.sourceAt.valid.covers
    actualFunctionType := by rw [root.callables]; rfl
    uninitialized := by
      intro current id code read _reached location
      exact CallableIndexedOwnedPreparedStagedMethodTerminalSupport.uninitialized principal diagnostic receiver
        packet.sourceAt.unique (by simpa only [sourceEq] using read) location
    callsReady := by
      intro callFuel callScope callId callee ids callMetadata code compiler _path
      rcases leaves callId compiler.original (by simpa only [sourceEq] using compiler.found) with
        ⟨name, binder, form⟩ | ⟨name, value, form⟩ <;>
        have impossible := compiler.originalForm <;> simp [form] at impossible
    directReady := by
      intro callFuel callScope callId callee ids instantiation code compiler _path
      rcases leaves callId compiler.node (by simpa only [sourceEq] using compiler.metadata.found) with
        ⟨name, binder, form⟩ | ⟨name, value, form⟩ <;>
        have impossible := compiler.form <;> simp [form] at impossible
    indexReady := by
      intro indexScope indexId base key actual baseNode keyNode layout comparison first second indexed _keyFound form _sourceType _path
      rcases leaves indexId actual (by simpa only [sourceEq] using indexed.metadata.found) with
        ⟨name, binder, readForm⟩ | ⟨name, value, readForm⟩ <;> simp [readForm] at form
    methodReady := by
      intro callFuel callScope callId code compiler _path
      rcases leaves callId compiler.node (by simpa only [sourceEq] using compiler.metadata.found) with
        ⟨name, binder, readForm⟩ | ⟨name, value, readForm⟩
      all_goals
        rcases compiler.operator.form with ⟨op, operand, form, _arguments⟩ | ⟨op, left, right, form, _arguments⟩ <;>
          simp [readForm] at form }
  exact ⟨result, rfl⟩

include diagnostic receiver wellFormed leaves metadata in
/-- The original scoped grammar and actual method compiler provide every child. -/
theorem of_actual
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax principal.sourceBody.source
      (fun id => GeneralSyntax principal.sourceBody.source id (fun _ => False))
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType) :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  apply CallableIndexedOwnedPreparedStagedMethodScopedCollectors.of_compiler principal packet ready member wellFormed diagnostic
    (CallableIndexedOwnedPreparedStagedMethodScopedCollectors.operands_of_diagnostic principal diagnostic receiver)
    (CallableIndexedOwnedPreparedStagedMethodScopedCollectors.unary_of_diagnostic principal diagnostic receiver) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations tree found typed accepted _nativeType _native
  exact of_child principal packet diagnostic receiver wellFormed leaves metadata selected fields
    declarations tree found typed accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedRoots
end
