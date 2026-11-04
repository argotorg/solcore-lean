import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DiscardSequences
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionMethods
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodPrincipal
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalDirectCalls

/-!
# Staged bounds: coercions

Coercion authority, chains and issuance, closed coercion selection, the transport of coerced and evidence body views, and bounds of coerced expressions.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionAuthority
/-! A coercion port retains the actual ordered compiler step and selected Source
method. Parameter entry and method execution use the shared physical family. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionAuthority
open Core Frontend SourceInference

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available
    scope node policy input coercion output call)

structure Port (context : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    (stages : Staging.Recursive.Registry) where
  principal : CallableIndexedOwnedMethodPrincipal.Principal compiled step.method
  signature : principal.named.signature = call.signature
  slot : principal.cached.index = step.globalIndex
  parameters : principal.named.inputs.map (fun binding => binding.1.scheme.body) = [coercion.source]
  result : principal.sourceBody.resultType = coercion.target
  selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
    context callerEvidence "Coerce" "coerce" coercion.requirements principal.sourceBody principal.dictionary
  agrees : ∀ sourceBody dictionary,
    Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
      context callerEvidence "Coerce" "coerce" coercion.requirements sourceBody dictionary →
      sourceBody = principal.sourceBody ∧ dictionary = principal.dictionary
  child : Staging.Recursive.Scope
  staged : stages.Closure principal.sourceFunction child
  diagnostics : ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
    compiled.indexed.base.diagnostics = some diagnostics ∧
    principal.cached.diagnostics = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}
  resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
    compiled.sourceProgram principal.named.specialized principal.dictionary
  sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
    (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionAuthority
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChain
/-! An ordered conversion certificate retains each actual compiler step and
its independent Source method selection, together with raw endpoint typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChain
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedCoercionAuthority (Port)

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  (project : SourceCoreEvidence.Projector) (compilation : SourceCoreFunctions.Context)
  (caller : SourceSpecialization.SpecializedFunction)
  (available : SourceTypedRuntime.RuntimeEvidenceEnvironment)
  (scope : SourceCoreBasic.Scope) (node : ExpressionNode)
  (policy : SourceCoreFunctions.CallablePolicy)
  (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
  (stages : Staging.Recursive.Registry)

inductive Chain : TypeSystem.Ty → TypeSystem.Ty → SourceCoreBasic.LoweredExpr →
    List SourceInference.CoercionStep → SourceCoreBasic.LoweredExpr → List CallableCoercionSpine.Call → Type where
  | nil {source input} : Chain source source input [] input []
  | cons {coercion target input middle output rest call calls}
      (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available
        scope node policy input coercion middle call)
      (port : Port step context invocation.evidence stages)
      (valid : CoercionStepValid context coercion)
      (tail : Chain coercion.target target middle rest output calls) :
      Chain coercion.source target input (coercion :: rest) output (call :: calls)

variable {compiled project compilation caller available scope node policy context invocation stages}
  {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
  {steps : List SourceInference.CoercionStep} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller available scope node policy context invocation stages
    source target input steps output calls)

include chain

theorem Chain.spine : CallableCoercionSpine.Spine compiled.sourceProgram project compilation caller available
    scope node policy input steps output calls := by
  induction chain with
  | nil => exact .nil
  | cons step _ _ _ ih => exact .cons step ih

theorem Chain.valid : CoercionPathValid context source target steps := by
  induction chain with
  | nil => exact .nil _
  | cons _ _ valid _ ih => exact .cons valid ih

theorem Chain.final_type (ξ : Renaming) :
    CallableCoercionSpine.finalType input.type (calls.map (CallableCoercionSpine.Call.rename ξ)) = output.type := by
  induction chain with
  | nil => rfl
  | cons step _ _ _ ih =>
      simpa only [List.map_cons, CallableCoercionSpine.finalType, CallableCoercionSpine.Call.rename,
        step.emitted] using ih

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChain
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEvidenceBodyViewTransport
/-! Evidence-bearing direct actions cross the same unchanged body occurrences.
The actual callee check and ordered child actions agree before the retained
compiler hook is compared; dictionaries are never replaced or assumed equal. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEvidenceBodyViewTransport
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open CallableIndexedOwnedPreparedStagedOrdinaryEvidencePolicy

private theorem mapM_eq_of_members {α β ε : Type} {items : List α}
    {left right : α → Except ε β} (same : ∀ item, item ∈ items → left item = right item) :
    items.mapM left = items.mapM right := by
  revert same
  induction items with
  | nil => intro _same; rfl
  | cons item rest ih =>
      intro same
      simp only [List.mapM_cons]
      rw [same item (by simp), ih (fun next member => same next (by simp [member]))]

/-- Full evidence authentication is identical at a direct node whose actual
callee and ordered child actions are unchanged. Error branches are retained. -/
theorem direct_evidence_eq
    (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (compilation : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    {source view : TypedSource} (scope : SourceCoreLocalCell.Scope)
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (viewFound : view.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (calleeLookup : source.lookupExpression? callee = view.lookupExpression? callee)
    (children : ∀ argument, argument ∈ ids →
      child budget source scope argument reasonAt = child budget view scope argument reasonAt) :
    SourceCoreEvidence.lowerWithProjector program projector caller compilation child budget source scope id reasonAt callables =
      SourceCoreEvidence.lowerWithProjector program projector caller compilation child budget view scope id reasonAt callables := by
  have validatorSame : SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation =
      SourceCompilationPlan.validateDirectDeclarationCallee view id callee instantiation := by
    simp only [SourceCompilationPlan.validateDirectDeclarationCallee, calleeLookup]
  have argumentsSame := mapM_eq_of_members children
  simp only [SourceCoreEvidence.lowerWithProjector, found, viewFound, form,
    bind, Except.bind, pure, Except.pure, validatorSame, argumentsSame]

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
  have sourceMetadata := CallableIndexedOwnedPreparedStagedOrdinaryEvidencePolicy.MetadataFor.on metadata
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
      apply direct_evidence_eq _ _ _ _ _ _ _ _ _ found viewFound form
      · exact expression_lookup edited avoids (.expression reached found (by simp [form, ExpressionForm.references]))
      · intro argument member
        have same := children argument (by simp [RuntimeChild, form, member])
        simpa only [child, Nat.min_eq_right (Nat.le_succ fuel)] using same
    · have ordinary : tree.NonDirect := by
        intro actual selected callee ids instantiation form
        have same := Option.some.inj (selected.symm.trans found)
        subst actual
        exact direct ⟨callee, ids, instantiation, form⟩
      have viewedOrdinary : viewTree.NonDirect := by
        intro actual selected callee ids instantiation form
        exact ordinary actual (lookup.trans selected) callee ids instantiation form
      rw [recipe.lowerSpecial]
      exact (special_none_on compilation rootFuel sourceMetadata reached tree ordinary _ _ scope reasonAt).trans
        (special_none_on compilation rootFuel viewMetadata (reached.metadata edited.metadata) viewTree viewedOrdinary _ _ scope reasonAt).symm
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEvidenceBodyViewTransport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedBodyViewTransport
/-! A direct evidence action may retain its original result coercions. The
unchanged body view and ordered no-coercion child actions authenticate the same
complete hook before ordinary compiler acceptance is reconstructed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedBodyViewTransport
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (contextual_same SupportedForm)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child)

section Recipe
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named} {source : TypedSource}

theorem direct_hook
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode}
    (noInitializer : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) =
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) := by
  have same := contextual_same (prepared := prepared) (named := named) found (form ▸ SupportedForm.direct callee ids instantiation)
    (by intro name binder impossible; rw [form] at impossible; cases impossible)
  rw [recipe.lowerSpecial]
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [same, bind, Except.bind, found, pure, Except.pure,
    noInitializer, Option.filter_none]
  cases actual : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
  | error error => rfl
  | ok output => cases output <;> simp [form]

theorem accepted_direct_action
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

    (noInitializer : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      (context prepared named) source scope id reasonAt = .ok lowered) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) (Child policy body fuel (context prepared named))
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none ∨
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) (Child policy body fuel (context prepared named))
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok (some lowered) := by
  have owner : id.occurrence.owner = source.owner := by
    apply Classical.byContradiction
    intro mismatch
    simp [SourceCoreFunctions.lowerExpressionWithPolicy, mismatch, bind, Except.bind] at accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
  have hook := direct_hook recipe noInitializer found form
    (Child policy body fuel (context prepared named)) (fuel + 1) scope reasonAt
  cases selectedHook : policy.lowerSpecial? with
  | none =>
    simp only [selectedHook] at hook
    exact .inl hook.symm
  | some lower =>
    simp only [selectedHook] at hook accepted
    rw [hook] at accepted
    cases action : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized (context prepared named) (Child policy body fuel (context prepared named))
        (fuel + 1) source scope id reasonAt
        (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
    | error error => rw [action] at accepted; cases accepted
    | ok output =>
      cases output with
      | none => exact .inl rfl
      | some actual =>
        rw [action] at accepted
        cases Except.ok.inj accepted
        exact .inr rfl


theorem accepted_of_action
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (noInitializer : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (owner : id.occurrence.owner = source.owner)
    (action : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) (Child policy body fuel (context prepared named))
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok (some lowered)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      (context prepared named) source scope id reasonAt = .ok lowered := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure]
  have hook := (direct_hook recipe noInitializer found form
    (Child policy body fuel (context prepared named)) (fuel + 1) scope reasonAt).trans action
  cases selectedHook : policy.lowerSpecial? with
  | none => simp only [selectedHook] at hook; cases hook
  | some lower =>
    simp only [selectedHook] at hook ⊢
    rw [hook]

end Recipe

/-- Nonempty original requirements select the actual evidence hook. Its child
compiler equality comes from the existing reached-body transport. -/
theorem accepted_original
    {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function parameterScope administrative)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
    (metadata : MetadataFor compiled.indexed named function.source (fun _ => False))
    {scope : SourceCoreLocalCell.Scope} {fuel : Nat} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (noInitializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none)
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (requirements : node.requirements ≠ [])
    (children : ∀ argument ∈ ids, GeneralSyntax function.source argument (fun _ => False))
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody (fuel + 1)
      code.compilation code.view scope id code.reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody (fuel + 1)
      code.compilation function.source scope id code.reasonAt = .ok lowered := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation] at accepted ⊢
  let edited := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids bodyView
  have lookup := expression_lookup edited avoids reached
  have viewFound := lookup.symm.trans found
  have action : SourceCoreEvidence.lowerWithProjector compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized (context compiled.indexed named)
      (Child code.policy code.lowerBody fuel (context compiled.indexed named))
      (fuel + 1) code.view scope id code.reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []) = .ok (some lowered) := by
    rcases accepted_direct_action recipe noInitializer viewFound form accepted with bypass | actual
    · exact False.elim (requirements (CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct viewFound form bypass).1)
    · exact actual
  have sameAction := CallableIndexedOwnedPreparedStagedEvidenceBodyViewTransport.direct_evidence_eq
    compiled.indexed.base.sourceProgram
    ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
    named.specialized (context compiled.indexed named)
    (Child code.policy code.lowerBody fuel (context compiled.indexed named))
    (fuel + 1) scope code.reasonAt
    (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []) found viewFound form
    (expression_lookup edited avoids (.expression reached found (by simp [form, ExpressionForm.references])))
    (by
      intro argument member
      have same := CallableIndexedOwnedPreparedStagedEvidenceBodyViewTransport.compiler_eq_on
        recipe edited avoids metadata callables code.lowerBody scope code.reasonAt fuel
        (children argument member) (.expression reached found (by simp [form, ExpressionForm.references, member]))
      simpa only [Child, Nat.min_eq_right (Nat.le_succ fuel)] using same)
  have owner : id.occurrence.owner = code.view.owner := by
    apply Classical.byContradiction
    intro mismatch
    simp [SourceCoreFunctions.lowerExpressionWithPolicy, mismatch, bind, Except.bind] at accepted
  exact accepted_of_action recipe noInitializer found form
    (owner.trans edited.metadata.owner.symm) (sameAction.trans action)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedBodyViewTransport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionIssuance
/-! The original coercion selector and final preparation supply the complete
method port. Only syntactic source shape and formation are static inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionIssuance
open Core Frontend SourceInference
open CallablePreparedMethodSelection
open CallableIndexedOwnedPreparedStagedCoercionAuthority
open CallableNamedMetadata (environment)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available
    scope node policy input coercion output call)

structure Support (selected : CallableCoercionSourceSelection.Certificate
    compiled.sourceProgram caller node available coercion step.method) : Prop where
  formed : CallableCoercionMethodInstantiation.Formation selected.selected.implementation selected.selected.declaration
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) step.method.specialized.parameterSubstitution
  covered : CallableCoercionEvidenceOrigins.CallerCovered caller step.method
  unique : NodeOccurrencesUnique (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram step.method).source
  empty : step.method.specialized.assumptions = []
  parameters : step.method.specialized.function.typedBody.inputs.map (fun binder => binder.scheme.body) = [coercion.source]
  result : step.method.specialized.function.inferredBodyType = coercion.target

private theorem exact_member {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected <;> try contradiction
  rename_i actual found
  cases selected
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [found]
    simp
  exact (List.mem_filter.mp member).1

private theorem exact_key {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected <;> try contradiction
  rename_i actual found
  cases selected
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [found]
    simp
  exact of_decide_eq_true (List.mem_filter.mp member).2

private theorem cached_key {method : ExecutableImplMethods.CheckedMethod}
    (cached : Cached compiled method.specialized) : cached.named.signature.key = method.specialized.key := by
  have record := CallableIndexedActualNamedSourceReceipts.cached_record compiled cached.selected cached.compilation.hook
  exact (exact_key record).symm.trans (congrArg (fun row : SourceSpecialization.SpecializedFunction => row.key) cached.same)

private theorem descriptor {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method) :
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named principal.named.signature.key)) := by
  obtain ⟨origin, selected, _, _⟩ := principal.hook_history
  cases made : SourceCoreCallableContracts.descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named principal.named.signature.key) with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at made
    split at made
    · next absent => rw [selected] at absent; cases absent
    · cases made
  | ok descriptor => exact ⟨descriptor⟩

include step in
theorem of_actual
    (selected : CallableCoercionSourceSelection.Certificate compiled.sourceProgram caller node available coercion step.method)
    (support : Support step selected)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Port (compiled := compiled) step context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  have same := CallableCoercionPreparation.step_specialized prepared callerMember nodeMember site resolved step
  have target := step.selected
  rw [same, samePlan] at target
  obtain ⟨initial⟩ := cached_row compiled (exact_member target)
  obtain ⟨diagnostics, code, diagnosticPresent, codeFound, codeAccepted⟩ := NamedCalls.compiled_at compiled.indexed initial.selected
  obtain ⟨generation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed codeAccepted
  let cached : Cached compiled step.method.specialized :=
    ⟨initial.index, initial.named, _, code, initial.selected, initial.same, codeFound, generation⟩
  have chosen := selected.selects checked support.formed support.range signatures ledger assumptions resolved support.covered step.materialized
  have chosen : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      "Coerce" "coerce" coercion.requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram step.method)
      (environment step.dictionary) := by simpa only [dictionary, CoercionStep.requirements] using chosen
  let principal := CallableIndexedOwnedMethodPrincipal.of_selected cached chosen
  have key : cached.named.signature.key = step.key :=
    (cached_key cached).trans (CallableCoercionPreparation.exact_call_key step.edge).symm
  have member : (cached.named.signature, cached.index) ∈ compilation.globals.zipIdx.filter
      (fun row => decide (row.1.key = step.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr ?_, ?_⟩
    · rw [globals]
      exact CallableIndexedPreparedInventories.cached_global_at compiled cached.selected
    · simp only [key, decide_true]
  rw [step.global] at member
  have aligned := Prod.mk.inj (List.mem_singleton.mp member)
  obtain ⟨descriptor⟩ := descriptor principal
  obtain ⟨sidecar, _, _, staged⟩ := RecursiveMethodPreparedStageScopes.selected_of_descriptor actualStages principal descriptor
  obtain ⟨retained⟩ := CallableCoercionBodyProvenance.of_accepted checked step.selectedMethod
  obtain ⟨sourceAt⟩ := CallablePreparedMethodRuntimeProfileFactory.source_at (values := .initial compiled.compatible.checked) cached rfl retained wellFormed
    chosen support.unique (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm
  have empty : principal.sourceBody.context.assumptions = [] := support.empty
  have emptyDictionary := RecursiveMethodSelectionIdentity.dictionary_empty chosen empty
  refine ⟨⟨principal, aligned.1, aligned.2, ?_, support.result, chosen, ?_, _, staged,
    ⟨diagnostics, diagnosticPresent, rfl⟩, ?_, sourceAt⟩⟩
  · change cached.named.inputs.map (fun binding => binding.1.scheme.body) = [coercion.source]
    have inputs := CallablePreparedMethodRuntimeProfileFactory.parameters cached
    have types := congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) inputs
    change step.method.specialized.function.typedBody.inputs.map (fun binder => binder.scheme.body) = _ at types
    simpa only [List.map_map, Function.comp_def] using types.symm.trans support.parameters
  · intro body dictionary selectedActual
    exact RecursiveMethodSelectionIdentity.same_empty catalog
      (fun _ _ first second => unique.contains_unique first second) chosen selectedActual empty
  · change CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
      cached.named.specialized (environment step.dictionary)
    rw [cached.same]
    exact ⟨[], by rw [support.empty]; rfl, emptyDictionary⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionIssuance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedCoercionSelection
/-! A finite catalog of closed coercion methods supplies selection support from
original method formation and actual final-plan source shape checks. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedCoercionSelection
open Core Frontend SourceInference
open CallableCoercionMethodInstantiation (Formation bodyInstance)

structure Catalog (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  parameters : ∀ implementation, implementation ∈ compiled.sourceProgram.signatures.implementations →
    ∀ method, method ∈ implementation.methods → implementation.parameters = []
  formed : ∀ implementation, implementation ∈ compiled.sourceProgram.signatures.implementations →
    ∀ method, method ∈ implementation.methods → Formation implementation method
  assumptions : ∀ implementation, implementation ∈ compiled.sourceProgram.signatures.implementations →
    ∀ method, method ∈ implementation.methods → ∀ trait, trait ∈ compiled.sourceProgram.signatures.traits →
      implementation.methodAssumptions trait method = []
  shapes : CallableCoercionSourceShapeTable.Ready compiled.sourceProgram compiled.indexed.base.plan.specializations

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available
    scope node policy input coercion output call)

include step in
theorem selection_support     (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (catalog : Catalog compiled)
    (selected : CallableCoercionSourceSelection.Certificate compiled.sourceProgram caller node available coercion step.method)
    (callerMember : caller ∈ compiled.indexed.base.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available) :
    CallableIndexedOwnedPreparedStagedCoercionIssuance.Support step selected := by
  let chosen := selected.selected
  have formed : Formation chosen.implementation chosen.declaration :=
    catalog.formed chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have domain := chosen.domain
  have parameters := catalog.parameters chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have substitution : step.method.specialized.parameterSubstitution = [] :=
    List.map_eq_nil_iff.mp (domain.trans parameters)
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
      step.method.specialized.parameterSubstitution := by
    intro parameter replacement member
    rw [substitution] at member
    cases member
  have assumptions : step.method.specialized.assumptions = [] := by
    have fields := CallableCoercionBodyProvenance.specialization_fields chosen.specialized
    rw [fields.2]
    change List.map _ (chosen.implementation.methodAssumptions chosen.trait chosen.declaration) = []
    rw [catalog.assumptions chosen.implementation chosen.implementationMember
      chosen.declaration chosen.methodMember chosen.trait chosen.traitMember]
    rfl
  have covered : CallableCoercionEvidenceOrigins.CallerCovered caller step.method := by
    obtain ⟨headers, resolved, assembled, goals⟩ := CallableCoercionEvidenceOrigins.materialized step.materialized
    have dictionary : step.dictionary = [] := List.map_eq_nil_iff.mp (goals.trans assumptions)
    have allEmpty := assembled.symm.trans dictionary
    have headersEmpty : headers = [] := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp allEmpty).1).1
    rw [headersEmpty] at resolved
    have goalsEmpty : step.method.traitPredicates = [] := by
      have lengths := resolved.length_eq
      simpa using lengths
    intro goal member
    rw [goalsEmpty] at member
    cases member
  obtain ⟨definition, _member, _id, instantiated⟩ := chosen.instantiates checked formed.parameters range
  obtain ⟨types, lexical, facts, typing⟩ := instantiated.certificate wellFormed
  have shape := catalog.shapes.shape callerMember nodeMember site resolved step.selectedMethod
  exact ⟨formed, range, covered, typing.graph_closed.wellFormed.nodeOccurrencesUnique,
    assumptions, shape.parameters, shape.result⟩

include step in
theorem of_actual
    (methods : Catalog compiled)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = CallableNamedMetadata.environment available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedCoercionAuthority.Port (compiled := compiled) step context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  obtain ⟨selected⟩ := CallableCoercionSourceSelection.of_accepted step.selectedMethod
  have support := selection_support step checked wellFormed methods selected (samePlan ▸ callerMember) nodeMember site resolved
  exact CallableIndexedOwnedPreparedStagedCoercionIssuance.of_actual step selected support checked wellFormed catalog
    prepared callerMember nodeMember site samePlan globals signatures ledger assumptions resolved unique dictionary actualStages

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedCoercionSelection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChainIssuance
/-! Original Source path typing and accepted compiler steps produce the ordered
method chain. Every method port is issued from the same final preparation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChainIssuance
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
  (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
    preparationFuel budget = .ok compilation.plan)
  (callerMember : caller ∈ compilation.plan.specializations)
  (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
  (samePlan : compilation.plan = compiled.indexed.base.plan)
  (globals : compilation.globals = compiled.indexed.base.globals)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  (signatures : context.signatures = compiled.sourceProgram.signatures)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
  (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available)
  (unique : RequirementIdsUnique context)
  (dictionary : invocation.evidence = CallableNamedMetadata.environment available)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

include methods checked wellFormed catalog prepared callerMember nodeMember samePlan globals
  signatures ledger assumptions resolved unique dictionary actualStages in
theorem of_spine {input output : SourceCoreBasic.LoweredExpr} {steps : List CoercionStep}
    {calls : List CallableCoercionSpine.Call}
    (spine : CallableCoercionSpine.Spine compiled.sourceProgram project compilation caller available
      scope node policy input steps output calls)
    {source target : TypeSystem.Ty} (valid : CoercionPathValid context source target steps)
    (sites : ∀ step ∈ steps, step ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node) :
    Nonempty (Chain compiled project compilation caller available scope node policy context invocation
      (RecursiveNamedPreparedStageScopes.registry actualStages) source target input steps output calls) := by
  induction spine generalizing source with
  | nil => cases valid; exact ⟨.nil⟩
  | @cons input step middle rest output call calls head tail ih =>
    cases valid with
    | cons valid remaining =>
      obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedClosedCoercionSelection.of_actual head methods checked
        wellFormed catalog prepared callerMember nodeMember (sites step (by simp)) samePlan globals
        signatures ledger assumptions resolved unique dictionary actualStages
      obtain ⟨chain⟩ := ih remaining (fun step member => sites step (List.mem_cons_of_mem _ member))
      exact ⟨.cons head port valid chain⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChainIssuance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionSourceArguments
/-! A reached coercion step retains its genuine selected body and dictionary.
The actual compiler requirement rows exclude competing requirement faults;
the selected method excludes primitive rules. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionSourceArguments
open Core Frontend SourceInference Staging.Recursive
open Solcore.SourceSemantics.Dynamic
open CallableIndexedOwnedPreparedStagedCoercionAuthority (Port)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : SourceInference.CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available
    scope node policy input coercion output call)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  (port : Port step context invocation.evidence stages)

private theorem roots_unique {nodes : List NodeId} {left right : List StatementId}
    (first : StatementRoots nodes left) (second : StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons first ih => cases second with | cons second => exact congrArg (List.cons _) (ih second)

/-- Every method body remains a strict child of the original conversion step. -/
theorem body {before after : Dynamic.Heap} {value : Dynamic.Value}
    {size : Nat} {outcome : Staging.Recursive.Outcome}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (trace : Size.CoercionStep (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before coercion value outcome after) :
    ∃ bodySize bodyEnvironment bound finalContext bodyOutcome child,
      stages.Closure port.principal.sourceFunction child ∧
      BindersAllocate [] before port.principal.sourceBody.source.inputs [value] bodyEnvironment bound ∧
      Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child port.sourceAt.context
        bodyEnvironment bound port.principal.cached.compilation.statements finalContext bodyOutcome after ∧
      BodyResult port.principal.sourceBody.resultType bodyOutcome outcome ∧ bodySize < size := by
  cases trace with
  | coercionPrimitive absent _ => exact False.elim (absent _ _ port.selected)
  | coercionPrimitiveInput absent _ _ => exact False.elim (absent _ _ port.selected)
  | coercionRequirement fault =>
      exact False.elim (CallableCoercionRequirementSafety.selected_safe ledger step.selectedMethod port.selected fault)
  | coercionMethod method rootsEq selected parameters allocate trace matched =>
      obtain ⟨rfl, rfl⟩ := port.agrees _ _ method
      have rootsSame := roots_unique rootsEq port.sourceAt.frame.roots
      cases rootsSame
      have typesSame := parameters.bodyTypes_eq.symm.trans port.sourceAt.extended.bodyTypes_eq
      cases typesSame
      have contextSame := parameters.functional port.sourceAt.extended
      cases contextSame
      exact ⟨_, _, _, _, _, _, selected, allocate, trace, matched, Size.child_lt_stepSize (by simp)⟩

/-- Actual parameter entry reconstructs the original independent conversion. -/
theorem applied {before bound after : Dynamic.Heap} {value : Dynamic.Value}
    {bodyEnvironment : Dynamic.Environment} {bodySize : Nat}
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {child : Staging.Recursive.Scope}
    (selected : stages.Closure port.principal.sourceFunction child)
    (allocate : BindersAllocate [] before port.principal.sourceBody.source.inputs [value] bodyEnvironment bound)
    (trace : Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child port.sourceAt.context
      bodyEnvironment bound port.principal.cached.compilation.statements finalContext bodyOutcome after)
    (matched : BodyResult port.principal.sourceBody.resultType bodyOutcome outcome) :
    ∃ size, Size.CoercionStep (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before coercion value outcome after :=
  ⟨_, .coercionMethod port.selected port.sourceAt.frame.roots selected port.sourceAt.extended allocate trace matched⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionSourceArguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionInvocationBounds
/-! Each actual conversion call uses the shared marked method entry engine.
The saved native closure is identified by the reached full physical cache;
independent Source selection supplies its body and complete dictionary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedStagedCoercionAuthority (Port)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {sourceCaller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : SourceInference.CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation sourceCaller available
    scope node policy input coercion output call)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  (port : Port step context invocation.evidence stages)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A strict Source body callback at an authentic reached argument state. -/
def SourceBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    CallableIndexedOwnedPreparedStagedMethodInvocationBounds.SourceContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

/-- The native counterpart uses the same independently typed argument heap. -/
def NativeBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    CallableIndexedOwnedPreparedStagedMethodInvocationBounds.NativeContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

theorem represented_arguments {mapping : LocationMap} {world : StoreTyping}
    {source : Dynamic.Value} {value : Value}
    (represented : ValueRep compiled.compatible.checked receiving functions mapping world
      coercion.source source value call.signature.parameterType) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs [source] [value] := by
  have row : DataExpressionSequence.Values model mapping world [coercion.source]
      [call.signature.parameterType] [source] [value] := .cons represented .nil
  apply CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles port.principal.named.inputs row
  · have lengths := congrArg List.length port.parameters
    simpa only [List.length_map, List.length_cons, List.length_nil] using lengths.symm
  · rw [port.parameters]
  · change call.signature.parameterType = _
    rw [← port.signature]
    exact port.sourceAt.parameterType

/-- Reached Source input typing is transported by the selected method's genuine
closed body certificate, keeping its complete dictionary and raw singleton row. -/
theorem source_arguments {source : TypedSource}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    {heap : Dynamic.Heap} {value : Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (valueTyped : Dynamic.ValueHasType context heap value coercion.source) :
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap ∧
      Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap [value] port.sourceAt.types := by
  obtain ⟨types, lexical, facts, certificate, _valid⟩ :=
    CallablePreparedMethodSelection.selected_typed port.selected wellFormed
  have signatures := certificate.signatures_eq.trans runtime.signatures.symm
  have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyValue := valueTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyArguments := Dynamic.ValuesHaveTypes.cons bodyValue Dynamic.ValuesHaveTypes.nil
  have row := port.sourceAt.extended.bodyTypes_eq
  rw [port.sourceAt.parameters, List.map_map] at row
  change port.principal.named.inputs.map (fun binding => binding.1.scheme.body) = port.sourceAt.types at row
  rw [port.parameters] at row
  exact ⟨port.principal.source_frame.context.symm ▸ bodyHeap,
    port.principal.source_frame.context.symm ▸ (row ▸ bodyArguments)⟩

private theorem capture_read {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {store : Store} {canonical : Environment}
    (capture : CallableIndexedOwnedMethodPhysicalCaptures.Capture port.principal.cached port.principal.dictionary
      functions mapping world heap store canonical)
    (authority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store) :
    store.read? (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index) = some (.inRight .unit
      (.closure port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        (port.principal.cached.compilation.output.rename capture.installed.embedding.lift) capture.installed.captured)) := by
  have cachedCode : compiled.indexed.secondPass.closures[port.principal.cached.index]? = some
      (.lambda port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        port.principal.cached.compilation.output) := by
    simpa only [port.principal.cached.compilation.emitted] using port.principal.cached.cached
  simpa only [capture.embedding_eq, capture.captured_eq] using (authority.cached cachedCode).2

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {ξ : Renaming}
  (pool : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (ownerFrame : owner.key.frameLocation = 0)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix scope canonical)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  {source : Dynamic.Value} {value : Value}
  (represented : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source source value call.signature.parameterType)
  (headerHeap : Dynamic.HeapWellTyped port.principal.sourceFunction.context before)
  (headerArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context before [source] port.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows pool)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include ownerFrame physical slots agrees heaps represented headerHeap headerArguments stable wellFormed in
theorem preserves (budget : Nat)
    (bodyMeaning : SourceBodies (headers := headers) (receiving := receiving) step port owner functions faults budget)
    (ledger : context.solvedRequirements = sourceCaller.function.solvedRequirements)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.CoercionStep (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before coercion source outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke actual compilation.internalReason (call.rename ξ) store (.inRight .word value) result finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld coercion.target call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨bodySize, bodyEnvironment, bound, finalContext, bodyOutcome, child, selected, allocated, bodyTrace, matched, strict⟩ :=
    CallableIndexedOwnedPreparedStagedCoercionSourceArguments.body step port ledger trace
  have parameters := represented_arguments step port functions represented
  obtain ⟨capture⟩ := CallableIndexedOwnedMethodPhysicalCaptures.of_selected
    port.principal.cached port.principal.dictionary functions owner pool ownerFrame
    physical heaps.runtime_hasTypes slots port.selected wellFormed
  have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
    rw [capture.canonical_eq]
    exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, resultRep, finalHeaps, maps, worlds, frame, metadata, finalState⟩ :=
    CallableIndexedOwnedPreparedStagedMethodInvocationBounds.preserves
      port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner pool
      (capture.frame_eq.trans ownerFrame.symm) heaps physical capturedSlots budget
      (bodyMeaning pool capture.installed parameters headerHeap headerArguments stable selected)
      allocated bodyTrace matched (Nat.lt_of_lt_of_le strict within)
  have reference := agrees (slots _ _ (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
  have read := capture_read step port functions capture physical
  refine ⟨result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, metadata, finalState⟩
  · apply CallableCoercionSpine.Invoke.applied (location := CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index)
      (body := port.principal.cached.compilation.output.rename capture.installed.embedding.lift)
      (captured := capture.installed.captured)
    · simpa only [CallableCoercionSpine.Call.rename, step.location, ← port.slot] using reference
    · exact read
    · simpa only [DataPatternValues.packValues] using evaluated
  · simpa only [port.result, port.signature] using resultRep

include ownerFrame physical slots agrees heaps represented headerHeap headerArguments stable wellFormed in
theorem reflects (budget : Nat)
    (bodyMeaning : NativeBodies (headers := headers) (receiving := receiving) step port owner functions faults budget)
    {result : Value} {finalStore : Store}
    (completed : CallableCoercionSpine.InvokeSized budget actual compilation.internalReason (call.rename ξ)
      store (.inRight .word value) result finalStore) :
    ∃ size outcome after finalMap finalWorld,
      Staging.Recursive.Size.CoercionStep (Program.ofChecked compiled.sourceProgram) stages size
        invocation context before coercion source outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld coercion.target call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have parameters := represented_arguments step port functions represented
  obtain ⟨capture⟩ := CallableIndexedOwnedMethodPhysicalCaptures.of_selected
    port.principal.cached port.principal.dictionary functions owner pool ownerFrame
    physical heaps.runtime_hasTypes slots port.selected wellFormed
  have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
    rw [capture.canonical_eq]
    exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
  have reference := agrees (slots _ _ (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
  have referenceAt : actual[(call.rename ξ).index]? = some
      (.cellRef (OptionalCell.cellType port.principal.named.signature.functionType)
        (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index)) := by
    simpa only [CallableCoercionSpine.Call.rename, step.location, ← port.slot] using reference
  have read := capture_read step port functions capture physical
  cases completed with
  | absent reference actualRead =>
      cases Option.some.inj (reference.symm.trans referenceAt)
      cases Option.some.inj (actualRead.symm.trans read)
  | applied reference actualRead evaluation smaller =>
      cases Option.some.inj (reference.symm.trans referenceAt)
      cases Option.some.inj (actualRead.symm.trans read)
      obtain ⟨bodySize, bodyEnvironment, bound, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld,
          allocated, bodyTrace, matched, resultRep, finalHeaps, maps, worlds, frame, metadata, finalState⟩ :=
        CallableIndexedOwnedPreparedStagedMethodInvocationBounds.reflects
          port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner pool
          (capture.frame_eq.trans ownerFrame.symm) heaps physical capturedSlots budget
          (bodyMeaning pool capture.installed parameters headerHeap headerArguments stable port.staged)
          (by simpa only [DataPatternValues.packValues] using evaluation) (Nat.le_of_lt smaller)
      obtain ⟨size, trace⟩ := CallableIndexedOwnedPreparedStagedCoercionSourceArguments.applied step port
        port.staged allocated bodyTrace matched
      exact ⟨size, outcome, after, finalMap, finalWorld, trace,
        by simpa only [port.result, port.signature] using resultRep,
        finalHeaps, maps, worlds, frame, metadata, finalState⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionPathBounds
/-! Ordered conversions preserve the exact reached pool, heap and physical
cache between calls. Each method continuation receives the original strict
budget; path recursion only composes already justified single steps. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionPathBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- Body continuations are supplied by the shared numerical induction. -/
def SourceBodies {source target input steps output calls}
    (chain : Chain compiled project compilation caller available scope node policy context invocation stages
      source target input steps output calls) (budget : Nat) : Prop :=
  match chain with
  | .nil => True
  | .cons step port _ tail =>
      CallableIndexedOwnedPreparedStagedCoercionInvocationBounds.SourceBodies (headers := headers) (receiving := receiving) step port owner functions faults budget ∧
        SourceBodies tail budget

def NativeBodies {source target input steps output calls}
    (chain : Chain compiled project compilation caller available scope node policy context invocation stages
      source target input steps output calls) (budget : Nat) : Prop :=
  match chain with
  | .nil => True
  | .cons step port _ tail =>
      CallableIndexedOwnedPreparedStagedCoercionInvocationBounds.NativeBodies (headers := headers) (receiving := receiving) step port owner functions faults budget ∧
        NativeBodies tail budget

variable {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
  {steps : List SourceInference.CoercionStep} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller available scope node policy context invocation stages
    source target input steps output calls)
  (ownerFrame : owner.key.frameLocation = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {ξ : Renaming}
  (pool : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix scope canonical)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  {sourceValue : Dynamic.Value} {nativeValue : Value}
  (represented : ValueRep compiled.compatible.checked receiving functions mapping world source sourceValue nativeValue input.type)
  (heapTyped : Dynamic.HeapWellTyped context before)
  (valueTyped : Dynamic.ValueHasType context before sourceValue source)
  (stable : StableRows pool)

include ownerFrame wellFormed runtime ledger physical slots agrees heaps represented heapTyped valueTyped stable in
theorem preserves (budget : Nat)
    (bodyMeaning : SourceBodies (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.CoercionPath (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before steps sourceValue outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs actual compilation.internalReason store (.inRight .word nativeValue)
        (calls.map (CallableCoercionSpine.Call.rename ξ)) result finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld target output.type faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  induction chain generalizing mapping world before store sourceValue nativeValue size outcome after with
  | nil =>
      cases trace
      exact ⟨_, store, mapping, world, .nil, .value represented, heaps,
        LocationMap.Extends.refl _, WorldExtends.refl _, AdministrativePreserved.refl _ _,
        Dynamic.HeapMetadataExtend.refl _, pool, Relates.refl pool⟩
  | @cons coercion target input middle output rest call calls step port valid tail ih =>
      obtain ⟨headerHeap, headerArguments⟩ := CallableIndexedOwnedPreparedStagedCoercionInvocationBounds.source_arguments step port wellFormed runtime heapTyped valueTyped
      have inputRep : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source
          sourceValue nativeValue call.signature.parameterType := step.inputType.symm ▸ represented
      cases trace with
      | coercionsCons head path =>
          obtain ⟨converted, middleStore, middleMap, middleWorld, invoked, resultRep, middleHeaps,
              maps, worlds, frame, metadata, reached, related⟩ :=
            CallableIndexedOwnedPreparedStagedCoercionInvocationBounds.preserves step port owner functions faults pool ownerFrame physical slots agrees heaps
              inputRep headerHeap headerArguments stable wellFormed budget bodyMeaning.1 ledger head
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
          cases resultRep with
          | value convertedRep =>
              obtain ⟨convertedTyped, middleTyped, _types⟩ := Dynamic.CoercionStepExecutes.preserved
                wellFormed runtime heapTyped valueTyped valid head.sound.value_plain
              have middleType : middle.type = call.signature.resultType := by rw [step.emitted]
              have nextRep := convertedRep
              rw [← middleType] at nextRep
              obtain ⟨result, finalStore, finalMap, finalWorld, remaining, resultRep, finalHeaps,
                  tailMaps, tailWorlds, tailFrame, tailMetadata, returned, tailRelated⟩ :=
                ih reached (physical.extend frame) middleHeaps nextRep middleTyped convertedTyped
                  (StableRows.after_administrative pool reached stable frame) bodyMeaning.2 path
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              exact ⟨result, finalStore, finalMap, finalWorld, .cons invoked remaining,
                resultRep, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
                frame.trans tailFrame, metadata.trans tailMetadata, returned, related.trans tailRelated⟩
      | coercionsFault head =>
          obtain ⟨converted, finalStore, finalMap, finalWorld, invoked, resultRep, finalHeaps,
              maps, worlds, frame, metadata, reached, related⟩ :=
            CallableIndexedOwnedPreparedStagedCoercionInvocationBounds.preserves step port owner functions faults pool ownerFrame physical slots agrees heaps
              inputRep headerHeap headerArguments stable wellFormed budget bodyMeaning.1 ledger head
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
          cases resultRep with
          | fault matched =>
              have finalType : CallableCoercionSpine.finalType call.signature.resultType
                  (calls.map (CallableCoercionSpine.Call.rename ξ)) = output.type := by
                simpa only [step.emitted] using tail.final_type ξ
              refine ⟨_, finalStore, finalMap, finalWorld, .cons invoked ?_, .fault matched,
                finalHeaps, maps, worlds, frame, metadata, reached, related⟩
              simpa only [finalType] using CallableCoercionSpine.Runs.failure actual compilation.internalReason
                finalStore call.signature.resultType _ (calls.map (CallableCoercionSpine.Call.rename ξ))

private theorem failed_runs {budget : Nat} {environment : Environment} {reason : Word}
    {store finalStore : Store} {tag : Ty} {payload result : Value} {calls : List CallableCoercionSpine.Call}
    (trace : CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized budget environment reason)
      store (.inLeft tag payload) calls result finalStore) :
    result = .inLeft (CallableCoercionSpine.finalType tag calls) payload ∧ finalStore = store := by
  generalize original : Value.inLeft tag payload = input at trace
  induction trace generalizing tag with
  | nil => cases original; exact ⟨rfl, rfl⟩
  | cons head tail ih =>
      cases original
      cases head with
      | skipped => exact ih rfl

include ownerFrame wellFormed runtime physical slots agrees heaps represented heapTyped valueTyped stable in
theorem reflects (budget : Nat)
    (bodyMeaning : NativeBodies (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {result : Value} {finalStore : Store}
    (completed : CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized budget actual compilation.internalReason)
      store (.inRight .word nativeValue) (calls.map (CallableCoercionSpine.Call.rename ξ)) result finalStore) :
    ∃ size outcome after finalMap finalWorld,
      Staging.Recursive.Size.CoercionPath (Program.ofChecked compiled.sourceProgram) stages size
        invocation context before steps sourceValue outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld target output.type faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  induction chain generalizing mapping world before store sourceValue nativeValue result finalStore with
  | nil =>
      cases completed
      exact ⟨_, .value sourceValue, before, mapping, world, .coercionsNil, .value represented, heaps,
        LocationMap.Extends.refl _, WorldExtends.refl _, AdministrativePreserved.refl _ _,
        Dynamic.HeapMetadataExtend.refl _, pool, Relates.refl pool⟩
  | @cons coercion target input middle output rest call calls step port valid tail ih =>
      obtain ⟨headerHeap, headerArguments⟩ := CallableIndexedOwnedPreparedStagedCoercionInvocationBounds.source_arguments
        step port wellFormed runtime heapTyped valueTyped
      have inputRep : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source
          sourceValue nativeValue call.signature.parameterType := step.inputType.symm ▸ represented
      cases completed with
      | cons head remaining =>
          obtain ⟨sourceSize, outcome, middleHeap, middleMap, middleWorld, trace, resultRep, middleHeaps,
              maps, worlds, frame, metadata, reached, related⟩ :=
            CallableIndexedOwnedPreparedStagedCoercionInvocationBounds.reflects
              step port owner functions faults pool ownerFrame physical slots agrees heaps
              inputRep headerHeap headerArguments stable wellFormed budget bodyMeaning.1 head
          cases resultRep with
          | value convertedRep =>
              obtain ⟨convertedTyped, middleTyped, _types⟩ := Dynamic.CoercionStepExecutes.preserved
                wellFormed runtime heapTyped valueTyped valid trace.sound.value_plain
              have middleType : middle.type = call.signature.resultType := by rw [step.emitted]
              have nextRep := convertedRep
              rw [← middleType] at nextRep
              obtain ⟨tailSize, outcome, after, finalMap, finalWorld, tailTrace, finalRep, finalHeaps,
                  tailMaps, tailWorlds, tailFrame, tailMetadata, returned, tailRelated⟩ :=
                ih reached (physical.extend frame) middleHeaps nextRep middleTyped convertedTyped
                  (StableRows.after_administrative pool reached stable frame) bodyMeaning.2 remaining
              exact ⟨_, outcome, after, finalMap, finalWorld, .coercionsCons trace tailTrace,
                finalRep, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
                frame.trans tailFrame, metadata.trans tailMetadata, returned, related.trans tailRelated⟩
          | fault matched =>
              have finalType : CallableCoercionSpine.finalType call.signature.resultType
                  (calls.map (CallableCoercionSpine.Call.rename ξ)) = output.type := by
                simpa only [step.emitted] using tail.final_type ξ
              obtain ⟨sameResult, rfl⟩ := failed_runs remaining
              rw [finalType] at sameResult
              subst result
              exact ⟨_, _, middleHeap, middleMap, middleWorld, .coercionsFault trace, .fault matched,
                middleHeaps, maps, worlds, frame, metadata, reached, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionPathBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedDirectExpressionBounds
/-! Original direct-call forms and their authentic ordered conversions compose
at the same reached physical state. Both internal body continuations use one
budget; the original staged trace supplies the final Source admission. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedDirectExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedPhysicalRawDirectHeadBounds (RawPreservesAt RawReflectsAt)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {lowerChild : SourceCoreEvidence.Child} {fuel : Nat} {callables : SourceCoreFunctions.CallablePolicy}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {output : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
  (receipt : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    lowerChild fuel invocation.source scope id callee ids instantiation reasonAt callables node output)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (slots : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix index.scope index.canonical)
  (ownerFrame : owner.key.frameLocation = 0)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)
  {stages : Staging.Recursive.Registry} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller receipt.available scope node callables context invocation stages
    node.rawType node.type receipt.operand node.coercions output calls)
  (nonempty : node.coercions ≠ [])
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable (typed : ExpressionHasType invocation.source context id node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrativeContext scope
    environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission callerBridge.forgetSlots context initial)

include physical slots ownerFrame chain nonempty unique wellFormed runtime covers ledger typed environments heaps locals agrees actualTyped admitted in
theorem preserves (budget : Nat)
    (rawMeaning : ∀ size, size ≤ budget → RawPreservesAt (context := context) (receiving := receiving) owner receipt callerBridge functions faults stages size)
    (bodyMeaning : CallableIndexedOwnedPreparedStagedCoercionPathBounds.SourceBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission callerBridge.forgetSlots context node.type outcome reached := by
  rcases CallableIndexedOwnedPreparedStagedCoercedExpressionSource.ordinary_branches receipt.found unique nonempty
      (by intro name binder impossible; rw [receipt.form] at impossible; cases impossible) trace with
    ⟨rawSize, pathSize, source, middle, sameSize, rawTrace, pathTrace⟩ |
    ⟨rawSize, failure, sameSize, outcomeEq, rawTrace⟩
  · have rawLess : rawSize < size := by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    have pathLess : pathSize < size := by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    have rawWithin : rawSize ≤ budget := Nat.le_trans (Nat.le_of_lt rawLess) within
    have pathWithin : pathSize ≤ budget := Nat.le_trans (Nat.le_of_lt pathLess) within
    obtain ⟨native, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
        maps, worlds, frame, metadata, middleState, related⟩ :=
      rawMeaning rawSize rawWithin typed environments heaps locals agrees actualTyped initial admitted rawTrace
    cases represented with
    | value valueRep =>
      obtain ⟨valueTyped, middleTyped, _types⟩ := CallableIndexedOwnedPreparedStagedCoercedExpressionSource.raw_value
        receipt.found unique wellFormed runtime covers locals admitted.heap typed rawTrace
      obtain ⟨value, finalStore, finalMap, finalWorld, runs, result, finalHeaps,
          tailMaps, tailWorlds, tailFrame, tailMetadata, finalPool, tailRelated⟩ :=
        CallableIndexedOwnedPreparedStagedCoercionPathBounds.preserves owner functions faults chain ownerFrame
          wellFormed runtime ledger (callerBridge.pool middleState) (physical middleState) (slots middleState)
          agrees middleHeaps valueRep middleTyped valueTyped
          (CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
            (callerBridge.pool initial) (callerBridge.pool middleState) admitted.rows frame)
          budget bodyMeaning pathTrace pathWithin
      obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore middleState finalPool
        tailMaps tailWorlds tailFrame tailMetadata tailRelated
      refine ⟨value, finalStore, finalMap, finalWorld, ?_, result, finalHeaps,
        maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame, metadata.trans tailMetadata,
        returned, callerProtocol.trans related returnedRelated, ?_⟩
      · exact (chain.spine.renamed_completed_iff ξ).mpr ⟨_, _, evaluated, runs⟩
      · exact after_expression_sized initial returned admitted wellFormed runtime covers locals typed trace
          (frame.trans tailFrame)
  · subst outcome
    have rawLess : rawSize < size := by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    have rawWithin : rawSize ≤ budget := Nat.le_trans (Nat.le_of_lt rawLess) within
    obtain ⟨native, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ :=
      rawMeaning rawSize rawWithin typed environments heaps locals agrees actualTyped initial admitted rawTrace
    cases represented with
    | @fault _ token matched =>
      have runs := CallableCoercionSpine.Runs.failure actual compilation.internalReason finalStore
        receipt.operand.type (.word token) (calls.map (CallableCoercionSpine.Call.rename ξ))
      rw [chain.final_type ξ] at runs
      exact ⟨_, finalStore, finalMap, finalWorld,
        (chain.spine.renamed_completed_iff ξ).mpr ⟨_, _, evaluated, runs⟩, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, reached, related,
        after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame⟩

private theorem failed_runs {budget : Nat} {environment : Environment} {reason : Word}
    {store finalStore : Store} {tag : Ty} {payload result : Value} {calls : List CallableCoercionSpine.Call}
    (trace : CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized budget environment reason)
      store (.inLeft tag payload) calls result finalStore) :
    result = .inLeft (CallableCoercionSpine.finalType tag calls) payload ∧ finalStore = store := by
  generalize original : Value.inLeft tag payload = input at trace
  induction trace generalizing tag with
  | nil => cases original; exact ⟨rfl, rfl⟩
  | cons head tail ih =>
      cases original
      cases head with
      | skipped => exact ih rfl

include physical slots ownerFrame chain nonempty unique wellFormed runtime covers typed environments heaps locals agrees actualTyped admitted in
theorem reflects (budget : Nat)
    (rawMeaning : ∀ size, size ≤ budget → RawReflectsAt (context := context) (receiving := receiving) owner receipt callerBridge functions faults stages size)
    (bodyMeaning : CallableIndexedOwnedPreparedStagedCoercionPathBounds.NativeBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (output.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission callerBridge.forgetSlots context node.type outcome reached := by
  obtain ⟨rawSize, native, middleStore, rawBound, _rawStrict, rawEvaluation, runs⟩ :=
    chain.spine.renamed_completed_sized ξ completed
  obtain ⟨sourceRawSize, rawOutcome, middle, middleMap, middleWorld, rawTrace, represented, middleHeaps,
      maps, worlds, frame, metadata, middleState, related⟩ :=
    rawMeaning rawSize (Nat.le_trans rawBound within) typed environments heaps locals agrees actualTyped initial admitted rawEvaluation
  cases represented with
  | value valueRep =>
      obtain ⟨valueTyped, middleTyped, _types⟩ := CallableIndexedOwnedPreparedStagedCoercedExpressionSource.raw_value
        receipt.found unique wellFormed runtime covers locals admitted.heap typed rawTrace
      obtain ⟨pathSize, outcome, after, finalMap, finalWorld, pathTrace, result, finalHeaps,
          tailMaps, tailWorlds, tailFrame, tailMetadata, finalPool, tailRelated⟩ :=
        CallableIndexedOwnedPreparedStagedCoercionPathBounds.reflects owner functions faults chain ownerFrame
          wellFormed runtime (callerBridge.pool middleState) (physical middleState) (slots middleState)
          agrees middleHeaps valueRep middleTyped valueTyped
          (CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
            (callerBridge.pool initial) (callerBridge.pool middleState) admitted.rows frame)
          budget bodyMeaning (runs.mono within)
      obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore middleState finalPool
        tailMaps tailWorlds tailFrame tailMetadata tailRelated
      have trace := Staging.Recursive.Size.Expression.coercedValue (lookupExpression?_sound receipt.found)
        nonempty rawTrace pathTrace
      exact ⟨_, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
        maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame, metadata.trans tailMetadata,
        returned, callerProtocol.trans related returnedRelated,
        after_expression_sized initial returned admitted wellFormed runtime covers locals typed trace (frame.trans tailFrame)⟩
  | fault matched =>
      obtain ⟨sameValue, rfl⟩ := failed_runs runs
      rw [chain.final_type ξ] at sameValue
      subst value
      have trace := Staging.Recursive.Size.Expression.coercedFault (lookupExpression?_sound receipt.found) nonempty rawTrace
      exact ⟨_, _, middle, middleMap, middleWorld, trace, .fault matched, middleHeaps,
        maps, worlds, frame, metadata, middleState, related,
        after_expression_sized initial middleState admitted wellFormed runtime covers locals typed trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedDirectExpressionBounds
end
