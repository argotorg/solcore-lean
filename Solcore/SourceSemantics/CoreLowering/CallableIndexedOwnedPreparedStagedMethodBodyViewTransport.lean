import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodPolicy
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEvidenceBodyViewTransport

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
