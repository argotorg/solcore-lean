import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax

/-! The retained contextual reader preserves the actual metadata lookup at
all unchanged body occurrences, including synthetic direct callees. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableLambdaViewEdits CallableLambdaBodyReachability LambdaMetadataViews
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private inductive Selection : Option Node → Option Node → Prop where
  | none : Selection none none
  | some {before after : Node} (related : NodeView before after) : Selection (some before) (some after)

private theorem find_related {a b : List Node} (related : DataPatternValues.ListRel NodeView a b) (id : OccurrenceId) :
    Selection (a.find? fun node => decide (node.occurrenceId = id))
      (b.find? fun node => decide (node.occurrenceId = id)) := by
  induction related with
  | nil => exact .none
  | @cons before tail after rest head _ ih =>
    simp only [List.find?_cons, head.occurrence]
    split
    · exact .some head
    · exact ih

/-- Metadata views preserve node kind, so equal expression lookups also
preserve the exact missing-node versus statement-node diagnostic branch. -/
theorem lookup_node {source view : TypedSource} (metadata : MetadataView source view)
    {id : ExpressionId} (same : source.lookupExpression? id = view.lookupExpression? id) :
    source.lookupNode? id.occurrence = view.lookupNode? id.occurrence := by
  have selected := find_related metadata.nodes id.occurrence
  change Selection (source.lookupNode? id.occurrence) (view.lookupNode? id.occurrence) at selected
  unfold TypedSource.lookupExpression? at same
  cases left : source.lookupNode? id.occurrence <;>
    cases right : view.lookupNode? id.occurrence <;>
    simp only [left, right] at selected same ⊢
  · cases selected
  · cases selected
  · cases selected with
    | some related =>
      cases related with
      | expression _ _ => exact congrArg (fun node => node.map Node.expression) same
      | statement => rfl

/-- The actual contextual reader skips normalization for these original
monomorphic local reads. Other references retain the same complete node. -/
theorem recipe_read_view {directSites : DeclarationInstantiation → Prop}
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor prepared named source directSites)
    (id : ExpressionId) (reached : Reaches source roots (.expression id)) :
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy
