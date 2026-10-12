import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBodyViewEdits

/-! General expression syntax follows actual unchanged body occurrences.
Declaration and builtin callees are static metadata; their ordered arguments
are the recursively evaluated children. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open Core Frontend SourceInference
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor NativeMetadataOn)

/-- Only actual evaluated subexpressions are recursive child obligations. -/
def RuntimeChild (form : ExpressionForm) (id : ExpressionId) : Prop :=
  match form with
  | .call _ ids (.declaration _) | .call _ ids (.builtinFunction _) => id ∈ ids
  | _ => (.expression id : NodeId) ∈ form.references

theorem runtime_child_references {form : ExpressionForm} {id : ExpressionId}
    (child : RuntimeChild form id) : (.expression id : NodeId) ∈ form.references := by
  unfold RuntimeChild at child
  split at child <;> simp_all [ExpressionForm.references]

theorem syntax_found {source : TypedSource} {id : ExpressionId}
    (tree : GeneralSyntax source id) : ∃ node, source.lookupExpression? id = some node := by
  cases tree with
  | leaf finite => cases finite <;> exact ⟨_, ‹source.lookupExpression? id = some _›⟩
  | group found _ _ => exact ⟨_, found⟩
  | tuple found _ _ => exact ⟨_, found⟩
  | constructor found _ _ _ => exact ⟨_, found⟩
  | builtin found _ _ => exact ⟨_, found⟩
  | direct found _ _ _ => exact ⟨_, found⟩
  | call found _ _ _ => exact ⟨_, found⟩
  | unary found _ _ => exact ⟨_, found⟩
  | binary found _ _ _ => exact ⟨_, found⟩
  | conditional found _ _ _ _ => exact ⟨_, found⟩

theorem syntax_child {source : TypedSource} {id child : ExpressionId}
    {node : ExpressionNode} (tree : GeneralSyntax source id)
    (found : source.lookupExpression? id = some node)
    (edge : RuntimeChild node.form child) : GeneralSyntax source child := by
  cases tree with
  | leaf finite =>
      cases finite with
      | literal selected atomic =>
          cases Option.some.inj (selected.symm.trans found)
          generalize formEq : node.form = actualForm at atomic
          cases atomic <;> simp [formEq, RuntimeChild, ExpressionForm.references] at edge
      | read selected form =>
          cases Option.some.inj (selected.symm.trans found)
          simp [form, RuntimeChild, ExpressionForm.references] at edge
      | @group _ _ inner selected form innerTree =>
          cases Option.some.inj (selected.symm.trans found)
          have same : child = inner := by simpa [form, RuntimeChild, ExpressionForm.references] using edge
          exact same.symm ▸ GeneralSyntax.leaf innerTree
      | @pair _ _ left right selected form first second =>
          cases Option.some.inj (selected.symm.trans found)
          have member : child = left ∨ child = right := by
            simpa [form, RuntimeChild, ExpressionForm.references] using edge
          rcases member with same | same
          · exact same.symm ▸ GeneralSyntax.leaf first
          · exact same.symm ▸ GeneralSyntax.leaf second
  | @group _ _ inner selected form innerTree =>
      cases Option.some.inj (selected.symm.trans found)
      have same : child = inner := by simpa [form, RuntimeChild, ExpressionForm.references] using edge
      exact same.symm ▸ innerTree
  | tuple selected form children =>
      cases Option.some.inj (selected.symm.trans found)
      exact children child (by simpa [form, RuntimeChild, ExpressionForm.references] using edge)
  | constructor selected form _ranges children =>
      cases Option.some.inj (selected.symm.trans found)
      exact children child (by simpa [form, RuntimeChild, ExpressionForm.references] using edge)
  | builtin selected form children =>
      cases Option.some.inj (selected.symm.trans found)
      exact children child (by simpa [form, RuntimeChild] using edge)
  | direct selected form _monomorphic children =>
      cases Option.some.inj (selected.symm.trans found)
      exact children child (by simpa [form, RuntimeChild] using edge)
  | @call _ _ callee ids _ selected form calleeTree children =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = callee ∨ child ∈ ids := by
        simpa [form, RuntimeChild, ExpressionForm.references] using edge
      rcases member with same | member
      · exact same.symm ▸ calleeTree
      · exact children child member
  | @unary _ _ operator operand selected form childTree =>
      cases Option.some.inj (selected.symm.trans found)
      have same : child = operand := by simpa [form, RuntimeChild, ExpressionForm.references] using edge
      exact same.symm ▸ childTree
  | @binary _ _ left operator right selected form first second =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = left ∨ child = right := by simpa [form, RuntimeChild, ExpressionForm.references] using edge
      rcases member with same | same
      · exact same.symm ▸ first
      · exact same.symm ▸ second
  | @conditional _ _ test yes no selected form testTree yesTree noTree =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = test ∨ child = yes ∨ child = no := by simpa [form, RuntimeChild, ExpressionForm.references] using edge
      rcases member with same | same | same
      · exact same.symm ▸ testTree
      · exact same.symm ▸ yesTree
      · exact same.symm ▸ noTree

section Syntax
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
include edited avoids

/-- Recursive syntax crosses only actual reached, unedited occurrences. -/
theorem syntax_view {id : ExpressionId} (tree : GeneralSyntax source id)
    (reached : Reaches source roots (.expression id)) : GeneralSyntax view id := by
  revert reached
  induction tree with
  | leaf finite =>
      intro reached
      exact .leaf (CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport.finite_syntax
        edited avoids finite reached)
  | @group id node inner found form child ih =>
      intro reached
      have innerReached : Reaches source roots (.expression inner) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .group ((expression_lookup edited avoids reached).symm.trans found) form (ih innerReached)
  | @tuple id node ids found form children ih =>
      intro reached
      exact .tuple ((expression_lookup edited avoids reached).symm.trans found) form
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @constructor id node instantiation ids found form ranges children ih =>
      intro reached
      exact .constructor ((expression_lookup edited avoids reached).symm.trans found) form ranges
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @builtin id node callee ids function found form children ih =>
      intro reached
      exact .builtin ((expression_lookup edited avoids reached).symm.trans found) form
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @direct id node callee ids instantiation found form monomorphic children ih =>
      intro reached
      exact .direct ((expression_lookup edited avoids reached).symm.trans found) form monomorphic
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @call id node callee ids metadata found form calleeTree children calleeIH childrenIH =>
      intro reached
      have calleeReached : Reaches source roots (.expression callee) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .call ((expression_lookup edited avoids reached).symm.trans found) form
        (calleeIH calleeReached)
        (fun child member => childrenIH child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @unary id node operator operand found form child ih =>
      intro reached
      exact .unary ((expression_lookup edited avoids reached).symm.trans found) form
        (ih (.expression reached found (by simp [form, ExpressionForm.references])))
  | @binary id node left operator right found form first second firstIH secondIH =>
      intro reached
      exact .binary ((expression_lookup edited avoids reached).symm.trans found) form
        (firstIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (secondIH (.expression reached found (by simp [form, ExpressionForm.references])))
  | @conditional id node condition yes no found form test thenBranch elseBranch testIH thenIH elseIH =>
      intro reached
      exact .conditional ((expression_lookup edited avoids reached).symm.trans found) form
        (testIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (thenIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (elseIH (.expression reached found (by simp [form, ExpressionForm.references])))

/-- Reverse syntax uses the original body's authentic reachability path. -/
theorem syntax_original {id : ExpressionId} (tree : GeneralSyntax view id)
    (reached : Reaches source roots (.expression id)) : GeneralSyntax source id := by
  have reverse : LocalView view source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  exact syntax_view reverse (avoids.view edited.metadata) tree (reached.metadata edited.metadata)
end Syntax

theorem viewed_metadata_native {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {named : CallableIndexedNamedGeneration.Named}
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (original : NativeMetadataFor compiled.indexed named function.source) :
    NativeMetadataOn compiled.indexed named code.view
      (fun id => Reaches code.view (function.body.map NodeId.statement) (.expression id)) := by
  let edited := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids bodyView
  have originalTree : ∀ id, Reaches code.view (function.body.map NodeId.statement) (.expression id) →
      GeneralSyntax code.view id → GeneralSyntax function.source id := fun id reached tree =>
    syntax_original edited avoids tree
      (reached.metadata code.viewOfSource.symm)
  have lookup : ∀ id, Reaches code.view (function.body.map NodeId.statement) (.expression id) →
      ∀ node, code.view.lookupExpression? id = some node → function.source.lookupExpression? id = some node :=
    fun id reached node found => (bodyView id (reached.metadata code.viewOfSource.symm)).trans found
  exact {
    requirements := fun id reached tree node found => original.requirements id (originalTree id reached tree) node (lookup id reached node found)
    coercions := fun id reached tree node found => original.coercions id (originalTree id reached tree) node (lookup id reached node found)
    initializer := fun id reached tree => original.initializer id (originalTree id reached tree)
    arguments := fun id reached tree node found => original.arguments id (originalTree id reached tree) node (lookup id reached node found)
    directCaller := fun id reached tree node found => original.directCaller id (originalTree id reached tree) node (lookup id reached node found)
    localRead := fun id reached tree node found => original.localRead id (originalTree id reached tree) node (lookup id reached node found) }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
