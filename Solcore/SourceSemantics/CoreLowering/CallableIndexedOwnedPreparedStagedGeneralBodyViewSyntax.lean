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

export CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
  (RuntimeChild runtime_child_references syntax_found syntax_child)

variable {directSites : DeclarationInstantiation → Prop}

section Syntax
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
include edited avoids

/-- Recursive syntax crosses only actual reached, unedited occurrences. -/
theorem syntax_view {id : ExpressionId} (tree : GeneralSyntax source id directSites)
    (reached : Reaches source roots (.expression id)) : GeneralSyntax view id directSites := by
  revert reached
  induction tree with
  | leaf finite =>
      intro reached
      exact .leaf (CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport.finite_syntax
        edited avoids finite reached)
  | proxy found form =>
      intro reached
      exact .proxy ((expression_lookup edited avoids reached).symm.trans found) form
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
  | @index id node base key keyNode found form keyFound first second firstIH secondIH =>
      intro reached
      have baseReached : Reaches source roots (.expression base) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      have keyReached : Reaches source roots (.expression key) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .index ((expression_lookup edited avoids reached).symm.trans found) form
        ((expression_lookup edited avoids keyReached).symm.trans keyFound)
        (firstIH baseReached) (secondIH keyReached)
  | @conditional id node condition yes no found form test thenBranch elseBranch testIH thenIH elseIH =>
      intro reached
      exact .conditional ((expression_lookup edited avoids reached).symm.trans found) form
        (testIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (thenIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (elseIH (.expression reached found (by simp [form, ExpressionForm.references])))

/-- Reverse syntax uses the original body's authentic reachability path. -/
theorem syntax_original {id : ExpressionId} (tree : GeneralSyntax view id directSites)
    (reached : Reaches source roots (.expression id)) : GeneralSyntax source id directSites := by
  have reverse : LocalView view source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  exact syntax_view reverse (avoids.view edited.metadata) tree (reached.metadata edited.metadata)
end Syntax

theorem viewed_metadata_native {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {named : CallableIndexedNamedGeneration.Named}
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (original : NativeMetadataFor compiled.indexed named function.source directSites) :
    NativeMetadataOn compiled.indexed named code.view
      (fun id => Reaches code.view (function.body.map NodeId.statement) (.expression id)) directSites := by
  let edited := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids bodyView
  have originalTree : ∀ id, Reaches code.view (function.body.map NodeId.statement) (.expression id) →
      GeneralSyntax code.view id directSites → GeneralSyntax function.source id directSites := fun id reached tree =>
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
