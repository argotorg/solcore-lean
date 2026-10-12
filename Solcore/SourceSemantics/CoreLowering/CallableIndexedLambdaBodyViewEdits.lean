import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance

/-! A finite list computed from the actual two source tables records exactly
which original expression lookups differ. BodyView excludes all reached edits;
no choice of metadata or compiler input is made in this projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBodyViewEdits
open Core Frontend SourceInference
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedContextualLambdaProvenance (BodyView)

def changed (source view : TypedSource) : List ExpressionId :=
  (source.nodes.filterMap (fun node => match node with
    | .expression expression => some expression.id
    | .statement _ => none)).filter (fun id => decide (source.lookupExpression? id ≠ view.lookupExpression? id))

theorem local_view {source view : TypedSource} (metadata : LambdaMetadataViews.MetadataView source view) :
    LocalView source view (changed source view) := by
  refine ⟨metadata, ?_⟩
  intro id fresh
  cases original : source.lookupExpression? id with
  | none =>
    cases viewed : view.lookupExpression? id with
    | none => rfl
    | some node =>
      obtain ⟨prior, found, _⟩ := metadata.expression viewed
      rw [original] at found
      cases found
  | some node =>
    by_cases same : some node = view.lookupExpression? id
    · exact same
    apply False.elim
    have different := same
    have member : id ∈ source.nodes.filterMap (fun entry => match entry with
        | .expression expression => some expression.id
        | .statement _ => none) := by
      obtain ⟨present, same⟩ := lookupExpression?_sound original
      exact List.mem_filterMap.mpr ⟨.expression node, present, congrArg some same⟩
    apply fresh
    exact List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq, original] using different⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}

theorem avoids (preserved : BodyView code) :
    Avoids function.source (function.body.map NodeId.statement) (changed function.source code.view) := by
  intro id member reached
  have different := of_decide_eq_true (List.mem_filter.mp member).2
  exact different (preserved id reached)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBodyViewEdits
