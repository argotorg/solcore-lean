import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyTyping
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Independent typing authenticates repeated key occurrences of an actual
prepared nested mapping route. Canonical member substitutions also preserve
staged raw arguments when the semantic substitution is permuted. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatiblePlaceKeyTyping
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreCompatibleDataPlaces CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceKeyTyping

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_key_typing", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_key_typing.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def rootType : TypeSystem.Ty := .mapping .bool (.mapping .bool .word)
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def projections : List PlaceProjection := [.index key, .index key]
private def assignment : AssignmentResolution := ⟨⟨binder.id, projections, .word⟩, []⟩
private def semanticContext := SourceSemantics.Context.ofSignatures signatures
private theorem unique : NodeOccurrencesUnique source := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]
private theorem keyTyped : ExpressionHasType source semanticContext key .bool := by
  apply ExpressionHasType.ofOrdinary (node := node) (rawType := .bool)
    (lookupExpression?_sound (show source.lookupExpression? key = some node by cbv))
    (.reference (.builtinBoolean true))
    (.bool (.ofSignatures signatures)) (.bool (.ofSignatures signatures))
  · intro id member; cases member
  · exact .nil _
  · rfl
private theorem projectionsTyped : SourceProjectionsHaveType source semanticContext rootType projections .word :=
  .index keyTyped (.index keyTyped (.nil _))

private def lowered : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun scope id code =>
  SourceCoreBasic.lowerExpression 10 source scope id Word.zero = .ok code
private theorem children : DataExpressionSequence.Tree source Child [] (DataPlaceKeyOrder.sourceKeys projections)
    [.bool, .bool] [lowered, lowered] := by
  change DataExpressionSequence.Tree source Child [] [key, key] [node.type, node.type] [lowered, lowered]
  exact .cons (node := node) (by cbv) (by cbv) (.single (node := node) (by cbv) (by cbv))

/-- No hand-supplied key view or source/native type cast is required. -/
private theorem actual_views {route : Route} {prepared : Prepared}
    (described : describe context checked.signatures source site assignment = .ok route)
    (preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared) :
    ∃ leaf, ∃ path : PreparedPath checked source site rootType projections 0 prepared.steps prepared.keys leaf,
      KeyViews path [.bool, .bool] ∧ SourceCoreRawMetadata.runtimeType leaf = .word := by
  obtain ⟨actualBinder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
  have binding : rootBinder source assignment.target.root = .ok binder := by cbv
  have same := Except.ok.inj (description.binding.symm.trans binding)
  subst actualBinder
  obtain ⟨_, _, path⟩ := description.prepared preparedBy
  exact ⟨selected, path, of_typing unique rfl path rfl projectionsTyped children⟩

private def p : TypeSystem.TypeParameterId := ⟨owner, 0⟩
private def q : TypeSystem.TypeParameterId := ⟨owner, 1⟩
private def permuted : TypeSystem.ParameterSubstitution := [(q, .comptime .word), (p, .comptime .bool)]
private theorem exactPermutation : ParameterSubstitution.Exact permuted [p, q] :=
  ⟨by decide, List.Perm.swap _ _ []⟩

example (type : TypeSystem.Ty) :
    SourceCoreRawMetadata.runtimeType (TypeSystem.ParameterSubstitution.apply [(p, .bool), (q, .word)] type) =
      SourceCoreRawMetadata.runtimeType (permuted.apply type) := by
  have canonical : [p, q].zip ((ParameterSubstitution.orderedArguments permuted [p, q]).map SourceCoreRawMetadata.runtimeType) =
      [(p, .bool), (q, .word)] := by cbv
  have result := canonical_substitution_view exactPermutation type
  rw [canonical] at result
  exact result

example : permuted ≠ [(p, .bool), (q, .word)] := by decide

def run : IO Unit := do
  match described : describe context checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"compatible key typing describe failed: {reprStr error}")
  | .ok route =>
    match preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) with
    | .error error => throw (IO.userError s!"compatible key typing prepare failed: {reprStr error}")
    | .ok prepared =>
      have _receipt := actual_views described preparedBy
      unless prepared.keys.map Prod.fst == [key, key] do
        throw (IO.userError "compatible key typing lost repeated key order")
  IO.println "compatible place key typing GREEN"

end Tests.SourceCoreCompatiblePlaceKeyTyping
