import Solcore.SourceSemantics.CoreLowering.DataPlaceRouteCertificates
import Solcore.SourceSemantics.CoreLowering.DataPlaceGetterTyping

/-! Actual place compilation and its enclosing Core checker produce the full
static layout consumed by target-resolution and assignment meaning. Children
supply static compiler certificates here, never runtime evaluations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceLayoutCertificates
open Core Frontend Frontend.SourceInference SourceCoreDataPlaces DataPatternValues
open DataPlaceCertificates DataPlaceRouteCertificates

/-- Every semantic-path and getter-typing field is extracted. The only source
profile assumption concerns exact retained metadata, not generated semantics. -/
theorem of_describe_prepare {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {route : Route} {prepared : Prepared}
    {fuel : Nat} {invalid : Word} {missing : TypeSystem.Ty → Word}
    {expression : ExpressionLowerer} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    {context : Core.Context} {reference rhs next : Expr} {outputType resultType : Ty}
    {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand : Word}
    (profile : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      Profile signatures source binder.scheme.body assignment.target.projections assignment.target.type)
    (described : describe checked signatures source site assignment = .ok route)
    (preparedBy : prepare checked fuel route invalid missing = .ok prepared)
    (generated : ListRel (KeyGenerated expression fuel source scope reasonAt) prepared.keys codes)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    (typed : HasType context (execute prepared reference (SourceCoreCalls.packArguments codes) rhs next
      outputType operator bitNot invalidOperand) resultType checked.catalog.definitions) :
    ∃ sourceTypes, DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope
      assignment.target prepared codes sourceTypes context := by
  obtain ⟨sourceTypes, tree, keyTypes⟩ := DataPlaceKeyOrder.tree_of_generated_keys described preparedBy generated extract
  obtain ⟨root, rawTypes, raw⟩ := DataPlaceRouteCertificates.described profile described
  have typesSame := raw.keyTypes.tree_types tree
  subst sourceTypes
  obtain ⟨sameRoute, _, preparation⟩ := DataPlaceMappingPreparation.steps_of_prepare preparedBy
  refine ⟨rawTypes, tree, keyTypes, ?_, ?_, DataPlaceGetterTyping.of_execute typed⟩
  · apply RootShape.layout
    simpa only [sameRoute] using root
  · intro mapping world sources values projections shaped represented
    have path := raw.prepared_path preparation shaped represented (allKeys := values) (by
      intro index value selected
      simpa only [Nat.zero_add] using selected)
    simpa only [sameRoute] using path

/-- A successful production lowering plus actual Core typing provides the
layout and the exact execute equation. The compiler is not duplicated here. -/
theorem of_lower {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {fuel : Nat} {expression : ExpressionLowerer} {scope : Scope}
    {reasonAt : ExpressionId → Word} {sourceOperator : Syntax.ValueAssignOp} {rhs : Option ExpressionId}
    {next lowered : Expr} {outputType resultType : Ty} {invalid invalidOperand : Word}
    {missing : TypeSystem.Ty → Word} {certificate : GenericExpressionMeaning.Certificate} {context : Core.Context}
    (profile : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      Profile signatures source binder.scheme.body assignment.target.projections assignment.target.type)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    (accepted : lower checked signatures expression fuel source scope site assignment sourceOperator rhs outputType
      next reasonAt invalid invalidOperand missing = .ok lowered)
    (typed : HasType context lowered resultType checked.catalog.definitions) :
    ∃ prepared codes sourceTypes index value,
      SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType) ∧
      DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope assignment.target
        prepared codes sourceTypes context ∧
      RhsGenerated expression fuel source scope reasonAt prepared.route.leafType rhs value ∧
      lowered = execute prepared (.var index) (SourceCoreCalls.packArguments codes) value next outputType
        (binaryOperator (prepared.route.leafType = .integer) sourceOperator) rhs.isNone invalidOperand := by
  have generated := generated_of_lower accepted
  cases generated with
  | intro route prepared index keys value described lookup preparedBy keysGenerated operatorValid rhsGenerated =>
    have sameRoute := (DataPlaceMappingPreparation.steps_of_prepare preparedBy).1
    obtain ⟨types, layout⟩ := of_describe_prepare profile described preparedBy keysGenerated extract typed
    exact ⟨prepared, keys, types, index, value, by simpa only [sameRoute] using lookup, layout,
      by simpa only [sameRoute] using rhsGenerated, by simp only [sameRoute]⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceLayoutCertificates
