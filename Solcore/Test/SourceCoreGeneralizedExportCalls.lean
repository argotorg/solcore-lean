import Solcore.Test.SourceCoreGeneralizedExportTrace

/-! Independent ordinary Source application of the exported instances. The
actual closure frame is static code/evidence validity; no target call is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics

theorem MakeShape.identity_applies {source : TypedSource} (shape : MakeShape source)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence callerEvidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (argument : Dynamic.Value)
    (frame : Dynamic.ClosureFrame program
      ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence)) :
    Dynamic.CallableApplies program context callerEvidence evidence before
      (.closure ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence))
      [argument] argument
      ⟨before.cells ++ [{type := (shape.principal.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  let function := (shape.principal.descriptor definitionContext captured).instantiate substitution evidence
  let parameter := shape.principal.parameter.applySubstitution substitution
  let after : Dynamic.Heap := ⟨before.cells ++ [{type := parameter.scheme.body, value := some argument}]⟩
  have allocation : Dynamic.Heap.Allocates before parameter.scheme.body (some argument)
      ⟨before.cells.length⟩ after := .append
  have read : Dynamic.ExpressionEvaluates program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨before.cells.length⟩) :: captured)
      after shape.principal.bodyRead.node.id argument after := by
    apply Dynamic.ExpressionEvaluates.intro
      (FlexibleSubstitution.ContainsExpression.applySubstitution substitution
        (lookupExpression?_sound shape.principal.bodyRead.found))
    · simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
        shape.principal.bodyRead.form, shape.identity, shape.principal.bodyRead.requirements, shape.principal.bodyRead.coercions]
      exact .local rfl .head allocation.reads_new rfl rfl
    · simp only [ExpressionNode.applySubstitution, shape.principal.bodyRead.coercions, List.map_nil]
      exact .nil
  have returned : Dynamic.StatementExecutes program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨before.cells.length⟩) :: captured)
      after shape.principal.bodyReturn.id
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      (.returned argument) after := by
    exact .returnValue
      (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
        (lookupStatement?_sound shape.principal.bodyFound))
      (by simp only [StatementNode.applySubstitution, shape.principal.bodyForm,
        StatementForm.applySubstitution]) read
  have parameters : ∃ types callContext,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext := by
    rcases frame.code.occurrence with ⟨id, node, _contains, form, _raw, typed⟩
    rw [form] at typed
    generalize rawEq : TypeSystem.Ty.function
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)))
      function.resultType = raw at typed
    cases typed with
    | lambda names parameters body completes => exact ⟨_, _, parameters⟩
  obtain ⟨types, callContext, parameters⟩ := parameters
  have parameterList : function.parameters = [parameter] := rfl
  rw [parameterList] at parameters
  cases parameters with
  | cons scheme extended tail =>
    cases tail
    cases extended with
    | intro wellformed fresh =>
      apply Dynamic.CallableApplies.closure rfl frame
        (parameterList.symm ▸ MonoBindersExtend.cons scheme (.intro wellformed fresh) (.nil _))
      · exact .cons allocation (.nil _ _)
      · apply Dynamic.FunctionStatementsExecute.singleton
          (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
            (lookupStatement?_sound shape.principal.bodyFound))
        · intro expression impossible
          simp only [StatementNode.applySubstitution, shape.principal.bodyForm,
            StatementForm.applySubstitution] at impossible
          cases impossible
        · exact returned
      · rfl


theorem CaptureShape.captured_applies {source : TypedSource} (shape : CaptureShape source)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence callerEvidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (argument saved : Dynamic.Value)
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (capturedLookup : Dynamic.Environment.LooksUp captured shape.principal.input.id location)
    (capturedRead : Dynamic.Heap.Reads before location cell)
    (ordinary : cell.generalized = none) (capturedValue : cell.value = some saved)
    (frame : Dynamic.ClosureFrame program
      ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence)) :
    Dynamic.CallableApplies program context callerEvidence evidence before
      (.closure ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence))
      [argument] saved
      ⟨before.cells ++ [{type := (shape.principal.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  let function := (shape.principal.descriptor definitionContext captured).instantiate substitution evidence
  let parameter := shape.principal.parameter.applySubstitution substitution
  let after : Dynamic.Heap := ⟨before.cells ++ [{type := parameter.scheme.body, value := some argument}]⟩
  have allocation : Dynamic.Heap.Allocates before parameter.scheme.body (some argument)
      ⟨before.cells.length⟩ after := .append
  have read : Dynamic.ExpressionEvaluates program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨before.cells.length⟩) :: captured)
      after shape.principal.bodyRead.node.id saved after := by
    apply Dynamic.ExpressionEvaluates.intro
      (FlexibleSubstitution.ContainsExpression.applySubstitution substitution
        (lookupExpression?_sound shape.principal.bodyRead.found))
    · simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
        shape.principal.bodyRead.form, shape.captured, shape.principal.bodyRead.requirements, shape.principal.bodyRead.coercions]
      exact .local rfl (.tail shape.principal.parameterInputDistinct capturedLookup)
        (allocation.preserves_read capturedRead) ordinary capturedValue
    · simp only [ExpressionNode.applySubstitution, shape.principal.bodyRead.coercions, List.map_nil]
      exact .nil
  have returned : Dynamic.StatementExecutes program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨before.cells.length⟩) :: captured)
      after shape.principal.bodyReturn.id
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      (.returned saved) after := by
    exact .returnValue
      (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
        (lookupStatement?_sound shape.principal.bodyFound))
      (by simp only [StatementNode.applySubstitution, shape.principal.bodyForm,
        StatementForm.applySubstitution]) read
  have parameters : ∃ types callContext,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext := by
    rcases frame.code.occurrence with ⟨id, node, _contains, form, _raw, typed⟩
    rw [form] at typed
    generalize rawEq : TypeSystem.Ty.function
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)))
      function.resultType = raw at typed
    cases typed with
    | lambda names parameters body completes => exact ⟨_, _, parameters⟩
  obtain ⟨types, callContext, parameters⟩ := parameters
  have parameterList : function.parameters = [parameter] := rfl
  rw [parameterList] at parameters
  cases parameters with
  | cons scheme extended tail =>
    cases tail
    cases extended with
    | intro wellformed fresh =>
      apply Dynamic.CallableApplies.closure rfl frame
        (parameterList.symm ▸ MonoBindersExtend.cons scheme (.intro wellformed fresh) (.nil _))
      · exact .cons allocation (.nil _ _)
      · apply Dynamic.FunctionStatementsExecute.singleton
          (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
            (lookupStatement?_sound shape.principal.bodyFound))
        · intro expression impossible
          simp only [StatementNode.applySubstitution, shape.principal.bodyForm,
            StatementForm.applySubstitution] at impossible
          cases impossible
        · exact returned
      · rfl


end Tests.SourceCoreGeneralizedExport
