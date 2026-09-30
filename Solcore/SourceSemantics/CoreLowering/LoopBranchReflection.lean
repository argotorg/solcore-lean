import Solcore.SourceSemantics.CoreLowering.LoopScopedReflection

/-! Reconstruct scoped block and conditional heads from finite generated Core
executions. Child reflection contracts are structural induction hypotheses;
no independent source execution is supplied as an external premise. Lexical
environments are restored while heap, location-map and world extensions remain. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

theorem reflects_block_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {type : Core.Ty} {code : Core.Expr}
    (contains : ContainsStatement source id node) (form : node.form = .block statements)
    (bodyCorrect : Reflects compilation program evidence source reasonAt scope context false statements type code) :
    ScopedReflects compilation program evidence source reasonAt scope context id type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
    bodyCorrect wellFormed valid environments heaps layout evaluated
  refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, worlds, frame⟩
  cases meaning with
  | control sourceBody related => exact .control (.block contains form sourceBody) related
  | fault sourceFault related => exact .fault (.block contains form sourceFault) related

theorem reflects_if_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {id : StatementId} {node : StatementNode} {type : Core.Ty}
    {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    {conditionCode thenCode elseCode : Core.Expr} {depth : Nat}
    (contains : ContainsStatement source id node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (thenCorrect : Reflects compilation program evidence source reasonAt scope context false thenBody type thenCode)
    (elseCorrect : Reflects compilation program evidence source reasonAt scope context false (elseBody.getD []) type elseCode) :
    ScopedReflects compilation program evidence source reasonAt scope context id type
      (Core.LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.conditional] at evaluated
  obtain ⟨conditionOutcome, conditionResult, sourceEvaluation, related, coreEvaluation⟩ :=
    expression_meaning conditionTree program context evidence valid environments heaps layout
  cases related with
  | uninitialized site location origin =>
    cases sourceEvaluation with
    | fault sourceFault =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated
        (Core.LocalControl.choose_failure (Core.LocalLoop.controlType type) coreEvaluation)
      exact ⟨_, heap, mapping, world, .fault (.ifCondition contains form sourceFault) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩
  | value staged typed =>
    obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
    cases sourceEvaluation with
    | value sourceCondition =>
      obtain ⟨size, sized⟩ := evaluation_has_size evaluated
      cases boolean with
      | true =>
        obtain ⟨_, _, branch⟩ := sized.choose_true coreEvaluation
        obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
          thenCorrect wellFormed valid environments heaps (layout.insert Core.RuntimeValueHasType.bool)
            (by simpa only [rename_insert] using branch.sound)
        refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, worlds, frame⟩
        cases meaning with
        | control sourceBody related => exact .control (.ifTrue contains form sourceCondition sourceBody) related
        | fault sourceFault related => exact .fault (.ifTrueBody contains form sourceCondition sourceFault) related
      | false =>
        obtain ⟨_, _, branch⟩ := sized.choose_false coreEvaluation
        obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
          elseCorrect wellFormed valid environments heaps (layout.insert Core.RuntimeValueHasType.bool)
            (by simpa only [rename_insert] using branch.sound)
        refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, worlds, frame⟩
        cases elseBody with
        | none =>
          cases meaning with
          | control sourceBody related =>
            cases sourceBody
            exact .control (.ifFalseWithoutElse contains form sourceCondition) related
          | fault sourceFault _ => cases sourceFault
        | some statements =>
          cases meaning with
          | control sourceBody related => exact .control (.ifFalseWithElse contains form sourceCondition sourceBody) related
          | fault sourceFault related => exact .fault (.ifFalseBody contains form sourceCondition sourceFault) related

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
