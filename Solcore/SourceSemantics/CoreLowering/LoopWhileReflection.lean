import Solcore.SourceSemantics.CoreLowering.LoopScopedComposition

/-! The actual generated while prelude determines its self-cell and closure.
A finite Core execution reconstructs a finite independent source while trace;
body reflection is supplied only as the structural child-tree hypothesis. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

theorem reflects_while_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {id : StatementId} {statements : List StatementId} {node : StatementNode} {type : Core.Ty}
    {condition : ExpressionId} {conditionCode bodyCode : Core.Expr} {depth : Nat} {selfReason : Core.Word}
    (contains : ContainsStatement source id node) (form : node.form = .whileLoop condition statements)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (bodyTyped : Core.Ty.WellFormed [] type → Core.HasType (SourceCoreLocalCell.coreContext scope) bodyCode (Core.LocalLoop.resultType type))
    (bodyCorrect : Reflects compilation program evidence source reasonAt scope context false statements type bodyCode) :
    ScopedReflects compilation program evidence source reasonAt scope context id type
      (Core.LocalLoop.whileLoop type conditionCode bodyCode selfReason) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.whileLoop] at evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨entrySize, _, entry⟩ := sized.iterate_entry
  obtain ⟨installedHeaps, extended, unmapped, selfTyped, installed, installFrame⟩ :=
    LoopAdministration.install selfReason heaps layout.typed wellFormed
      (conditionTree.hasType.rename layout.respects) ((bodyTyped wellFormed).rename layout.respects)
      (Core.LocalLoop.fallthrough_hasType wellFormed)
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
    while_reflect conditionTree valid layout.agrees
      (bodyCorrect.body wellFormed valid layout.respects layout.agrees) entrySize
      (environments.extend (.refl _) extended) installedHeaps
      (Core.RuntimeEnvironmentHasTypes.weaken extended layout.typed) selfTyped unmapped installed entry
  refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, extended.trans worlds, installFrame.trans frame⟩
  cases meaning with
  | control sourceLoop related => exact .control (.whileLoop contains form sourceLoop) related
  | fault sourceFault related => exact .fault (.whileIteration contains form sourceFault) related

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
