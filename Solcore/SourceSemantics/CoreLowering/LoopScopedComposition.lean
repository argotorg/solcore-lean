import Solcore.SourceSemantics.CoreLowering.LoopScopedReflection

/-! Reconstruct scoped statement sequencing from finite Core evaluation.
The head and tail contracts are static-tree induction hypotheses, and the
actual helper evaluation selects whether the tail is entered. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

theorem reflects_scoped
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type : Core.Ty} {code body : Core.Expr}
    (contains : ContainsStatement source id node) (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : ScopedReflects compilation program evidence source reasonAt scope context id type code)
    (tail : Reflects compilation program evidence source reasonAt scope context mode rest type body) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.sequence type code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.sequence] at evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨_, middleStore, headResult, _, headSized⟩ := sized.bind_computation
  obtain ⟨headOutcome, middle, middleMap, middleWorld, headMeaning, middleHeaps, maps, worlds, frame⟩ :=
    head wellFormed valid environments heaps layout headSized.sound
  cases headMeaning with
  | control sourceHead related =>
    cases related with
    | fallthrough nextEnvironment =>
      have shiftedLayout := (((layout.extend worlds).insert
        (Core.RuntimeValueHasType.inLeft (rightType := Core.LocalLoop.transferType) (Core.RuntimeValueHasType.inLeft (rightType := type) .unit))).insert
        (Core.RuntimeValueHasType.inLeft (rightType := type) .unit)).insert Core.RuntimeValueHasType.unit
      obtain ⟨_, _, continuation⟩ := sized.sequence_fallthrough headSized.sound
      obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, futureMaps, futureWorlds, futureFrame⟩ :=
        tail wellFormed valid (environments.extend maps worlds) middleHeaps shiftedLayout
          (by simpa only [rename_insert] using continuation.sound)
      exact ⟨finalContext, outcome, after, finalMap, finalWorld,
        prepend contains (fun _ _ => notTail) sourceHead meaning,
        finalHeaps, maps.trans futureMaps, worlds.trans futureWorlds, frame.trans futureFrame⟩
    | returned staged typed =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.sequence_returned type headSized.sound)
      exact ⟨context, _, middle, middleMap, middleWorld,
        terminal contains notTail sourceHead (.returned _) (.returned staged typed),
        middleHeaps, maps, worlds, frame⟩
    | breaking nextEnvironment =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.sequence_transfer type headSized.sound)
      exact ⟨context, _, middle, middleMap, middleWorld,
        terminal contains notTail sourceHead (.breaking environment) (.breaking environment),
        middleHeaps, maps, worlds, frame⟩
    | continuing nextEnvironment =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.sequence_transfer type headSized.sound)
      exact ⟨context, _, middle, middleMap, middleWorld,
        terminal contains notTail sourceHead (.continuing environment) (.continuing environment),
        middleHeaps, maps, worlds, frame⟩
  | fault sourceFault related =>
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.sequence_failure type headSized.sound)
    exact ⟨context, _, middle, middleMap, middleWorld, head_fault sourceFault related,
      middleHeaps, maps, worlds, frame⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
