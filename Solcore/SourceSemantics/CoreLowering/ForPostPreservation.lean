import Solcore.SourceSemantics.CoreLowering.ForHeaderFault
import Solcore.SourceSemantics.CoreLowering.ForFiniteFault
import Solcore.SourceSemantics.CoreLowering.ForLoopReflectionInterfaces

/-! Static post headers discharge the success and fault interfaces used by
finite source for induction, under the actual six temporary loop binders. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell CoreProof

theorem post_preserves
    {compilation : SourceCorePrimitive.Context} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {items : List ForItemForm} {code : Core.Expr} {ξ : Core.Renaming}
    (tree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context items code)
    (unique : NodeOccurrencesUnique source)
    (respects : Core.Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope) actualContext)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    Internal.PostPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location items (code.rename ξ) := by
  intro mapping world heap after store finalContext finalEnvironment environments heaps actualTyped locationTyped executed continued
  have layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ := ⟨respects, agree, actualTyped⟩
  have entry := ((layout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert Core.RuntimeValueHasType.unit).insert
    (Core.RuntimeValueHasType.bool (value := true))
  cases continued with
  | false =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inLeft (rightType := Core.LocalLoop.transferType)
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit))).insert
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit)).insert Core.RuntimeValueHasType.unit
    obtain ⟨tail, _, _, heapEq, maps, worlds, frame, agreement⟩ :=
      tree.source_success unique program evidence environments heaps shifted executed
    have endpoint : tail.code = Core.LocalLoop.fallthrough type := tail.certificate
    have completed : Core.Evaluates tail.actual tail.store (tail.code.rename tail.embedding)
        (Core.LocalLoop.fallthroughValue type) tail.store := by
      rw [endpoint, Core.LoopRenaming.fallthrough]
      exact Core.LocalLoop.fallthrough_evaluates _ _ _
    refine ⟨tail.store, tail.mapping, tail.world, ?_, heapEq ▸ tail.heaps, maps, worlds, frame⟩
    have result := agreement.wrap completed
    simpa only [ForLoop.postCode_eq, rename_insert, ForLoop.fallthroughPrefix, Core.LoopExecution.entryEnvironment,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] using result
  | true =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inRight (leftType := Core.LocalControl.controlType type)
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit))).insert
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit)).insert Core.RuntimeValueHasType.unit
    obtain ⟨tail, _, _, heapEq, maps, worlds, frame, agreement⟩ :=
      tree.source_success unique program evidence environments heaps shifted executed
    have endpoint : tail.code = Core.LocalLoop.fallthrough type := tail.certificate
    have completed : Core.Evaluates tail.actual tail.store (tail.code.rename tail.embedding)
        (Core.LocalLoop.fallthroughValue type) tail.store := by
      rw [endpoint, Core.LoopRenaming.fallthrough]
      exact Core.LocalLoop.fallthrough_evaluates _ _ _
    refine ⟨tail.store, tail.mapping, tail.world, ?_, heapEq ▸ tail.heaps, maps, worlds, frame⟩
    have result := agreement.wrap completed
    simpa only [ForLoop.postCode_eq, rename_insert, ForLoop.continuingPrefix, Core.LoopExecution.entryEnvironment,
      ↓reduceIte, List.cons_append, List.nil_append] using result

theorem post_fault_preserves
    {compilation : SourceCorePrimitive.Context} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {items : List ForItemForm} {code : Core.Expr} {ξ : Core.Renaming}
    (tree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context items code)
    (unique : NodeOccurrencesUnique source)
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    (respects : Core.Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope) actualContext)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    Internal.PostFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location items (code.rename ξ) reasonAt := by
  intro mapping world heap after store finalContext reason environments heaps actualTyped locationTyped fault continued
  have layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ := ⟨respects, agree, actualTyped⟩
  have entry := ((layout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert Core.RuntimeValueHasType.unit).insert
    (Core.RuntimeValueHasType.bool (value := true))
  cases continued with
  | false =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inLeft (rightType := Core.LocalLoop.transferType)
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit))).insert
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit)).insert Core.RuntimeValueHasType.unit
    have result := tree.source_fault unique program evidence valid covers environments heaps shifted fault
    simpa only [ForHeaders.FaultResult, ForLoop.postCode_eq, rename_insert, ForLoop.fallthroughPrefix, Core.LoopExecution.entryEnvironment,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] using result
  | true =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inRight (leftType := Core.LocalControl.controlType type)
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit))).insert
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit)).insert Core.RuntimeValueHasType.unit
    have result := tree.source_fault unique program evidence valid covers environments heaps shifted fault
    simpa only [ForHeaders.FaultResult, ForLoop.postCode_eq, rename_insert, ForLoop.continuingPrefix, Core.LoopExecution.entryEnvironment,
      ↓reduceIte, List.cons_append, List.nil_append] using result


end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
