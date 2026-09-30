import Solcore.SourceSemantics.CoreLowering.LoopReflectionInterfaces

/-! Reconstruct a finite independent while execution from a finite execution
of its installed Core closure. Body reflection is the structural child-tree
induction hypothesis; the next iteration is proved by decreasing Core
execution size, never assumed as an external source execution. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof
open Core.LoopExecution

private theorem self_retained
    {mapping futureMapping : GeneralHeap.LocationMap} {before after : Core.Store}
    {location : Core.Location} {value : Core.Value}
    (unmapped : location ∉ mapping) (read : before.read? location = some value)
    (frame : GeneralHeap.AdministrativePreserved mapping before futureMapping after) :
    location ∉ futureMapping ∧ after.read? location = some value := by
  have bounded : location < before.length := (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨unmapped, same⟩ := frame location unmapped bounded
  exact ⟨unmapped, same.trans read⟩

private theorem while_context
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.WhileExecutes program context evidence source environment before condition statements finalContext outcome after) :
    finalContext = context := by cases execution <;> rfl

/-- The static condition constructs its source execution without any source
trace premise. The body contract is discharged by the statement-tree theorem. -/
theorem while_reflect
    {compilation : SourceCorePrimitive.Context} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {condition : ExpressionId} {conditionCode : Core.Expr} {conditionDepth : Nat}
    {statements : List StatementId} {body : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {administrativeContext : Core.Context}
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual)
    (bodyCorrect : BodyReflects program context evidence source reasonAt scope administrativeContext
      environment canonical actual actualContext type location statements body) :
    ∀ (size : Nat) {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap}
      {store finalStore : Core.Store} {result : Core.Value},
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
      GeneralHeap.HeapRepresents mapping world heap store →
      Core.RuntimeEnvironmentHasTypes world actual actualContext →
      world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
      location ∉ mapping →
      store.read? location = some (.inRight .unit
        (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body (Core.LocalLoop.fallthrough type) selfReason location actual)) →
      EvaluationSize size (entryEnvironment type location actual) store
        (Core.LocalLoop.loopBody type (conditionCode.rename ξ) body (Core.LocalLoop.fallthrough type) selfReason) result finalStore →
      WhileResult program context evidence source reasonAt environment heap condition statements type mapping world store result finalStore := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro mapping world heap store finalStore result environments heaps actualTyped locationTyped unmapped installed evaluation
    obtain ⟨conditionOutcome, conditionValue, conditionSource, related, conditionCore⟩ :=
      GeneralExpressions.Primitive.preserves conditionTree program context evidence valid environments heaps
    have restricted := GeneralExpressions.Primitive.readOnly conditionTree
    have renamed := restricted.evaluation_rename conditionCore agree
    have first := (restricted.rename ξ).evaluation_weakenAt_zero renamed
      (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) location)
    have shifted := ((restricted.rename ξ).weakenAt 0).evaluation_weakenAt_zero first .unit
    cases related with
    | uninitialized site faultLocation origin =>
      cases conditionSource with
      | fault sourceFault =>
        obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure shifted)
        exact ⟨context, _, heap, mapping, world,
          .fault (.condition sourceFault) (.uninitialized site faultLocation origin), heaps, .refl _, .refl _, .refl _ _⟩
    | value staged typed =>
      obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
      cases conditionSource with
      | value sourceCondition =>
        cases boolean with
        | false =>
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false shifted)
          exact ⟨context, _, heap, mapping, world,
            .control (.done sourceCondition) (.fallthrough environment), heaps, .refl _, .refl _, .refl _ _⟩
        | true =>
          obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch shifted
          obtain ⟨bodySize, bodyStore, bodyValue, _, bodyEvaluation⟩ := branch.bind_computation
          obtain ⟨bodyContext, bodyOutcome, bodyHeap, bodyMapping, bodyWorld, bodyMeaning,
            bodyHeaps, maps, worlds, frame⟩ :=
            bodyCorrect environments heaps actualTyped locationTyped bodyEvaluation.sound
          cases bodyMeaning with
          | fault sourceFault related =>
            obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound
              (Core.LoopExecution.body_failure shifted bodyEvaluation.sound)
            exact ⟨context, _, bodyHeap, bodyMapping, bodyWorld,
              .fault (.body sourceCondition sourceFault) related, bodyHeaps, maps, worlds, frame⟩
          | control sourceBody related =>
            cases related with
            | returned staged typed =>
              obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_returned shifted bodyEvaluation.sound)
              exact ⟨context, _, bodyHeap, bodyMapping, bodyWorld,
                .control (.returns sourceCondition sourceBody) (.returned staged typed), bodyHeaps, maps, worlds, frame⟩
            | breaking bodyEnvironment =>
              obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_breaking shifted bodyEvaluation.sound)
              exact ⟨context, _, bodyHeap, bodyMapping, bodyWorld,
                .control (.breaks sourceCondition sourceBody) (.fallthrough environment), bodyHeaps, maps, worlds, frame⟩
            | fallthrough bodyEnvironment =>
              obtain ⟨unmappedAgain, installedAgain⟩ := self_retained unmapped installed frame
              obtain ⟨nextSize, nextSmaller, nextEvaluation⟩ := branch.loop_next_fallthrough bodyEvaluation.sound installedAgain
              obtain ⟨nextContext, nextOutcome, after, finalMapping, finalWorld, nextMeaning,
                finalHeaps, mapsAgain, worldsAgain, frameAgain⟩ :=
                ih nextSize (Nat.lt_trans nextSmaller branchSmaller)
                  (environments.extend maps worlds) bodyHeaps (Core.RuntimeEnvironmentHasTypes.weaken worlds actualTyped)
                  (worlds.lookup locationTyped) unmappedAgain installedAgain nextEvaluation
              cases nextMeaning with
              | control nextSource nextRelated =>
                have sameContext := while_context nextSource
                subst nextContext
                exact ⟨context, _, after, finalMapping, finalWorld,
                  .control (.nextFallthrough sourceCondition sourceBody nextSource) nextRelated,
                  finalHeaps, maps.trans mapsAgain, worlds.trans worldsAgain, frame.trans frameAgain⟩
              | fault nextFault nextRelated =>
                exact ⟨context, _, after, finalMapping, finalWorld,
                  .fault (.nextFallthrough sourceCondition sourceBody nextFault) nextRelated,
                  finalHeaps, maps.trans mapsAgain, worlds.trans worldsAgain, frame.trans frameAgain⟩
            | continuing bodyEnvironment =>
              obtain ⟨unmappedAgain, installedAgain⟩ := self_retained unmapped installed frame
              obtain ⟨nextSize, nextSmaller, nextEvaluation⟩ := branch.loop_next_continuing bodyEvaluation.sound installedAgain
              obtain ⟨nextContext, nextOutcome, after, finalMapping, finalWorld, nextMeaning,
                finalHeaps, mapsAgain, worldsAgain, frameAgain⟩ :=
                ih nextSize (Nat.lt_trans nextSmaller branchSmaller)
                  (environments.extend maps worlds) bodyHeaps (Core.RuntimeEnvironmentHasTypes.weaken worlds actualTyped)
                  (worlds.lookup locationTyped) unmappedAgain installedAgain nextEvaluation
              cases nextMeaning with
              | control nextSource nextRelated =>
                have sameContext := while_context nextSource
                subst nextContext
                exact ⟨context, _, after, finalMapping, finalWorld,
                  .control (.nextContinue sourceCondition sourceBody nextSource) nextRelated,
                  finalHeaps, maps.trans mapsAgain, worlds.trans worldsAgain, frame.trans frameAgain⟩
              | fault nextFault nextRelated =>
                exact ⟨context, _, after, finalMapping, finalWorld,
                  .fault (.nextContinue sourceCondition sourceBody nextFault) nextRelated,
                  finalHeaps, maps.trans mapsAgain, worlds.trans worldsAgain, frame.trans frameAgain⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
