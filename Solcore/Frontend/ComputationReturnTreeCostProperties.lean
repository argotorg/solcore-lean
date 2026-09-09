import Solcore.Frontend.ComputationReturnTreeExecutionProperties
import Solcore.Frontend.ComputationReturnTreeEvaluationProperties
import Solcore.Frontend.ComputationBodyFragmentInsertionPaths
import Solcore.Core.ExactFuelProperties
import Solcore.Frontend.WordMatchProperties

/-! Supplied actual costs compose through mixed statements. A hidden discard
slot preserves the complete tail path, including its effects and actual captures. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem insert_zero_path {F : Core.Expr → Prop}
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    {expr : Core.Expr} (fragment : ComputationBodyFragment F expr)
    {environment : Core.Environment} {initialStore finalStore : Core.Store}
    {value : Core.Value} {cost : Nat}
    (path : Core.Steps cost (.initial expr environment initialStore) (.final value finalStore))
    (inserted : Core.Value) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval (expr.weakenAt 0) (inserted :: environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  obtain ⟨commonCost, paths⟩ := ComputationBodyFragment.insertion_paths (F := F) childPaths fragment [] environment inserted (Core.steps_from_initial_sound path)
  have sameCost := (path.final_unique (paths []).1).1
  exact sameCost.symm ▸ (paths continuation).2

private theorem fold_path
    (entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)))
    (defaultEntry : Option (Syntax.Block × Core.Expr))
    {actual value : Core.Value} {environment : Core.Environment} {initialStore finalStore : Core.Store}
    {selected : Syntax.Block} {tests branchCost : Nat} {core : Core.Expr}
    (patterns : ∀ entry ∈ entries, match entry.2.1 with
      | none => ∃ marker, entry.1.value.pattern.value = .wildcard marker
      | some word => WordMatchPatternDenotes entry.1.value.pattern word)
    (choice : WordMatchChooses actual (entries.map Prod.fst) (defaultEntry.map Prod.fst) selected tests)
    (branches : ∀ entry ∈ entries, entry.1.value.body = selected → ∀ continuation,
      Core.Steps branchCost ⟨.eval (entry.2.2.weakenAt 0) (actual :: environment), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    (fallback : ∀ entry ∈ defaultEntry.toList, entry.1 = selected → ∀ continuation,
      Core.Steps branchCost ⟨.eval (entry.2.weakenAt 0) (actual :: environment), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    (lowered : entries.foldr
      (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map fun body => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) body)
      (defaultEntry.map fun entry => entry.2.weakenAt 0) = some core)
    (continuation : List Core.Frame) :
    Core.Steps (branchCost + 7 * tests)
      ⟨.eval core (actual :: environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction entries generalizing actual selected tests core with
  | nil =>
      cases defaultEntry with
      | none => simp at lowered
      | some entry =>
          simp only [List.foldr_nil, Option.map_some, Option.some.injEq] at lowered
          subst core
          cases choice
          simpa using fallback entry (by simp) rfl continuation
  | cons entry rest ih =>
      rcases entry with ⟨arm, tag, branchCore⟩
      have pattern := patterns ⟨arm, tag, branchCore⟩ (by simp)
      cases tag with
      | none =>
          obtain ⟨marker, shape⟩ := pattern
          simp only [List.foldr_cons, Option.some.injEq] at lowered
          subst core
          cases choice with
          | wildcard _ => simpa using branches ⟨arm, none, branchCore⟩ (by simp) rfl continuation
          | hit meaning | miss meaning _ _ =>
              obtain ⟨literal, literalShape, _⟩ := meaning
              rw [shape] at literalShape
              cases literalShape
      | some literal =>
          simp only [List.foldr_cons, Option.map_eq_some_iff] at lowered
          obtain ⟨tailCore, tailLowered, rfl⟩ := lowered
          cases choice with
          | wildcard shape =>
              obtain ⟨source, literalShape, _⟩ := pattern
              rw [shape] at literalShape
              cases literalShape
          | hit meaning =>
              have equal := meaning.value_unique pattern
              subst_vars
              rename_i literal
              have guard (k) : Core.Steps 5
                  ⟨.eval (.binary .wordEq (.var 0) (.word literal)) (.word literal :: environment), k, initialStore⟩
                  ⟨.ret (.bool true), k, initialStore⟩ :=
                CostStepComposition.binary (.cons (.var rfl) .refl) (.cons .word .refl) (by simp [Core.BinaryOp.apply])
              have costEq : 5 + branchCost + 2 = branchCost + 7 * 1 := by omega
              rw [← costEq]
              exact CostStepComposition.ifTrue (guard _) (branches ⟨arm, some literal, branchCore⟩ (by simp) rfl continuation)
          | miss meaning different tail =>
              have equal := meaning.value_unique pattern
              subst_vars
              rename_i word literal tests
              have guard (k) : Core.Steps 5
                  ⟨.eval (.binary .wordEq (.var 0) (.word literal)) (.word word :: environment), k, initialStore⟩
                  ⟨.ret (.bool false), k, initialStore⟩ :=
                CostStepComposition.binary (.cons (.var rfl) .refl) (.cons .word .refl) (by simp [Core.BinaryOp.apply, different])
              have restPath := ih (fun item member => patterns item (by simp [member])) tail
                (fun item member => branches item (by simp [member])) fallback tailLowered
              have costEq : 5 + (branchCost + 7 * tests) + 2 = branchCost + 7 * (tests + 1) := by omega
              rw [← costEq]
              exact CostStepComposition.ifFalse (guard _) restPath

theorem ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    {F : Core.Expr → Prop}
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    (childSteps : ∀ {table context environment initialStore finalStore source value cost},
      ChildCost table environment initialStore source value finalStore cost →
      ∀ {core type}, ChildElab table context source core type → environment.ids = context.ids →
      ∀ continuation, Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction elaboration generalizing environment initialStore finalStore value cost continuation with
  | bare => cases evaluation; exact .cons .unit .refl
  | expression child =>
      cases evaluation with
      | expression actual => exact childSteps actual child sameIds continuation
  | block _ ih =>
      cases evaluation with
      | block actual => exact ih actual sameIds continuation
  | @binding inputs _ _ _ _ _ _ _ _ _ _ _ _ child _ ih =>
      cases evaluation with
      | binding initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          apply CostStepComposition.letE (childSteps initializer child sameIds _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ _ _ _ _ _ _ _ _ child _ ih =>
      cases evaluation with
      | inferred initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          apply CostStepComposition.letE (childSteps initializer child sameIds _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | discard child tailElaboration ih =>
      cases evaluation with
      | discard expression tail =>
          rename_i middleStore discardedValue expressionCost tailCost
          exact CostStepComposition.letE (childSteps expression child sameIds _)
            (insert_zero_path (F := F) childPaths
              (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening tailElaboration) (ih tail sameIds []) discardedValue continuation)
  | conditional guard _ _ thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch =>
          exact CostStepComposition.ifTrue (childSteps condition guard sameIds _)
            (thenIH branch sameIds continuation)
      | ifFalse condition branch =>
          exact CostStepComposition.ifFalse (childSteps condition guard sameIds _)
            (elseIH branch sameIds continuation)
  | wordMatch scrutinee ordered patterns branches defaultOrdered fallback lowered branchIH defaultIH =>
      cases evaluation with
      | wordMatch initializer choice branch =>
          rw [← ordered, ← defaultOrdered] at choice
          have selectedPath := fold_path _ _ patterns choice
            (fun entry member selectedEq k => by
              have actual := branch
              rw [← selectedEq] at actual
              exact insert_zero_path (F := F) childPaths
                (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening (branches entry member))
                (branchIH entry member actual sameIds []) _ k)
            (fun entry member selectedEq k => by
              have actual := branch
              rw [← selectedEq] at actual
              exact insert_zero_path (F := F) childPaths
                (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening (fallback entry member))
                (defaultIH entry member actual sameIds []) _ k) lowered continuation
          have path := CostStepComposition.letE (childSteps initializer scrutinee sameIds _) selectedPath
          simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at path ⊢
          exact path

theorem ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    {F : Core.Expr → Prop}
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (childInserts : ∀ {core}, F core → ∀ leading suffix inserted {initialStore finalStore value},
      Core.Evaluates (leading ++ inserted :: suffix) initialStore (core.weakenAt leading.length) value finalStore ↔
        Core.Evaluates (leading ++ suffix) initialStore core value finalStore)
    (childExecution : ∀ {table context environment source core type},
      ChildElab table context source core type → environment.ids = context.ids →
      ∀ {initialStore finalStore value}, ChildEval table environment initialStore source value finalStore ↔
        Core.Evaluates environment.values initialStore core value finalStore)
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    (childSteps : ∀ {table context environment initialStore finalStore source value cost},
      ChildCost table environment initialStore source value finalStore cost →
      ∀ {core type}, ChildElab table context source core type → environment.ids = context.ids →
      ∀ continuation, Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    ComputationReturnTreeEvaluatesWithCost ChildCost owner inputs.names environment
      initialStore body value finalStore cost ↔
      Core.Steps cost (.initial core environment.values initialStore) (.final value finalStore) := by
  constructor
  · intro evaluation
    exact ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := F)
      childMembership childWeakening childPaths childSteps evaluation elaboration sameIds []
  · intro path
    have evaluation := (ComputationReturnTreeElaborates.evaluates_iff (F := F) (ChildElab := ChildElab) (ChildEval := ChildEval)
      childMembership childWeakening childInserts childExecution elaboration sameIds).mpr (Core.steps_from_initial_sound path)
    obtain ⟨actualCost, actual⟩ := (computationReturnTreeEvaluates_iff_exists_cost (ChildEval := ChildEval) (ChildCost := ChildCost) childCostIff).mp evaluation
    have sameCost := (path.final_unique (ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := F)
      childMembership childWeakening childPaths childSteps actual elaboration sameIds [])).1
    exact sameCost.symm ▸ actual

end Solcore.Frontend
