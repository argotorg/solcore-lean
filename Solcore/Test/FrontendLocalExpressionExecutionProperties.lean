import Solcore.Frontend.LocalExpressionExecutionProperties

/-! Open typed conditional execution, opaque values, and the identity-order boundary. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def localId (index : Nat) : Resolved.LocalId :=
  ⟨⟨⟨.main, ⟨[⟨"Execution", by decide⟩], by decide⟩⟩, 0⟩, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "execution.sol"⟩, 0, 1⟩
private def name (text : String) : Syntax.Expr := ⟨span, .identifier ⟨span, text⟩⟩
private def source : Syntax.Expr := ⟨span, .conditional (name "c") span (name "l") span (name "r")⟩
private def names : LocalNameTable := [("c", localId 0), ("l", localId 1), ("r", localId 2)]
private def context (type : Core.Ty) : Resolved.Context :=
  [(localId 0, .bool), (localId 1, type), (localId 2, type)]
private def environment (decision : Bool) (left right : Core.Value) : Resolved.Environment :=
  [(localId 0, .bool decision), (localId 1, left), (localId 2, right)]
private def core : Core.Expr := .ifE (.var 0) (.var 1) (.var 2)

private theorem checked (type : Core.Ty) :
    elaborateLocalExpression? names (context type) source = some (core, type) := by
  apply elaborateLocalExpression?_complete
    (resolved := .ifE (.var (localId 0)) (.var (localId 1)) (.var (localId 2)))
  · exact .conditional (.identifier .head) (.identifier (.tail (by decide) .head))
      (.identifier (.tail (by decide) (.tail (by decide) .head)))
  · exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by change localId 1 ≠ localId 2; decide) .head)))
  · exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by decide) .head)))

private theorem environmentTyped (decision : Bool) {left right : Core.Value} {type : Core.Ty}
    (leftTyped : Core.ValueHasType left type) (rightTyped : Core.ValueHasType right type) :
    Core.EnvironmentHasTypes (Resolved.LocalScope.values (environment decision left right))
      (Resolved.LocalScope.values (context type)) :=
  .cons .bool (.cons leftTyped (.cons rightTyped .nil))

theorem localConditional_typed_execution (decision : Bool) {left right : Core.Value} {type : Core.Ty}
    (leftTyped : Core.ValueHasType left type) (rightTyped : Core.ValueHasType right type)
    (store : Core.Store) :
    ∃ value required, LocalExpressionEvaluates names (environment decision left right) store source value store ∧
      Core.ValueHasType value type ∧ ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (Core.State.initial core
          (Resolved.LocalScope.values (environment decision left right)) store) = .done value store :=
  elaborateLocalExpression?_typed_execution (checked type) rfl
    (environmentTyped decision leftTyped rightTyped) store

theorem localConditional_evaluation_iff (decision : Bool) (left right value : Core.Value)
    (type : Core.Ty) (initialStore finalStore : Core.Store) :
    LocalExpressionEvaluates names (environment decision left right) initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values (environment decision left right))
        initialStore core value finalStore :=
  elaborateLocalExpression?_evaluates_iff (checked type) rfl

theorem localConditional_never_faults (decision : Bool) {left right : Core.Value} {type : Core.Ty}
    (leftTyped : Core.ValueHasType left type) (rightTyped : Core.ValueHasType right type)
    (store : Core.Store) (fuel : Nat) (error : Core.MachineFault) (faultState : Core.State) :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values (environment decision left right)) store) ≠ .fault error faultState :=
  elaborateLocalExpression?_run_never_faults (checked type) rfl
    (environmentTyped decision leftTyped rightTyped) store fuel error faultState

/-- Merely returning a cell reference needs no valid location or typed store. -/
theorem localConditional_opaque_cell (location : Nat) (store : Core.Store) :
    ∃ required, ∀ fuel, required ≤ fuel → Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values
        (environment true (.cellRef .word location) (.cellRef .word (location + 1)))) store) =
      .done (.cellRef .word location) store := by
  obtain ⟨value, required, evaluation, _, enough⟩ :=
    localConditional_typed_execution true (left := .cellRef .word location)
      (right := .cellRef .word (location + 1)) Core.ValueHasType.cellRef Core.ValueHasType.cellRef store
  have expected : LocalExpressionEvaluates names
      (environment true (.cellRef .word location) (.cellRef .word (location + 1)))
      store source (.cellRef .word location) store :=
    .ifTrue (.identifier .head .head)
      (.identifier (.tail (by decide) .head) (.tail (by decide) .head))
  obtain ⟨rfl, _⟩ := evaluation.deterministic expected
  exact ⟨required, enough⟩

private def reordered : Resolved.Environment :=
  [(localId 1, .bool false), (localId 0, .bool true), (localId 2, .bool true)]

/-- Positional Boolean typing survives this reorder, but the compiled condition reads another ID. -/
theorem localConditional_identity_order_required (store : Core.Store) :
    Core.EnvironmentHasTypes (Resolved.LocalScope.values reordered) (Resolved.LocalScope.values (context .bool)) ∧
    Resolved.LocalScope.ids reordered ≠ Resolved.LocalScope.ids (context .bool) ∧
    LocalExpressionEvaluates names reordered store source (.bool false) store ∧
    Core.runStateful 4 (Core.State.initial core (Resolved.LocalScope.values reordered) store) =
      .done (.bool true) store := by
  refine ⟨.cons .bool (.cons .bool (.cons .bool .nil)), by decide, ?_, rfl⟩
  exact .ifTrue (.identifier .head (.tail (by decide) .head))
    (.identifier (.tail (by decide) .head) .head)

end Tests
