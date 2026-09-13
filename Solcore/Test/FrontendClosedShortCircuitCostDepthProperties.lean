import Solcore.Frontend.ClosedSourceEvaluation
import Solcore.Frontend.ClosedSourceEvaluator
import Solcore.Frontend.LocalExpressionCostExecutionProperties

/-! Independent counts for the same nested original AST.
Closed depth uses arbitrary RuntimeValue capture tails and whole raw stores.
Local cost uses separate arbitrary Core.Value tails and Core.Store; no relation
between those tails/stores, data-image bridge, runtime typing or NoDup is assumed.
The selected right is group (!(!ref r)): depth 4, Core transition cost 5.
Its group consumes closed depth but contributes no Core transition. Whole
selected depth/cost are 5/8; skipped depth/cost are 2/4. Core counts concern
successful machine transitions, not frontend traversal, gas or elapsed time.
Eleven independently supplied ranges remain in the original AST. -/

set_option autoImplicit false
namespace Tests.ClosedShortCircuitCostDepth
open Solcore Solcore.Frontend

private def reference (span nameSpan : Syntax.SourceSpan) (name : String) : Syntax.Expr :=
  ⟨span, .identifier ⟨nameSpan, name⟩⟩
private def rightSource (ranges : Fin 11 → Syntax.SourceSpan) (name : String) : Syntax.Expr :=
  ⟨ranges 4, .group ⟨ranges 5, .unary ⟨ranges 6, .logicalNot⟩
    ⟨ranges 7, .unary ⟨ranges 8, .logicalNot⟩ (reference (ranges 9) (ranges 10) name)⟩⟩⟩
private def source (ranges : Fin 11 → Syntax.SourceSpan)
    (leftName rightName : String) (isOr : Bool) : Syntax.Expr :=
  ⟨ranges 0, .binary (reference (ranges 2) (ranges 3) leftName)
    ⟨ranges 1, if isOr then .logicalOr else .logicalAnd⟩ (rightSource ranges rightName)⟩
private def names (owner : Resolved.DeclarationId) (leftName rightName : String)
    (tail : LocalNameTable) : LocalNameTable :=
  (leftName, ⟨owner, 1⟩) :: (rightName, ⟨owner, 0⟩) :: tail
private def rows {α : Type} (owner : Resolved.DeclarationId) (left right : α)
    (tail : Resolved.LocalScope α) : Resolved.LocalScope α :=
  (⟨owner, 1⟩, left) :: (⟨owner, 0⟩, right) :: tail
private theorem ids_ne (owner : Resolved.DeclarationId) :
    (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by
  intro equal
  have impossible := congrArg Resolved.LocalId.binderIndex equal
  cases impossible
private def resolved (owner : Resolved.DeclarationId) (isOr : Bool) : Resolved.Expr :=
  let right := Resolved.Expr.unary .boolNot (.unary .boolNot (.var ⟨owner, 0⟩))
  if isOr then .ifE (.var ⟨owner, 1⟩) (.bool true) right
  else .ifE (.var ⟨owner, 1⟩) right (.bool false)
private def core (isOr : Bool) : Core.Expr :=
  let right := Core.Expr.unary .boolNot (.unary .boolNot (.var 1))
  if isOr then .ifE (.var 0) (.bool true) right
  else .ifE (.var 0) right (.bool false)

private theorem whole_resolution (owner : Resolved.DeclarationId)
    (ranges : Fin 11 → Syntax.SourceSpan) (leftName rightName : String)
    (different : leftName ≠ rightName) (nameTail : LocalNameTable) (isOr : Bool) :
    ResolvesLocalExpression (names owner leftName rightName nameTail)
      (source ranges leftName rightName isOr) (resolved owner isOr) := by
  cases isOr
  · exact .logicalAnd (.identifier .head)
      (.group (.logicalNot (.logicalNot (.identifier (.tail different .head)))))
  · exact .logicalOr (.identifier .head)
      (.group (.logicalNot (.logicalNot (.identifier (.tail different .head)))))

private theorem whole_lowered (owner : Resolved.DeclarationId) (isOr : Bool)
    (left right : Core.Value) (tail : Resolved.Environment) :
    Resolved.Lowers (Resolved.LocalScope.ids (rows owner left right tail))
      (resolved owner isOr) (core isOr) := by
  cases isOr
  · exact .ifE (.var .head) (.unary (.unary (.var (.tail (ids_ne owner) .head)))) .bool
  · exact .ifE (.var .head) .bool (.unary (.unary (.var (.tail (ids_ne owner) .head))))

private theorem closed_right (owner : Resolved.DeclarationId)
    (ranges : Fin 11 → Syntax.SourceSpan) (leftName rightName : String)
    (different : leftName ≠ rightName) (nameTail : LocalNameTable)
    (left right : Bool) (tail : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) :
    ClosedSourceExpressionEvaluates owner (names owner leftName rightName nameTail)
      (rows owner (.bool left) (.bool right) tail) store
      (rightSource ranges rightName) (.bool right) store := by
  have leaf : ClosedSourceExpressionEvaluates owner (names owner leftName rightName nameTail)
      (rows owner (.bool left) (.bool right) tail) store
      (reference (ranges 9) (ranges 10) rightName) (.bool right) store :=
    .reference (.tail different .head) (.tail (ids_ne owner) .head)
  simpa only [rightSource, Bool.not_not] using ClosedSourceExpressionEvaluates.group (span := ranges 4)
    (ClosedSourceExpressionEvaluates.logicalNot (span := ranges 5) (operatorSpan := ranges 6)
      (ClosedSourceExpressionEvaluates.logicalNot (span := ranges 7) (operatorSpan := ranges 8) leaf))

/-- No right-name lookup or right evaluation is needed for the closed skip.
This raw-store theorem is not a theorem about Core environments or costs. -/
theorem skipped_closed_original_and_exact_depth (owner : Resolved.DeclarationId)
    (ranges : Fin 11 → Syntax.SourceSpan) (leftName rightName : String)
    (nameTail : LocalNameTable) (isOr right : Bool)
    (captureTail : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) :
    ClosedSourceExpressionEvaluates owner (names owner leftName rightName nameTail)
      (rows owner (.bool isOr) (.bool right) captureTail) store
      (source ranges leftName rightName isOr) (.bool isOr) store ∧
    ∀ budget, evaluateClosedSourceExpression? budget owner
      (names owner leftName rightName nameTail)
      (rows owner (.bool isOr) (.bool right) captureTail) store
      (source ranges leftName rightName isOr) =
        if 2 ≤ budget then some (.bool isOr, store) else none := by
  constructor
  · cases isOr
    · exact .andFalse (.reference .head .head)
    · exact .orTrue (.reference .head .head)
  · intro budget
    by_cases enough : 2 ≤ budget
    · have split : budget = (budget - 2) + 2 := by omega
      rw [split]
      cases isOr <;> simp [source, reference, names, rows, evaluateClosedSourceExpression?,
        LocalNameTable.lookup?, Resolved.LocalScope.lookup?]
    · have small : budget = 0 ∨ budget = 1 := by omega
      rcases small with rfl | rfl
      all_goals cases isOr <;> simp [source, reference, evaluateClosedSourceExpression?]

/-- The selected raw right is independently derived before the budget formula.
All five insufficient budgets fail, and every larger budget has the same endpoint. -/
theorem selected_closed_original_and_exact_depth (owner : Resolved.DeclarationId)
    (ranges : Fin 11 → Syntax.SourceSpan) (leftName rightName : String)
    (different : leftName ≠ rightName) (nameTail : LocalNameTable) (isOr right : Bool)
    (captureTail : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) :
    ClosedSourceExpressionEvaluates owner (names owner leftName rightName nameTail)
      (rows owner (.bool (!isOr)) (.bool right) captureTail) store
      (source ranges leftName rightName isOr) (.bool right) store ∧
    ∀ budget, evaluateClosedSourceExpression? budget owner
      (names owner leftName rightName nameTail)
      (rows owner (.bool (!isOr)) (.bool right) captureTail) store
      (source ranges leftName rightName isOr) =
        if 5 ≤ budget then some (.bool right, store) else none := by
  have originalRight := closed_right owner ranges leftName rightName different
    nameTail (!isOr) right captureTail store
  constructor
  · cases isOr
    · exact .andTrue (.reference .head .head) originalRight
    · exact .orFalse (.reference .head .head) originalRight
  · intro budget
    by_cases enough : 5 ≤ budget
    · have split : budget = (budget - 5) + 5 := by omega
      rw [split]
      cases isOr <;> cases right <;>
        simp [source, rightSource, reference, names, rows, evaluateClosedSourceExpression?,
          LocalNameTable.lookup?, Resolved.LocalScope.lookup?, different]
    · have small : budget = 0 ∨ budget = 1 ∨ budget = 2 ∨ budget = 3 ∨ budget = 4 := by omega
      rcases small with rfl | rfl | rfl | rfl | rfl
      all_goals cases isOr <;> cases right <;>
        simp [source, rightSource, reference, names, rows, evaluateClosedSourceExpression?,
          LocalNameTable.lookup?, Resolved.LocalScope.lookup?]

private theorem local_right_cost (owner : Resolved.DeclarationId)
    (ranges : Fin 11 → Syntax.SourceSpan) (leftName rightName : String)
    (different : leftName ≠ rightName) (nameTail : LocalNameTable)
    (left right : Bool) (tail : Resolved.Environment) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (names owner leftName rightName nameTail)
      (rows owner (.bool left) (.bool right) tail) store
      (rightSource ranges rightName) (.bool right) store 5 := by
  have leaf : LocalExpressionEvaluatesWithCost (names owner leftName rightName nameTail)
      (rows owner (.bool left) (.bool right) tail) store
      (reference (ranges 9) (ranges 10) rightName) (.bool right) store 1 :=
    .identifier (.tail different .head) (.tail (ids_ne owner) .head)
  simpa only [rightSource, Bool.not_not] using LocalExpressionEvaluatesWithCost.group (span := ranges 4)
    (LocalExpressionEvaluatesWithCost.logicalNot (span := ranges 5) (operatorSpan := ranges 6)
      (LocalExpressionEvaluatesWithCost.logicalNot (span := ranges 7) (operatorSpan := ranges 8) leaf))

/-- Independent Core-valued source cost, actual resolution and identity-order
lowering. The skipped right still resolves for the whole lowering. No closed
RuntimeValue evaluation is used to infer this cost or the machine path. -/
theorem skipped_local_cost_and_core_steps (owner : Resolved.DeclarationId)
    (ranges : Fin 11 → Syntax.SourceSpan) (leftName rightName : String)
    (different : leftName ≠ rightName) (nameTail : LocalNameTable) (isOr right : Bool)
    (environmentTail : Resolved.Environment) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (names owner leftName rightName nameTail)
      (rows owner (.bool isOr) (.bool right) environmentTail) store
      (source ranges leftName rightName isOr) (.bool isOr) store 4 ∧
    (∀ continuation, Core.Steps 4
      ⟨.eval (core isOr) (Resolved.LocalScope.values
        (rows owner (.bool isOr) (.bool right) environmentTail)), continuation, store⟩
      ⟨.ret (.bool isOr), continuation, store⟩) ∧
    ∀ fuel, Core.runStateful fuel (Core.State.initial (core isOr)
      (Resolved.LocalScope.values (rows owner (.bool isOr) (.bool right) environmentTail)) store) =
        .done (.bool isOr) store ↔ 4 ≤ fuel := by
  have costed : LocalExpressionEvaluatesWithCost (names owner leftName rightName nameTail)
      (rows owner (.bool isOr) (.bool right) environmentTail) store
      (source ranges leftName rightName isOr) (.bool isOr) store 4 := by
    cases isOr
    · exact .andFalse (.identifier .head .head)
    · exact .orTrue (.identifier .head .head)
  have resolution := whole_resolution owner ranges leftName rightName different nameTail isOr
  have lowering := whole_lowered owner isOr (.bool isOr) (.bool right) environmentTail
  exact ⟨costed, costed.toStepsWithContinuation resolution lowering,
    fun _ => costed.runStateful_done_iff resolution lowering⟩

/-- Independently costed selected source: left cost 1 plus right cost 5 plus
two conditional transitions. These eight transitions are not five depth units. -/
theorem selected_local_cost_and_core_steps (owner : Resolved.DeclarationId)
    (ranges : Fin 11 → Syntax.SourceSpan) (leftName rightName : String)
    (different : leftName ≠ rightName) (nameTail : LocalNameTable) (isOr right : Bool)
    (environmentTail : Resolved.Environment) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (names owner leftName rightName nameTail)
      (rows owner (.bool (!isOr)) (.bool right) environmentTail) store
      (source ranges leftName rightName isOr) (.bool right) store 8 ∧
    (∀ continuation, Core.Steps 8
      ⟨.eval (core isOr) (Resolved.LocalScope.values
        (rows owner (.bool (!isOr)) (.bool right) environmentTail)), continuation, store⟩
      ⟨.ret (.bool right), continuation, store⟩) ∧
    ∀ fuel, Core.runStateful fuel (Core.State.initial (core isOr)
      (Resolved.LocalScope.values (rows owner (.bool (!isOr)) (.bool right) environmentTail)) store) =
        .done (.bool right) store ↔ 8 ≤ fuel := by
  have originalRight := local_right_cost owner ranges leftName rightName different
    nameTail (!isOr) right environmentTail store
  have originalLeft : LocalExpressionEvaluatesWithCost (names owner leftName rightName nameTail)
      (rows owner (.bool (!isOr)) (.bool right) environmentTail) store
      (reference (ranges 2) (ranges 3) leftName) (.bool (!isOr)) store 1 :=
    .identifier .head .head
  have costed : LocalExpressionEvaluatesWithCost (names owner leftName rightName nameTail)
      (rows owner (.bool (!isOr)) (.bool right) environmentTail) store
      (source ranges leftName rightName isOr) (.bool right) store 8 := by
    cases isOr
    · exact .andTrue originalLeft originalRight
    · exact .orFalse originalLeft originalRight
  have resolution := whole_resolution owner ranges leftName rightName different nameTail isOr
  have lowering := whole_lowered owner isOr (.bool (!isOr)) (.bool right) environmentTail
  exact ⟨costed, costed.toStepsWithContinuation resolution lowering,
    fun _ => costed.runStateful_done_iff resolution lowering⟩

end Tests.ClosedShortCircuitCostDepth
