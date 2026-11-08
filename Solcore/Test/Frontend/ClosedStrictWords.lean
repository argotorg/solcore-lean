import Solcore.Frontend.Fragments.Internal.ClosedSource
import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Frontend.Fragments.Internal.Foundations
import Solcore.Syntax.Parser.Internal.TermBasics

/-!
# Closed strict word tests

Closed strict word operators and short circuits: depth, cost, saved calls and negative results.
-/

section
-- leanmerge: from Solcore.Test.FrontendClosedShortCircuitCostDepthProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendClosedShortCircuitDepthProperties
/- Exact-depth composition. The selected right operand starts from
the actual left endpoint; skipped operands have no depth or execution premise. -/
set_option autoImplicit false
open Solcore Frontend
namespace Tests.ClosedShortCircuitDepth

variable {owner : Resolved.DeclarationId} {names : LocalNameTable}
  {captured : Resolved.LocalScope RuntimeValue}
  {initialStore middleStore finalStore : List RuntimeValue}
  {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
  {value : RuntimeValue} {leftDepth rightDepth : Nat}

theorem skipped_and_exact_depth
    (leftCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured initialStore left =
        if leftDepth ≤ n then some (.bool false, finalStore) else none) :
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ =
        if leftDepth + 1 ≤ budget then some (.bool false, finalStore) else none := by
  intro budget
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
      rw [evaluateClosedSourceExpression?_logicalAnd, leftCutoff]
      by_cases enough : leftDepth ≤ n
      · rw [if_pos enough, if_pos (show leftDepth + 1 ≤ n + 1 by omega)]
        rfl
      · rw [if_neg enough, if_neg (show ¬ leftDepth + 1 ≤ n + 1 by omega)]
        rfl

theorem skipped_or_exact_depth
    (leftCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured initialStore left =
        if leftDepth ≤ n then some (.bool true, finalStore) else none) :
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ =
        if leftDepth + 1 ≤ budget then some (.bool true, finalStore) else none := by
  intro budget
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
      rw [evaluateClosedSourceExpression?_logicalOr, leftCutoff]
      by_cases enough : leftDepth ≤ n
      · rw [if_pos enough, if_pos (show leftDepth + 1 ≤ n + 1 by omega)]
        rfl
      · rw [if_neg enough, if_neg (show ¬ leftDepth + 1 ≤ n + 1 by omega)]
        rfl

theorem selected_and_exact_depth
    (leftCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured initialStore left =
        if leftDepth ≤ n then some (.bool true, middleStore) else none)
    (rightCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured middleStore right =
        if rightDepth ≤ n then some (value, finalStore) else none) :
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ =
        if max leftDepth rightDepth + 1 ≤ budget then some (value, finalStore) else none := by
  intro budget
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
      rw [evaluateClosedSourceExpression?_logicalAnd, leftCutoff]
      by_cases leftEnough : leftDepth ≤ n
      · rw [if_pos leftEnough]
        change evaluateClosedSourceExpression? n owner names captured middleStore right = _
        rw [rightCutoff]
        by_cases rightEnough : rightDepth ≤ n
        · rw [if_pos rightEnough, if_pos (show max leftDepth rightDepth + 1 ≤ n + 1 from
            Nat.succ_le_succ (Nat.max_le.mpr ⟨leftEnough, rightEnough⟩))]
        · have insufficient : ¬ max leftDepth rightDepth + 1 ≤ n + 1 := by
            intro enough
            exact rightEnough (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_succ_le_succ enough))
          rw [if_neg rightEnough, if_neg insufficient]
      · have insufficient : ¬ max leftDepth rightDepth + 1 ≤ n + 1 := by
          intro enough
          exact leftEnough (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_succ_le_succ enough))
        rw [if_neg leftEnough, if_neg insufficient]
        rfl

theorem selected_or_exact_depth
    (leftCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured initialStore left =
        if leftDepth ≤ n then some (.bool false, middleStore) else none)
    (rightCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured middleStore right =
        if rightDepth ≤ n then some (value, finalStore) else none) :
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ =
        if max leftDepth rightDepth + 1 ≤ budget then some (value, finalStore) else none := by
  intro budget
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
      rw [evaluateClosedSourceExpression?_logicalOr, leftCutoff]
      by_cases leftEnough : leftDepth ≤ n
      · rw [if_pos leftEnough]
        change evaluateClosedSourceExpression? n owner names captured middleStore right = _
        rw [rightCutoff]
        by_cases rightEnough : rightDepth ≤ n
        · rw [if_pos rightEnough, if_pos (show max leftDepth rightDepth + 1 ≤ n + 1 from
            Nat.succ_le_succ (Nat.max_le.mpr ⟨leftEnough, rightEnough⟩))]
        · have insufficient : ¬ max leftDepth rightDepth + 1 ≤ n + 1 := by
            intro enough
            exact rightEnough (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_succ_le_succ enough))
          rw [if_neg rightEnough, if_neg insufficient]
      · have insufficient : ¬ max leftDepth rightDepth + 1 ≤ n + 1 := by
          intro enough
          exact leftEnough (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_succ_le_succ enough))
        rw [if_neg leftEnough, if_neg insufficient]
        rfl

end Tests.ClosedShortCircuitDepth
end

section
-- leanmerge: from Solcore.Test.FrontendClosedShortCircuitMissingRightProperties
/- Original-syntax consumers. Missing lookup is excluded before any
whole-expression argument. Successful skipped witnesses precede iff conversion;
selected impossibility precedes the all-budget consequence from soundness.
Opaque capture tails, foreign or repeated IDs and full stores are unrestricted.
No whole-expression checking, parser, Core-cost or canonical-runtime claim. -/
set_option autoImplicit false
open Solcore Solcore.Frontend

namespace Tests.ClosedShortCircuitMissingRight

private theorem missing_lookup_is_impossible (id target : Resolved.LocalId) :
    ¬ LocalNameTable.Lookup [("guard", id)] "missing" target := by
  intro found
  have pairEq : ("missing", target) = ("guard", id) := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using found.mem
  exact (by decide : ("missing" : String) ≠ "guard") (Prod.mk.inj pairEq).1

variable {owner : Resolved.DeclarationId} {id : Resolved.LocalId}
  {captured : Resolved.LocalScope RuntimeValue} {store : List RuntimeValue}
  {span operatorSpan guardSpan guardNameSpan missingSpan missingNameSpan : Syntax.SourceSpan}
  {unitSpan tupleSpan : Syntax.SourceSpan}

/-- The missing reference has no endpoint at any complete input store. -/
theorem missing_reference_has_no_success :
    ∀ value finalStore,
      ¬ ClosedSourceExpressionEvaluates owner [("guard", id)] captured store
        ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩ value finalStore := by
  intro value finalStore evaluated
  cases evaluated with
  | reference named _ => exact missing_lookup_is_impossible id _ named
  | creation shape => cases shape

/-- A missing right operand has no premise in either independently built skip. -/
theorem missing_right_skip_successes :
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool false) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalAnd⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
      (.bool false) store ∧
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool true) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalOr⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
      (.bool true) store := by
  have leftFalse : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool false) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool false) store :=
    .reference .head .head
  have leftTrue : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool true) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool true) store :=
    .reference .head .head
  have originalAnd : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool false) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalAnd⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
      (.bool false) store := .andFalse leftFalse
  have originalOr : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool true) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalOr⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
      (.bool true) store := .orTrue leftTrue
  have decomposedAnd := closedSourceExpressionEvaluates_logicalAnd_iff.mp originalAnd
  have decomposedOr := closedSourceExpressionEvaluates_logicalOr_iff.mp originalOr
  exact ⟨closedSourceExpressionEvaluates_logicalAnd_iff.mpr decomposedAnd,
    closedSourceExpressionEvaluates_logicalOr_iff.mpr decomposedOr⟩

/-- Selecting the missing right excludes all values and all complete final stores. -/
theorem missing_right_selected_has_no_success :
    ∀ value finalStore,
      (¬ ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool true) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalAnd⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
        value finalStore) ∧
      (¬ ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool false) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalOr⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
        value finalStore) := by
  have leftTrue : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool true) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool true) store :=
    .reference .head .head
  have leftFalse : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool false) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool false) store :=
    .reference .head .head
  intro value finalStore
  constructor
  · intro evaluated
    rcases closedSourceExpressionEvaluates_logicalAnd_iff.mp evaluated with
      ⟨_, forcedLeft⟩ | ⟨middleStore, _, forcedRight⟩
    · cases (leftTrue.deterministic forcedLeft).1
    · exact missing_reference_has_no_success value finalStore forcedRight
  · intro evaluated
    rcases closedSourceExpressionEvaluates_logicalOr_iff.mp evaluated with
      ⟨_, forcedLeft⟩ | ⟨middleStore, _, forcedRight⟩
    · cases (leftFalse.deterministic forcedLeft).1
    · exact missing_reference_has_no_success value finalStore forcedRight

/-- Rejection at every budget is a consequence of the preceding semantic exclusion. -/
theorem missing_right_selected_none_at_every_depth :
    ∀ budget,
      evaluateClosedSourceExpression? budget owner [("guard", id)] ((id, .bool true) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalAnd⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩ = none ∧
      evaluateClosedSourceExpression? budget owner [("guard", id)] ((id, .bool false) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalOr⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩ = none := by
  intro budget
  constructor
  · cases accepted : evaluateClosedSourceExpression? budget owner [("guard", id)]
        ((id, .bool true) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalAnd⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩ with
    | none => rfl
    | some endpoint =>
        rcases endpoint with ⟨value, finalStore⟩
        exact False.elim
          ((missing_right_selected_has_no_success value finalStore).1
            (evaluateClosedSourceExpression?_sound accepted))
  · cases accepted : evaluateClosedSourceExpression? budget owner [("guard", id)]
        ((id, .bool false) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalOr⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩ with
    | none => rfl
    | some endpoint =>
        rcases endpoint with ⟨value, finalStore⟩
        exact False.elim
          ((missing_right_selected_has_no_success value finalStore).2
            (evaluateClosedSourceExpression?_sound accepted))

/-- The available empty-tuple right gives four direct original-rule witnesses.
The selected result is unit, not a claim of Boolean whole-expression typing. -/
theorem unit_right_has_all_four_original_witnesses :
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool false) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalAnd⟩ ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩⟩ (.bool false) store ∧
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool true) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalAnd⟩ ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩⟩ .unit store ∧
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool true) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalOr⟩ ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩⟩ (.bool true) store ∧
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool false) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalOr⟩ ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩⟩ .unit store := by
  have leftFalse : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool false) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool false) store :=
    .reference .head .head
  have leftTrue : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool true) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool true) store :=
    .reference .head .head
  have rightFalse : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool false) :: captured) store ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩ .unit store := .unit
  have rightTrue : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool true) :: captured) store ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩ .unit store := .unit
  exact ⟨.andFalse leftFalse, .andTrue leftTrue rightTrue,
    .orTrue leftTrue, .orFalse leftFalse rightFalse⟩

end Tests.ClosedShortCircuitMissingRight
end

section
-- leanmerge: from Solcore.Test.FrontendClosedShortCircuitNegativeProperties
/- Semantic negative consumers. A successful non-Bool left witness
excludes every whole-expression endpoint before soundness is used for all depths.
Right syntax, lexical inputs and complete stores have no additional restrictions.
This includes every non-Bool RuntimeValue, including arbitrary source closures.
No typing, projection, termination, exact-depth or canonical-runtime claim. -/
set_option autoImplicit false
open Solcore Solcore.Frontend

namespace Tests.ClosedShortCircuitNegative

/-- A non-Bool left result excludes every conjunction value and final store. -/
theorem logicalAnd_nonBool_left_has_no_success
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore leftStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {leftValue : RuntimeValue}
    (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
      initialStore left leftValue leftStore)
    (notBool : ∀ b : Bool, leftValue ≠ .bool b) :
    ∀ value finalStore,
      ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ value finalStore := by
  intro value finalStore evaluated
  rcases closedSourceExpressionEvaluates_logicalAnd_iff.mp evaluated with
    ⟨_, forcedLeft⟩ | ⟨middleStore, forcedLeft, _⟩
  · exact notBool false (leftEvaluation.deterministic forcedLeft).1
  · exact notBool true (leftEvaluation.deterministic forcedLeft).1

/-- A non-Bool left result excludes every disjunction value and final store. -/
theorem logicalOr_nonBool_left_has_no_success
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore leftStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {leftValue : RuntimeValue}
    (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
      initialStore left leftValue leftStore)
    (notBool : ∀ b : Bool, leftValue ≠ .bool b) :
    ∀ value finalStore,
      ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ value finalStore := by
  intro value finalStore evaluated
  rcases closedSourceExpressionEvaluates_logicalOr_iff.mp evaluated with
    ⟨_, forcedLeft⟩ | ⟨middleStore, forcedLeft, _⟩
  · exact notBool true (leftEvaluation.deterministic forcedLeft).1
  · exact notBool false (leftEvaluation.deterministic forcedLeft).1

/-- Every-depth rejection follows from semantic impossibility, not one failed run. -/
theorem logicalAnd_nonBool_left_none_at_every_depth
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore leftStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {leftValue : RuntimeValue}
    (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
      initialStore left leftValue leftStore)
    (notBool : ∀ b : Bool, leftValue ≠ .bool b) :
    ∀ budget,
      evaluateClosedSourceExpression? budget owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ = none := by
  intro budget
  cases accepted : evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ with
  | none => rfl
  | some endpoint =>
      rcases endpoint with ⟨value, finalStore⟩
      exact False.elim
        (logicalAnd_nonBool_left_has_no_success leftEvaluation notBool value finalStore
          (evaluateClosedSourceExpression?_sound accepted))

/-- Every-depth disjunction rejection uses the same all-endpoint source argument. -/
theorem logicalOr_nonBool_left_none_at_every_depth
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore leftStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {leftValue : RuntimeValue}
    (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
      initialStore left leftValue leftStore)
    (notBool : ∀ b : Bool, leftValue ≠ .bool b) :
    ∀ budget,
      evaluateClosedSourceExpression? budget owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ = none := by
  intro budget
  cases accepted : evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ with
  | none => rfl
  | some endpoint =>
      rcases endpoint with ⟨value, finalStore⟩
      exact False.elim
        (logicalOr_nonBool_left_has_no_success leftEvaluation notBool value finalStore
          (evaluateClosedSourceExpression?_sound accepted))

end Tests.ClosedShortCircuitNegative
end

section
-- leanmerge: from Solcore.Test.FrontendClosedShortCircuitSavedCallProperties
/- A selected lambda captures
the original saved rows; the actual returned closure and store are reused by a
foreign caller. The argument named p is evaluated in the caller, then the fresh
parameter p shadows the saved p. Capture tails and runtime payloads are arbitrary.
No typing, NoDup, Core correspondence, exact-depth or parser claim is made. -/
set_option autoImplicit false
open Solcore Solcore.Frontend
namespace Tests.ClosedShortCircuitSavedCall

private def ref (s : Nat → Syntax.SourceSpan) (i : Nat) (name : String) : Syntax.Expr :=
  ⟨s i, .identifier ⟨s (i + 1), name⟩⟩
private def selected (b : Bool) (s : Nat → Syntax.SourceSpan) (l r : Syntax.Expr) : Syntax.Expr :=
  ⟨s 0, .binary l ⟨s 1, if b then .logicalAnd else .logicalOr⟩ r⟩
private def skipped (b : Bool) (s : Nat → Syntax.SourceSpan) (l r : Syntax.Expr) : Syntax.Expr :=
  ⟨s 0, .binary l ⟨s 1, if b then .logicalOr else .logicalAnd⟩ r⟩
private def body (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 10, [⟨s 11, .returnStmt (some (ref s 12 "p"))⟩]⟩
private def original (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 4, .lambda (s 5) ⟨s 6, [⟨s 7, .inferred ⟨s 8, "p"⟩⟩]⟩ none (body s)⟩
private def call (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 14, .call (ref s 15 "picked") ⟨s 17, [ref s 18 "p"]⟩⟩
private def savedNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) : LocalNameTable :=
  ("guard", ⟨owner, 0⟩) :: ("p", ⟨owner, 2⟩) :: tail
private def savedCaptured (owner : Resolved.DeclarationId) (b : Bool) (old : RuntimeValue)
    (tail : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  (⟨owner, 0⟩, .bool b) :: (⟨owner, 2⟩, old) :: tail
private def callerNames (owner : Resolved.DeclarationId) : LocalNameTable :=
  [("guard", ⟨owner, 0⟩), ("picked", ⟨owner, 1⟩), ("p", ⟨owner, 2⟩)]
private def callerCaptured (owner : Resolved.DeclarationId) (b : Bool) (made argument : RuntimeValue)
    (tail : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  (⟨owner, 0⟩, .bool b) :: (⟨owner, 1⟩, made) :: (⟨owner, 2⟩, argument) :: tail

private theorem index_ne (owner : Resolved.DeclarationId) {i j : Nat} (different : i ≠ j) :
    (⟨owner, i⟩ : Resolved.LocalId) ≠ ⟨owner, j⟩ := by
  intro equal
  exact different (congrArg Resolved.LocalId.binderIndex equal)

private theorem endpoint {owner names captured store source value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured store source value finalStore) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store source actual final ↔
      actual = value ∧ final = finalStore := by
  intro actual final
  constructor
  · exact fun evaluated => evaluated.deterministic original
  · rintro ⟨rfl, rfl⟩
    exact original

private theorem selected_original {owner names captured store middle final left right value}
    (b : Bool) (s : Nat → Syntax.SourceSpan)
    (l : ClosedSourceExpressionEvaluates owner names captured store left (.bool b) middle)
    (r : ClosedSourceExpressionEvaluates owner names captured middle right value final) :
    ClosedSourceExpressionEvaluates owner names captured store (selected b s left right) value final := by
  cases b
  · exact .orFalse l r
  · exact .andTrue l r

private theorem skipped_original {owner names captured store final left right}
    (b : Bool) (s : Nat → Syntax.SourceSpan)
    (l : ClosedSourceExpressionEvaluates owner names captured store left (.bool b) final) :
    ClosedSourceExpressionEvaluates owner names captured store (skipped b s left right) (.bool b) final := by
  cases b
  · exact .andFalse l
  · exact .orTrue l

private theorem selected_iff {owner names captured store middle left right value final}
    (b : Bool) (s : Nat → Syntax.SourceSpan)
    (l : ClosedSourceExpressionEvaluates owner names captured store left (.bool b) middle) :
    ClosedSourceExpressionEvaluates owner names captured store (selected b s left right) value final ↔
      ClosedSourceExpressionEvaluates owner names captured middle right value final := by
  cases b
  · constructor
    · intro evaluated
      rcases closedSourceExpressionEvaluates_logicalOr_iff.mp evaluated with
        ⟨_, forced⟩ | ⟨actualMiddle, forced, child⟩
      · cases (l.deterministic forced).1
      · obtain ⟨_, sameStore⟩ := l.deterministic forced
        rw [← sameStore] at child
        exact child
    · intro child
      exact closedSourceExpressionEvaluates_logicalOr_iff.mpr (.inr ⟨middle, l, child⟩)
  · constructor
    · intro evaluated
      rcases closedSourceExpressionEvaluates_logicalAnd_iff.mp evaluated with
        ⟨_, forced⟩ | ⟨actualMiddle, forced, child⟩
      · cases (l.deterministic forced).1
      · obtain ⟨_, sameStore⟩ := l.deterministic forced
        rw [← sameStore] at child
        exact child
    · intro child
      exact closedSourceExpressionEvaluates_logicalAnd_iff.mpr (.inr ⟨middle, l, child⟩)

private theorem missing {owner captured store value final} (s : Nat → Syntax.SourceSpan) :
    ¬ ClosedSourceExpressionEvaluates owner (callerNames owner) captured store
      (ref s 20 "missing") value final := by
  intro evaluated
  cases evaluated with
  | creation shape => cases shape
  | reference named _ =>
      have impossible := LocalNameTable.lookup?_iff.mpr named
      simp [callerNames, LocalNameTable.lookup?] at impossible

theorem selected_returned_closure_shadow_call_and_all_actual_endpoints
    (s : Nat → Syntax.SourceSpan) (savedOwner callerOwner : Resolved.DeclarationId)
    (different : callerOwner ≠ savedOwner) (choice : Bool)
    (savedNameTail : LocalNameTable) (savedTail callerTail : Resolved.LocalScope RuntimeValue)
    (oldSavedP argument : RuntimeValue) (creationStore : List RuntimeValue) :
    let sn := savedNames savedOwner savedNameTail
    let sc := savedCaptured savedOwner choice oldSavedP savedTail
    let creation := selected choice s (ref s 2 "guard") (original s)
    let closure := RuntimeValue.sourceClosure (original s) savedOwner sn sc
    ClosedSourceExpressionEvaluates savedOwner sn sc creationStore creation closure creationStore ∧
    (∀ actual final, ClosedSourceExpressionEvaluates savedOwner sn sc creationStore creation actual final ↔
      actual = closure ∧ final = creationStore) ∧
    ∀ made madeStore, ClosedSourceExpressionEvaluates savedOwner sn sc creationStore creation made madeStore →
      let cn := callerNames callerOwner
      let cc := callerCaptured callerOwner (!choice) made argument callerTail
      let run := selected (!choice) s (ref s 2 "guard") (call s)
      let skip := skipped (!choice) s (ref s 2 "guard") (ref s 20 "missing")
      callerOwner ≠ savedOwner ∧ made = closure ∧ madeStore = creationStore ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore run argument madeStore ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore skip (.bool (!choice)) madeStore ∧
      (∀ actual final, ClosedSourceExpressionEvaluates callerOwner cn cc madeStore run actual final ↔
        actual = argument ∧ final = madeStore) ∧
      (∀ actual final, ClosedSourceExpressionEvaluates callerOwner cn cc madeStore skip actual final ↔
        actual = .bool (!choice) ∧ final = madeStore) ∧
      (∀ actual final, ¬ ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (ref s 20 "missing") actual final) ∧
      (∀ budget actual final,
        evaluateClosedSourceExpression? budget callerOwner cn cc madeStore run = some (actual, final) →
        actual = argument ∧ final = madeStore) ∧
      (∃ required, ∀ budget, required ≤ budget →
        evaluateClosedSourceExpression? budget callerOwner cn cc madeStore run = some (argument, madeStore)) := by
  dsimp only
  let sn := savedNames savedOwner savedNameTail
  let sc := savedCaptured savedOwner choice oldSavedP savedTail
  let closure := RuntimeValue.sourceClosure (original s) savedOwner sn sc
  have savedLeft : ClosedSourceExpressionEvaluates savedOwner sn sc creationStore
      (ref s 2 "guard") (.bool choice) creationStore := .reference .head .head
  have literalCreation : ClosedSourceExpressionEvaluates savedOwner sn sc creationStore
      (original s) closure creationStore := .creation .inferred
  have created := selected_original choice s savedLeft literalCreation
  have creationExact : ∀ actual final, ClosedSourceExpressionEvaluates savedOwner sn sc creationStore
      (selected choice s (ref s 2 "guard") (original s)) actual final ↔
      actual = closure ∧ final = creationStore := by
    intro actual final
    exact (selected_iff choice s savedLeft).trans (endpoint literalCreation actual final)
  refine ⟨created, creationExact, ?_⟩
  intro made madeStore returned
  obtain ⟨actualClosure, actualCreationStore⟩ := (creationExact made madeStore).mp returned
  let cn := callerNames callerOwner
  let cc := callerCaptured callerOwner (!choice) made argument callerTail
  let calleeStore := madeStore
  let argumentStore := calleeStore
  have callerLeft : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 2 "guard") (.bool (!choice)) madeStore := .reference .head .head
  have fetchedActual : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 15 "picked") made calleeStore :=
    .reference (.tail (by change "guard" ≠ "picked"; decide) .head)
      (.tail (index_ne callerOwner (by decide)) .head)
  have fetchedClosure : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 15 "picked") closure calleeStore := by
    rw [← actualClosure]
    exact fetchedActual
  have argumentEvaluation : ClosedSourceExpressionEvaluates callerOwner cn cc calleeStore
      (ref s 18 "p") argument argumentStore :=
    .reference (.tail (by change "guard" ≠ "p"; decide)
      (.tail (by change "picked" ≠ "p"; decide) .head))
      (.tail (index_ne callerOwner (by decide)) (.tail (index_ne callerOwner (by decide)) .head))
  let parameter := Resolved.freshLocalId savedOwner (sn.map Prod.snd)
  have bodyEvaluation : ClosedSourceBodyEvaluates savedOwner (("p", parameter) :: sn)
      ((parameter, argument) :: sc) argumentStore (body s) argument argumentStore :=
    .expression (.reference .head .head)
  have invoked : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore (call s) argument argumentStore :=
    .call (calleeStore := calleeStore) (argumentStore := argumentStore)
      .inferred fetchedClosure argumentEvaluation bodyEvaluation
  have selectedCall := selected_original (!choice) s callerLeft invoked
  have skippedMissing : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (skipped (!choice) s (ref s 2 "guard") (ref s 20 "missing")) (.bool (!choice)) madeStore :=
    skipped_original (!choice) s callerLeft
  have callExact : ∀ actual final, ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (selected (!choice) s (ref s 2 "guard") (call s)) actual final ↔
      actual = argument ∧ final = madeStore := by
    intro actual final
    exact (selected_iff (!choice) s callerLeft).trans (endpoint invoked actual final)
  refine ⟨different, actualClosure, actualCreationStore, selectedCall, skippedMissing,
    callExact, endpoint skippedMissing, ?_, ?_, ?_⟩
  · intro actual final
    exact missing s
  · intro budget actual final accepted
    exact (callExact actual final).mp (evaluateClosedSourceExpression?_sound accepted)
  · exact evaluateClosedSourceExpression?_eventually_complete selectedCall

end Tests.ClosedShortCircuitSavedCall
end

section
-- leanmerge: from Solcore.Test.FrontendClosedStrictWordBinaryCostProperties
/- Independent source cost for fourteen strict Word meanings. The two child
costs and all three stores are supplied separately; no closed runner, typing,
data-image bridge or whole-environment well-formedness is used. -/
set_option autoImplicit false
namespace Tests.ClosedStrictWordBinaryCost
open Solcore Solcore.Frontend

private def overhead : Syntax.BinaryOp → Nat
  | .notEqual | .lessEqual => 5
  | .less => 9
  | .greaterEqual => 11
  | _ => 3

private theorem costed {names environment initialStore middleStore finalStore}
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    {left right : Syntax.Expr} {a b : Core.Word} {value : Core.Value} {kl kr : Nat}
    (meaning : StrictWordBinaryDenotes operator a b value)
    (l : LocalExpressionEvaluatesWithCost names environment initialStore left (.word a) middleStore kl)
    (r : LocalExpressionEvaluatesWithCost names environment middleStore right (.word b) finalStore kr) :
    LocalExpressionEvaluatesWithCost names environment initialStore
      ⟨span,.binary left ⟨operatorSpan,operator⟩ right⟩ value finalStore (kl+kr+overhead operator) := by
  cases meaning with
  | add => exact .add l r
  | subtract => exact .subtract l r
  | multiply => exact .multiply l r
  | divide => exact .divide l r
  | modulo => exact .modulo l r
  | bitAnd => exact .bitAnd l r
  | bitOr => exact .bitOr l r
  | bitXor => exact .bitXor l r
  | greater => exact .greater l r
  | less => exact .less l r
  | equal => exact .equal l r
  | notEqual => exact .notEqual l r
  | lessEqual => exact .lessEqual l r
  | greaterEqual => exact .greaterEqual l r

/-- The direct ten add three transitions, != and <= add five, < adds nine,
and >= adds eleven. These are Core transitions, not source derivation depth.
Original independent costs precede any resolution/lowering or machine path. -/
theorem original_cost_and_machine_steps {names environment initialStore middleStore finalStore}
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    {left right : Syntax.Expr} {a b : Core.Word} {value : Core.Value} {kl kr : Nat}
    (meaning : StrictWordBinaryDenotes operator a b value)
    (l : LocalExpressionEvaluatesWithCost names environment initialStore left (.word a) middleStore kl)
    (r : LocalExpressionEvaluatesWithCost names environment middleStore right (.word b) finalStore kr) :
    LocalExpressionEvaluatesWithCost names environment initialStore
      ⟨span,.binary left ⟨operatorSpan,operator⟩ right⟩ value finalStore (kl+kr+overhead operator) ∧
    ∀ {resolved core},
      ResolvesLocalExpression names ⟨span,.binary left ⟨operatorSpan,operator⟩ right⟩ resolved →
      Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core →
      (∀ continuation, Core.Steps (kl+kr+overhead operator)
        ⟨.eval core (Resolved.LocalScope.values environment),continuation,initialStore⟩
        ⟨.ret value,continuation,finalStore⟩) ∧
      ∀ fuel, Core.runStateful fuel
        (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
          .done value finalStore ↔ kl+kr+overhead operator ≤ fuel := by
  have original := costed (span:=span) (operatorSpan:=operatorSpan) meaning l r
  refine ⟨original,?_⟩
  intro resolved core resolution lowering
  exact ⟨original.toStepsWithContinuation resolution lowering,
    fun _ => original.runStateful_done_iff resolution lowering⟩

end Tests.ClosedStrictWordBinaryCost
end

section
-- leanmerge: from Solcore.Test.FrontendClosedStrictWordBinaryNegativeProperties
/- Independent child witnesses precede semantic rejection of every whole endpoint.
Both strict operands are required, including beside zero; mixed rows remain unrestricted. -/
set_option autoImplicit false
namespace Tests.ClosedStrictWordBinaryNegative
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .identifier name⟩
private def binary (span operatorSpan : Syntax.SourceSpan) (operator : Syntax.BinaryOp)
    (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨operatorSpan, operator⟩ right⟩

private theorem wrong_left {owner names captured store left value middle}
    (original : ClosedSourceExpressionEvaluates owner names captured store left value middle)
    (notWord : ∀ word, value ≠ .word word)
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    (right : Syntax.Expr) :
    ∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      (binary span operatorSpan operator left right) actual final := by
  intro actual final evaluated
  obtain ⟨lw, _, _, _, _, leftRun, _, _⟩ :=
    (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mp evaluated
  exact notWord lw (original.deterministic leftRun).1

private theorem wrong_right {owner names captured store left leftWord middle right value final}
    (leftOriginal : ClosedSourceExpressionEvaluates owner names captured store left (.word leftWord) middle)
    (rightOriginal : ClosedSourceExpressionEvaluates owner names captured middle right value final)
    (notWord : ∀ word, value ≠ .word word)
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr) :
    ∀ actual actualFinal, ¬ ClosedSourceExpressionEvaluates owner names captured store
      (binary span operatorSpan operator left right) actual actualFinal := by
  intro actual actualFinal evaluated
  obtain ⟨_, rw, _, actualMiddle, _, leftRun, rightRun, _⟩ :=
    (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mp evaluated
  have sameMiddle := (leftRun.deterministic leftOriginal).2
  cases sameMiddle
  exact notWord rw (rightOriginal.deterministic rightRun).1

private theorem missing_reference {owner names captured store final actual span name}
    (missing : LocalNameTable.lookup? names name.value = none ∨
      ∃ id, LocalNameTable.Lookup names name.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    ¬ ClosedSourceExpressionEvaluates owner names captured store (reference span name) actual final := by
  intro evaluated
  cases evaluated with
  | reference named found =>
      rcases missing with missing | ⟨id, correctName, missing⟩
      · have accepted := LocalNameTable.lookup?_iff.mpr named
        rw [missing] at accepted
        cases accepted
      · cases named.id_unique correctName
        have accepted := Resolved.LocalScope.lookup?_iff.mpr found
        rw [missing] at accepted
        cases accepted
  | creation shape => cases shape

theorem non_word_reference_on_either_side_never_succeeds
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span operatorSpan goodSpan badSpan : Syntax.SourceSpan)
    (operator : Syntax.BinaryOp) (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    (goodName badName : Syntax.Identifier) (goodId badId : Resolved.LocalId)
    (word : Core.Word) (bad : RuntimeValue) (notWord : ∀ w, bad ≠ .word w)
    (goodNamed : LocalNameTable.Lookup names goodName.value goodId)
    (badNamed : LocalNameTable.Lookup names badName.value badId)
    (goodFound : Resolved.LocalScope.Lookup captured goodId (.word word))
    (badFound : Resolved.LocalScope.Lookup captured badId bad) :
    ClosedSourceExpressionEvaluates owner names captured store (reference goodSpan goodName) (.word word) store ∧
    ClosedSourceExpressionEvaluates owner names captured store (reference badSpan badName) bad store ∧
    (∀ actual final,
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator (reference badSpan badName) (reference goodSpan goodName)) actual final) ∧
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator (reference goodSpan goodName) (reference badSpan badName)) actual final)) := by
  have goodOriginal : ClosedSourceExpressionEvaluates owner names captured store
      (reference goodSpan goodName) (.word word) store := .reference goodNamed goodFound
  have badOriginal : ClosedSourceExpressionEvaluates owner names captured store
      (reference badSpan badName) bad store := .reference badNamed badFound
  refine ⟨goodOriginal, badOriginal, ?_⟩
  intro actual final
  exact ⟨wrong_left badOriginal notWord notAnd notOr _ actual final,
    wrong_right goodOriginal badOriginal notWord notAnd notOr actual final⟩

theorem missing_reference_on_either_side_never_succeeds
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span operatorSpan missingSpan : Syntax.SourceSpan)
    (operator : Syntax.BinaryOp) (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    (other : Syntax.Expr) (missingName : Syntax.Identifier)
    (missing : LocalNameTable.lookup? names missingName.value = none ∨
      ∃ id, LocalNameTable.Lookup names missingName.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    ∀ actual final,
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator other (reference missingSpan missingName)) actual final) ∧
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator (reference missingSpan missingName) other) actual final) := by
  intro actual final
  constructor
  · intro evaluated
    obtain ⟨_, _, _, _, _, _, rightRun, _⟩ :=
      (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mp evaluated
    exact missing_reference missing rightRun
  · intro evaluated
    obtain ⟨_, _, _, _, _, leftRun, _, _⟩ :=
      (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mp evaluated
    exact missing_reference missing leftRun

theorem zero_never_skips_a_missing_reference_on_either_side
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span operatorSpan zeroSpan missingSpan : Syntax.SourceSpan)
    (operator : Syntax.BinaryOp) (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    (zeroName missingName : Syntax.Identifier) (zeroId : Resolved.LocalId)
    (zeroNamed : LocalNameTable.Lookup names zeroName.value zeroId)
    (zeroFound : Resolved.LocalScope.Lookup captured zeroId (.word Core.Word.zero))
    (missing : LocalNameTable.lookup? names missingName.value = none ∨
      ∃ id, LocalNameTable.Lookup names missingName.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    ClosedSourceExpressionEvaluates owner names captured store
      (reference zeroSpan zeroName) (.word Core.Word.zero) store ∧
    (∀ actual final,
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator (reference zeroSpan zeroName) (reference missingSpan missingName)) actual final) ∧
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator (reference missingSpan missingName) (reference zeroSpan zeroName)) actual final)) := by
  have zeroOriginal : ClosedSourceExpressionEvaluates owner names captured store
      (reference zeroSpan zeroName) (.word Core.Word.zero) store := .reference zeroNamed zeroFound
  exact ⟨zeroOriginal, missing_reference_on_either_side_never_succeeds owner names captured store
    span operatorSpan missingSpan operator notAnd notOr (reference zeroSpan zeroName) missingName missing⟩

end Tests.ClosedStrictWordBinaryNegative
end

section
-- leanmerge: from Solcore.Test.FrontendClosedStrictWordBinarySavedCallProperties
/- Original saved closures can occur on either strict operand side. Caller
arguments are read before the fresh saved-owner parameter shadows saved p.
All tails and stores are arbitrary mixed rows; duplicate identities are allowed.
These reference/identity-body fixtures preserve stores and make no claim about
additional state-changing caller prefixes, typing, or Core closure identity. -/
set_option autoImplicit false
open Solcore Solcore.Frontend
namespace Tests.ClosedStrictWordBinarySavedCall

private def ref (s : Nat → Syntax.SourceSpan) (i : Nat) (name : String) : Syntax.Expr :=
  ⟨s i, .identifier ⟨s (i + 1), name⟩⟩
private def body (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 10, [⟨s 11, .returnStmt (some (ref s 12 "p"))⟩]⟩
private def original (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 4, .lambda (s 5) ⟨s 6, [⟨s 7, .inferred ⟨s 8, "p"⟩⟩]⟩ none (body s)⟩
private def call (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 14, .call (ref s 15 "picked") ⟨s 17, [ref s 18 "p"]⟩⟩
private def binary (s : Nat → Syntax.SourceSpan) (onLeft : Bool)
    (operator : Syntax.BinaryOp) : Syntax.Expr :=
  ⟨s 0, .binary (if onLeft then call s else ref s 20 "other") ⟨s 1, operator⟩
    (if onLeft then ref s 20 "other" else call s)⟩
private def savedNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) : LocalNameTable :=
  ("p", ⟨owner, 2⟩) :: tail
private def savedCaptured (owner : Resolved.DeclarationId) (old : RuntimeValue)
    (tail : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  (⟨owner, 2⟩, old) :: tail
private def callerNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) : LocalNameTable :=
  ("picked", ⟨owner, 0⟩) :: ("p", ⟨owner, 1⟩) :: ("other", ⟨owner, 2⟩) :: tail
private def callerCaptured (owner : Resolved.DeclarationId) (made : RuntimeValue)
    (argument other : Core.Word) (tail : Resolved.LocalScope RuntimeValue) :
    Resolved.LocalScope RuntimeValue :=
  (⟨owner, 0⟩, made) :: (⟨owner, 1⟩, .word argument) :: (⟨owner, 2⟩, .word other) :: tail

private theorem index_ne (owner : Resolved.DeclarationId) {i j : Nat} (different : i ≠ j) :
    (⟨owner, i⟩ : Resolved.LocalId) ≠ ⟨owner, j⟩ := by
  intro equal
  exact different (congrArg Resolved.LocalId.binderIndex equal)

private theorem strict_endpoints {owner names captured store middle final left right}
    {leftWord rightWord result} (s : Nat → Syntax.SourceSpan) (operator : Syntax.BinaryOp)
    (l : ClosedSourceExpressionEvaluates owner names captured store left (.word leftWord) middle)
    (r : ClosedSourceExpressionEvaluates owner names captured middle right (.word rightWord) final)
    (meaning : StrictWordBinaryDenotes operator leftWord rightWord result) :
    ∀ actual actualFinal, ClosedSourceExpressionEvaluates owner names captured store
      ⟨s 0, .binary left ⟨s 1, operator⟩ right⟩ actual actualFinal ↔
      actual = RuntimeValue.ofCore result ∧ actualFinal = final := by
  intro actual actualFinal
  obtain ⟨notAnd, notOr⟩ := meaning.operator_is_strict
  constructor
  · intro evaluated
    obtain ⟨lw, rw, value, actualMiddle, sameValue, actualLeft, actualRight, actualMeaning⟩ :=
      (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mp evaluated
    obtain ⟨sameLeft, sameMiddle⟩ := l.deterministic actualLeft
    cases RuntimeValue.word.inj sameLeft
    cases sameMiddle
    obtain ⟨sameRight, sameFinal⟩ := r.deterministic actualRight
    cases RuntimeValue.word.inj sameRight
    cases sameFinal
    cases meaning.value_unique actualMeaning
    exact ⟨sameValue, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mpr
      ⟨leftWord, rightWord, result, middle, rfl, l, r, meaning⟩

theorem original_saved_call_on_either_side_and_all_actual_endpoints
    (s : Nat → Syntax.SourceSpan) (savedOwner callerOwner : Resolved.DeclarationId)
    (different : callerOwner ≠ savedOwner) (onLeft : Bool)
    (savedNameTail callerNameTail : LocalNameTable)
    (savedTail callerTail : Resolved.LocalScope RuntimeValue)
    (oldSavedP : RuntimeValue) (argument other : Core.Word) (store : List RuntimeValue)
    (operator : Syntax.BinaryOp) (result : Core.Value)
    (meaning : StrictWordBinaryDenotes operator
      (if onLeft then argument else other) (if onLeft then other else argument) result) :
    let sn := savedNames savedOwner savedNameTail
    let sc := savedCaptured savedOwner oldSavedP savedTail
    let closure := RuntimeValue.sourceClosure (original s) savedOwner sn sc
    ClosedSourceExpressionEvaluates savedOwner sn sc store (original s) closure store ∧
    ∀ made madeStore,
      ClosedSourceExpressionEvaluates savedOwner sn sc store (original s) made madeStore →
      let cn := callerNames callerOwner callerNameTail
      let cc := callerCaptured callerOwner made argument other callerTail
      let parameter := Resolved.freshLocalId savedOwner (sn.map Prod.snd)
      made = closure ∧ madeStore = store ∧ callerOwner ≠ savedOwner ∧
      parameter ∉ sn.map Prod.snd ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (ref s 15 "picked") made madeStore ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (ref s 18 "p") (.word argument) madeStore ∧
      ClosedSourceBodyEvaluates savedOwner (("p", parameter) :: sn)
        ((parameter, .word argument) :: sc) madeStore (body s) (.word argument) madeStore ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (call s) (.word argument) madeStore ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (binary s onLeft operator) (RuntimeValue.ofCore result) madeStore ∧
      (∀ actual final, ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (binary s onLeft operator) actual final ↔
        actual = RuntimeValue.ofCore result ∧ final = madeStore) := by
  dsimp only
  let sn := savedNames savedOwner savedNameTail
  let sc := savedCaptured savedOwner oldSavedP savedTail
  let closure := RuntimeValue.sourceClosure (original s) savedOwner sn sc
  have created : ClosedSourceExpressionEvaluates savedOwner sn sc store
      (original s) closure store := .creation .inferred
  refine ⟨created, ?_⟩
  intro made madeStore returned
  obtain ⟨actualClosure, actualCreationStore⟩ := returned.deterministic created
  let cn := callerNames callerOwner callerNameTail
  let cc := callerCaptured callerOwner made argument other callerTail
  let calleeStore := madeStore
  let argumentStore := calleeStore
  have fetched : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 15 "picked") made calleeStore := .reference .head .head
  have fetchedClosure : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 15 "picked") closure calleeStore := by
    rw [← actualClosure]
    exact fetched
  have actualArgument : ClosedSourceExpressionEvaluates callerOwner cn cc calleeStore
      (ref s 18 "p") (.word argument) argumentStore :=
    .reference (.tail (by change "picked" ≠ "p"; decide) .head)
      (.tail (index_ne callerOwner (by decide)) .head)
  have actualOther : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 20 "other") (.word other) madeStore :=
    .reference (.tail (by change "picked" ≠ "other"; decide)
      (.tail (by change "p" ≠ "other"; decide) .head))
      (.tail (index_ne callerOwner (by decide)) (.tail (index_ne callerOwner (by decide)) .head))
  let parameter := Resolved.freshLocalId savedOwner (sn.map Prod.snd)
  have actualBody : ClosedSourceBodyEvaluates savedOwner (("p", parameter) :: sn)
      ((parameter, .word argument) :: sc) argumentStore (body s) (.word argument) argumentStore :=
    .expression (.reference .head .head)
  have invoked : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (call s) (.word argument) argumentStore :=
    .call (calleeStore := calleeStore) (argumentStore := argumentStore)
      .inferred fetchedClosure actualArgument actualBody
  have originalBinary : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (binary s onLeft operator) (RuntimeValue.ofCore result) madeStore := by
    cases onLeft
    · exact .strictWordBinary actualOther invoked meaning
    · exact .strictWordBinary invoked actualOther meaning
  refine ⟨actualClosure, actualCreationStore, different, Resolved.freshLocalId_not_mem _ _,
    fetched, actualArgument, actualBody, invoked, originalBinary, ?_⟩
  cases onLeft
  · exact strict_endpoints s operator actualOther invoked meaning
  · exact strict_endpoints s operator invoked actualOther meaning

theorem saved_calls_preserve_wrap_and_zero_division
    (s : Nat → Syntax.SourceSpan) (savedOwner callerOwner : Resolved.DeclarationId)
    (different : callerOwner ≠ savedOwner) (savedNameTail callerNameTail : LocalNameTable)
    (savedTail callerTail : Resolved.LocalScope RuntimeValue)
    (oldSavedP : RuntimeValue) (dividend : Core.Word) (store : List RuntimeValue) :
    let closure := RuntimeValue.sourceClosure (original s) savedOwner
      (savedNames savedOwner savedNameTail) (savedCaptured savedOwner oldSavedP savedTail)
    let cn := callerNames callerOwner callerNameTail
    ClosedSourceExpressionEvaluates callerOwner cn
      (callerCaptured callerOwner closure Core.Word.maximum (Core.Word.ofNatModulo 1) callerTail)
      store (binary s true .add) (.word Core.Word.zero) store ∧
    ClosedSourceExpressionEvaluates callerOwner cn
      (callerCaptured callerOwner closure Core.Word.zero dividend callerTail)
      store (binary s false .divide) (.word Core.Word.zero) store := by
  have wrapped := original_saved_call_on_either_side_and_all_actual_endpoints
    s savedOwner callerOwner different true savedNameTail callerNameTail savedTail callerTail
    oldSavedP Core.Word.maximum (Core.Word.ofNatModulo 1) store .add (.word Core.Word.zero) .add
  have divided := original_saved_call_on_either_side_and_all_actual_endpoints
    s savedOwner callerOwner different false savedNameTail callerNameTail savedTail callerTail
    oldSavedP Core.Word.zero dividend store .divide (.word Core.Word.zero) .divide
  obtain ⟨wrapCreation, wrapActual⟩ := wrapped
  obtain ⟨divideCreation, divideActual⟩ := divided
  obtain ⟨_, _, _, _, _, _, _, _, wrapResult, _⟩ := wrapActual _ _ wrapCreation
  obtain ⟨_, _, _, _, _, _, _, _, divideResult, _⟩ := divideActual _ _ divideCreation
  constructor
  · simpa only [RuntimeValue.ofCore] using wrapResult
  · simpa only [RuntimeValue.ofCore] using divideResult

end Tests.ClosedStrictWordBinarySavedCall
end

section
-- leanmerge: from Solcore.Test.FrontendClosedStrictWordBinarySymbolicProperties
/- Fourteen original strict Word witnesses over arbitrary ordered mixed inputs.
No typing, unique-row, whole-resolution or bounded-execution premise is used. -/
set_option autoImplicit false
namespace Tests.ClosedStrictWordBinarySymbolic
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .identifier name⟩
private def source (spans : Fin 4 → Syntax.SourceSpan) (left right : Syntax.Identifier)
    (operator : Syntax.BinaryOp) : Syntax.Expr :=
  ⟨spans 0, .binary (reference (spans 2) left) ⟨spans 1, operator⟩
    (reference (spans 3) right)⟩
private def outcomes (left right : Core.Word) : List (Syntax.BinaryOp × Core.Value) :=
  [(.add, .word (left.add right)), (.subtract, .word (left.sub right)),
   (.multiply, .word (left.mul right)), (.divide, .word (left.udiv right)),
   (.modulo, .word (left.umod right)), (.bitAnd, .word (left.bitAnd right)),
   (.bitOr, .word (left.bitOr right)), (.bitXor, .word (left.bitXor right)),
   (.greater, .bool (decide (left > right))), (.less, .bool (decide (left < right))),
   (.equal, .bool (left == right)), (.notEqual, .bool (!(left == right))),
   (.lessEqual, .bool (!(decide (left > right)))),
   (.greaterEqual, .bool (!(decide (left < right))))]

private theorem original_meaning {left right : Core.Word} {operator : Syntax.BinaryOp}
    {value : Core.Value} (member : (operator, value) ∈ outcomes left right) :
    StrictWordBinaryDenotes operator left right value := by
  simp only [outcomes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h; constructor

theorem all_fourteen_original_and_exact_actual_results
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (spans : Fin 4 → Syntax.SourceSpan) (leftName rightName : Syntax.Identifier)
    (leftId rightId : Resolved.LocalId) (leftWord rightWord : Core.Word)
    (leftNamed : LocalNameTable.Lookup names leftName.value leftId)
    (rightNamed : LocalNameTable.Lookup names rightName.value rightId)
    (leftFound : Resolved.LocalScope.Lookup captured leftId (.word leftWord))
    (rightFound : Resolved.LocalScope.Lookup captured rightId (.word rightWord)) :
    ∀ operator result, (operator, result) ∈ outcomes leftWord rightWord →
      ClosedSourceExpressionEvaluates owner names captured store
        (source spans leftName rightName operator) (RuntimeValue.ofCore result) store ∧
      (∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
        (source spans leftName rightName operator) actual final ↔
        actual = RuntimeValue.ofCore result ∧ final = store) ∧
      ClosedSourceDataExpression (source spans leftName rightName operator) := by
  intro operator result member
  have meaning := original_meaning member
  have leftOriginal : ClosedSourceExpressionEvaluates owner names captured store
      (reference (spans 2) leftName) (.word leftWord) store := .reference leftNamed leftFound
  have rightOriginal : ClosedSourceExpressionEvaluates owner names captured store
      (reference (spans 3) rightName) (.word rightWord) store := .reference rightNamed rightFound
  have original : ClosedSourceExpressionEvaluates owner names captured store
      (source spans leftName rightName operator) (RuntimeValue.ofCore result) store :=
    .strictWordBinary leftOriginal rightOriginal meaning
  obtain ⟨notAnd, notOr⟩ := meaning.operator_is_strict
  refine ⟨original, ?_, ?_⟩
  · intro actual final
    have decomposition := closedSourceExpressionEvaluates_strictWordBinary_iff
      (owner := owner) (names := names) (captured := captured) (initialStore := store)
      (finalStore := final) (span := spans 0) (operatorSpan := spans 1)
      (left := reference (spans 2) leftName) (right := reference (spans 3) rightName)
      (value := actual) notAnd notOr
    constructor
    · intro evaluated
      obtain ⟨lw, rw, value, middle, actualEq, leftRun, rightRun, actualMeaning⟩ :=
        decomposition.mp evaluated
      obtain ⟨leftEq, middleEq⟩ := leftRun.deterministic leftOriginal
      cases RuntimeValue.word.inj leftEq
      cases middleEq
      obtain ⟨rightEq, finalEq⟩ := rightRun.deterministic rightOriginal
      cases RuntimeValue.word.inj rightEq
      exact ⟨actualEq.trans (congrArg RuntimeValue.ofCore (actualMeaning.value_unique meaning)), finalEq⟩
    · intro endpoints
      exact decomposition.mpr ⟨leftWord, rightWord, result, store, endpoints.1,
        leftOriginal, by simpa only [endpoints.2] using rightOriginal, meaning⟩
  · exact .strictWordBinary .reference .reference notAnd notOr

end Tests.ClosedStrictWordBinarySymbolic
end

section
-- leanmerge: from Solcore.Test.FrontendClosedStrictWordDepthProperties
/- Exact search depth composes both actual Word children in their original order.
This is a cutoff theorem at every budget, not a Core transition-cost equation. -/
set_option autoImplicit false
open Solcore Frontend
namespace Tests.ClosedStrictWordDepth

theorem strict_binary_exact_depth
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore middleStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    {left right : Syntax.Expr} {leftWord rightWord : Core.Word}
    {result : Core.Value} {leftDepth rightDepth : Nat}
    (meaning : StrictWordBinaryDenotes operator leftWord rightWord result)
    (leftCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured initialStore left =
        if leftDepth ≤ n then some (.word leftWord, middleStore) else none)
    (rightCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured middleStore right =
        if rightDepth ≤ n then some (.word rightWord, finalStore) else none) :
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, operator⟩ right⟩ =
        if max leftDepth rightDepth + 1 ≤ budget then
          some (RuntimeValue.ofCore result, finalStore) else none := by
  intro budget
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
      rw [evaluateClosedSourceExpression?_strictWordBinary _ _ _ _ _ _ _ _
        meaning.operator_is_strict.1 meaning.operator_is_strict.2, leftCutoff]
      by_cases leftEnough : leftDepth ≤ n
      · rw [if_pos leftEnough]
        simp only [bind, Option.bind_some]
        rw [rightCutoff]
        by_cases rightEnough : rightDepth ≤ n
        · rw [if_pos rightEnough,
            if_pos (show max leftDepth rightDepth + 1 ≤ n + 1 by omega)]
          simp only [Option.bind_some, evaluateStrictWordBinary?_iff.mpr meaning]
          rfl
        · rw [if_neg rightEnough,
            if_neg (show ¬ max leftDepth rightDepth + 1 ≤ n + 1 by omega)]
          rfl
      · rw [if_neg leftEnough,
          if_neg (show ¬ max leftDepth rightDepth + 1 ≤ n + 1 by omega)]
        rfl

end Tests.ClosedStrictWordDepth
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedStrictWordBinary
/- Actual parsed grouped references, fourteen operator spellings, five unsigned
Word pairs and two separate raw/Core stores. Original closed and local-cost
witnesses are constructed before running either machine. No data gate, runtime
typing of opaque tails, source/Core closure identity or parser proof is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Tests.ParsedClosedStrictWordBinary
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedStrictWord",by decide⟩],by decide⟩⟩,300⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex:=903}
private def fid : Resolved.LocalId := ⟨foreign,700⟩
private def names : LocalNameTable := [("x",sid 7),("y",sid 31),("x",fid)]
private def opaqueCore : Core.Value := .closure .unit .word (.var 99)
  [.hostFunction .storageWrite,.cellRef .word 700]
private def rawRows (p : RuntimeValue) (a b : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(sid 0,p),(sid 7,.word a),(sid 31,.word b),(sid 7,.unit),(fid,p)]
private def coreRows (a b : Core.Word) : Resolved.Environment :=
  [(sid 7,.word a),(sid 31,.word b),(sid 7,opaqueCore),(fid,.cellRef .word 900)]
private def context : Resolved.Context := [(sid 7,.word),(sid 31,.word),(sid 7,.unit),(fid,.unit)]
private def range (file : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨file.id,a,b⟩
private def leaf (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def binary (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat) : Syntax.Expr :=
  ⟨range f 1 (w+5),.binary (leaf (range f 1 2) "x") ⟨range f 3 (w+3),op⟩
    (leaf (range f (w+4) (w+5)) "y")⟩
private def source (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat) : Syntax.Expr :=
  ⟨range f 0 (w+6),.group (binary f op w)⟩
private def overhead : Syntax.BinaryOp → Nat
  | .notEqual | .lessEqual => 5
  | .less => 9
  | .greaterEqual => 11
  | _ => 3
private def primitive (op : Syntax.BinaryOp) (a b : Core.Word) :
    Option {value : Core.Value // StrictWordBinaryDenotes op a b value} :=
  match op with
  | .add => some ⟨.word (a.add b),.add⟩
  | .subtract => some ⟨.word (a.sub b),.subtract⟩
  | .multiply => some ⟨.word (a.mul b),.multiply⟩
  | .divide => some ⟨.word (a.udiv b),.divide⟩
  | .modulo => some ⟨.word (a.umod b),.modulo⟩
  | .bitAnd => some ⟨.word (a.bitAnd b),.bitAnd⟩
  | .bitOr => some ⟨.word (a.bitOr b),.bitOr⟩
  | .bitXor => some ⟨.word (a.bitXor b),.bitXor⟩
  | .greater => some ⟨.bool (decide (a>b)),.greater⟩
  | .less => some ⟨.bool (decide (a<b)),.less⟩
  | .equal => some ⟨.bool (a==b),.equal⟩
  | .notEqual => some ⟨.bool (!(a==b)),.notEqual⟩
  | .lessEqual => some ⟨.bool (!(decide (a>b))),.lessEqual⟩
  | .greaterEqual => some ⟨.bool (!(decide (a<b))),.greaterEqual⟩
  | .shiftLeft | .shiftRight | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply
  | .logicalAnd | .logicalOr => none
private theorem original (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat)
    (a b : Core.Word) (value : Core.Value) (meaning : StrictWordBinaryDenotes op a b value)
    (p : RuntimeValue) (store : List RuntimeValue) :
    ClosedSourceExpressionEvaluates owner names (rawRows p a b) store
      (source f op w) (RuntimeValue.ofCore value) store := by
  exact .group (.strictWordBinary (.reference .head (.tail (by decide) .head))
    (.reference (.tail (by change "x" ≠ "y"; decide) .head)
      (.tail (by decide) (.tail (by decide) .head))) meaning)
private theorem costed (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat)
    (a b : Core.Word) (value : Core.Value) (meaning : StrictWordBinaryDenotes op a b value)
    (store : Core.Store) : LocalExpressionEvaluatesWithCost names (coreRows a b) store
      (source f op w) value store (2+overhead op) := by
  have l : LocalExpressionEvaluatesWithCost names (coreRows a b) store
      (leaf (range f 1 2) "x") (.word a) store 1 := .identifier .head .head
  have r : LocalExpressionEvaluatesWithCost names (coreRows a b) store
      (leaf (range f (w+4) (w+5)) "y") (.word b) store 1 :=
    .identifier (.tail (by change "x" ≠ "y"; decide) .head) (.tail (by decide) .head)
  apply LocalExpressionEvaluatesWithCost.group
  cases meaning with
  | add => exact .add l r
  | subtract => exact .subtract l r
  | multiply => exact .multiply l r
  | divide => exact .divide l r
  | modulo => exact .modulo l r
  | bitAnd => exact .bitAnd l r
  | bitOr => exact .bitOr l r
  | bitXor => exact .bitXor l r
  | greater => exact .greater l r
  | less => exact .less l r
  | equal => exact .equal l r
  | notEqual => exact .notEqual l r
  | lessEqual => exact .lessEqual l r
  | greaterEqual => exact .greaterEqual l r
private theorem cutoff (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat)
    (a b : Core.Word) (value : Core.Value) (meaning : StrictWordBinaryDenotes op a b value)
    (p : RuntimeValue) (store : List RuntimeValue) : ∀ n,
    evaluateClosedSourceExpression? n owner names (rawRows p a b) store (source f op w) =
      if 3 ≤ n then some (RuntimeValue.ofCore value,store) else none := by
  cases meaning <;> intro n
  all_goals
    by_cases high : 3 ≤ n
    · have split : n=(n-3)+3 := by omega
      rw [split]
      simp [source,binary,leaf,evaluateClosedSourceExpression?,evaluateStrictWordBinary?,
        names,rawRows,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,sid,owner,fid,foreign]
    · have small : n=0 ∨ n=1 ∨ n=2 := by omega
      rcases small with rfl | rfl | rfl
      all_goals simp [source,binary,leaf,evaluateClosedSourceExpression?]
private theorem image {captured store src value}
    (original : ClosedSourceExpressionEvaluates owner names captured store src value store) :
    ∀ a st, ClosedSourceExpressionEvaluates owner names captured store src a st ↔ a=value ∧ st=store := by
  intro a st; constructor
  · exact fun h => h.deterministic original
  · rintro ⟨rfl,rfl⟩; exact original
private theorem coreImage {e s c v k} (h : Core.Steps k (.initial c e s) (.final v s)) (fuel a st) :
    Core.runStateful fuel (.initial c e s) = .done a st ↔ a=v ∧ st=s ∧ k≤fuel := by
  constructor
  · intro run
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic (Core.runStateful_evaluation_sound run)
      (Core.steps_from_initial_sound h)
    exact ⟨rfl,rfl,h.runStateful_done_iff.mp run⟩
  · rintro ⟨rfl,rfl,enough⟩; exact h.runStateful_done_iff.mpr enough
private def closedLane {captured store src value} (d : Nat)
    (orig : ClosedSourceExpressionEvaluates owner names captured store src value store)
    (cut : ∀ n, evaluateClosedSourceExpression? n owner names captured store src =
      if d≤n then some (value,store) else none) : IO Unit := do
  proof orig
  for n in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? n owner names captured store src with
    | none =>
      have below : n<d := by
        by_cases enough : d≤n
        · have eq := cut n; rw [run,if_pos enough] at eq; cases eq
        · omega
      proof below; check (n<d) "closed exact depth rejection"
    | some (actual,finalStore) =>
      have endpoints : actual=value ∧ finalStore=store := by
        by_cases enough : d≤n
        · have eq := cut n; rw [run,if_pos enough] at eq; exact Prod.mk.inj (Option.some.inj eq)
        · have eq := cut n; rw [run,if_neg enough] at eq; cases eq
      have witness := (image orig actual finalStore).mpr endpoints
      proof endpoints; proof witness; proof ((image orig actual finalStore).mp witness)
      check (n≥d) "closed full actual endpoints proved at sufficient depth"
private def exercise (f : Syntax.SourceFile) (src : Syntax.Expr) (op : Syntax.BinaryOp) (w : Nat)
    (shape : src=source f op w) (a b : Core.Word) (p : RuntimeValue)
    (rawStore : List RuntimeValue) (coreStore : Core.Store) : IO Unit := do
  let some ⟨value,meaning⟩ := primitive op a b | throw (IO.userError "strict primitive constructor")
  have orig : ClosedSourceExpressionEvaluates owner names (rawRows p a b) rawStore src
      (RuntimeValue.ofCore value) rawStore := by rw [shape]; exact original f op w a b value meaning p rawStore
  have lc : LocalExpressionEvaluatesWithCost names (coreRows a b) coreStore src value coreStore
      (2+overhead op) := by rw [shape]; exact costed f op w a b value meaning coreStore
  proof orig; proof lc
  have cut : ∀ n, evaluateClosedSourceExpression? n owner names (rawRows p a b) rawStore src =
      if 3≤n then some (RuntimeValue.ofCore value,rawStore) else none := by
    intro n; rw [shape]; exact cutoff f op w a b value meaning p rawStore n
  let inner := match src.value with | .group child => child | _ => src
  have innerShape : inner=binary f op w := by simp only [inner,shape,source]
  have innerOrig : ClosedSourceExpressionEvaluates owner names (rawRows p a b) rawStore inner
      (RuntimeValue.ofCore value) rawStore := by
    rw [innerShape]
    exact .strictWordBinary (.reference .head (.tail (by decide) .head))
      (.reference (.tail (by change "x" ≠ "y"; decide) .head)
        (.tail (by decide) (.tail (by decide) .head))) meaning
  have innerCut : ∀ n, evaluateClosedSourceExpression? n owner names (rawRows p a b) rawStore inner =
      if 2≤n then some (RuntimeValue.ofCore value,rawStore) else none := by
    intro n
    have h := cutoff f op w a b value meaning p rawStore (n+1)
    rw [source,evaluateClosedSourceExpression?] at h
    have bound : (3≤n+1) ↔ (2≤n) := by omega
    simpa only [innerShape,bound] using h
  closedLane 2 innerOrig innerCut
  closedLane 3 orig cut
  match checked : elaborateLocalExpression? names context src with
  | none => throw (IO.userError "whole actual source checking")
  | some (core,ty) =>
    have aligned : (coreRows a b).ids=context.ids := rfl
    have steps := lc.checked_toSteps checked aligned
    have paths : ∀ continuation, Core.Steps (2+overhead op)
        ⟨.eval core (coreRows a b).values,continuation,coreStore⟩
        ⟨.ret value,continuation,coreStore⟩ := by
      obtain ⟨resolved,resolution,lowering,_⟩ := elaborateLocalExpression?_sound checked
      exact lc.toStepsWithContinuation resolution (aligned ▸ lowering)
    proof steps; proof paths
    let k := 2+overhead op
    for fuel in [0,k-1,k,k+3] do
      match run : Core.runStateful fuel (.initial core (coreRows a b).values coreStore) with
      | .done actual finalStore =>
        have endpoints := (coreImage steps fuel actual finalStore).mp run
        proof endpoints; proof ((coreImage steps fuel actual finalStore).mpr endpoints)
        check (actual==value && finalStore==coreStore && fuel≥k) "Core full actual endpoints and cost"
      | .outOfFuel suspended =>
        have below := steps.runStateful_outOfFuel_iff.mp ⟨suspended,run⟩
        proof below; proof (steps.runStateful_outOfFuel_iff.mpr below)
        check (fuel<k) "Core exact exhaustion"
      | _ => throw (IO.userError "independently costed Core expression stuck")
private def parsedCase (op : Syntax.BinaryOp) (spelling : String) : IO Nat := do
  let text := "(x "++spelling++" y)"
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-strict-word.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "strict Word lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span==Syntax.SourceSpan.fullFile file) "EOF, diagnostics, full source ownership"
    let w := spelling.utf8ByteSize
    match actualShape : src with
    | ⟨gs,.group ⟨bs,.binary ⟨ls,.identifier ⟨ln,"x"⟩⟩ ⟨os,actualOp⟩ ⟨rs,.identifier ⟨rn,"y"⟩⟩⟩⟩ =>
      if exactFields : gs=range file 0 (w+6) ∧ bs=range file 1 (w+5) ∧ ls=range file 1 2 ∧
          ln=range file 1 2 ∧ os=range file 3 (w+3) ∧ actualOp=op ∧
          rs=range file (w+4) (w+5) ∧ rn=range file (w+4) (w+5) then
        have shape : src=source file op w := by
          rcases exactFields with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
          exact actualShape
        check (src==source file op w && [gs,bs,ls,ln,os,rs,rn].all (fun r => r.isValidFor file))
          "whole handwritten AST and all seven actual ranges"
        let inert := leaf (range file 0 (w+6)) "opaque-unused"
        let p := RuntimeValue.sourceClosure inert foreign [("x",fid)] [(fid,.unit)]
        let pairs : List (Core.Word × Core.Word) := [(Core.Word.zero,Core.Word.zero),
          (Core.Word.ofNatModulo 7,Core.Word.ofNatModulo 3),(Core.Word.maximum,Core.Word.ofNatModulo 1),
          (Core.Word.ofNatModulo 1,Core.Word.maximum),(Core.Word.ofNatModulo (2^255),Core.Word.zero)]
        let mut count := 0
        for (a,b) in pairs do
          for (rawStore,coreStore) in [([],[]),
            ([p,RuntimeValue.ofCore opaqueCore,.hostFunction .storageWrite,.cellRef .word 701],
             [opaqueCore,.hostFunction .storageWrite,.cellRef .word 901,.unit])] do
            exercise file src op w shape a b p rawStore coreStore
            count := count+1
        return count
      else throw (IO.userError "complete actual AST differs from handwritten tree and all ranges")
    | _ => throw (IO.userError "actual grouped binary references")
  | _ => throw (IO.userError "strict Word parser")
end Tests.ParsedClosedStrictWordBinary
open Tests.ParsedClosedStrictWordBinary in
def Tests.frontendParsedClosedStrictWordBinaryTests : IO Unit := do
  let mut count := 0
  for (op,spelling) in [(.add,"+"),(.subtract,"-"),(.multiply,"*"),(.divide,"/"),(.modulo,"%"),
    (.bitAnd,"&"),(.bitOr,"|"),(.bitXor,"^"),(.greater,">"),(.less,"<"),(.equal,"=="),
    (.notEqual,"!="),(.lessEqual,"<="),(.greaterEqual,">=")] do
    count := count + (← parsedCase op spelling)
  check (count==140) "all fourteen operators, five Word pairs, two stores completed"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedStrictWordBinaryDataImage
/- Fourteen parsed operators, five Word pairs and two stores use the same Core
environment/store and their explicit ofCore images. Independent original and
Local-cost/Core witnesses precede both public image directions at all actual
values and full stores. No tail typing, source/Core closure identity or parser proof. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Tests.ParsedClosedStrictWordBinaryDataImage
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedStrictWord",by decide⟩],by decide⟩⟩,300⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex:=903}
private def fid : Resolved.LocalId := ⟨foreign,700⟩
private def names : LocalNameTable := [("x",sid 7),("y",sid 31),("x",fid)]
private def opaqueCore : Core.Value := .closure .unit .word (.var 99)
  [.hostFunction .storageWrite,.cellRef .word 700]
private def coreRows (a b : Core.Word) : Resolved.Environment :=
  [(sid 7,.word a),(sid 31,.word b),(sid 7,opaqueCore),(fid,.cellRef .word 900)]
private def rawRows (a b : Core.Word) : Resolved.LocalScope RuntimeValue :=
  (coreRows a b).map (fun row => (row.1,RuntimeValue.ofCore row.2))
private def context : Resolved.Context := [(sid 7,.word),(sid 31,.word),(sid 7,.unit),(fid,.unit)]
private def range (file : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨file.id,a,b⟩
private def leaf (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def binary (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat) : Syntax.Expr :=
  ⟨range f 1 (w+5),.binary (leaf (range f 1 2) "x") ⟨range f 3 (w+3),op⟩
    (leaf (range f (w+4) (w+5)) "y")⟩
private def source (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat) : Syntax.Expr :=
  ⟨range f 0 (w+6),.group (binary f op w)⟩
private def overhead : Syntax.BinaryOp → Nat
  | .notEqual | .lessEqual => 5
  | .less => 9
  | .greaterEqual => 11
  | _ => 3
private def primitive (op : Syntax.BinaryOp) (a b : Core.Word) :
    Option {value : Core.Value // StrictWordBinaryDenotes op a b value} :=
  match op with
  | .add => some ⟨.word (a.add b),.add⟩
  | .subtract => some ⟨.word (a.sub b),.subtract⟩
  | .multiply => some ⟨.word (a.mul b),.multiply⟩
  | .divide => some ⟨.word (a.udiv b),.divide⟩
  | .modulo => some ⟨.word (a.umod b),.modulo⟩
  | .bitAnd => some ⟨.word (a.bitAnd b),.bitAnd⟩
  | .bitOr => some ⟨.word (a.bitOr b),.bitOr⟩
  | .bitXor => some ⟨.word (a.bitXor b),.bitXor⟩
  | .greater => some ⟨.bool (decide (a>b)),.greater⟩
  | .less => some ⟨.bool (decide (a<b)),.less⟩
  | .equal => some ⟨.bool (a==b),.equal⟩
  | .notEqual => some ⟨.bool (!(a==b)),.notEqual⟩
  | .lessEqual => some ⟨.bool (!(decide (a>b))),.lessEqual⟩
  | .greaterEqual => some ⟨.bool (!(decide (a<b))),.greaterEqual⟩
  | .shiftLeft | .shiftRight | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply
  | .logicalAnd | .logicalOr => none
private theorem original (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat)
    (a b : Core.Word) (value : Core.Value) (meaning : StrictWordBinaryDenotes op a b value)
    (store : List RuntimeValue) :
    ClosedSourceExpressionEvaluates owner names (rawRows a b) store
      (source f op w) (RuntimeValue.ofCore value) store := by
  simp only [rawRows,coreRows,List.map_cons,List.map_nil,RuntimeValue.ofCore]
  exact .group (.strictWordBinary (leftWord := a) (rightWord := b) (.reference .head .head)
    (.reference (.tail (by change "x" ≠ "y"; decide) .head)
      (.tail (by change sid 7 ≠ sid 31; decide) .head)) meaning)
private theorem costed (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat)
    (a b : Core.Word) (value : Core.Value) (meaning : StrictWordBinaryDenotes op a b value)
    (store : Core.Store) : LocalExpressionEvaluatesWithCost names (coreRows a b) store
      (source f op w) value store (2+overhead op) := by
  have l : LocalExpressionEvaluatesWithCost names (coreRows a b) store
      (leaf (range f 1 2) "x") (.word a) store 1 := .identifier .head .head
  have r : LocalExpressionEvaluatesWithCost names (coreRows a b) store
      (leaf (range f (w+4) (w+5)) "y") (.word b) store 1 :=
    .identifier (.tail (by change "x" ≠ "y"; decide) .head) (.tail (by decide) .head)
  apply LocalExpressionEvaluatesWithCost.group
  cases meaning with
  | add => exact .add l r
  | subtract => exact .subtract l r
  | multiply => exact .multiply l r
  | divide => exact .divide l r
  | modulo => exact .modulo l r
  | bitAnd => exact .bitAnd l r
  | bitOr => exact .bitOr l r
  | bitXor => exact .bitXor l r
  | greater => exact .greater l r
  | less => exact .less l r
  | equal => exact .equal l r
  | notEqual => exact .notEqual l r
  | lessEqual => exact .lessEqual l r
  | greaterEqual => exact .greaterEqual l r
private theorem cutoff (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat)
    (a b : Core.Word) (value : Core.Value) (meaning : StrictWordBinaryDenotes op a b value)
    (store : List RuntimeValue) : ∀ n,
    evaluateClosedSourceExpression? n owner names (rawRows a b) store (source f op w) =
      if 3 ≤ n then some (RuntimeValue.ofCore value,store) else none := by
  cases meaning <;> intro n
  all_goals
    by_cases high : 3 ≤ n
    · have split : n=(n-3)+3 := by omega
      rw [split]
      simp [source,binary,leaf,evaluateClosedSourceExpression?,evaluateStrictWordBinary?,
        names,rawRows,coreRows,RuntimeValue.ofCore,LocalNameTable.lookup?,
        Resolved.LocalScope.lookup?,sid,owner,fid,foreign]
    · have small : n=0 ∨ n=1 ∨ n=2 := by omega
      rcases small with rfl | rfl | rfl
      all_goals simp [source,binary,leaf,evaluateClosedSourceExpression?]
private theorem image {captured store src value}
    (original : ClosedSourceExpressionEvaluates owner names captured store src value store) :
    ∀ a st, ClosedSourceExpressionEvaluates owner names captured store src a st ↔ a=value ∧ st=store := by
  intro a st; constructor
  · exact fun h => h.deterministic original
  · rintro ⟨rfl,rfl⟩; exact original
private theorem imageEndpoints {captured store src value}
    (orig : ClosedSourceExpressionEvaluates owner names captured store src value store)
    {target : RuntimeValue → List RuntimeValue → Prop}
    (contract : ∀ a st, ClosedSourceExpressionEvaluates owner names captured store src a st ↔ target a st) :
    ∀ a st, target a st ↔ a=value ∧ st=store := by
  intro a st; constructor
  · intro h; exact (image orig a st).mp ((contract a st).mpr h)
  · intro h; exact (contract a st).mp ((image orig a st).mpr h)
private theorem coreImage {e s c v k} (h : Core.Steps k (.initial c e s) (.final v s)) (fuel a st) :
    Core.runStateful fuel (.initial c e s) = .done a st ↔ a=v ∧ st=s ∧ k≤fuel := by
  constructor
  · intro run
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic (Core.runStateful_evaluation_sound run)
      (Core.steps_from_initial_sound h)
    exact ⟨rfl,rfl,h.runStateful_done_iff.mp run⟩
  · rintro ⟨rfl,rfl,enough⟩; exact h.runStateful_done_iff.mpr enough
private def closedLane {captured store src value} (d : Nat)
    (orig : ClosedSourceExpressionEvaluates owner names captured store src value store)
    (cut : ∀ n, evaluateClosedSourceExpression? n owner names captured store src =
      if d≤n then some (value,store) else none) : IO Unit := do
  proof orig
  for n in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? n owner names captured store src with
    | none =>
      have below : n<d := by
        by_cases enough : d≤n
        · have eq := cut n; rw [run,if_pos enough] at eq; cases eq
        · omega
      proof below; check (n<d) "closed exact depth rejection"
    | some (actual,finalStore) =>
      have endpoints : actual=value ∧ finalStore=store := by
        by_cases enough : d≤n
        · have eq := cut n; rw [run,if_pos enough] at eq; exact Prod.mk.inj (Option.some.inj eq)
        · have eq := cut n; rw [run,if_neg enough] at eq; cases eq
      have witness := (image orig actual finalStore).mpr endpoints
      proof endpoints; proof witness; proof ((image orig actual finalStore).mp witness)
      check (n≥d) "closed full actual endpoints proved at sufficient depth"
private def exercise (f : Syntax.SourceFile) (src : Syntax.Expr) (op : Syntax.BinaryOp) (w : Nat)
    (shape : src=source f op w) (a b : Core.Word) (coreStore : Core.Store) : IO Unit := do
  let rawStore := coreStore.map RuntimeValue.ofCore
  let some ⟨value,meaning⟩ := primitive op a b | throw (IO.userError "strict primitive constructor")
  have orig : ClosedSourceExpressionEvaluates owner names (rawRows a b) rawStore src
      (RuntimeValue.ofCore value) rawStore := by rw [shape]; exact original f op w a b value meaning rawStore
  have lc : LocalExpressionEvaluatesWithCost names (coreRows a b) coreStore src value coreStore
      (2+overhead op) := by rw [shape]; exact costed f op w a b value meaning coreStore
  proof orig; proof lc
  have cut : ∀ n, evaluateClosedSourceExpression? n owner names (rawRows a b) rawStore src =
      if 3≤n then some (RuntimeValue.ofCore value,rawStore) else none := by
    intro n; rw [shape]; exact cutoff f op w a b value meaning rawStore n
  let inner := match src.value with | .group child => child | _ => src
  have innerShape : inner=binary f op w := by simp only [inner,shape,source]
  have innerOrig : ClosedSourceExpressionEvaluates owner names (rawRows a b) rawStore inner
      (RuntimeValue.ofCore value) rawStore := by
    rw [innerShape]
    simp only [rawRows,coreRows,List.map_cons,List.map_nil,RuntimeValue.ofCore]
    exact .strictWordBinary (leftWord := a) (rightWord := b) (.reference .head .head)
      (.reference (.tail (by change "x" ≠ "y"; decide) .head)
        (.tail (by change sid 7 ≠ sid 31; decide) .head)) meaning
  have innerCut : ∀ n, evaluateClosedSourceExpression? n owner names (rawRows a b) rawStore inner =
      if 2≤n then some (RuntimeValue.ofCore value,rawStore) else none := by
    intro n
    have h := cutoff f op w a b value meaning rawStore (n+1)
    rw [source,evaluateClosedSourceExpression?] at h
    have bound : (3≤n+1) ↔ (2≤n) := by omega
    simpa only [innerShape,bound] using h
  closedLane 2 innerOrig innerCut
  closedLane 3 orig cut
  match checked : elaborateLocalExpression? names context src with
  | none => throw (IO.userError "whole actual source checking")
  | some (core,ty) =>
    have aligned : (coreRows a b).ids=context.ids := rfl
    have steps := lc.checked_toSteps checked aligned
    have paths : ∀ continuation, Core.Steps (2+overhead op)
        ⟨.eval core (coreRows a b).values,continuation,coreStore⟩
        ⟨.ret value,continuation,coreStore⟩ := by
      obtain ⟨resolved,resolution,lowering,_⟩ := elaborateLocalExpression?_sound checked
      exact lc.toStepsWithContinuation resolution (aligned ▸ lowering)
    have ce := Core.steps_from_initial_sound steps
    proof steps; proof paths; proof ce; proof lc.erase
    have admitted : ClosedSourceDataExpression src := by
      rw [shape]
      obtain ⟨notAnd,notOr⟩ := meaning.operator_is_strict
      exact .group (.strictWordBinary .reference .reference notAnd notOr)
    have localLaw (actual : RuntimeValue) (final : List RuntimeValue) :
        ClosedSourceExpressionEvaluates owner names (rawRows a b) rawStore src actual final ↔
        ∃ v st, actual=RuntimeValue.ofCore v ∧ final=st.map RuntimeValue.ofCore ∧
          LocalExpressionEvaluates names (coreRows a b) coreStore src v st :=
      admitted.local_evaluates_iff
    have coreLaw (actual : RuntimeValue) (final : List RuntimeValue) :
        ClosedSourceExpressionEvaluates owner names (rawRows a b) rawStore src actual final ↔
        ∃ v st, actual=RuntimeValue.ofCore v ∧ final=st.map RuntimeValue.ofCore ∧
          Core.Evaluates (coreRows a b).values coreStore core v st := by
      obtain ⟨resolved,resolution,lowering,_⟩ := elaborateLocalExpression?_sound checked
      exact admitted.core_evaluates_iff resolution (aligned ▸ lowering)
    proof ((localLaw _ _).mp orig); proof ((coreLaw _ _).mp orig)
    proof ((localLaw _ _).mpr ⟨value,coreStore,rfl,rfl,lc.erase⟩)
    proof ((coreLaw _ _).mpr ⟨value,coreStore,rfl,rfl,ce⟩)
    proof (imageEndpoints orig localLaw); proof (imageEndpoints orig coreLaw)
    let k := 2+overhead op
    for fuel in [0,k-1,k,k+3] do
      match run : Core.runStateful fuel (.initial core (coreRows a b).values coreStore) with
      | .done actual finalStore =>
        have endpoints := (coreImage steps fuel actual finalStore).mp run
        proof endpoints; proof ((coreImage steps fuel actual finalStore).mpr endpoints)
        have rawFromCore := (coreLaw (RuntimeValue.ofCore actual)
          (finalStore.map RuntimeValue.ofCore)).mpr
          ⟨actual,finalStore,rfl,rfl,Core.runStateful_evaluation_sound run⟩
        proof rawFromCore; proof ((localLaw _ _).mp rawFromCore)
        check (actual==value && finalStore==coreStore && fuel≥k) "Core full actual endpoints and cost"
      | .outOfFuel suspended =>
        have below := steps.runStateful_outOfFuel_iff.mp ⟨suspended,run⟩
        proof below; proof (steps.runStateful_outOfFuel_iff.mpr below)
        check (fuel<k) "Core exact exhaustion"
      | _ => throw (IO.userError "independently costed Core expression stuck")
private def parsedCase (op : Syntax.BinaryOp) (spelling : String) : IO Nat := do
  let text := "(x "++spelling++" y)"
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-strict-word.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "strict Word lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span==Syntax.SourceSpan.fullFile file) "EOF, diagnostics, full source ownership"
    let w := spelling.utf8ByteSize
    match actualShape : src with
    | ⟨gs,.group ⟨bs,.binary ⟨ls,.identifier ⟨ln,"x"⟩⟩ ⟨os,actualOp⟩ ⟨rs,.identifier ⟨rn,"y"⟩⟩⟩⟩ =>
      if exactFields : gs=range file 0 (w+6) ∧ bs=range file 1 (w+5) ∧ ls=range file 1 2 ∧
          ln=range file 1 2 ∧ os=range file 3 (w+3) ∧ actualOp=op ∧
          rs=range file (w+4) (w+5) ∧ rn=range file (w+4) (w+5) then
        have shape : src=source file op w := by
          rcases exactFields with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
          exact actualShape
        check (src==source file op w && [gs,bs,ls,ln,os,rs,rn].all (fun r => r.isValidFor file))
          "whole handwritten AST and all seven actual ranges"
        let pairs : List (Core.Word × Core.Word) := [(Core.Word.zero,Core.Word.zero),
          (Core.Word.ofNatModulo 7,Core.Word.ofNatModulo 3),(Core.Word.maximum,Core.Word.ofNatModulo 1),
          (Core.Word.ofNatModulo 1,Core.Word.maximum),(Core.Word.ofNatModulo (2^255),Core.Word.zero)]
        let mut count := 0
        for (a,b) in pairs do
          for coreStore in [[],[opaqueCore,.hostFunction .storageWrite,.cellRef .word 901,.unit]] do
            exercise file src op w shape a b coreStore
            count := count+1
        return count
      else throw (IO.userError "complete actual AST differs from handwritten tree and all ranges")
    | _ => throw (IO.userError "actual grouped binary references")
  | _ => throw (IO.userError "strict Word parser")
end Tests.ParsedClosedStrictWordBinaryDataImage
open Tests.ParsedClosedStrictWordBinaryDataImage in
def Tests.frontendParsedClosedStrictWordBinaryDataImageTests : IO Unit := do
  let mut count := 0
  for (op,spelling) in [(.add,"+"),(.subtract,"-"),(.multiply,"*"),(.divide,"/"),(.modulo,"%"),
    (.bitAnd,"&"),(.bitOr,"|"),(.bitXor,"^"),(.greater,">"),(.less,"<"),(.equal,"=="),
    (.notEqual,"!="),(.lessEqual,"<="),(.greaterEqual,">=")] do
    count := count + (← parsedCase op spelling)
  check (count==140) "all fourteen operators, five Word pairs, two stores completed"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedStrictWordSavedCalls
set_option autoImplicit false
namespace Tests.ParsedClosedStrictWordSavedCalls
open Solcore Solcore.Frontend
private def check (ok : Bool) (message : String) : IO Unit := unless ok do throw (IO.userError message)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def savedOwner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"SavedStrictWord",by decide⟩],by decide⟩⟩,300⟩
private def caller := {savedOwner with declarationIndex := 9300}
private def sid (i : Nat) : Resolved.LocalId := ⟨savedOwner,i⟩
private def cid (i : Nat) : Resolved.LocalId := ⟨caller,i⟩
private def old : RuntimeValue := .coreClosure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700]
private def savedNames : LocalNameTable := [("p",sid 2),("p",sid 2),("foreign",cid 900)]
private def savedRows (fs : Syntax.Expr) : Resolved.LocalScope RuntimeValue :=
  [(sid 2,old),(sid 2,.unit),(cid 900,.sourceClosure fs savedOwner [] [])]
private def names : LocalNameTable := [("picked",cid 0),("p",cid 1),("other",cid 2),("p",cid 1)]
private def rows (made : RuntimeValue) (argument other : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(cid 0,made),(cid 1,.word argument),(cid 2,.word other),(cid 1,old),(sid 2,made),(cid 0,.unit)]
private def file (name text : String) : Syntax.SourceFile := ⟨⟨.main,name⟩,text⟩
private def sp (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (name : String) : Syntax.Expr :=
  ⟨sp f a b,.identifier ⟨sp f a b,name⟩⟩
private def expectedLambda (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨sp f 0 17,.lambda (sp f 0 3) ⟨sp f 3 6,[⟨sp f 4 5,.inferred ⟨sp f 4 5,"p"⟩⟩]⟩ none
    ⟨sp f 6 17,[⟨sp f 7 16,.returnStmt (some (ref f 14 15 "p"))⟩]⟩⟩
private def expectedCall (f : Syntax.SourceFile) (offset : Nat) : Syntax.Expr :=
  ⟨sp f offset (offset+9),.call (ref f offset (offset+6) "picked")
    ⟨sp f (offset+6) (offset+9),[ref f (offset+7) (offset+8) "p"]⟩⟩
private def expectedBinary (f : Syntax.SourceFile) (onLeft : Bool) (symbol : String)
    (op : Syntax.BinaryOp) : Syntax.Expr :=
  let n := symbol.utf8ByteSize
  if onLeft then ⟨sp f 0 (16+n),.binary (expectedCall f 0) ⟨sp f 10 (10+n),op⟩ (ref f (11+n) (16+n) "other")⟩
  else ⟨sp f 0 (16+n),.binary (ref f 0 5 "other") ⟨sp f 6 (6+n),op⟩ (expectedCall f (7+n))⟩
private def parsed (f : Syntax.SourceFile) (expected : Syntax.Expr) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok src next =>
    check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span==Syntax.SourceSpan.fullFile f && src==expected) "exact original AST/all handwritten spans/EOF"
    return src
  | _ => throw (IO.userError "parser")

private structure Trace (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope RuntimeValue) (s : List RuntimeValue) (src : Syntax.Expr) where
  value : RuntimeValue
  final : List RuntimeValue
  original : ClosedSourceExpressionEvaluates o n e s src value final
  store_eq : final=s
private def observe {o n e s src v} (d : Nat)
    (original : ClosedSourceExpressionEvaluates o n e s src v s) : IO (Trace o n e s src) := do
  proof original
  match run : evaluateClosedSourceExpression? d o n e s src with
  | none => throw (IO.userError "actual expression absent")
  | some (value,final) =>
    have eq := (evaluateClosedSourceExpression?_sound run).deterministic original
    check (reprStr value==reprStr v && reprStr final==reprStr s) "actual complete expression endpoint"
    return ⟨value,final,by rw [eq.1,eq.2]; exact original,eq.2⟩
private structure BodyTrace (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope RuntimeValue) (s : List RuntimeValue) (src : Syntax.Block) where
  value : RuntimeValue
  final : List RuntimeValue
  original : ClosedSourceBodyEvaluates o n e s src value final
  store_eq : final=s
private def observeBody {o n e s src v}
    (original : ClosedSourceBodyEvaluates o n e s src v s) : IO (BodyTrace o n e s src) := do
  proof original
  match run : evaluateClosedSourceBody? 2 o n e s src with
  | none => throw (IO.userError "actual saved body absent")
  | some (value,final) =>
    have eq := (evaluateClosedSourceBody?_sound run).deterministic original
    check (reprStr value==reprStr v && reprStr final==reprStr s) "actual complete body endpoint"
    return ⟨value,final,by rw [eq.1,eq.2]; exact original,eq.2⟩
private def adjacent {o n e s src v} (d : Nat)
    (original : ClosedSourceExpressionEvaluates o n e s src v s) : IO Unit := do
  proof original
  for budget in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? budget o n e s src with
    | none => check (budget<d) "closed adjacent exhaustion"
    | some (value,final) =>
      proof ((evaluateClosedSourceExpression?_sound run).deterministic original)
      check (budget≥d && reprStr value==reprStr v && reprStr final==reprStr s) "closed adjacent actual endpoint"

private def meaning (op : Syntax.BinaryOp) (l r : Core.Word) : IO {v : Core.Value // StrictWordBinaryDenotes op l r v} :=
  match op with
  | .add => pure ⟨.word (l.add r),.add⟩
  | .subtract => pure ⟨.word (l.sub r),.subtract⟩
  | .multiply => pure ⟨.word (l.mul r),.multiply⟩
  | .divide => pure ⟨.word (l.udiv r),.divide⟩
  | .modulo => pure ⟨.word (l.umod r),.modulo⟩
  | .bitAnd => pure ⟨.word (l.bitAnd r),.bitAnd⟩
  | .bitOr => pure ⟨.word (l.bitOr r),.bitOr⟩
  | .bitXor => pure ⟨.word (l.bitXor r),.bitXor⟩
  | .greater => pure ⟨.bool (decide (l>r)),.greater⟩
  | .less => pure ⟨.bool (decide (l<r)),.less⟩
  | .equal => pure ⟨.bool (l==r),.equal⟩
  | .notEqual => pure ⟨.bool (!(l==r)),.notEqual⟩
  | .lessEqual => pure ⟨.bool (!(decide (l>r))),.lessEqual⟩
  | .greaterEqual => pure ⟨.bool (!(decide (l<r))),.greaterEqual⟩
  | .shiftLeft | .shiftRight | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply
  | .logicalAnd | .logicalOr => throw (IO.userError "not a strict Word operator")

private def invoke (fs : Syntax.Expr) (made : RuntimeValue) (argument other : Core.Word)
    (s : List RuntimeValue) (src : Syntax.Expr)
    (createdEq : made=.sourceClosure fs savedOwner savedNames (savedRows fs)) :
    IO (Trace caller names (rows made argument other) s src) := do
  match lambda : fs, callShape : src with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred ⟨ps,"p"⟩⟩]⟩ none ⟨bs,[⟨rs,.returnStmt (some ⟨es,.identifier ⟨ns,"p"⟩⟩)⟩]⟩⟩,
      ⟨cs,.call ⟨fs0,.identifier ⟨fn,"picked"⟩⟩ ⟨args,[⟨as0,.identifier ⟨an,"p"⟩⟩]⟩⟩ =>
    let body : Syntax.Block := ⟨bs,[⟨rs,.returnStmt (some ⟨es,.identifier ⟨ns,"p"⟩⟩)⟩]⟩
    have shape : SourceUnaryLambdaShape fs ⟨ps,"p"⟩ body := by rw [lambda]; exact .inferred
    have fetchedOriginal : ClosedSourceExpressionEvaluates caller names (rows made argument other) s
        ⟨fs0,.identifier ⟨fn,"picked"⟩⟩ made s := .reference .head .head
    let fetched ← observe 1 fetchedOriginal
    match fetchedShape : fetched.value with
    | .sourceClosure actualSource actualOwner actualNames actualRows =>
      have fetchedEq := (fetched.original.deterministic fetchedOriginal).1
      have fields := RuntimeValue.sourceClosure.inj (show RuntimeValue.sourceClosure actualSource actualOwner actualNames actualRows =
          .sourceClosure fs savedOwner savedNames (savedRows fs) from by rw [← fetchedShape]; exact fetchedEq.trans createdEq)
      proof fields
      check (actualSource==fs && actualOwner==savedOwner && actualOwner != caller && actualNames==savedNames &&
        reprStr actualRows==reprStr (savedRows fs)) "all returned closure fields and foreign saved owner"
      have returnedShape : SourceUnaryLambdaShape actualSource ⟨ps,"p"⟩ body := by rw [fields.1]; exact shape
      have argumentOriginal : ClosedSourceExpressionEvaluates caller names (rows made argument other) fetched.final
          ⟨as0,.identifier ⟨an,"p"⟩⟩ (.word argument) fetched.final :=
        .reference (.tail (by change ("picked" : String) ≠ "p"; decide) .head) (.tail (by decide) .head)
      let actualArgument ← observe 1 argumentOriginal
      let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
      have bodyOriginal : ClosedSourceBodyEvaluates actualOwner (("p",fresh)::actualNames)
          ((fresh,actualArgument.value)::actualRows) actualArgument.final body actualArgument.value actualArgument.final :=
        .expression (.reference .head .head)
      let actualBody ← observeBody bodyOriginal
      check (fresh.owner==actualOwner && fresh==sid 3) "fresh saved parameter shadows old opaque p"
      have callOriginal : ClosedSourceExpressionEvaluates caller names (rows made argument other) s src actualBody.value actualBody.final := by
        rw [callShape]
        exact .call returnedShape (by rw [← fetchedShape]; exact fetched.original) actualArgument.original actualBody.original
      have finalEq := actualBody.store_eq.trans (actualArgument.store_eq.trans fetched.store_eq)
      have complete : ClosedSourceExpressionEvaluates caller names (rows made argument other) s src actualBody.value s := by
        simpa only [finalEq] using callOriginal
      adjacent 3 complete
      observe 3 complete
    | _ => throw (IO.userError "actual saved closure expected")
  | _,_ => throw (IO.userError "exact original identity lambda and unary saved call")

private def otherReference (made : RuntimeValue) (argument other : Core.Word)
    (s : List RuntimeValue) (src : Syntax.Expr) : IO (Trace caller names (rows made argument other) s src) := do
  match shape : src with
  | ⟨es,.identifier ⟨ns,"other"⟩⟩ =>
    have original : ClosedSourceExpressionEvaluates caller names (rows made argument other) s src (.word other) s := by
      rw [shape]
      exact .reference (.tail (by change ("picked" : String) ≠ "other"; decide)
        (.tail (by change ("p" : String) ≠ "other"; decide) .head)) (.tail (by decide) (.tail (by decide) .head))
    observe 1 original
  | _ => throw (IO.userError "original other reference")

private def exercise (symbol : String) (op : Syntax.BinaryOp) (onLeft : Bool)
    (argument other : Core.Word) (s : List RuntimeValue) : IO Unit := do
  let lf := file "strict-word-saved-lambda.sol" "lam(p){return p;}"
  let fs ← parsed lf (expectedLambda lf)
  let f := file "strict-word-saved-call.sol" (if onLeft then "picked(p) "++symbol++" other" else "other "++symbol++" picked(p)")
  let src ← parsed f (expectedBinary f onLeft symbol op)
  match lambda : fs with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred name⟩]⟩ none body⟩ =>
    have shape : SourceUnaryLambdaShape fs name body := by rw [lambda]; exact .inferred
    have creation : ClosedSourceExpressionEvaluates savedOwner savedNames (savedRows fs) s fs
        (.sourceClosure fs savedOwner savedNames (savedRows fs)) s := .creation shape
    adjacent 1 creation
    let made ← observe 1 creation
    have createdEq := (made.original.deterministic creation).1
    match outer : src with
    | ⟨span,.binary left ⟨operatorSpan,actualOp⟩ right⟩ =>
      if opEq : actualOp=op then
        let l ← if onLeft then invoke fs made.value argument other made.final left createdEq
          else otherReference made.value argument other made.final left
        let r ← if onLeft then otherReference made.value argument other l.final right
          else invoke fs made.value argument other l.final right createdEq
        match lv : l.value, rv : r.value with
        | .word lw,.word rw =>
          let m ← meaning actualOp lw rw
          have leftOriginal : ClosedSourceExpressionEvaluates caller names (rows made.value argument other) made.final left (.word lw) l.final := by
            rw [← lv]; exact l.original
          have rightOriginal : ClosedSourceExpressionEvaluates caller names (rows made.value argument other) l.final right (.word rw) r.final := by
            rw [← rv]; exact r.original
          have original : ClosedSourceExpressionEvaluates caller names (rows made.value argument other) made.final src (RuntimeValue.ofCore m.val) r.final := by
            rw [outer]; exact .strictWordBinary leftOriginal rightOriginal m.property
          proof original
          have decomposition := closedSourceExpressionEvaluates_strictWordBinary_iff
            (value:=RuntimeValue.ofCore m.val) (span:=span) (operatorSpan:=operatorSpan)
            m.property.operator_is_strict.1 m.property.operator_is_strict.2
          proof (decomposition.mp (by simpa only [outer] using original))
          proof (decomposition.mpr ⟨lw,rw,m.val,l.final,rfl,leftOriginal,rightOriginal,m.property⟩)
          have finalEq := r.store_eq.trans l.store_eq
          adjacent 4 (show ClosedSourceExpressionEvaluates caller names (rows made.value argument other) made.final src (RuntimeValue.ofCore m.val) made.final from by
            simpa only [finalEq] using original)
          check (lw==(if onLeft then argument else other) && rw==(if onLeft then other else argument)) "actual operand order"
        | _,_ => throw (IO.userError "strict operands must be actual Words")
      else throw (IO.userError "original operator differs from explicit spelling")
    | _ => throw (IO.userError "original binary AST")
  | _ => throw (IO.userError "original unary lambda AST")
end Tests.ParsedClosedStrictWordSavedCalls
open Tests.ParsedClosedStrictWordSavedCalls in
def Tests.frontendParsedClosedStrictWordSavedCallsTests : IO Unit := do
  let operations : List (String × Solcore.Syntax.BinaryOp) :=
    [("+",.add),("-",.subtract),("*",.multiply),("/",.divide),("%",.modulo),("&",.bitAnd),("|",.bitOr),
     ("^",.bitXor),(">",.greater),("<",.less),("==",.equal),("!=",.notEqual),("<=",.lessEqual),(">=",.greaterEqual)]
  for (symbol,op) in operations do
    for onLeft in [false,true] do
      exercise symbol op onLeft Solcore.Core.Word.maximum (Solcore.Core.Word.ofNatModulo 1) []
      exercise symbol op onLeft Solcore.Core.Word.zero (Solcore.Core.Word.ofNatModulo 7)
        [old,.hostFunction .storageWrite,.cellRef .word 900,.unit]
end
