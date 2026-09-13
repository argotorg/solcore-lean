import Solcore.Frontend.ClosedSourceDataDepthDecisionProperties
import Solcore.Test.FrontendClosedStrictWordBinarySymbolicProperties

/- Independent original witnesses precede every new bounded-search law.
Arbitrary mixed values, first-match rows, source ranges and whole stores stay literal. -/
set_option autoImplicit false
namespace Tests.DataDepthSymbolic
open Solcore Solcore.Frontend

private def groups (span : Syntax.SourceSpan) : Nat → Syntax.Expr → Syntax.Expr
  | 0, source => source
  | n + 1, source => ⟨span, .group (groups span n source)⟩
private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .identifier name⟩
private def tupleSource (span tupleSpan : Syntax.SourceSpan) (child : Syntax.Expr) (n : Nat) : Syntax.Expr :=
  ⟨span, .tuple ⟨tupleSpan, List.replicate (n + 2) child⟩⟩
private def tupleValue (value : RuntimeValue) : Nat → RuntimeValue
  | 0 => .pair value value
  | n + 1 => .pair value (tupleValue value n)

private theorem groups_bound (span : Syntax.SourceSpan) (n : Nat) (source : Syntax.Expr) :
    closedSourceDataDepthBound (groups span n source) = closedSourceDataDepthBound source + n := by
  induction n with
  | zero => simp only [groups, Nat.add_zero]
  | succ n ih => simp only [groups, closedSourceDataDepthBound, ih]; omega

private theorem groups_syntax {source : Syntax.Expr} (admitted : ClosedSourceDataExpression source)
    (span : Syntax.SourceSpan) (n : Nat) : ClosedSourceDataExpression (groups span n source) := by
  induction n with
  | zero => exact admitted
  | succ _ ih => exact .group ih

private theorem groups_original {owner names captured initialStore finalStore source value}
    (original : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore)
    (span : Syntax.SourceSpan) (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured initialStore (groups span n source) value finalStore := by
  induction n with
  | zero => exact original
  | succ _ ih => exact .group ih

private theorem groups_before (span : Syntax.SourceSpan) (n budget : Nat) (source : Syntax.Expr)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (small : budget ≤ n) :
    evaluateClosedSourceExpression? budget owner names captured store (groups span n source) = none := by
  induction n generalizing budget with
  | zero =>
      have same : budget = 0 := by omega
      subst budget
      simp only [evaluateClosedSourceExpression?]
  | succ n ih =>
      cases budget with
      | zero => simp only [evaluateClosedSourceExpression?]
      | succ budget => simpa only [groups, evaluateClosedSourceExpression?] using ih budget (by omega)

private theorem tuple_bound (span tupleSpan : Syntax.SourceSpan) (child : Syntax.Expr) (n : Nat) :
    closedSourceDataDepthBound (tupleSource span tupleSpan child n) =
      closedSourceDataDepthBound child + n + 1 := by
  induction n with
  | zero => simp only [tupleSource, List.replicate_succ, List.replicate_zero,
      closedSourceDataDepthBound, Nat.max_self, Nat.add_zero]
  | succ n ih =>
      change closedSourceDataDepthBound
        ⟨span, .tuple ⟨tupleSpan, child :: child :: child :: List.replicate n child⟩⟩ = _
      rw [closedSourceDataDepthBound]
      change max (closedSourceDataDepthBound child)
        (closedSourceDataDepthBound (tupleSource span tupleSpan child n)) + 1 = _
      rw [ih]; omega

private theorem tuple_original {owner names captured store child value}
    (original : ClosedSourceExpressionEvaluates owner names captured store child value store)
    (span tupleSpan : Syntax.SourceSpan) (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured store
      (tupleSource span tupleSpan child n) (tupleValue value n) store := by
  induction n with
  | zero => exact .pair original original
  | succ n ih => exact .many original ih

private theorem tuple_syntax {child : Syntax.Expr} (admitted : ClosedSourceDataExpression child)
    (span tupleSpan : Syntax.SourceSpan) (n : Nat) :
    ClosedSourceDataExpression (tupleSource span tupleSpan child n) := by
  induction n with
  | zero => exact .pair admitted admitted
  | succ _ ih => exact .many admitted ih

private theorem tuple_before (span tupleSpan groupSpan : Syntax.SourceSpan) (n k budget : Nat)
    (source : Syntax.Expr) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (small : budget ≤ n + k + 1) :
    evaluateClosedSourceExpression? budget owner names captured store
      (tupleSource span tupleSpan (groups groupSpan k source) n) = none := by
  induction n generalizing budget store with
  | zero =>
      cases budget with
      | zero => simp only [evaluateClosedSourceExpression?]
      | succ budget =>
          have absent := groups_before groupSpan k budget source owner names captured store (by omega)
          simp only [tupleSource, List.replicate_succ, List.replicate_zero,
            evaluateClosedSourceExpression?, absent, bind, Option.bind_none]
  | succ n ih =>
      cases budget with
      | zero => simp only [evaluateClosedSourceExpression?]
      | succ budget =>
          cases head : evaluateClosedSourceExpression? budget owner names captured store
              (groups groupSpan k source) with
          | none => simp only [tupleSource, List.replicate_succ,
              evaluateClosedSourceExpression?, head, bind, Option.bind_none]
          | some endpoint =>
              obtain ⟨headValue, middleStore⟩ := endpoint
              have tail := ih budget middleStore (by omega)
              simp only [tupleSource, List.replicate_succ] at tail
              simp only [tupleSource, List.replicate_succ,
                evaluateClosedSourceExpression?, head, bind, Option.bind_some, tail, Option.bind_none]

/-- Every group depth and original tuple arity has a sharp source-depth boundary. -/
theorem groups_and_original_many_tuples (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (spans : Fin 4 → Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (value : RuntimeValue) (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) (n k extra : Nat) :
    let leaf := groups (spans 0) k (reference (spans 1) name)
    let source := tupleSource (spans 2) (spans 3) leaf n
    ClosedSourceExpressionEvaluates owner names captured store leaf value store ∧
    ClosedSourceExpressionEvaluates owner names captured store source (tupleValue value n) store ∧
    closedSourceDataDepthBound leaf = k + 1 ∧ closedSourceDataDepthBound source = n + k + 2 ∧
    evaluateClosedSourceExpression? k owner names captured store leaf = none ∧
    evaluateClosedSourceExpression? (n + k + 1) owner names captured store source = none ∧
    evaluateClosedSourceExpression? (k + 1) owner names captured store leaf = some (value, store) ∧
    evaluateClosedSourceExpression? (n + k + 2) owner names captured store source = some (tupleValue value n, store) ∧
    evaluateClosedSourceExpression? (n + k + 2 + extra) owner names captured store source =
      some (tupleValue value n, store) := by
  dsimp only
  have original : ClosedSourceExpressionEvaluates owner names captured store
      (groups (spans 0) k (reference (spans 1) name)) value store :=
    groups_original (.reference named found) (spans 0) k
  have whole := tuple_original original (spans 2) (spans 3) n
  have leafGate := groups_syntax (ClosedSourceDataExpression.reference (span := spans 1) (name := name)) (spans 0) k
  have gate := tuple_syntax leafGate (spans 2) (spans 3) n
  have leafBound : closedSourceDataDepthBound (groups (spans 0) k (reference (spans 1) name)) = k + 1 := by
    rw [groups_bound]; simp only [reference, closedSourceDataDepthBound]; omega
  have wholeBound : closedSourceDataDepthBound
      (tupleSource (spans 2) (spans 3) (groups (spans 0) k (reference (spans 1) name)) n) = n + k + 2 := by
    rw [tuple_bound, leafBound]; omega
  simp only [reference] at leafBound wholeBound
  refine ⟨original, whole, leafBound, wholeBound, groups_before _ _ _ _ _ _ _ _ (Nat.le_refl _),
    tuple_before _ _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _),
    leafGate.evaluates_at_depthBound original (by omega),
    gate.evaluates_at_depthBound whole (by omega), gate.evaluates_at_depthBound whole (by omega)⟩

private def outcomes (left right : Core.Word) : List (Syntax.BinaryOp × Core.Value) :=
  [(.add, .word (left.add right)), (.subtract, .word (left.sub right)),
   (.multiply, .word (left.mul right)), (.divide, .word (left.udiv right)),
   (.modulo, .word (left.umod right)), (.bitAnd, .word (left.bitAnd right)),
   (.bitOr, .word (left.bitOr right)), (.bitXor, .word (left.bitXor right)),
   (.greater, .bool (decide (left > right))), (.less, .bool (decide (left < right))),
   (.equal, .bool (left == right)), (.notEqual, .bool (!(left == right))),
   (.lessEqual, .bool (!(decide (left > right)))), (.greaterEqual, .bool (!(decide (left < right))))]

/-- All fourteen independent old original witnesses consume the new bound and actual-output iff. -/
theorem all_fourteen_strict_at_bound (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (spans : Fin 4 → Syntax.SourceSpan) (leftName rightName : Syntax.Identifier)
    (leftId rightId : Resolved.LocalId) (leftWord rightWord : Core.Word)
    (leftNamed : LocalNameTable.Lookup names leftName.value leftId)
    (rightNamed : LocalNameTable.Lookup names rightName.value rightId)
    (leftFound : Resolved.LocalScope.Lookup captured leftId (.word leftWord))
    (rightFound : Resolved.LocalScope.Lookup captured rightId (.word rightWord)) :
    ∀ operator result, (operator, result) ∈ outcomes leftWord rightWord →
    let source : Syntax.Expr := ⟨spans 0, .binary (reference (spans 2) leftName) ⟨spans 1, operator⟩
      (reference (spans 3) rightName)⟩
    ClosedSourceExpressionEvaluates owner names captured store source (RuntimeValue.ofCore result) store ∧
    closedSourceDataDepthBound source = 2 ∧
    (∀ extra, evaluateClosedSourceExpression? (2 + extra) owner names captured store source =
      some (RuntimeValue.ofCore result, store)) ∧
    (∀ actual final extra, evaluateClosedSourceExpression? (2 + extra) owner names captured store source =
      some (actual, final) ↔ actual = RuntimeValue.ofCore result ∧ final = store) := by
  intro operator result member source
  obtain ⟨original, exactResult, gate⟩ := ClosedStrictWordBinarySymbolic.all_fourteen_original_and_exact_actual_results
    owner names captured store spans leftName rightName leftId rightId leftWord rightWord
    leftNamed rightNamed leftFound rightFound operator result member
  have bound : closedSourceDataDepthBound source = 2 := by
    simp only [source, reference, closedSourceDataDepthBound, Nat.max_self]
  refine ⟨original, bound, ?_, ?_⟩
  · intro extra; exact gate.evaluates_at_depthBound original (by change closedSourceDataDepthBound source ≤ _; omega)
  · intro actual final extra
    exact (gate.evaluate_at_depthBound_iff (by change closedSourceDataDepthBound source ≤ _; omega)).trans
      (exactResult actual final)

private def short (span operatorSpan : Syntax.SourceSpan) (useOr : Bool) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .binary left ⟨operatorSpan, if useOr then .logicalOr else .logicalAnd⟩ right⟩

/-- Selected right values can be arbitrary mixed payloads, with every actual endpoint retained. -/
theorem selected_short_circuit_mixed_values (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (spans : Fin 4 → Syntax.SourceSpan) (leftName rightName : Syntax.Identifier)
    (leftId rightId : Resolved.LocalId) (useOr : Bool) (value : RuntimeValue)
    (leftNamed : LocalNameTable.Lookup names leftName.value leftId)
    (rightNamed : LocalNameTable.Lookup names rightName.value rightId)
    (leftFound : Resolved.LocalScope.Lookup captured leftId (.bool (!useOr)))
    (rightFound : Resolved.LocalScope.Lookup captured rightId value) :
    let source := short (spans 0) (spans 1) useOr (reference (spans 2) leftName) (reference (spans 3) rightName)
    ClosedSourceExpressionEvaluates owner names captured store source value store ∧
    (∀ actual final extra, evaluateClosedSourceExpression? (2 + extra) owner names captured store source =
      some (actual, final) ↔ actual = value ∧ final = store) := by
  intro source
  have left : ClosedSourceExpressionEvaluates owner names captured store
      (reference (spans 2) leftName) (.bool (!useOr)) store := .reference leftNamed leftFound
  have right : ClosedSourceExpressionEvaluates owner names captured store
      (reference (spans 3) rightName) value store := .reference rightNamed rightFound
  have original : ClosedSourceExpressionEvaluates owner names captured store source value store := by
    cases useOr with
    | false => exact .andTrue left right
    | true => exact .orFalse left right
  have gate : ClosedSourceDataExpression source := by
    cases useOr with
    | false => exact .logicalAnd .reference .reference
    | true => exact .logicalOr .reference .reference
  have bound : closedSourceDataDepthBound source = 2 := by
    simp only [source, short, reference, closedSourceDataDepthBound, Nat.max_self]
  refine ⟨original, ?_⟩
  intro actual final extra
  rw [gate.evaluate_at_depthBound_iff (by omega : closedSourceDataDepthBound source ≤ 2 + extra)]
  exact ⟨fun result => result.deterministic original, fun ⟨rfl, rfl⟩ => original⟩

/-- Arbitrarily deep unvisited string data increases the bound, not the necessary depth. -/
theorem skipped_deep_data_bound_is_not_minimal (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (spans : Fin 5 → Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (useOr : Bool) (spelling : String) (n extra : Nat)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool useOr)) :
    let ignored := groups (spans 3) (n + 1) ⟨spans 4, .literal ⟨spans 4, .string spelling⟩⟩
    let source := short (spans 0) (spans 1) useOr (reference (spans 2) name) ignored
    ClosedSourceDataExpression source ∧ closedSourceDataDepthBound source = n + 3 ∧
    ClosedSourceExpressionEvaluates owner names captured store source (.bool useOr) store ∧
    evaluateClosedSourceExpression? 2 owner names captured store source = some (.bool useOr, store) ∧
    evaluateClosedSourceExpression? (closedSourceDataDepthBound source - 1)
      owner names captured store source = some (.bool useOr, store) ∧
    evaluateClosedSourceExpression? (closedSourceDataDepthBound source + extra)
      owner names captured store source = some (.bool useOr, store) := by
  intro ignored source
  have left : ClosedSourceExpressionEvaluates owner names captured store
      (reference (spans 2) name) (.bool useOr) store := .reference named found
  have original : ClosedSourceExpressionEvaluates owner names captured store source (.bool useOr) store := by
    cases useOr with
    | false => exact .andFalse left
    | true => exact .orTrue left
  have ignoredGate : ClosedSourceDataExpression ignored := groups_syntax .literal _ _
  have gate : ClosedSourceDataExpression source := by
    cases useOr with
    | false => exact .logicalAnd .reference ignoredGate
    | true => exact .logicalOr .reference ignoredGate
  have bound : closedSourceDataDepthBound source = n + 3 := by
    dsimp only [source, short]; rw [closedSourceDataDepthBound]
    simp only [reference, closedSourceDataDepthBound, ignored, groups_bound]; omega
  have early : evaluateClosedSourceExpression? 2 owner names captured store source = some (.bool useOr, store) := by
    cases useOr <;> simp only [source, short, reference, Bool.false_eq_true, ↓reduceIte,
      evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
      Resolved.LocalScope.lookup?_iff.mpr found, bind, Option.bind_some, pure]
  exact ⟨gate, bound, original, early, evaluateClosedSourceExpression?_monotone (by omega) early,
    gate.evaluates_at_depthBound original (by omega)⟩

end Tests.DataDepthSymbolic
