import Solcore.Frontend.LocalInputsExtensionProperties

/-! ADR-0159 consumers distinguish Boolean checking from selected-value raw
evaluation, and fixed internal constants from caller-controlled spellings. -/

set_option autoImplicit false

namespace Tests.FrontendLocalShortCircuit

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ShortCircuit", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "short-circuit.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def andE (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .logicalAnd⟩ right⟩
private def orE (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .logicalOr⟩ right⟩
private def pair (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "r" rightType right rightTyped).bindFresh owner "l" leftType left leftTyped
private def inputs (left right : Bool) : LocalInputs := pair .bool .bool (.bool left) (.bool right) .bool .bool
private theorem names_ne : "l" ≠ "r" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private def andSource : Syntax.Expr := andE (ref "l") (ref "r")
private def orSource : Syntax.Expr := orE (ref "l") (ref "r")
private def andCore : Core.Expr := .ifE (.var 0) (.var 1) (.bool false)
private def orCore : Core.Expr := .ifE (.var 0) (.bool true) (.var 1)
private theorem checked_and (left right : Bool) : (inputs left right).check? andSource = some (andCore, .bool) :=
  elaborateLocalExpression?_complete (.logicalAnd (.identifier .head) (.identifier (.tail names_ne .head)))
    (.ifE (.var .head) (.var (.tail ids_ne .head)) .bool)
    (.ifE (.var .head) (.var (.tail ids_ne .head)) .bool)
private theorem checked_or (left right : Bool) : (inputs left right).check? orSource = some (orCore, .bool) :=
  elaborateLocalExpression?_complete (.logicalOr (.identifier .head) (.identifier (.tail names_ne .head)))
    (.ifE (.var .head) .bool (.var (.tail ids_ne .head)))
    (.ifE (.var .head) .bool (.var (.tail ids_ne .head)))

theorem all_boolean_pairs_have_exact_checked_expansions (left right : Bool) :
    (inputs left right).check? andSource = some (andCore, .bool) ∧
    (inputs left right).check? orSource = some (orCore, .bool) :=
  ⟨checked_and left right, checked_or left right⟩

theorem all_boolean_pairs_have_exact_source_and_core_values (left right : Bool) (store : Core.Store) :
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment store andSource (.bool (left && right)) store ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment store orSource (.bool (left || right)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs left right).environment) store andCore (.bool (left && right)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs left right).environment) store orCore (.bool (left || right)) store := by
  have conjunction : LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store andSource (.bool (left && right)) store := by
    cases left
    · exact .andFalse (.identifier .head .head)
    · exact .andTrue (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head))
  have disjunction : LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store orSource (.bool (left || right)) store := by
    cases left
    · exact .orFalse (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head))
    · exact .orTrue (.identifier .head .head)
  exact ⟨conjunction, disjunction,
    (elaborateLocalExpression?_evaluates_iff (checked_and left right) (inputs left right).sameIds).mp conjunction,
    (elaborateLocalExpression?_evaluates_iff (checked_or left right) (inputs left right).sameIds).mp disjunction⟩

private def payload : Core.Value := .word (Core.Word.ofNatModulo 7)
private def leftBad : LocalInputs := pair .word .bool payload (.bool true) .word .bool
private def rightBad (left : Bool) : LocalInputs := pair .bool .word (.bool left) payload .bool .word

theorem non_boolean_left_has_neither_checked_nor_raw_result (store : Core.Store) :
    leftBad.check? andSource = none ∧ leftBad.check? orSource = none ∧
    ∀ value finalStore, (¬ LocalExpressionEvaluates leftBad.names leftBad.environment store andSource value finalStore) ∧
      (¬ LocalExpressionEvaluates leftBad.names leftBad.environment store orSource value finalStore) := by
  have typed : LocalExpressionHasType leftBad.names leftBad.context (ref "l") .word := .identifier .head .head
  have evaluated : LocalExpressionEvaluates leftBad.names leftBad.environment store (ref "l") payload store :=
    .identifier .head .head
  refine ⟨?_, ?_, ?_⟩
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    cases typing with | logicalAnd left _ => cases typed.type_unique left
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    cases typing with | logicalOr left _ => cases typed.type_unique left
  · intro value finalStore
    constructor <;> intro evaluation
    · cases evaluation with
      | andTrue left _ | andFalse left => cases (evaluated.deterministic left).1
    · cases evaluation with
      | orTrue left | orFalse left _ => cases (evaluated.deterministic left).1

theorem selected_non_boolean_right_is_forwarded_only_at_the_raw_boundary (left : Bool) (store : Core.Store) :
    (rightBad left).check? andSource = none ∧ (rightBad left).check? orSource = none ∧
    LocalExpressionEvaluates (rightBad true).names (rightBad true).environment store andSource payload store ∧
    LocalExpressionEvaluates (rightBad false).names (rightBad false).environment store orSource payload store ∧
    Core.Evaluates (Resolved.LocalScope.values (rightBad true).environment) store andCore payload store ∧
    Core.Evaluates (Resolved.LocalScope.values (rightBad false).environment) store orCore payload store := by
  have typed : LocalExpressionHasType (rightBad left).names (rightBad left).context (ref "r") .word :=
    .identifier (.tail names_ne .head) (.tail ids_ne .head)
  refine ⟨?_, ?_, .andTrue (.identifier .head .head)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)),
    .orFalse (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head)),
    .ifTrue (.var rfl) (.var rfl), .ifFalse (.var rfl) (.var rfl)⟩
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    cases typing with | logicalAnd _ right => cases typed.type_unique right
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    cases typing with | logicalOr _ right => cases typed.type_unique right

private def unsupported : Syntax.Expr := ⟨span, .literal ⟨span, .string "7"⟩⟩
private def badRights : List Syntax.Expr := [ref "missing", unsupported]
private theorem bad_resolutions (right : Syntax.Expr) (member : right ∈ badRights) :
    resolveLocalExpression? (inputs false true).names (andE (ref "l") right) = none ∧
    resolveLocalExpression? (inputs true false).names (orE (ref "l") right) = none := by
  simp only [badRights, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals constructor <;> simp [resolveLocalExpression?, andE, orE, ref, unsupported,
    interpretWordLiteral?, numericLiteralValue?,
    inputs, pair, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

theorem skipped_missing_or_unsupported_right_still_fails_whole_checking (store : Core.Store) :
    ∀ right ∈ badRights,
      LocalExpressionEvaluates (inputs false true).names (inputs false true).environment store
        (andE (ref "l") right) (.bool false) store ∧
      LocalExpressionEvaluates (inputs true false).names (inputs true false).environment store
        (orE (ref "l") right) (.bool true) store ∧
      resolveLocalExpression? (inputs false true).names (andE (ref "l") right) = none ∧
      resolveLocalExpression? (inputs true false).names (orE (ref "l") right) = none ∧
      (inputs false true).check? (andE (ref "l") right) = none ∧
      (inputs true false).check? (orE (ref "l") right) = none := by
  intro right member
  obtain ⟨andRejected, orRejected⟩ := bad_resolutions right member
  refine ⟨.andFalse (.identifier .head .head), .orTrue (.identifier .head .head),
    andRejected, orRejected, ?_, ?_⟩
  · simp [LocalInputs.check?, elaborateLocalExpression?, andRejected]
  · simp [LocalInputs.check?, elaborateLocalExpression?, orRejected]

private def neg (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ operand⟩
private def nestedRight : Syntax.Expr := ⟨span, .group (neg (neg (ref "r")))⟩
private def nestedSource (isOr : Bool) : Syntax.Expr :=
  if isOr then orE (ref "l") nestedRight else andE (ref "l") nestedRight
private def nestedCore (isOr : Bool) : Core.Expr :=
  let right := Core.Expr.unary .boolNot (.unary .boolNot (.var 1))
  if isOr then .ifE (.var 0) (.bool true) right else .ifE (.var 0) right (.bool false)
private theorem checked_nested (isOr left right : Bool) :
    (inputs left right).check? (nestedSource isOr) = some (nestedCore isOr, .bool) := by
  cases isOr
  · exact elaborateLocalExpression?_complete
      (.logicalAnd (.identifier .head) (.group (.logicalNot (.logicalNot (.identifier (.tail names_ne .head))))))
      (.ifE (.var .head) (.unary (.unary (.var (.tail ids_ne .head)))) .bool)
      (.ifE (.var .head) (.unary (.unary (.var (.tail ids_ne .head)))) .bool)
  · exact elaborateLocalExpression?_complete
      (.logicalOr (.identifier .head) (.group (.logicalNot (.logicalNot (.identifier (.tail names_ne .head))))))
      (.ifE (.var .head) .bool (.unary (.unary (.var (.tail ids_ne .head)))))
      (.ifE (.var .head) .bool (.unary (.unary (.var (.tail ids_ne .head)))))

theorem skipped_and_selected_nested_right_have_different_exact_fuel
    (isOr right : Bool) (store : Core.Store) :
    (inputs isOr right).run? 3 (nestedSource isOr) store = some (.bool, .outOfFuel
      (Core.State.initial (.bool isOr) (Resolved.LocalScope.values (inputs isOr right).environment) store)) ∧
    (inputs isOr right).run? 4 (nestedSource isOr) store = some (.bool, .done (.bool isOr) store) ∧
    (inputs (!isOr) right).run? 7 (nestedSource isOr) store =
      some (.bool, .outOfFuel ⟨.ret (.bool (!right)), [.unaryApply .boolNot], store⟩) ∧
    ∀ extra, (inputs (!isOr) right).run? (extra + 8) (nestedSource isOr) store =
      some (.bool, .done (.bool right) store) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LocalInputs.run?, checked_nested]; cases isOr <;> rfl
  · rw [LocalInputs.run?, checked_nested]; cases isOr <;> rfl
  · rw [LocalInputs.run?, checked_nested]; cases isOr <;> rfl
  · intro extra
    rw [LocalInputs.run?, checked_nested]
    change some (Core.Ty.bool, Core.runStateful (extra + 8)
      (Core.State.initial (nestedCore isOr) [.bool (!isOr), .bool right] store)) = _
    cases isOr <;> simp [Core.runStateful, Core.State.initial, Core.advance, nestedCore, Core.UnaryOp.apply]

private def baseSource (isOr : Bool) : Syntax.Expr := if isOr then orSource else andSource
private def baseCore (isOr : Bool) : Core.Expr := if isOr then orCore else andCore
private theorem checked_base (isOr left right : Bool) :
    (inputs left right).check? (baseSource isOr) = some (baseCore isOr, .bool) := by
  cases isOr
  · exact checked_and left right
  · exact checked_or left right
private theorem avoids_base (isOr : Bool) (name : String) (left : name ≠ "l") (right : name ≠ "r") :
    AvoidsLocalName name (baseSource isOr) := by
  cases isOr
  · exact .logicalAnd (.identifier left) (.identifier right)
  · exact .logicalOr (.identifier left) (.identifier right)
private def reversed (left right : Bool) : LocalInputs :=
  ((inputs left right).bindFresh owner "false" .bool (.bool true) .bool).bindFresh
    owner "true" .bool (.bool false) .bool
private def reversedCore (isOr : Bool) : Core.Expr :=
  if isOr then .ifE (.var 2) (.bool true) (.var 3) else .ifE (.var 2) (.var 3) (.bool false)
private theorem checked_reversed (isOr left right : Bool) :
    (reversed left right).check? (baseSource isOr) = some (reversedCore isOr, .bool) := by
  have first := (avoids_base isOr "false" (by decide) (by decide)).check_bindFresh_complete
    (inputs left right) owner .bool (.bool true) .bool (checked_base isOr left right)
  have second := (avoids_base isOr "true" (by decide) (by decide)).check_bindFresh_complete
    ((inputs left right).bindFresh owner "false" .bool (.bool true) .bool) owner .bool (.bool false) .bool first
  cases isOr <;> simpa [reversed, reversedCore, baseCore, andCore, orCore, Core.Expr.weakenAt] using second

theorem caller_reversed_spellings_cannot_change_inserted_constants (isOr right : Bool) (store : Core.Store) :
    LocalExpressionEvaluates (reversed isOr right).names (reversed isOr right).environment store (ref "true") (.bool false) store ∧
    LocalExpressionEvaluates (reversed isOr right).names (reversed isOr right).environment store (ref "false") (.bool true) store ∧
    (reversed isOr right).check? (baseSource isOr) = some (reversedCore isOr, .bool) ∧
    (reversed isOr right).run? 4 (baseSource isOr) store = some (.bool, .done (.bool isOr) store) := by
  refine ⟨.identifier .head .head, .identifier (.tail ?_ .head) (.tail ?_ .head),
    checked_reversed isOr isOr right, ?_⟩
  · change "true" ≠ "false"; decide
  · change (⟨owner, 3⟩ : Resolved.LocalId) ≠ ⟨owner, 2⟩; decide
  · rw [LocalInputs.run?, checked_reversed]; cases isOr <;> rfl

private def extended (left right : Bool) : LocalInputs := (inputs left right).bindFresh owner "extra" .unit .unit .unit

theorem unused_name_insertion_preserves_short_circuiting (isOr left right : Bool) (value : Core.Value)
    (initialStore finalStore : Core.Store) :
    (extended left right).check? (baseSource isOr) = some ((baseCore isOr).weakenAt 0, .bool) ∧
    (LocalExpressionEvaluates (extended left right).names (extended left right).environment
      initialStore (baseSource isOr) value finalStore ↔
      LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
        initialStore (baseSource isOr) value finalStore) ∧
    ((∃ fuel, (extended left right).run? fuel (baseSource isOr) initialStore = some (.bool, .done value finalStore)) ↔
      ∃ fuel, (inputs left right).run? fuel (baseSource isOr) initialStore = some (.bool, .done value finalStore)) := by
  have avoids := avoids_base isOr "extra" (by decide) (by decide)
  exact ⟨avoids.check_bindFresh_complete (inputs left right) owner .unit .unit .unit (checked_base isOr left right),
    avoids.bindFresh_evaluates_iff (inputs left right) owner .unit .unit .unit,
    avoids.bindFresh_run_done_iff (inputs left right) owner .unit .unit .unit⟩

end Tests.FrontendLocalShortCircuit
