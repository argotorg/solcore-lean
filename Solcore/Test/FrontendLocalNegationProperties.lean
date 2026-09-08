import Solcore.Frontend.LocalInputsExtensionProperties

/-! Boolean-only canonical negation: exact syntax, dynamic values, and fuel.
The spellings `true` and `false` remain ordinary caller-supplied names. -/

set_option autoImplicit false

namespace Tests.FrontendLocalNegation

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"Negation", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "negation.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def neg (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ operand⟩
private def group (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .group operand⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .conditional condition span left span right⟩
private def supplied (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "x" type value typed
private def inputs (choice : Bool) : LocalInputs := supplied .bool (.bool choice) .bool
private def source : Syntax.Expr := neg (ref "x")
private def twice : Syntax.Expr := neg source
private def core : Core.Expr := .unary .boolNot (.var 0)
private def twiceCore : Core.Expr := .unary .boolNot core

private theorem checked (choice : Bool) : (inputs choice).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete (.logicalNot (.identifier .head))
    (.unary (.var .head)) (.unary (.var .head))
private theorem checked_twice (choice : Bool) : (inputs choice).check? twice = some (twiceCore, .bool) :=
  elaborateLocalExpression?_complete (.logicalNot (.logicalNot (.identifier .head)))
    (.unary (.unary (.var .head))) (.unary (.unary (.var .head)))
private theorem evaluated (choice : Bool) (store : Core.Store) :
    LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store source (.bool (!choice)) store :=
  .logicalNot (.identifier .head .head)

theorem boolean_and_double_negation_have_exact_meanings (choice : Bool) (store : Core.Store) :
    (inputs choice).check? source = some (core, .bool) ∧
    (inputs choice).check? twice = some (twiceCore, .bool) ∧
    LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store source (.bool (!choice)) store ∧
    LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store twice (.bool choice) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs choice).environment) store core (.bool (!choice)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs choice).environment) store twiceCore (.bool choice) store := by
  have double : LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store twice (.bool choice) store := by
    simpa [twice, neg] using LocalExpressionEvaluates.logicalNot (evaluated choice store)
  exact ⟨checked choice, checked_twice choice, evaluated choice store, double,
    (elaborateLocalExpression?_evaluates_iff (checked choice) (inputs choice).sameIds).mp (evaluated choice store),
    (elaborateLocalExpression?_evaluates_iff (checked_twice choice) (inputs choice).sameIds).mp double⟩

theorem exact_negation_fuel_is_a_present_typed_result (choice : Bool) (store : Core.Store) :
    (inputs choice).run? 2 source store =
      some (.bool, .outOfFuel ⟨.ret (.bool choice), [.unaryApply .boolNot], store⟩) ∧
    ∀ extra, (inputs choice).run? (extra + 3) source store = some (.bool, .done (.bool (!choice)) store) := by
  constructor
  · rw [LocalInputs.run?, checked]; rfl
  · intro extra
    rw [LocalInputs.run?, checked]
    change some (Core.Ty.bool, Core.runStateful (extra + 3)
      (Core.State.initial core [.bool choice] store)) = _
    simp [Core.runStateful, Core.State.initial, Core.advance, core, Core.UnaryOp.apply]

private def nested : Syntax.Expr := neg (group (branch source twice (group (ref "x"))))
private def nestedCore : Core.Expr := .unary .boolNot (.ifE core twiceCore (.var 0))
private theorem checked_nested (choice : Bool) : (inputs choice).check? nested = some (nestedCore, .bool) :=
  elaborateLocalExpression?_complete
    (.logicalNot (.group (.conditional (.logicalNot (.identifier .head))
      (.logicalNot (.logicalNot (.identifier .head))) (.group (.identifier .head)))))
    (.unary (.ifE (.unary (.var .head)) (.unary (.unary (.var .head))) (.var .head)))
    (.unary (.ifE (.unary (.var .head)) (.unary (.unary (.var .head))) (.var .head)))

theorem groups_and_conditionals_keep_exact_negation_core (choice : Bool) (store : Core.Store) :
    (inputs choice).check? nested = some (nestedCore, .bool) ∧
    LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store nested (.bool (!choice)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs choice).environment) store nestedCore (.bool (!choice)) store := by
  have raw : LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store nested (.bool (!choice)) store := by
    cases choice
    · exact .logicalNot (.group (.ifTrue (evaluated false store) (.logicalNot (evaluated false store))))
    · exact .logicalNot (.group (.ifFalse (evaluated true store) (.group (.identifier .head .head))))
  exact ⟨checked_nested choice, raw,
    (elaborateLocalExpression?_evaluates_iff (checked_nested choice) (inputs choice).sameIds).mp raw⟩

private def spellings : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "false" .bool (.bool true) .bool).bindFresh
    owner "true" .bool (.bool false) .bool

theorem true_and_false_spellings_still_use_supplied_values (store : Core.Store) :
    spellings.check? (neg (ref "true")) = some (.unary .boolNot (.var 0), .bool) ∧
    spellings.check? (neg (ref "false")) = some (.unary .boolNot (.var 1), .bool) ∧
    spellings.run? 3 (neg (ref "true")) store = some (.bool, .done (.bool true) store) ∧
    spellings.run? 3 (neg (ref "false")) store = some (.bool, .done (.bool false) store) := by
  have first : spellings.check? (neg (ref "true")) = some (.unary .boolNot (.var 0), .bool) :=
    elaborateLocalExpression?_complete (.logicalNot (.identifier .head))
      (.unary (.var .head)) (.unary (.var .head))
  have second : spellings.check? (neg (ref "false")) = some (.unary .boolNot (.var 1), .bool) :=
    elaborateLocalExpression?_complete (.logicalNot (.identifier (.tail (by decide) .head)))
      (.unary (.var (.tail (by decide) .head))) (.unary (.var (.tail (by decide) .head)))
  refine ⟨first, second, ?_, ?_⟩
  · rw [LocalInputs.run?, first]; rfl
  · rw [LocalInputs.run?, second]; rfl

private theorem non_boolean_rejected (type : Core.Ty) (value : Core.Value)
    (typed : Core.ValueHasType value type) (wrongType : type ≠ .bool)
    (wrongValue : ∀ flag, value ≠ .bool flag) (store : Core.Store) :
    (supplied type value typed).check? source = none ∧ ∀ result finalStore,
      ¬ LocalExpressionEvaluates (supplied type value typed).names (supplied type value typed).environment
        store source result finalStore := by
  constructor
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨resultType, typing⟩
    cases typing with
    | logicalNot operand =>
        have original : LocalExpressionHasType (supplied type value typed).names
            (supplied type value typed).context (ref "x") type := .identifier .head .head
        exact wrongType (original.type_unique operand)
  · intro result finalStore evaluation
    have original : LocalExpressionEvaluates (supplied type value typed).names
        (supplied type value typed).environment store (ref "x") value store := .identifier .head .head
    cases evaluation with
    | logicalNot operand => exact wrongValue _ (original.deterministic operand).1

private def wordInputs : LocalInputs := supplied .word (.word Core.Word.zero) .word
private def opaqueInputs (location : Nat) : LocalInputs := supplied (.cell .word) (.cellRef .word location) .cellRef

theorem word_and_opaque_operands_have_no_truthiness (location : Nat) (store : Core.Store) :
    wordInputs.check? source = none ∧ (opaqueInputs location).check? source = none ∧
    ∀ value finalStore, (¬ LocalExpressionEvaluates wordInputs.names wordInputs.environment store source value finalStore) ∧
      (¬ LocalExpressionEvaluates (opaqueInputs location).names (opaqueInputs location).environment
        store source value finalStore) := by
  have wordBad := non_boolean_rejected .word (.word Core.Word.zero) .word
    (by decide) (by intro flag same; cases same) store
  have opaqueBad := non_boolean_rejected (.cell .word) (.cellRef .word location) .cellRef
    (by decide) (by intro flag same; cases same) store
  exact ⟨wordBad.1, opaqueBad.1, fun value finalStore => ⟨wordBad.2 value finalStore, opaqueBad.2 value finalStore⟩⟩

private def bitNeg : Syntax.Expr := ⟨span, .unary ⟨span, .bitNot⟩ (ref "x")⟩

theorem bitwise_negation_remains_outside_this_adapter (choice : Bool) (store : Core.Store) :
    resolveLocalExpression? (inputs choice).names bitNeg = none ∧ (inputs choice).check? bitNeg = none ∧
    ∀ value finalStore, ¬ LocalExpressionEvaluates (inputs choice).names (inputs choice).environment
      store bitNeg value finalStore := by
  refine ⟨?_, ?_, ?_⟩
  · simp [resolveLocalExpression?, bitNeg]
  · simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, bitNeg]
  · intro value finalStore evaluation; cases evaluation

private def extended (choice : Bool) : LocalInputs := (inputs choice).bindFresh owner "extra" .unit .unit .unit

theorem unused_input_extension_preserves_negation (choice : Bool) (value : Core.Value)
    (initialStore finalStore : Core.Store) :
    (extended choice).check? source = some (.unary .boolNot (.var 1), .bool) ∧
    (LocalExpressionEvaluates (extended choice).names (extended choice).environment initialStore source value finalStore ↔
      LocalExpressionEvaluates (inputs choice).names (inputs choice).environment initialStore source value finalStore) ∧
    ((∃ fuel, (extended choice).run? fuel source initialStore = some (.bool, .done value finalStore)) ↔
      ∃ fuel, (inputs choice).run? fuel source initialStore = some (.bool, .done value finalStore)) := by
  have avoids : AvoidsLocalName "extra" source := .logicalNot (.identifier (by decide))
  refine ⟨?_, avoids.bindFresh_evaluates_iff (inputs choice) owner .unit .unit .unit,
    avoids.bindFresh_run_done_iff (inputs choice) owner .unit .unit .unit⟩
  simpa [extended, core, Core.Expr.weakenAt] using
    avoids.check_bindFresh_complete (inputs choice) owner .unit .unit .unit (checked choice)

end Tests.FrontendLocalNegation
