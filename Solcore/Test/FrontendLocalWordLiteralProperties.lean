import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.UnaryPrimitives

/-! ADR-0163: independent strict Word meanings feed the monomorphic expression
adapter. Checked execution still requires whole-expression type checking. -/

set_option autoImplicit false

namespace Tests.FrontendLocalWordLiteral

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"WordLiteral", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "literal-expressions.sol"⟩, 0, 1⟩
private def literal (payload : Syntax.CoreLiteralValue) : Syntax.CoreLiteral := ⟨span, payload⟩
private def source (payload : Syntax.CoreLiteralValue) : Syntax.Expr := ⟨span, .literal (literal payload)⟩
private def ref : Syntax.Expr := ⟨span, .identifier ⟨span, "c"⟩⟩
private def group (child : Syntax.Expr) : Syntax.Expr := ⟨span, .group child⟩
private def complement (child : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .bitNot⟩ child⟩
private def neg (child : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ child⟩
private def andE (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .logicalAnd⟩ right⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr := ⟨span, .conditional condition span left span right⟩
private def inputs (choice : Bool) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool
private def seven : Core.Word := ⟨7, by decide⟩
private def sevenSource : Syntax.Expr := source (.decimal "7")
private theorem sevenMeaning : WordLiteralDenotes (literal (.decimal "7")) seven :=
  NumericLiteralDenotes.decimal (by decide)
    (.cons (.decimal (digit := 7) (by decide) (by decide)) .nil)

private theorem checked_literal (supplied : LocalInputs) {value : Core.Word} {payload : Syntax.CoreLiteralValue}
    (meaning : WordLiteralDenotes (literal payload) value) :
    supplied.check? (source payload) = some (.word value, .word) :=
  elaborateLocalExpression?_complete (.wordLiteral meaning) .word .word
private theorem checked_seven (supplied : LocalInputs) : supplied.check? sevenSource = some (.word seven, .word) :=
  checked_literal supplied sevenMeaning

theorem independent_literal_meaning_has_exact_resolution_typing_and_evaluation
    (supplied : LocalInputs) (outer : Syntax.SourceSpan) (value : Core.Word)
    (written : Syntax.CoreLiteral) (meaning : WordLiteralDenotes written value) (store : Core.Store) :
    ResolvesLocalExpression supplied.names ⟨outer, .literal written⟩ (.word value) ∧
    LocalExpressionHasType supplied.names supplied.context ⟨outer, .literal written⟩ .word ∧
    LocalExpressionEvaluates supplied.names supplied.environment store ⟨outer, .literal written⟩ (.word value) store ∧
    supplied.check? ⟨outer, .literal written⟩ = some (.word value, .word) ∧
    Core.Evaluates (Resolved.LocalScope.values supplied.environment) store (.word value) (.word value) store :=
  ⟨.wordLiteral meaning, .wordLiteral meaning, .wordLiteral meaning,
    elaborateLocalExpression?_complete (.wordLiteral meaning) .word .word, .word⟩

private def maximumPayload : Syntax.CoreLiteralValue :=
  .decimal "115792089237316195423570985008687907853269984665640564039457584007913129639935"
private def mixedCase : Syntax.CoreLiteralValue := .hexadecimal "0xaBcDeF"
private def mixedValue : Core.Word := ⟨11259375, by decide⟩

theorem zero_seven_maximum_and_mixed_hex_are_exact_word_constants (supplied : LocalInputs) :
    supplied.check? (source (.decimal "0")) = some (.word Core.Word.zero, .word) ∧
    supplied.check? sevenSource = some (.word seven, .word) ∧
    supplied.check? (source maximumPayload) = some (.word Core.Word.maximum, .word) ∧
    supplied.check? (source mixedCase) = some (.word mixedValue, .word) :=
  ⟨checked_literal supplied (interpretWordLiteral?_sound (by decide)), checked_literal supplied sevenMeaning,
    checked_literal supplied (interpretWordLiteral?_sound (by decide)),
    checked_literal supplied (interpretWordLiteral?_sound (by decide))⟩

private def once : Syntax.Expr := complement (group sevenSource)
private def twice : Syntax.Expr := group (complement once)
private def onceCore : Core.Expr := .unary .wordNot (.word seven)
private def twiceCore : Core.Expr := .unary .wordNot onceCore
private theorem checked_once (supplied : LocalInputs) : supplied.check? once = some (onceCore, .word) :=
  elaborateLocalExpression?_complete (.bitNot (.group (.wordLiteral sevenMeaning))) (.unary .word) (.unary .word)
private theorem checked_twice (supplied : LocalInputs) : supplied.check? twice = some (twiceCore, .word) :=
  elaborateLocalExpression?_complete (.group (.bitNot (.bitNot (.group (.wordLiteral sevenMeaning)))))
    (.unary (.unary .word)) (.unary (.unary .word))

theorem grouped_double_complement_preserves_the_independently_denoted_word
    (supplied : LocalInputs) (store : Core.Store) :
    supplied.check? twice = some (twiceCore, .word) ∧
    LocalExpressionHasType supplied.names supplied.context twice .word ∧
    LocalExpressionEvaluates supplied.names supplied.environment store twice (.word seven) store ∧
    Core.Evaluates (Resolved.LocalScope.values supplied.environment) store twiceCore (.word seven) store := by
  have evaluation : LocalExpressionEvaluates supplied.names supplied.environment store twice (.word seven) store := by
    simpa [twice, once, complement, group, sevenSource, source] using
      LocalExpressionEvaluates.group (LocalExpressionEvaluates.bitNot
        (LocalExpressionEvaluates.bitNot (LocalExpressionEvaluates.group
          (LocalExpressionEvaluates.wordLiteral (table := supplied.names)
            (environment := supplied.environment) sevenMeaning))))
  exact ⟨checked_twice supplied, .group (.bitNot (.bitNot (.group (.wordLiteral sevenMeaning)))),
    evaluation, (elaborateLocalExpression?_evaluates_iff (checked_twice supplied) supplied.sameIds).mp evaluation⟩

theorem literal_and_complements_have_exact_one_three_five_transition_boundaries
    (supplied : LocalInputs) (store : Core.Store) :
    supplied.run? 0 sevenSource store = some (.word, .outOfFuel
      (Core.State.initial (.word seven) (Resolved.LocalScope.values supplied.environment) store)) ∧
    supplied.run? 2 once store = some (.word, .outOfFuel ⟨.ret (.word seven), [.unaryApply .wordNot], store⟩) ∧
    supplied.run? 4 twice store = some (.word, .outOfFuel ⟨.ret (.word seven.bitNot), [.unaryApply .wordNot], store⟩) ∧
    ∀ extra, supplied.run? (extra + 1) sevenSource store = some (.word, .done (.word seven) store) ∧
      supplied.run? (extra + 3) once store = some (.word, .done (.word seven.bitNot) store) ∧
      supplied.run? (extra + 5) twice store = some (.word, .done (.word seven) store) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LocalInputs.run?, checked_seven]; rfl
  · rw [LocalInputs.run?, checked_once]; rfl
  · rw [LocalInputs.run?, checked_twice]; rfl
  · intro extra
    constructor
    · rw [LocalInputs.run?, checked_seven]
      change some (Core.Ty.word, Core.runStateful (extra + 1)
        (Core.State.initial (.word seven) (Resolved.LocalScope.values supplied.environment) store)) = _
      apply congrArg (fun result => some (Core.Ty.word, result))
      exact Core.runStateful_complete_with_fuel
        (Core.Steps.cons Core.Transition.word Core.Steps.refl) (Nat.le_add_left 1 extra)
    · constructor
      · rw [LocalInputs.run?, checked_once]
        change some (Core.Ty.word, Core.runStateful (extra + 3)
          (Core.State.initial onceCore (Resolved.LocalScope.values supplied.environment) store)) = _
        apply congrArg (fun result => some (Core.Ty.word, result))
        exact Core.runStateful_complete_with_fuel
          (Core.Steps.cons Core.Transition.enterUnary (.cons .word (.cons (.applyUnary rfl) .refl)))
          (Nat.le_add_left 3 extra)
      · rw [LocalInputs.run?, checked_twice]
        change some (Core.Ty.word, Core.runStateful (extra + 5)
          (Core.State.initial twiceCore (Resolved.LocalScope.values supplied.environment) store)) = _
        apply congrArg (fun result => some (Core.Ty.word, result))
        exact Core.runStateful_complete_with_fuel
          (Core.Steps.cons Core.Transition.enterUnary (.cons .enterUnary (.cons .word
            (.cons (.applyUnary rfl) (.cons (.applyUnary (by simp [Core.UnaryOp.apply])) .refl)))))
          (Nat.le_add_left 5 extra)

theorem word_literals_are_not_boolean_conditions_or_operands (choice : Bool) (store : Core.Store) :
    (inputs choice).check? (neg sevenSource) = none ∧
    (inputs choice).check? (andE sevenSource ref) = none ∧
    (inputs choice).check? (branch sevenSource ref ref) = none ∧
    (inputs choice).check? (branch ref sevenSource ref) = none ∧
    ∀ value finalStore, ¬ LocalExpressionEvaluates (inputs choice).names (inputs choice).environment
      store (neg sevenSource) value finalStore := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typed⟩
    cases typed with | logicalNot child => cases child
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typed⟩
    cases typed with | logicalAnd left _ => cases left
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typed⟩
    cases typed with | conditional condition _ _ => cases condition
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typed⟩
    cases typed with
    | conditional _ left right =>
        cases left
        have boolean : LocalExpressionHasType (inputs choice).names (inputs choice).context ref .bool :=
          .identifier .head .head
        cases boolean.type_unique right
  · intro value finalStore evaluated
    cases evaluated with | logicalNot child => cases child

theorem selected_word_right_resolves_and_evaluates_but_is_not_a_checked_conjunction (store : Core.Store) :
    ResolvesLocalExpression (inputs true).names (andE ref sevenSource)
      (.ifE (.var ⟨owner, 0⟩) (.word seven) (.bool false)) ∧
    (inputs true).check? (andE ref sevenSource) = none ∧
    LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      (andE ref sevenSource) (.word seven) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs true).environment) store
      (.ifE (.var 0) (.word seven) (.bool false)) (.word seven) store := by
  have resolution : ResolvesLocalExpression (inputs true).names (andE ref sevenSource)
      (.ifE (.var ⟨owner, 0⟩) (.word seven) (.bool false)) :=
    .logicalAnd (.identifier .head) (.wordLiteral sevenMeaning)
  have evaluation : LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      (andE ref sevenSource) (.word seven) store := .andTrue (.identifier .head .head) (.wordLiteral sevenMeaning)
  refine ⟨resolution, ?_, evaluation,
    (resolution.core_evaluates_iff (environment := (inputs true).environment) (.ifE (.var .head) .word .bool)).mp evaluation⟩
  apply elaborateLocalExpression?_eq_none_iff.mpr
  rintro ⟨type, typed⟩
  cases typed with | logicalAnd _ right => cases right

private def overflow : Syntax.CoreLiteralValue :=
  .hexadecimal "0x10000000000000000000000000000000000000000000000000000000000000000"
private def badPayloads : List Syntax.CoreLiteralValue := [.decimal "1_0", overflow, .string "7"]

theorem skipped_bad_literals_are_raw_evaluable_but_never_checked
    (payload : Syntax.CoreLiteralValue) (present : payload ∈ badPayloads) (fuel : Nat) (store : Core.Store) :
    LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      (branch ref sevenSource (source payload)) (.word seven) store ∧
    (inputs true).check? (branch ref sevenSource (source payload)) = none ∧
    (inputs true).run? fuel (branch ref sevenSource (source payload)) store = none ∧
    (¬ ∃ value finalStore, LocalExpressionEvaluates (inputs true).names (inputs true).environment
      store (source payload) value finalStore) := by
  have allRejected : ∀ candidate ∈ badPayloads, interpretWordLiteral? (literal candidate) = none := by decide
  have rejected := allRejected payload present
  have checkRejected : (inputs true).check? (branch ref sevenSource (source payload)) = none := by
    simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, branch, source,
      ref, inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?,
      rejected]
  refine ⟨.ifTrue (.identifier .head .head) (.wordLiteral sevenMeaning), checkRejected,
    (LocalInputs.run?_eq_none_iff fuel store).mpr checkRejected, ?_⟩
  rintro ⟨value, finalStore, evaluation⟩
  cases evaluation with
  | wordLiteral meaning =>
      have impossible := interpretWordLiteral?_complete meaning
      rw [rejected] at impossible
      cases impossible

theorem unused_input_and_identity_mapping_keep_literal_constants
    (supplied : LocalInputs) (name : String) (type : Core.Ty) (value : Core.Value)
    (typed : Core.ValueHasType value type) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) :
    (supplied.bindFresh owner name type value typed).check? sevenSource = some (.word seven, .word) ∧
    LocalExpressionEvaluates (supplied.bindFresh owner name type value typed).names
      (supplied.bindFresh owner name type value typed).environment store sevenSource (.word seven) store ∧
    (supplied.mapIds mapping injective).check? sevenSource = some (.word seven, .word) ∧
    (supplied.mapIds mapping injective).run? fuel sevenSource store = supplied.run? fuel sevenSource store := by
  have avoids : AvoidsLocalName name sevenSource := .literal
  refine ⟨?_, (avoids.bindFresh_evaluates_iff supplied owner type value typed).mpr (.wordLiteral sevenMeaning),
    (supplied.check?_mapIds mapping injective sevenSource).trans (checked_literal supplied sevenMeaning),
    supplied.run?_mapIds mapping injective fuel sevenSource store⟩
  simpa [Core.Expr.weakenAt] using
    avoids.check_bindFresh_complete supplied owner type value typed (checked_literal supplied sevenMeaning)

theorem every_invalid_literal_avoids_names_and_keeps_failed_checking
    (supplied : LocalInputs) (name : String) (type : Core.Ty) (value : Core.Value)
    (typed : Core.ValueHasType value type) (payload : Syntax.CoreLiteralValue)
    (rejected : interpretWordLiteral? (literal payload) = none)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (fuel : Nat) (store : Core.Store) :
    AvoidsLocalName name (source payload) ∧ supplied.check? (source payload) = none ∧
    (supplied.bindFresh owner name type value typed).check? (source payload) = none ∧
    (supplied.mapIds mapping injective).run? fuel (source payload) store = none := by
  have avoids : AvoidsLocalName name (source payload) := .literal
  have failed : supplied.check? (source payload) = none := by
    simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, source, rejected]
  refine ⟨avoids, failed, ?_, ?_⟩
  · simpa only [failed, Option.map_none] using avoids.check_bindFresh_eq supplied owner type value typed
  · rw [LocalInputs.run?_mapIds]
    exact (LocalInputs.run?_eq_none_iff fuel store).mpr failed

end Tests.FrontendLocalWordLiteral
