import Solcore.Frontend.LocalInputsExtensionProperties
import Solcore.Frontend.LocalInputsRenamingProperties
import Solcore.Core.UnaryPrimitives

/-! ADR-0161: fixed Word complement, distinct from Boolean negation and from
acceptance of numeric source literals or untyped short-circuit expressions. -/

set_option autoImplicit false

namespace Tests.FrontendLocalWordComplement

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"WordComplement", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "word-complement.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def complement (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .bitNot⟩ operand⟩
private def negate (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ operand⟩
private def supplied (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "x" type value typed
private def inputs (word : Core.Word) : LocalInputs := supplied .word (.word word) .word
private def source : Syntax.Expr := complement (ref "x")
private def twice : Syntax.Expr := complement source
private def core : Core.Expr := .unary .wordNot (.var 0)
private def twiceCore : Core.Expr := .unary .wordNot core
private theorem checked (word : Core.Word) : (inputs word).check? source = some (core, .word) :=
  elaborateLocalExpression?_complete (.bitNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head))
private theorem checked_twice (word : Core.Word) : (inputs word).check? twice = some (twiceCore, .word) :=
  elaborateLocalExpression?_complete (.bitNot (.bitNot (.identifier .head)))
    (.unary (.unary (.var .head))) (.unary (.unary (.var .head)))
private theorem evaluated (word : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluates (inputs word).names (inputs word).environment store source (.word word.bitNot) store :=
  .bitNot (.identifier .head .head)

theorem arbitrary_words_and_double_complement_have_exact_meanings (word : Core.Word) (store : Core.Store) :
    (inputs word).check? source = some (core, .word) ∧ (inputs word).check? twice = some (twiceCore, .word) ∧
    LocalExpressionEvaluates (inputs word).names (inputs word).environment store source (.word word.bitNot) store ∧
    LocalExpressionEvaluates (inputs word).names (inputs word).environment store twice (.word word) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs word).environment) store core (.word word.bitNot) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs word).environment) store twiceCore (.word word) store := by
  have double : LocalExpressionEvaluates (inputs word).names (inputs word).environment store twice (.word word) store := by
    simpa [twice, complement] using LocalExpressionEvaluates.bitNot (evaluated word store)
  exact ⟨checked word, checked_twice word, evaluated word store, double,
    (elaborateLocalExpression?_evaluates_iff (checked word) (inputs word).sameIds).mp (evaluated word store),
    (elaborateLocalExpression?_evaluates_iff (checked_twice word) (inputs word).sameIds).mp double⟩

private theorem run_enough (word : Core.Word) (extra : Nat) (store : Core.Store) :
    (inputs word).run? (extra + 3) source store = some (.word, .done (.word word.bitNot) store) := by
  rw [LocalInputs.run?, checked]
  change some (Core.Ty.word, Core.runStateful (extra + 3) (Core.State.initial core [.word word] store)) = _
  simp [Core.runStateful, Core.State.initial, Core.advance, core, Core.UnaryOp.apply]

theorem single_and_double_complement_have_exact_fuel (word : Core.Word) (store : Core.Store) :
    (inputs word).run? 2 source store = some (.word, .outOfFuel ⟨.ret (.word word), [.unaryApply .wordNot], store⟩) ∧
    (inputs word).run? 4 twice store = some (.word, .outOfFuel ⟨.ret (.word word.bitNot), [.unaryApply .wordNot], store⟩) ∧
    (∀ extra, (inputs word).run? (extra + 3) source store = some (.word, .done (.word word.bitNot) store)) ∧
    ∀ extra, (inputs word).run? (extra + 5) twice store = some (.word, .done (.word word) store) := by
  refine ⟨?_, ?_, fun extra => run_enough word extra store, ?_⟩
  · rw [LocalInputs.run?, checked]; rfl
  · rw [LocalInputs.run?, checked_twice]; rfl
  · intro extra
    rw [LocalInputs.run?, checked_twice]
    change some (Core.Ty.word, Core.runStateful (extra + 5) (Core.State.initial twiceCore [.word word] store)) = _
    simp [Core.runStateful, Core.State.initial, Core.advance, twiceCore, core, Core.UnaryOp.apply]

theorem zero_one_and_maximum_have_expected_complements (store : Core.Store) :
    (inputs .zero).run? 3 source store = some (.word, .done (.word .maximum) store) ∧
    (inputs (Core.Word.ofNatModulo 1)).run? 3 source store =
      some (.word, .done (.word (Core.Word.ofNatModulo (Core.wordModulus - 2))) store) ∧
    (inputs .maximum).run? 3 source store = some (.word, .done (.word .zero) store) := by
  refine ⟨by simpa using run_enough .zero 0 store, ?_, by simpa using run_enough .maximum 0 store⟩
  have one : (Core.Word.ofNatModulo 1).bitNot = Core.Word.ofNatModulo (Core.wordModulus - 2) := by decide
  simpa only [Nat.zero_add, one] using run_enough (Core.Word.ofNatModulo 1) 0 store

private theorem non_word_rejected (type : Core.Ty) (value : Core.Value)
    (typed : Core.ValueHasType value type) (wrongType : type ≠ .word)
    (wrongValue : ∀ word, value ≠ .word word) (store : Core.Store) :
    (supplied type value typed).check? source = none ∧ ∀ result finalStore,
      ¬ LocalExpressionEvaluates (supplied type value typed).names (supplied type value typed).environment
        store source result finalStore := by
  constructor
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨resultType, typing⟩
    cases typing with
    | bitNot operand =>
        have original : LocalExpressionHasType (supplied type value typed).names
            (supplied type value typed).context (ref "x") type := .identifier .head .head
        exact wrongType (original.type_unique operand)
  · intro result finalStore evaluation
    have original : LocalExpressionEvaluates (supplied type value typed).names
        (supplied type value typed).environment store (ref "x") value store := .identifier .head .head
    cases evaluation with
    | bitNot operand => exact wrongValue _ (original.deterministic operand).1

theorem boolean_and_reference_values_are_not_coerced (flag : Bool) (location : Nat) (store : Core.Store) :
    (supplied .bool (.bool flag) .bool).check? source = none ∧
    (supplied (.cell .word) (.cellRef .word location) .cellRef).check? source = none ∧
    ∀ value finalStore,
      (¬ LocalExpressionEvaluates (supplied .bool (.bool flag) .bool).names
        (supplied .bool (.bool flag) .bool).environment store source value finalStore) ∧
      (¬ LocalExpressionEvaluates (supplied (.cell .word) (.cellRef .word location) .cellRef).names
        (supplied (.cell .word) (.cellRef .word location) .cellRef).environment store source value finalStore) := by
  have boolean := non_word_rejected .bool (.bool flag) .bool (by decide) (by intro word same; cases same) store
  have reference := non_word_rejected (.cell .word) (.cellRef .word location) .cellRef
    (by decide) (by intro word same; cases same) store
  exact ⟨boolean.1, reference.1, fun value finalStore => ⟨boolean.2 value finalStore, reference.2 value finalStore⟩⟩

theorem logical_and_word_negation_do_not_convert_operand_types (word : Core.Word) (flag : Bool) :
    (inputs word).check? (negate source) = none ∧
    (supplied .bool (.bool flag) .bool).check? (complement (negate (ref "x"))) = none := by
  constructor
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    have actual : LocalExpressionHasType (inputs word).names (inputs word).context source .word :=
      .bitNot (.identifier .head .head)
    cases typing with | logicalNot operand => cases actual.type_unique operand
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    have actual : LocalExpressionHasType (supplied .bool (.bool flag) .bool).names
        (supplied .bool (.bool flag) .bool).context (negate (ref "x")) .bool := .logicalNot (.identifier .head .head)
    cases typing with | bitNot operand => cases actual.type_unique operand

private def unsupported : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "7"⟩⟩
private def badOperands : List Syntax.Expr := [ref "missing", unsupported]

theorem missing_names_and_numeric_syntax_remain_rejected (word : Core.Word) :
    ∀ operand ∈ badOperands, resolveLocalExpression? (inputs word).names (complement operand) = none ∧
      (inputs word).check? (complement operand) = none := by
  intro operand member
  simp only [badOperands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, complement, ref,
    unsupported, inputs, supplied, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

private def withFlag (word : Core.Word) (flag : Bool) : LocalInputs :=
  (inputs word).bindFresh owner "a" .bool (.bool flag) .bool
private theorem names_ne : "a" ≠ "x" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private def nested : Syntax.Expr := complement
  ⟨span, .group ⟨span, .conditional (ref "a") span source span (ref "x")⟩⟩
private def nestedCore : Core.Expr := .unary .wordNot (.ifE (.var 0) (.unary .wordNot (.var 1)) (.var 1))
private theorem checked_nested (word : Core.Word) (flag : Bool) :
    (withFlag word flag).check? nested = some (nestedCore, .word) :=
  elaborateLocalExpression?_complete (.bitNot (.group (.conditional (.identifier .head)
    (.bitNot (.identifier (.tail names_ne .head))) (.identifier (.tail names_ne .head)))))
    (.unary (.ifE (.var .head) (.unary (.var (.tail ids_ne .head))) (.var (.tail ids_ne .head))))
    (.unary (.ifE (.var .head) (.unary (.var (.tail ids_ne .head))) (.var (.tail ids_ne .head))))

theorem grouped_conditionals_keep_word_complement_meaning (word : Core.Word) (flag : Bool) (store : Core.Store) :
    (withFlag word flag).check? nested = some (nestedCore, .word) ∧
    LocalExpressionEvaluates (withFlag word flag).names (withFlag word flag).environment store nested
      (.word (if flag then word else word.bitNot)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (withFlag word flag).environment) store nestedCore
      (.word (if flag then word else word.bitNot)) store := by
  have coreEvaluation : Core.Evaluates (Resolved.LocalScope.values (withFlag word flag).environment) store nestedCore
      (.word (if flag then word else word.bitNot)) store := by
    cases flag
    · exact .unary (.ifFalse (.var rfl) (.var rfl)) rfl
    · exact .unary (.ifTrue (.var rfl) (.unary (.var rfl) rfl)) (by simp [Core.UnaryOp.apply])
  exact ⟨checked_nested word flag, (elaborateLocalExpression?_evaluates_iff
    (checked_nested word flag) (withFlag word flag).sameIds).mpr coreEvaluation, coreEvaluation⟩

private def rawSource : Syntax.Expr := complement ⟨span, .binary (ref "a") ⟨span, .logicalAnd⟩ (ref "x")⟩
private def rawCore : Core.Expr := .unary .wordNot (.ifE (.var 0) (.var 1) (.bool false))

/-- Raw conjunction forwards its selected Word, but whole-expression checking
still fails. Core correspondence here requires resolution, not typing. -/
theorem raw_selected_word_can_be_complemented_without_being_checked (word : Core.Word) (store : Core.Store) :
    (withFlag word true).check? rawSource = none ∧
    LocalExpressionEvaluates (withFlag word true).names (withFlag word true).environment
      store rawSource (.word word.bitNot) store ∧
    Core.Evaluates (Resolved.LocalScope.values (withFlag word true).environment) store rawCore (.word word.bitNot) store := by
  have raw : LocalExpressionEvaluates (withFlag word true).names (withFlag word true).environment
      store rawSource (.word word.bitNot) store :=
    .bitNot (.andTrue (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head)))
  have resolution : ResolvesLocalExpression (withFlag word true).names rawSource
      (.unary .wordNot (.ifE (.var ⟨owner, 1⟩) (.var ⟨owner, 0⟩) (.bool false))) :=
    .bitNot (.logicalAnd (.identifier .head) (.identifier (.tail names_ne .head)))
  refine ⟨?_, raw, (resolution.core_evaluates_iff (environment := (withFlag word true).environment)
    (.unary (.ifE (.var .head) (.var (.tail ids_ne .head)) .bool))).mp raw⟩
  apply elaborateLocalExpression?_eq_none_iff.mpr
  rintro ⟨type, typing⟩
  cases typing with | bitNot operand => cases operand

private def shift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 5 }
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  cases left
  cases right
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases owners
  cases indices
  rfl
private def extended (word : Core.Word) : LocalInputs := (inputs word).bindFresh owner "extra" .unit .unit .unit
private def renamed (word : Core.Word) : LocalInputs := (inputs word).mapIds shift shift_injective

theorem input_extension_and_id_relabeling_preserve_complement (word : Core.Word) (fuel : Nat) (store : Core.Store) :
    (extended word).check? source = some (.unary .wordNot (.var 1), .word) ∧
    (renamed word).check? source = some (core, .word) ∧
    (renamed word).run? fuel source store = (inputs word).run? fuel source store ∧
    LocalExpressionEvaluates (extended word).names (extended word).environment store source (.word word.bitNot) store := by
  have avoids : AvoidsLocalName "extra" source := .bitNot (.identifier (by decide))
  refine ⟨?_, ((inputs word).check?_mapIds shift shift_injective source).trans (checked word),
    (inputs word).run?_mapIds shift shift_injective fuel source store,
    (avoids.bindFresh_evaluates_iff (inputs word) owner .unit .unit .unit).mpr (evaluated word store)⟩
  simpa [extended, core, Core.Expr.weakenAt] using
    avoids.check_bindFresh_complete (inputs word) owner .unit .unit .unit (checked word)

end Tests.FrontendLocalWordComplement
