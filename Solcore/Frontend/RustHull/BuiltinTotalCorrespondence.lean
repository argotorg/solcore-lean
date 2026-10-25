import Solcore.Frontend.RustHull.CallFaultCorrespondence

/-! Accepted pure builtin calls derive their argument shape and source result
from the actual compiler checks, then reuse the existing Core execution bridge. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.BuiltinTotalCorrespondence
open Correspondence BuiltinCorrespondence PureCallCorrespondence ScalarExecution

private def checkWords (arguments : List Lowered) : LowerM PUnit :=
  forIn arguments PUnit.unit fun argument _ => do
    expectType .word argument.type
    pure (.yield PUnit.unit)

private theorem checkedWords {arguments : List Lowered}
    (checked : checkWords arguments = .ok PUnit.unit) :
    ∀ argument ∈ arguments, argument.type = .word := by
  induction arguments with
  | nil => simp
  | cons argument rest ih =>
      by_cases same : argument.type = .word
      · have tail : checkWords rest = .ok PUnit.unit := by
          simpa [checkWords, List.forIn_cons, expectType, same] using checked
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact same
        · exact ih tail value member
      · simp [checkWords, List.forIn_cons, expectType, Ne.symm same, fail,
          Bind.bind, Except.bind] at checked

private theorem ordinary_components {scope : Scope} {name : String} {type : Core.Ty}
    {arguments : List Lowered} {lowered : Lowered}
    (effect : Effects.supports name = false)
    (notTo : name ≠ "wordToInteger") (notFrom : name ≠ "wordFromInteger")
    (notZero : name ≠ "iszero")
    (compiled : lowerBuiltin scope name type arguments = .ok lowered) :
    (∀ argument ∈ arguments, argument.type = .word) ∧
      ∃ raw, RustYulPrimitives.compile (primitiveName name)
        ((List.range arguments.length).map fun index =>
          projectArgument index arguments.length (.var 0)) = .ok raw := by
  simp only [lowerBuiltin, effect, notTo, notFrom, notZero, Bool.false_eq_true,
    ↓reduceIte] at compiled
  obtain ⟨checked, wordChecked, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  obtain ⟨raw, rawCompiled, _⟩ := lower_bind_eq_ok.mp compiled
  refine ⟨checkedWords wordChecked, raw, ?_⟩
  cases found : RustYulPrimitives.compile (primitiveName name)
      ((List.range arguments.length).map fun index => projectArgument index arguments.length (.var 0)) with
  | error reason => simp [found, Except.mapError] at rawCompiled
  | ok result => simpa [found, Except.mapError] using rawCompiled

private def arity : PureBuiltin → Nat
  | .binary _ | .comparison _ => 2
  | .ternary _ => 3
  | _ => 1

private theorem raw_arity (operation : PureBuiltin) {arguments : List Core.Expr}
    {raw : RustYulPrimitives.Lowered}
    (compiled : RustYulPrimitives.compile operation.name arguments = .ok raw) :
    arguments.length = arity operation := by
  by_cases wrong : arguments.length = arity operation
  · exact wrong
  exfalso
  cases operation with
  | binary op =>
      cases op <;> change (if arguments.length = 2 then _ else Except.error _) = .ok raw at compiled
      all_goals simp only [arity] at wrong
      all_goals simp [wrong] at compiled
  | unary op =>
      cases op <;> change (if arguments.length = 1 then _ else Except.error _) = .ok raw at compiled
      all_goals simp only [arity] at wrong
      all_goals simp [wrong] at compiled
  | ternary op =>
      cases op <;> change (if arguments.length = 3 then _ else Except.error _) = .ok raw at compiled
      all_goals simp only [arity] at wrong
      all_goals simp [wrong] at compiled
  | comparison op =>
      cases op <;> change (if arguments.length = 2 then _ else Except.error _) = .ok raw at compiled
      all_goals simp only [arity] at wrong
      all_goals simp [wrong] at compiled
  | toInteger | fromInteger => contradiction
  | iszero | pop =>
      change (if arguments.length = 1 then _ else Except.error _) = .ok raw at compiled
      simp only [arity] at wrong
      simp [wrong] at compiled

private theorem normalized_compiled {scope : Scope} {name : String} {type : Core.Ty}
    {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type arguments = .ok lowered) :
    lowerBuiltin scope (primitiveName name) type arguments = .ok lowered := by
  have normalized := lowerBuiltin_primitiveName scope name type arguments
  rw [compiled] at normalized
  cases accepted : lowerBuiltin scope (primitiveName name) type arguments with
  | error error => rw [accepted] at normalized; cases normalized
  | ok result =>
      rw [accepted] at normalized
      exact congrArg Except.ok (Option.some.inj normalized).symm

private theorem canonical_name (operation : PureBuiltin) :
    primitiveName operation.name = operation.name := by
  cases operation with
  | binary op => cases op <;> rfl
  | unary op => cases op <;> rfl
  | ternary op => cases op <;> rfl
  | comparison op => cases op <;> rfl
  | toInteger | fromInteger | iszero | pop => rfl

private def Ordinary : PureBuiltin → Prop
  | .toInteger | .fromInteger | .iszero => False
  | _ => True

private theorem ordinary_arguments (operation : PureBuiltin) (ordinary : Ordinary operation)
    {scope : Scope} {type : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type arguments = .ok lowered) :
    (∀ argument ∈ arguments, argument.type = .word) ∧ arguments.length = arity operation := by
  have effect : Effects.supports operation.name = false := by
    cases operation with
    | binary op => cases op <;> rfl
    | unary op => cases op <;> rfl
    | ternary op => cases op <;> rfl
    | comparison op => cases op <;> rfl
    | toInteger | fromInteger | iszero | pop => rfl
  have noTo : operation.name ≠ "wordToInteger" := by
    cases operation with
    | binary op => cases op <;> decide
    | unary op => cases op <;> decide
    | ternary op => cases op <;> decide
    | comparison op => cases op <;> decide
    | toInteger | fromInteger | iszero => exact ordinary.elim
    | pop => decide
  have noFrom : operation.name ≠ "wordFromInteger" := by
    cases operation with
    | binary op => cases op <;> decide
    | unary op => cases op <;> decide
    | ternary op => cases op <;> decide
    | comparison op => cases op <;> decide
    | toInteger | fromInteger | iszero => exact ordinary.elim
    | pop => decide
  have noZero : operation.name ≠ "iszero" := by
    cases operation with
    | binary op => cases op <;> decide
    | unary op => cases op <;> decide
    | ternary op => cases op <;> decide
    | comparison op => cases op <;> decide
    | toInteger | fromInteger | iszero => exact ordinary.elim
    | pop => decide
  obtain ⟨words, raw, accepted⟩ := ordinary_components effect noTo noFrom noZero compiled
  rw [canonical_name] at accepted
  exact ⟨words, by simpa only [List.length_map, List.length_range] using raw_arity operation accepted⟩

private theorem word_arguments {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) :
    ∃ (expressions : List Core.Expr) (values : List Core.Word),
      arguments = expressions.map (fun expression => Lowered.mk .word expression) ∧
      sources = values.map Semantics.Value.word ∧ targets = values.map Core.Value.word ∧
      expressions.length = values.length := by
  induction related with
  | nil => exact ⟨[], [], rfl, rfl, rfl, rfl⟩
  | @cons argument arguments source sources target targets head tail ih =>
      obtain ⟨expressions, values, rfl, rfl, rfl, lengths⟩ :=
        ih (fun member selected => words member (List.mem_cons_of_mem _ selected))
      have typed := words argument (List.mem_cons_self ..)
      cases argument with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word value =>
              exact ⟨expression :: expressions, value :: values, rfl, rfl, rfl, congrArg Nat.succ lengths⟩

private theorem one_word {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 1) :
    ∃ expression value, arguments = [⟨.word, expression⟩] ∧
      sources = [.word value] ∧ targets = [.word value] := by
  obtain ⟨expressions, values, rfl, rfl, rfl, sizes⟩ := word_arguments related words
  simp only [List.length_map] at length
  cases expressions with
  | nil => cases length
  | cons expression rest =>
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj length)
      subst rest
      cases values with
      | nil => cases sizes
      | cons value rest =>
          have empty : rest = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj sizes.symm)
          subst rest
          exact ⟨expression, value, rfl, rfl, rfl⟩

private theorem two_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 2) :
    ∃ leftCode rightCode left right, arguments = [⟨.word, leftCode⟩, ⟨.word, rightCode⟩] ∧
      sources = [.word left, .word right] ∧ targets = [.word left, .word right] := by
  cases related with
  | nil => cases length
  | @cons argument arguments source sources target targets head tail =>
      obtain ⟨rightCode, right, rfl, rfl, rfl⟩ := one_word tail
        (fun member selected => words member (List.mem_cons_of_mem _ selected)) (Nat.succ.inj length)
      have typed := words argument (List.mem_cons_self ..)
      cases argument with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word left => exact ⟨expression, rightCode, left, right, rfl, rfl, rfl⟩

private theorem three_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 3) :
    ∃ firstCode secondCode thirdCode first second third,
      arguments = [⟨.word, firstCode⟩, ⟨.word, secondCode⟩, ⟨.word, thirdCode⟩] ∧
      sources = [.word first, .word second, .word third] ∧ targets = [.word first, .word second, .word third] := by
  cases related with
  | nil => cases length
  | @cons argument arguments source sources target targets head tail =>
      obtain ⟨secondCode, thirdCode, second, third, rfl, rfl, rfl⟩ := two_words tail
        (fun member selected => words member (List.mem_cons_of_mem _ selected)) (Nat.succ.inj length)
      have typed := words argument (List.mem_cons_self ..)
      cases argument with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word first => exact ⟨expression, secondCode, thirdCode, first, second, third, rfl, rfl, rfl⟩

private theorem conversion_arguments {name : String}
    (named : name = "wordToInteger" ∨ name = "wordFromInteger")
    {scope : Scope} {type : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets) :
    ∃ expression value, arguments = [⟨.word, expression⟩] ∧
      sources = [.word value] ∧ targets = [.word value] := by
  have size : arguments.length = 1 := by
    by_cases size : arguments.length = 1
    · exact size
    · rcases named with rfl | rfl
      all_goals
        change (if arguments.length = 1 then _ else _) = (Except.ok lowered : LowerM Lowered) at compiled
        simp [size, fail, Bind.bind, Except.bind] at compiled
  obtain ⟨argument, rfl⟩ := List.length_eq_one_iff.mp size
  have reduced : lowerBuiltin scope name type [argument] = (do
      expectType .word argument.type
      expectType .word type
      pure argument) := by rcases named with rfl | rfl <;> rfl
  rw [reduced] at compiled
  obtain ⟨checked, typed, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  have word := (expectType_eq_of_ok typed).symm
  exact one_word related (by intro member found; simp only [List.mem_singleton] at found; subst member; exact word) rfl

private theorem iszero_arguments {scope : Scope} {type : Core.Ty}
    {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope "iszero" type arguments = .ok lowered) :
    ∃ argument, arguments = [argument] := by
  apply List.length_eq_one_iff.mp
  by_cases size : arguments.length = 1
  · exact size
  · change (if decide (arguments.length = 1) && boolLike (packArguments arguments).type then _ else _) =
        (Except.ok lowered : LowerM Lowered) at compiled
    simp [size, fail, Bind.bind, Except.bind] at compiled

private theorem preserved_value {name : String} {sourceType : Ty}
    {sources : List Semantics.Value} {lowered : Lowered}
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (preserved : ∃ result target, Semantics.primitive? name sourceType sources = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final) :
    ∃ source target, Semantics.primitive? name sourceType sources = some (.value source) ∧
      ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  obtain ⟨result, target, meaning, related, evaluated⟩ := preserved
  cases related with
  | value related => exact ⟨_, _, meaning, related, evaluated⟩
  | language reason => exact (NamedCallCorrespondence.primitive_not_language name sourceType sources reason meaning).elim

private theorem canonical_total (operation : PureBuiltin)
    {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) final) :
    ∃ source target, Semantics.primitive? operation.name sourceType sources = some (.value source) ∧
      ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  cases operation with
  | binary op =>
      obtain ⟨words, length⟩ := ordinary_arguments (.binary op) trivial compiled
      obtain ⟨leftCode, rightCode, left, right, rfl, rfl, rfl⟩ := two_words related words length
      have meaning := op.meaning sourceType left right
      obtain ⟨target, represented, executed⟩ := canonical_preserves (.binary op)
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩
  | unary op =>
      obtain ⟨words, length⟩ := ordinary_arguments (.unary op) trivial compiled
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := one_word related words length
      have meaning := op.meaning sourceType value
      obtain ⟨target, represented, executed⟩ := canonical_preserves (.unary op)
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩
  | ternary op =>
      obtain ⟨words, length⟩ := ordinary_arguments (.ternary op) trivial compiled
      obtain ⟨firstCode, secondCode, thirdCode, first, second, third, rfl, rfl, rfl⟩ :=
        three_words related words length
      have meaning := op.meaning sourceType first second third
      obtain ⟨target, represented, executed⟩ := canonical_preserves (.ternary op)
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩
  | comparison op =>
      obtain ⟨words, length⟩ := ordinary_arguments (.comparison op) trivial compiled
      obtain ⟨leftCode, rightCode, left, right, rfl, rfl, rfl⟩ := two_words related words length
      exact preserved_value (wordComparison op (by cases op <;> rfl) typeCompiled compiled evaluated)
  | toInteger =>
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := conversion_arguments (Or.inl rfl) compiled related
      have meaning : Semantics.primitive? PureBuiltin.toInteger.name sourceType [.word value] =
          some (.value (.word value)) := rfl
      obtain ⟨target, represented, executed⟩ := canonical_preserves .toInteger
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩
  | fromInteger =>
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := conversion_arguments (Or.inr rfl) compiled related
      have meaning : Semantics.primitive? PureBuiltin.fromInteger.name sourceType [.word value] =
          some (.value (.word value)) := rfl
      obtain ⟨target, represented, executed⟩ := canonical_preserves .fromInteger
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩
  | iszero =>
      obtain ⟨argument, rfl⟩ := iszero_arguments compiled
      cases related with
      | cons head tail =>
          cases tail
          exact preserved_value (iszero typeCompiled compiled head evaluated)
  | pop =>
      obtain ⟨words, length⟩ := ordinary_arguments .pop trivial compiled
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := one_word related words length
      have meaning : Semantics.primitive? PureBuiltin.pop.name sourceType [.word value] =
          some (.value .unit) := rfl
      obtain ⟨target, represented, executed⟩ := canonical_preserves .pop
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩

/-- Actual builtin checks determine a successful source primitive result; no
source computation premise is needed. The argument pack's heap is retained. -/
theorem builtin_preserves_result {name : String} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) final) :
    ∃ source target, Semantics.primitive? name sourceType sources = some (.value source) ∧
      ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  have accepted := normalized_compiled compiled
  rw [pureBuiltin_name classified] at accepted
  obtain ⟨source, target, meaning, represented, executed⟩ :=
    canonical_total operation typeCompiled accepted related evaluated
  exact ⟨source, target, by rw [primitiveName_meaning, pureBuiltin_name classified]; exact meaning,
    represented, executed⟩

end Solcore.Frontend.RustHull.BuiltinTotalCorrespondence
