import Solcore.Frontend.RustHull.ExpressionCorrespondence

/-! Pure Hull builtin meaning through the actual builtin compiler. Argument
premises describe the emitted argument pack and its exact resulting store;
they can be supplied by expression-list preservation. External effects are not
assumed here. The raw Yul word operator executes only after that pack succeeds. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.BuiltinCorrespondence
open Correspondence

theorem primitiveName_meaning (name : String) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = Semantics.primitive? (primitiveName name) type arguments := by
  unfold primitiveName
  split <;> rfl

private theorem toOption_bind {α β ε : Type} (value : Except ε α) (next : α → Except ε β) :
    (value >>= next).toOption = value.toOption.bind (fun value => (next value).toOption) := by
  cases value <;> rfl

private theorem toOption_mapError {α ε δ : Type} (value : Except ε α) (map : ε → δ) :
    (value.mapError map).toOption = value.toOption := by
  cases value <;> rfl

theorem lowerBuiltin_primitiveName (scope : Scope) (name : String) (expected : Core.Ty)
    (arguments : List Lowered) :
    (lowerBuiltin scope name expected arguments).toOption =
      (lowerBuiltin scope (primitiveName name) expected arguments).toOption := by
  unfold primitiveName
  split <;> try rfl
  all_goals
    simp [lowerBuiltin, Effects.supports, Ambient.supports, AccountInspection.supports,
      primitiveName, toOption_bind, toOption_mapError]

inductive WordBinary where
  | add | sub | mul | udiv | umod | sdiv | smod | pow | signExtend
  | bitAnd | bitOr | bitXor | byteAt | shl | shr | sar
  deriving Repr, DecidableEq

def WordBinary.name : WordBinary → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .udiv => "div" | .umod => "mod"
  | .sdiv => "sdiv" | .smod => "smod" | .pow => "exp" | .signExtend => "signextend"
  | .bitAnd => "and" | .bitOr => "or" | .bitXor => "xor" | .byteAt => "byte"
  | .shl => "shl" | .shr => "shr" | .sar => "sar"

def WordBinary.eval : WordBinary → Core.Word → Core.Word → Core.Word
  | .add => Core.Word.add | .sub => Core.Word.sub | .mul => Core.Word.mul
  | .udiv => Core.Word.udiv | .umod => Core.Word.umod
  | .sdiv => Core.Word.sdiv | .smod => Core.Word.smod
  | .pow => Core.Word.pow | .signExtend => Core.Word.signExtend
  | .bitAnd => Core.Word.bitAnd | .bitOr => Core.Word.bitOr | .bitXor => Core.Word.bitXor
  | .byteAt => Core.Word.byteAt
  | .shl => fun distance value => Core.Word.shiftLeft value distance
  | .shr => fun distance value => Core.Word.shiftRight value distance
  | .sar => fun distance value => Core.Word.shiftArithmeticRight value distance

def WordBinary.operation : WordBinary → Core.BinaryOp
  | .add => .wordAdd | .sub => .wordSub | .mul => .wordMul
  | .udiv => .wordDiv | .umod => .wordMod | .sdiv => .wordSdiv | .smod => .wordSmod
  | .pow => .wordPow | .signExtend => .wordSignExtend
  | .bitAnd => .wordAnd | .bitOr => .wordOr | .bitXor => .wordXor | .byteAt => .wordByte
  | .shl => .wordShl | .shr => .wordShr | .sar => .wordSar

def WordBinary.body (operation : WordBinary) : Core.Expr :=
  match operation with
  | .shl | .shr | .sar => .binary operation.operation (.var 1) (.var 0)
  | _ => .binary operation.operation (.var 0) (.var 1)

/-- The actual pure-Yul adapter binds the right projection and then the left
projection. The enclosing Hull argument pack has already evaluated its inputs. -/
def WordBinary.code (operation : WordBinary) : Core.Expr :=
  .apply (.lambda .word .word
    (.apply (.lambda .word .word operation.body) (.first (.var 1)))) (.second (.var 0))

theorem WordBinary.lowered (operation : WordBinary) (scope : Scope) (left right : Core.Expr) :
    lowerBuiltin scope operation.name .word [⟨.word, left⟩, ⟨.word, right⟩] =
      .ok ⟨.word, Core.LanguageResult.bind .word
        (packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression
        (Core.LanguageResult.success operation.code)⟩ := by
  cases operation <;> rfl

theorem WordBinary.meaning (operation : WordBinary) (type : Ty) (left right : Core.Word) :
    Semantics.primitive? operation.name type [.word left, .word right] =
      some (.value (.word (operation.eval left right))) := by
  cases operation <;> rfl

theorem WordBinary.evaluates (operation : WordBinary) (left right : Core.Word)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (.pair (.word left) (.word right) :: environment) store operation.code
      (.word (operation.eval left right)) store := by
  cases operation <;>
    exact .apply .lambda (.second (.var rfl))
      (.apply .lambda (.first (.var rfl)) (.binary (.var rfl) (.var rfl) rfl))

theorem WordBinary.renamed (operation : WordBinary) (mapping : Core.Renaming) :
    operation.code.rename mapping.lift = operation.code := by
  cases operation <;> rfl

/-- All ordinary word binary builtins and their Hull aliases preserve their
independent arithmetic result and the exact argument-evaluation heap. -/
theorem wordBinary {name : String} (operation : WordBinary)
    (named : primitiveName name = operation.name)
    {scope : Scope} {left right : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope name .word [⟨.word, left⟩, ⟨.word, right⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {leftValue rightValue : Core.Word}
    (arguments : Core.Evaluates environment initial
      ((packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression.rename mapping)
      (.inRight .word (.pair (.word leftValue) (.word rightValue))) final)
    (sourceType : Ty) :
    ∃ result target, Semantics.primitive? name sourceType [.word leftValue, .word rightValue] = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final := by
  have normalized := lowerBuiltin_primitiveName scope name .word [⟨.word, left⟩, ⟨.word, right⟩]
  rw [compiled, named, operation.lowered] at normalized
  have same : lowered = ⟨.word, Core.LanguageResult.bind .word
      (packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression
      (Core.LanguageResult.success operation.code)⟩ := Option.some.inj normalized
  cases same
  refine ⟨.value (.word (operation.eval leftValue rightValue)),
    .inRight .word (.word (operation.eval leftValue rightValue)), ?_, .value (.word _), ?_⟩
  · rw [primitiveName_meaning, named]
    exact operation.meaning sourceType leftValue rightValue
  · change Core.Evaluates environment initial
      (Core.LanguageResult.bind .word
        ((packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression.rename mapping)
        (Core.LanguageResult.success (operation.code.rename mapping.lift))) _ final
    rw [operation.renamed]
    exact Core.LanguageResult.bind_success .word arguments
      (.inRight (operation.evaluates leftValue rightValue environment final))

inductive WordUnary where
  | bitNot | clz
  deriving Repr, DecidableEq

def WordUnary.name : WordUnary → String
  | .bitNot => "not" | .clz => "clz"

def WordUnary.eval : WordUnary → Core.Word → Core.Word
  | .bitNot => Core.Word.bitNot | .clz => Core.Word.clz

def WordUnary.operation : WordUnary → Core.UnaryOp
  | .bitNot => .wordNot | .clz => .wordClz

def WordUnary.code (operation : WordUnary) : Core.Expr :=
  .apply (.lambda .word .word (.unary operation.operation (.var 0))) (.var 0)

theorem WordUnary.lowered (operation : WordUnary) (scope : Scope) (argument : Core.Expr) :
    lowerBuiltin scope operation.name .word [⟨.word, argument⟩] =
      .ok ⟨.word, Core.LanguageResult.bind .word argument
        (Core.LanguageResult.success operation.code)⟩ := by
  cases operation <;> rfl

theorem WordUnary.meaning (operation : WordUnary) (type : Ty) (value : Core.Word) :
    Semantics.primitive? operation.name type [.word value] =
      some (.value (.word (operation.eval value))) := by
  cases operation <;> rfl

theorem WordUnary.evaluates (operation : WordUnary) (value : Core.Word)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (.word value :: environment) store operation.code
      (.word (operation.eval value)) store := by
  cases operation <;> exact .apply .lambda (.var rfl) (.unary (.var rfl) rfl)

theorem WordUnary.renamed (operation : WordUnary) (mapping : Core.Renaming) :
    operation.code.rename mapping.lift = operation.code := by
  cases operation <;> rfl

theorem wordUnary {name : String} (operation : WordUnary)
    (named : primitiveName name = operation.name)
    {scope : Scope} {argument : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope name .word [⟨.word, argument⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {value : Core.Word}
    (evaluated : Core.Evaluates environment initial (argument.rename mapping)
      (.inRight .word (.word value)) final) (sourceType : Ty) :
    ∃ result target, Semantics.primitive? name sourceType [.word value] = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final := by
  have normalized := lowerBuiltin_primitiveName scope name .word [⟨.word, argument⟩]
  rw [compiled, named, operation.lowered] at normalized
  have same : lowered = ⟨.word, Core.LanguageResult.bind .word argument
      (Core.LanguageResult.success operation.code)⟩ := Option.some.inj normalized
  cases same
  refine ⟨.value (.word (operation.eval value)), .inRight .word (.word (operation.eval value)),
    ?_, .value (.word _), ?_⟩
  · rw [primitiveName_meaning, named]
    exact operation.meaning sourceType value
  · change Core.Evaluates environment initial
      (Core.LanguageResult.bind .word (argument.rename mapping)
        (Core.LanguageResult.success (operation.code.rename mapping.lift))) _ final
    rw [operation.renamed]
    exact Core.LanguageResult.bind_success .word evaluated
      (.inRight (operation.evaluates value environment final))

/-- The Hull integer conversions are word-preserving in both specifications. -/
theorem conversion {name : String}
    (named : name = "wordToInteger" ∨ name = "wordFromInteger")
    {scope : Scope} {argument : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope name .word [⟨.word, argument⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {value : Core.Word}
    (evaluated : Core.Evaluates environment initial (argument.rename mapping)
      (.inRight .word (.word value)) final) (sourceType : Ty) :
    Semantics.primitive? name sourceType [.word value] = some (.value (.word value)) ∧
      ResultRel lowered.type (.value (.word value)) (.inRight .word (.word value)) ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping)
        (.inRight .word (.word value)) final := by
  rcases named with rfl | rfl
  all_goals
    have same : ⟨.word, argument⟩ = lowered := Except.ok.inj compiled
    cases same
    exact ⟨rfl, .value (.word _), evaluated⟩

inductive WordTernary where
  | addMod | mulMod
  deriving Repr, DecidableEq

def WordTernary.name : WordTernary → String
  | .addMod => "addmod" | .mulMod => "mulmod"

def WordTernary.eval : WordTernary → Core.Word → Core.Word → Core.Word → Core.Word
  | .addMod => Core.Word.addMod | .mulMod => Core.Word.mulMod

def WordTernary.operation : WordTernary → Core.TernaryOp
  | .addMod => .wordAddMod | .mulMod => .wordMulMod

def WordTernary.code (operation : WordTernary) : Core.Expr :=
  .apply (.lambda .word .word
    (.apply (.lambda .word .word
      (.apply (.lambda .word .word (.ternary operation.operation (.var 0) (.var 1) (.var 2)))
        (.first (.var 2)))) (.first (.second (.var 1))))) (.second (.second (.var 0)))

theorem WordTernary.lowered (operation : WordTernary) (scope : Scope) (first second third : Core.Expr) :
    lowerBuiltin scope operation.name .word [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩] =
      .ok ⟨.word, Core.LanguageResult.bind .word
        (packArguments [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩]).expression
        (Core.LanguageResult.success operation.code)⟩ := by
  cases operation <;> rfl

theorem WordTernary.meaning (operation : WordTernary) (type : Ty) (first second third : Core.Word) :
    Semantics.primitive? operation.name type [.word first, .word second, .word third] =
      some (.value (.word (operation.eval first second third))) := by
  cases operation <;> rfl

theorem WordTernary.evaluates (operation : WordTernary) (first second third : Core.Word)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (.pair (.word first) (.pair (.word second) (.word third)) :: environment)
      store operation.code (.word (operation.eval first second third)) store := by
  cases operation <;>
    exact .apply .lambda (.second (.second (.var rfl)))
      (.apply .lambda (.first (.second (.var rfl)))
        (.apply .lambda (.first (.var rfl)) (.ternary (.var rfl) (.var rfl) (.var rfl) rfl)))

theorem WordTernary.renamed (operation : WordTernary) (mapping : Core.Renaming) :
    operation.code.rename mapping.lift = operation.code := by
  cases operation <;> rfl

theorem wordTernary (operation : WordTernary)
    {scope : Scope} {first second third : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name .word
      [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {firstValue secondValue thirdValue : Core.Word}
    (arguments : Core.Evaluates environment initial
      ((packArguments [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩]).expression.rename mapping)
      (.inRight .word (.pair (.word firstValue) (.pair (.word secondValue) (.word thirdValue)))) final)
    (sourceType : Ty) :
    ∃ result target, Semantics.primitive? operation.name sourceType
        [.word firstValue, .word secondValue, .word thirdValue] = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final := by
  rw [operation.lowered] at compiled
  cases compiled
  refine ⟨.value (.word (operation.eval firstValue secondValue thirdValue)),
    .inRight .word (.word (operation.eval firstValue secondValue thirdValue)),
    operation.meaning sourceType firstValue secondValue thirdValue, .value (.word _), ?_⟩
  change Core.Evaluates environment initial
    (Core.LanguageResult.bind .word
      ((packArguments [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩]).expression.rename mapping)
      (Core.LanguageResult.success (operation.code.rename mapping.lift))) _ final
  rw [operation.renamed]
  exact Core.LanguageResult.bind_success .word arguments
    (.inRight (operation.evaluates firstValue secondValue thirdValue environment final))

theorem pop {scope : Scope} {argument : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope "pop" .unit [⟨.word, argument⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {value : Core.Word}
    (evaluated : Core.Evaluates environment initial (argument.rename mapping)
      (.inRight .word (.word value)) final) (sourceType : Ty) :
    Semantics.primitive? "pop" sourceType [.word value] = some (.value .unit) ∧
      ResultRel lowered.type (.value .unit) (.inRight .word .unit) ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word .unit) final := by
  have same : ⟨.unit, Core.LanguageResult.bind .unit argument
      (Core.LanguageResult.success (.apply (.lambda .word .unit .unit) (.var 0)))⟩ = lowered :=
    Except.ok.inj compiled
  cases same
  exact ⟨rfl, .value .unit, Core.LanguageResult.bind_success .unit evaluated
    (.inRight (.apply .lambda (.var rfl) .unit))⟩

/-- Repackage an evaluated Core boolean according to the actual checked Hull
result type. This also covers Hull's sum-of-Unit boolean representation. -/
theorem booleanResult {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    {conditionCode expression : Core.Expr} {value : Bool}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    (compiled : boolean type conditionCode = .ok expression)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial (conditionCode.rename mapping) (.bool value) final) :
    ∃ source target, Semantics.booleanResult sourceType value = .value source ∧
      ValueRel type source target ∧
      Core.Evaluates environment initial (expression.rename mapping) target final := by
  obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape typeCompiled
  by_cases native : type = .bool
  · have same : shape = .bool := coreType_injective (targetShape.trans native)
    subst shape
    simp only [boolean, native, ↓reduceIte] at compiled
    cases compiled
    rw [native]
    exact ⟨.bool value, .bool value,
      by simp [Semantics.booleanResult, Semantics.boolean?, sourceShape], .bool _, evaluated⟩
  · by_cases sum : type = .sum .unit .unit
    · have same : shape = .sum .unit .unit := coreType_injective (targetShape.trans sum)
      subst shape
      simp only [boolean, sum, ↓reduceIte] at compiled
      cases compiled
      rw [sum]
      cases value with
      | false => exact ⟨.inl .unit, .inLeft .unit .unit,
          by simp [Semantics.booleanResult, Semantics.boolean?, sourceShape],
          .inl .unit, .ifFalse evaluated (.inLeft .unit)⟩
      | true => exact ⟨.inr .unit, .inRight .unit .unit,
          by simp [Semantics.booleanResult, Semantics.boolean?, sourceShape],
          .inr .unit, .ifTrue evaluated (.inRight .unit)⟩
    · simp [boolean, native, sum, fail] at compiled

inductive WordComparison where
  | eq | lt | gt | slt | sgt
  deriving Repr, DecidableEq

def WordComparison.name : WordComparison → String
  | .eq => "eq" | .lt => "lt" | .gt => "gt" | .slt => "slt" | .sgt => "sgt"

def WordComparison.eval : WordComparison → Core.Word → Core.Word → Bool
  | .eq => (· == ·)
  | .lt => fun left right => left.val < right.val
  | .gt => fun left right => left.val > right.val
  | .slt => fun left right => Core.Word.signedGt right left
  | .sgt => Core.Word.signedGt

def WordComparison.body : WordComparison → Core.Expr
  | .eq => .binary .wordEq (.var 0) (.var 1)
  | .lt => .binary .wordGt (.var 1) (.var 0)
  | .gt => .binary .wordGt (.var 0) (.var 1)
  | .slt => .binary .wordSgt (.var 1) (.var 0)
  | .sgt => .binary .wordSgt (.var 0) (.var 1)

def WordComparison.wordCode (operation : WordComparison) : Core.Expr :=
  .apply (.lambda .word .word
    (.apply (.lambda .word .word
      (.ifE operation.body (.word (Core.Word.ofNatModulo 1)) (.word Core.Word.zero)))
      (.first (.var 1)))) (.second (.var 0))

def WordComparison.code (operation : WordComparison) : Core.Expr :=
  .unary .boolNot (.binary .wordEq operation.wordCode (.word Core.Word.zero))

theorem WordComparison.lowered (operation : WordComparison) (scope : Scope)
    (type : Core.Ty) (left right : Core.Expr) :
    lowerBuiltin scope operation.name type [⟨.word, left⟩, ⟨.word, right⟩] = (do
      let output ← boolean type operation.code
      pure ⟨type, Core.LanguageResult.bind type
        (packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression
        (Core.LanguageResult.success output)⟩) := by
  cases operation <;> rfl

theorem WordComparison.meaning (operation : WordComparison) (type : Ty) (left right : Core.Word) :
    Semantics.primitive? operation.name type [.word left, .word right] =
      some (Semantics.booleanResult type (operation.eval left right)) := by
  cases operation <;> rfl

theorem WordComparison.body_evaluates (operation : WordComparison) (left right : Core.Word)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (.word left :: .word right :: environment) store operation.body
      (.bool (operation.eval left right)) store := by
  cases operation <;> exact .binary (.var rfl) (.var rfl) rfl

theorem WordComparison.evaluates (operation : WordComparison) (left right : Core.Word)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (.pair (.word left) (.word right) :: environment) store operation.code
      (.bool (operation.eval left right)) store := by
  have body := operation.body_evaluates left right
    (.pair (.word left) (.word right) :: environment) store
  cases truth : operation.eval left right with
  | false =>
      rw [truth] at body
      exact .unary (.binary
        (.apply .lambda (.second (.var rfl))
          (.apply .lambda (.first (.var rfl)) (.ifFalse body .word))) .word rfl) rfl
  | true =>
      rw [truth] at body
      exact .unary (.binary
        (.apply .lambda (.second (.var rfl))
          (.apply .lambda (.first (.var rfl)) (.ifTrue body .word))) .word rfl) rfl

theorem WordComparison.renamed (operation : WordComparison) (mapping : Core.Renaming) :
    operation.code.rename mapping.lift = operation.code := by
  cases operation <;> rfl

theorem wordComparison {name : String} (operation : WordComparison)
    (named : primitiveName name = operation.name)
    {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {left right : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type [⟨.word, left⟩, ⟨.word, right⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {leftValue rightValue : Core.Word}
    (arguments : Core.Evaluates environment initial
      ((packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression.rename mapping)
      (.inRight .word (.pair (.word leftValue) (.word rightValue))) final) :
    ∃ result target, Semantics.primitive? name sourceType [.word leftValue, .word rightValue] = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final := by
  have normalized := lowerBuiltin_primitiveName scope name type [⟨.word, left⟩, ⟨.word, right⟩]
  rw [compiled, named, operation.lowered] at normalized
  cases boolCompiled : boolean type operation.code with
  | error error =>
      rw [boolCompiled] at normalized
      cases normalized
  | ok output =>
      rw [boolCompiled] at normalized
      have same : lowered = ⟨type, Core.LanguageResult.bind type
          (packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression
          (Core.LanguageResult.success output)⟩ := Option.some.inj normalized
      cases same
      have evaluated := operation.evaluates leftValue rightValue environment final
      rw [← operation.renamed mapping] at evaluated
      obtain ⟨source, target, meaning, related, evaluated⟩ := booleanResult typeCompiled boolCompiled evaluated
      refine ⟨.value source, .inRight .word target, ?_, .value related, ?_⟩
      · rw [primitiveName_meaning, named, operation.meaning, meaning]
      · exact Core.LanguageResult.bind_success type arguments (.inRight evaluated)

theorem boolLike_condition {type : Core.Ty} {source : Semantics.Value} {target : Core.Value}
    (supported : boolLike type = true) (related : ValueRel type source target) :
    ∃ truth, Semantics.condition? source = some truth := by
  have alternatives : type = .bool ∨ type = .sum .unit .unit := by
    cases type <;> simp_all [boolLike, BEq.beq, Core.instBEqTy.beq]
    rename_i left right
    cases left <;> cases right <;> simp_all [Core.instBEqTy.beq]
  rcases alternatives with native | sum
  · rw [native] at related
    cases related
    exact ⟨_, rfl⟩
  · rw [sum] at related
    cases related with
    | inl payload => cases payload; exact ⟨false, rfl⟩
    | inr payload => cases payload; exact ⟨true, rfl⟩

theorem iszero_lowered (scope : Scope) (type : Core.Ty) (argument : Lowered) :
    lowerBuiltin scope "iszero" type [argument] =
      (if boolLike argument.type then do
        let input ← condition argument
        let output ← boolean type (.unary .boolNot (.var 0))
        pure ⟨type, Core.LanguageResult.bind type input (Core.LanguageResult.success output)⟩
      else fail "Hull iszero expects one boolean value") := by
  rfl

theorem iszero {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {argument lowered : Lowered}
    (compiled : lowerBuiltin scope "iszero" type [argument] = .ok lowered)
    {source : Semantics.Value} {target : Core.Value}
    (related : ValueRel argument.type source target)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial (argument.expression.rename mapping)
      (.inRight .word target) final) :
    ∃ result target, Semantics.primitive? "iszero" sourceType [source] = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final := by
  rw [iszero_lowered] at compiled
  split at compiled
  next supported =>
    obtain ⟨truth, sourceCondition⟩ := boolLike_condition supported related
    obtain ⟨input, inputCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨output, outputCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    have inputEvaluation := ExpressionCorrespondence.condition_evaluates inputCompiled related sourceCondition evaluated
    have negate : Core.Evaluates (.bool truth :: environment) final
        ((Core.Expr.unary .boolNot (.var 0)).rename mapping.lift) (.bool (!truth)) final :=
      .unary (.var rfl) rfl
    obtain ⟨sourceResult, targetResult, meaning, resultRelated, resultEvaluation⟩ :=
      booleanResult typeCompiled outputCompiled negate
    refine ⟨.value sourceResult, .inRight .word targetResult, ?_, .value resultRelated, ?_⟩
    · simp only [Semantics.primitive?, sourceCondition, meaning]
    · exact Core.LanguageResult.bind_success type inputEvaluation (.inRight resultEvaluation)
  next rejected => cases compiled

/-- A failed argument pack never executes the builtin body, including effect
builtins. The language error and the exact heap reached by the arguments are
preserved through the real compiler's wrapper. -/
theorem argument_failure {scope : Scope} {name : String} {type : Core.Ty}
    {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type arguments = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {reason : Core.Word}
    (evaluated : Core.Evaluates environment initial
      ((packArguments arguments).expression.rename mapping)
      (.inLeft (packArguments arguments).type (.word reason)) final) :
    Core.Evaluates environment initial (lowered.expression.rename mapping)
      (.inLeft lowered.type (.word reason)) final := by
  simp only [lowerBuiltin] at compiled
  split at compiled
  next effect =>
    obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    cases compiled
    exact Core.LanguageResult.bind_failure _ evaluated
  next pureOperation =>
    split at compiled
    next conversion =>
      split at compiled
      next arity =>
        obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
        cases checked
        obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
        cases checked
        cases compiled
        exact evaluated
      next arity => cases compiled
    next ordinary =>
      split at compiled
      next zero =>
        split at compiled
        next supported =>
          obtain ⟨input, inputCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
          obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
          cases compiled
          exact Core.LanguageResult.bind_failure _
            (ExpressionCorrespondence.condition_failure inputCompiled evaluated)
        next unsupported => cases compiled
      next other =>
        obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
        obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
        split at compiled
        next comparison =>
          obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
          cases compiled
          exact Core.LanguageResult.bind_failure _ evaluated
        next word =>
          obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
          cases checked
          cases compiled
          exact Core.LanguageResult.bind_failure _ evaluated

end Solcore.Frontend.RustHull.BuiltinCorrespondence
