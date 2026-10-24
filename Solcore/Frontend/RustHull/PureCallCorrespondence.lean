import Solcore.Frontend.RustHull.BuiltinCorrespondence
import Solcore.Frontend.RustHull.StatementCorrespondence
import Solcore.Frontend.RustHull.ScalarInputCorrespondence

/-! Pure calls preserve the independent Hull meaning through the actual
expression-list compiler and argument pack. Every argument may allocate or
update source locals; the world and exact Core heap are threaded in order. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.PureCallCorrespondence

open Correspondence StatementCorrespondence ScalarExecution

inductive ArgumentsRel : List Lowered → List Semantics.Value → List Core.Value → Prop where
  | nil : ArgumentsRel [] [] []
  | cons {argument : Lowered} {arguments : List Lowered} {source : Semantics.Value}
      {sources : List Semantics.Value} {target : Core.Value} {targets : List Core.Value}
      (head : ValueRel argument.type source target) (tail : ArgumentsRel arguments sources targets) :
      ArgumentsRel (argument :: arguments) (source :: sources) (target :: targets)

private theorem pair_rename (leftType rightType : Core.Ty) (left right : Core.Expr)
    (mapping : Core.Renaming) :
    (Core.LocalSequence.pair leftType rightType left right).rename mapping =
      Core.LocalSequence.pair leftType rightType (left.rename mapping) (right.rename mapping) := by
  simp [Core.LocalSequence.pair, Core.LanguageResult.bind, Core.LanguageResult.success,
    Core.Expr.rename, Core.Renaming.lift]

private theorem exprs_cons {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {argument : Expr} {rest : List Expr} {initial final : Semantics.State σ}
    {sources : List Semantics.Value}
    (evaluated : Semantics.EvalExprs functions effects sourceEnvironment (argument :: rest)
      initial (.value sources) final) :
    ∃ source values middle, sources = source :: values ∧
      Semantics.EvalExpr functions effects sourceEnvironment argument initial (.value source) middle ∧
      Semantics.EvalExprs functions effects sourceEnvironment rest middle (.value values) final := by
  generalize resultEq : Semantics.Result.value sources = result at evaluated
  cases evaluated with
  | cons head tail =>
      rename_i middle source result
      cases result with
      | fault reason => simp [Semantics.Result.map] at resultEq
      | value values =>
          simp only [Semantics.Result.map, Semantics.Result.value.injEq] at resultEq
          exact ⟨source, values, middle, resultEq, head, tail⟩
  | fault => cases resultEq

theorem arguments_preserve {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} {arguments : List Expr}
    (preserves : ∀ argument ∈ arguments, NormalExprPreserves functions effects signatures external argument)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {sources : List Semantics.Value}
    (evaluated : Semantics.EvalExprs functions effects sourceEnvironment arguments initial (.value sources) final)
    {fuel : Nat} {scope : Scope} {lowered : List Lowered}
    (compiled : arguments.mapM (lowerExpression fuel signatures scope) = .ok lowered)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heap : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension targets finalStore,
      ArgumentsRel lowered sources targets ∧
      Core.Evaluates environment store ((packArguments lowered).expression.rename mapping)
        (.inRight .word (bundleValues targets)) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  induction arguments generalizing initial final sources lowered world mapping environment store with
  | nil =>
      cases compiled
      cases evaluated
      exact ⟨[], [], store, .nil, .inRight .unit, by simpa using heap, externalRelated⟩
  | cons argument rest ih =>
      obtain ⟨source, sources, middle, rfl, head, tail⟩ := exprs_cons evaluated
      simp only [List.mapM_cons] at compiled
      obtain ⟨headCode, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tailCode, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨headExtension, target, middleStore, related, headEvaluation, middleHeap, middleExternal⟩ :=
        preserves argument (by simp) head headCompiled environmentRelated heap externalRelated
      cases rest with
      | nil =>
          cases tailCompiled
          cases tail
          exact ⟨headExtension, [target], middleStore, .cons related .nil,
            headEvaluation, middleHeap, middleExternal⟩
      | cons next rest =>
          have tailPreserves : ∀ value ∈ next :: rest,
              NormalExprPreserves functions effects signatures external value := by
            intro value member
            exact preserves value (by simp [member])
          have middleEnvironment := (environmentRelated.extendWorld headExtension).prepend [target]
          obtain ⟨tailExtension, targets, finalStore, tailRelated, tailEvaluation, finalHeap, finalExternal⟩ :=
            ih tailPreserves tail tailCompiled middleEnvironment middleHeap middleExternal
          have nonempty : tailCode ≠ [] := by
            intro empty
            subst tailCode
            simp only [List.mapM_cons] at tailCompiled
            obtain ⟨_, _, tailCompiled⟩ := lower_bind_eq_ok.mp tailCompiled
            obtain ⟨_, _, returned⟩ := lower_bind_eq_ok.mp tailCompiled
            cases returned
          have targetsNonempty : targets ≠ [] := by
            intro empty
            subst targets
            cases tailRelated
            exact nonempty rfl
          refine ⟨headExtension ++ tailExtension, target :: targets, finalStore,
            .cons related tailRelated, ?_, ?_, finalExternal⟩
          · have renamed : ((packArguments tailCode).expression.rename mapping).weakenAt 0 =
                (packArguments tailCode).expression.rename (fun index => 1 + mapping index) := by
              simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
              congr 1
              funext index
              simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
            cases tailCode with
            | nil => exact (nonempty rfl).elim
            | cons nextCode restCode =>
                change Core.Evaluates environment store
                  ((Core.LocalSequence.pair headCode.type (packArguments (nextCode :: restCode)).type
                    headCode.expression (packArguments (nextCode :: restCode)).expression).rename mapping) _ _
                rw [pair_rename]
                have tailEvaluation' : Core.Evaluates (target :: environment) middleStore
                    (((packArguments (nextCode :: restCode)).expression.rename mapping).weakenAt 0)
                    (.inRight .word (bundleValues targets)) finalStore := by
                  rw [renamed]
                  exact tailEvaluation
                have paired := Core.LocalSequence.pair_success headCode.type
                  (packArguments (nextCode :: restCode)).type headEvaluation tailEvaluation'
                cases targets with
                | nil => exact (targetsNonempty rfl).elim
                | cons firstTarget restTargets => exact paired
          · simpa only [List.append_assoc] using finalHeap

open BuiltinCorrespondence

inductive PureBuiltin where
  | binary (operation : WordBinary)
  | unary (operation : WordUnary)
  | ternary (operation : WordTernary)
  | comparison (operation : WordComparison)
  | toInteger | fromInteger | iszero | pop
  deriving Repr, DecidableEq

def PureBuiltin.name : PureBuiltin → String
  | .binary operation => operation.name | .unary operation => operation.name
  | .ternary operation => operation.name | .comparison operation => operation.name
  | .toInteger => "wordToInteger" | .fromInteger => "wordFromInteger"
  | .iszero => "iszero" | .pop => "pop"

def pureBuiltin? (name : String) : Option PureBuiltin :=
  match primitiveName name with
  | "add" => some (.binary .add) | "sub" => some (.binary .sub) | "mul" => some (.binary .mul)
  | "div" => some (.binary .udiv) | "mod" => some (.binary .umod)
  | "sdiv" => some (.binary .sdiv) | "smod" => some (.binary .smod)
  | "exp" => some (.binary .pow) | "signextend" => some (.binary .signExtend)
  | "and" => some (.binary .bitAnd) | "or" => some (.binary .bitOr) | "xor" => some (.binary .bitXor)
  | "byte" => some (.binary .byteAt) | "shl" => some (.binary .shl) | "shr" => some (.binary .shr)
  | "sar" => some (.binary .sar)
  | "not" => some (.unary .bitNot) | "clz" => some (.unary .clz)
  | "addmod" => some (.ternary .addMod) | "mulmod" => some (.ternary .mulMod)
  | "eq" => some (.comparison .eq) | "lt" => some (.comparison .lt) | "gt" => some (.comparison .gt)
  | "slt" => some (.comparison .slt) | "sgt" => some (.comparison .sgt)
  | "wordToInteger" => some .toInteger | "wordFromInteger" => some .fromInteger
  | "iszero" => some .iszero | "pop" => some .pop
  | _ => none

theorem pureBuiltin_name {name : String} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation) : primitiveName name = operation.name := by
  unfold pureBuiltin? at classified
  split at classified <;> cases classified <;> assumption

theorem pureBuiltin_known {name : String} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation) (type : Ty) (values : List Semantics.Value) :
    (Semantics.primitive? name type values).isSome = true := by
  rw [primitiveName_meaning, pureBuiltin_name classified]
  cases operation with
  | binary op => cases op <;> rfl
  | unary op => cases op <;> rfl
  | ternary op => cases op <;> rfl
  | comparison op => cases op <;> rfl
  | toInteger => rfl
  | fromInteger => rfl
  | iszero => rfl
  | pop => rfl

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
      have same : lowered = result := Option.some.inj normalized
      exact congrArg Except.ok same.symm

private theorem ArgumentsRel.oneWord {arguments : List Lowered} {targets : List Core.Value}
    {value : Core.Word} (related : ArgumentsRel arguments [.word value] targets) :
    ∃ expression, arguments = [⟨.word, expression⟩] ∧ targets = [.word value] := by
  cases related with
  | cons head tail =>
      cases tail
      rename_i argument target
      cases argument with
      | mk type expression =>
          cases head
          exact ⟨expression, rfl, rfl⟩

private theorem ArgumentsRel.twoWords {arguments : List Lowered} {targets : List Core.Value}
    {left right : Core.Word} (related : ArgumentsRel arguments [.word left, .word right] targets) :
    ∃ leftCode rightCode, arguments = [⟨.word, leftCode⟩, ⟨.word, rightCode⟩] ∧
      targets = [.word left, .word right] := by
  cases related with
  | cons head tail =>
      obtain ⟨rightCode, rfl, rfl⟩ := tail.oneWord
      rename_i argument target
      cases argument with
      | mk type expression =>
          cases head
          exact ⟨expression, rightCode, rfl, rfl⟩

private theorem ArgumentsRel.threeWords {arguments : List Lowered} {targets : List Core.Value}
    {first second third : Core.Word}
    (related : ArgumentsRel arguments [.word first, .word second, .word third] targets) :
    ∃ firstCode secondCode thirdCode,
      arguments = [⟨.word, firstCode⟩, ⟨.word, secondCode⟩, ⟨.word, thirdCode⟩] ∧
      targets = [.word first, .word second, .word third] := by
  cases related with
  | cons head tail =>
      obtain ⟨secondCode, thirdCode, rfl, rfl⟩ := tail.twoWords
      rename_i argument target
      cases argument with
      | mk type expression =>
          cases head
          exact ⟨expression, secondCode, thirdCode, rfl, rfl⟩

private theorem binary_value (operation : Core.Word → Core.Word → Core.Word)
    {values : List Semantics.Value} {result : Semantics.Value}
    (computed : Semantics.binaryWords operation values = .value result) :
    ∃ left right, values = [.word left, .word right] ∧ result = .word (operation left right) := by
  unfold Semantics.binaryWords at computed
  split at computed
  next left right => cases computed; exact ⟨left, right, rfl, rfl⟩
  next => cases computed

private theorem unary_value (operation : Core.Word → Core.Word)
    {values : List Semantics.Value} {result : Semantics.Value}
    (computed : Semantics.unaryWord operation values = .value result) :
    ∃ value, values = [.word value] ∧ result = .word (operation value) := by
  unfold Semantics.unaryWord at computed
  split at computed
  next value => cases computed; exact ⟨value, rfl, rfl⟩
  next => cases computed

private theorem ternary_value (operation : Core.Word → Core.Word → Core.Word → Core.Word)
    {values : List Semantics.Value} {result : Semantics.Value}
    (computed : Semantics.ternaryWords operation values = .value result) :
    ∃ first second third, values = [.word first, .word second, .word third] ∧
      result = .word (operation first second third) := by
  unfold Semantics.ternaryWords at computed
  split at computed
  next first second third => cases computed; exact ⟨first, second, third, rfl, rfl⟩
  next => cases computed

private theorem comparison_value (type : Ty) (operation : Core.Word → Core.Word → Bool)
    {values : List Semantics.Value} {result : Semantics.Value}
    (computed : Semantics.compareWords type operation values = .value result) :
    ∃ left right, values = [.word left, .word right] ∧
      Semantics.booleanResult type (operation left right) = .value result := by
  unfold Semantics.compareWords at computed
  split at computed
  next left right => exact ⟨left, right, rfl, computed⟩
  next => cases computed

private theorem binary_expected (operation : WordBinary) (scope : Scope) (type : Core.Ty)
    (left right : Core.Expr) {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type [⟨.word, left⟩, ⟨.word, right⟩] = .ok lowered) : type = .word := by
  have reduced : lowerBuiltin scope operation.name type [⟨.word, left⟩, ⟨.word, right⟩] = (do
      expectType type .word
      pure ⟨type, Core.LanguageResult.bind type (packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression
        (Core.LanguageResult.success operation.code)⟩) := by
    cases operation <;> rfl
  rw [reduced] at compiled
  obtain ⟨checked, checkedType, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  exact expectType_eq_of_ok checkedType

private theorem unary_expected (operation : WordUnary) (scope : Scope) (type : Core.Ty)
    (argument : Core.Expr) {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type [⟨.word, argument⟩] = .ok lowered) : type = .word := by
  have reduced : lowerBuiltin scope operation.name type [⟨.word, argument⟩] = (do
      expectType type .word
      pure ⟨type, Core.LanguageResult.bind type (packArguments [⟨.word, argument⟩]).expression
        (Core.LanguageResult.success operation.code)⟩) := by
    cases operation <;> rfl
  rw [reduced] at compiled
  obtain ⟨checked, checkedType, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  exact expectType_eq_of_ok checkedType

private theorem ternary_expected (operation : WordTernary) (scope : Scope) (type : Core.Ty)
    (first second third : Core.Expr) {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩] = .ok lowered) : type = .word := by
  have reduced : lowerBuiltin scope operation.name type [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩] = (do
      expectType type .word
      pure ⟨type, Core.LanguageResult.bind type (packArguments [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩]).expression
        (Core.LanguageResult.success operation.code)⟩) := by
    cases operation <;> rfl
  rw [reduced] at compiled
  obtain ⟨checked, checkedType, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  exact expectType_eq_of_ok checkedType

private theorem conversion_expected {name : String}
    (named : name = "wordToInteger" ∨ name = "wordFromInteger")
    (scope : Scope) (type : Core.Ty) (argument : Core.Expr) {lowered : Lowered}
    (compiled : lowerBuiltin scope name type [⟨.word, argument⟩] = .ok lowered) : type = .word := by
  have reduced : lowerBuiltin scope name type [⟨.word, argument⟩] = (do
      expectType .word type
      pure ⟨.word, argument⟩) := by
    rcases named with rfl | rfl <;> rfl
  rw [reduced] at compiled
  obtain ⟨checked, checkedType, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  exact (expectType_eq_of_ok checkedType).symm

private theorem pop_expected (scope : Scope) (type : Core.Ty) (argument : Core.Expr) {lowered : Lowered}
    (compiled : lowerBuiltin scope "pop" type [⟨.word, argument⟩] = .ok lowered) : type = .unit := by
  have reduced : lowerBuiltin scope "pop" type [⟨.word, argument⟩] = (do
      expectType type .unit
      pure ⟨type, Core.LanguageResult.bind type argument
        (Core.LanguageResult.success (.apply (.lambda .word .unit .unit) (.var 0)))⟩) := by rfl
  rw [reduced] at compiled
  obtain ⟨checked, checkedType, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  exact expectType_eq_of_ok checkedType

private theorem normal_result {name : String} {sourceType : Ty} {sources : List Semantics.Value}
    {source : Semantics.Value} {lowered : Lowered} {mapping : Core.Renaming}
    {environment : Core.Environment} {initial final : Core.Store}
    (computed : Semantics.primitive? name sourceType sources = some (.value source))
    (preserved : ∃ result target, Semantics.primitive? name sourceType sources = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final) :
    ∃ target, ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  obtain ⟨result, target, meaning, related, evaluated⟩ := preserved
  rw [computed] at meaning
  cases meaning
  cases related with
  | value related => exact ⟨_, related, evaluated⟩

theorem canonical_preserves (operation : PureBuiltin)
    {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value} {source : Semantics.Value}
    (computed : Semantics.primitive? operation.name sourceType sources = some (.value source))
    (related : ArgumentsRel arguments sources targets)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) final) :
    ∃ target, ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  cases operation with
  | binary op =>
      dsimp only [PureBuiltin.name] at compiled computed
      have model : Semantics.primitive? op.name sourceType sources =
          some (Semantics.binaryWords op.eval sources) := by cases op <;> rfl
      have sourceComputed := computed
      rw [model] at sourceComputed
      obtain ⟨left, right, rfl, rfl⟩ := binary_value op.eval (Option.some.inj sourceComputed)
      obtain ⟨leftCode, rightCode, rfl, rfl⟩ := related.twoWords
      have expected := binary_expected op scope type leftCode rightCode compiled
      subst type
      exact normal_result computed (wordBinary op (by cases op <;> rfl) compiled evaluated sourceType)
  | unary op =>
      dsimp only [PureBuiltin.name] at compiled computed
      have model : Semantics.primitive? op.name sourceType sources =
          some (Semantics.unaryWord op.eval sources) := by cases op <;> rfl
      have sourceComputed := computed
      rw [model] at sourceComputed
      obtain ⟨value, rfl, rfl⟩ := unary_value op.eval (Option.some.inj sourceComputed)
      obtain ⟨code, rfl, rfl⟩ := related.oneWord
      have expected := unary_expected op scope type code compiled
      subst type
      exact normal_result computed (wordUnary op (by cases op <;> rfl) compiled evaluated sourceType)
  | ternary op =>
      dsimp only [PureBuiltin.name] at compiled computed
      have model : Semantics.primitive? op.name sourceType sources =
          some (Semantics.ternaryWords op.eval sources) := by cases op <;> rfl
      have sourceComputed := computed
      rw [model] at sourceComputed
      obtain ⟨first, second, third, rfl, rfl⟩ := ternary_value op.eval (Option.some.inj sourceComputed)
      obtain ⟨firstCode, secondCode, thirdCode, rfl, rfl⟩ := related.threeWords
      have expected := ternary_expected op scope type firstCode secondCode thirdCode compiled
      subst type
      exact normal_result computed (wordTernary op compiled evaluated sourceType)
  | comparison op =>
      dsimp only [PureBuiltin.name] at compiled computed
      have model : Semantics.primitive? op.name sourceType sources =
          some (Semantics.compareWords sourceType op.eval sources) := by cases op <;> rfl
      have sourceComputed := computed
      rw [model] at sourceComputed
      obtain ⟨left, right, rfl, _⟩ := comparison_value sourceType op.eval (Option.some.inj sourceComputed)
      obtain ⟨leftCode, rightCode, rfl, rfl⟩ := related.twoWords
      exact normal_result computed
        (wordComparison op (by cases op <;> rfl) typeCompiled compiled evaluated)
  | toInteger | fromInteger =>
      have sourceComputed : Semantics.unaryWord id sources = .value source := Option.some.inj computed
      obtain ⟨value, rfl, rfl⟩ := unary_value id sourceComputed
      obtain ⟨code, rfl, rfl⟩ := related.oneWord
      have expected := conversion_expected (by first | exact Or.inl rfl | exact Or.inr rfl)
        scope type code compiled
      subst type
      obtain ⟨_, resultRelated, resultEvaluation⟩ := conversion
        (by first | exact Or.inl rfl | exact Or.inr rfl) compiled evaluated sourceType
      cases resultRelated with
      | value related => exact ⟨_, related, resultEvaluation⟩
  | iszero =>
      have originalComputed := computed
      change (some (match sources with
        | [value] => match Semantics.condition? value with
          | some truth => Semantics.booleanResult sourceType (!truth)
          | none => .fault (.invalidValue "boolean argument")
        | _ => .fault .arityMismatch)) = some (.value source) at computed
      split at computed
      next value =>
        cases related with
        | cons head tail =>
            cases tail
            exact normal_result originalComputed (iszero typeCompiled compiled head evaluated)
      next => cases computed
  | pop =>
      change (some (match sources with
        | [.word _] => Semantics.Result.value Semantics.Value.unit
        | _ => .fault (.invalidValue "pop argument"))) = some (.value source) at computed
      split at computed
      next value =>
        have same : Semantics.Value.unit = source := Semantics.Result.value.inj (Option.some.inj computed)
        subst source
        obtain ⟨code, rfl, rfl⟩ := related.oneWord
        have expected := pop_expected scope type code compiled
        subst type
        obtain ⟨_, resultRelated, resultEvaluation⟩ := pop compiled evaluated sourceType
        cases resultRelated with
        | value related => exact ⟨_, related, resultEvaluation⟩
      next => cases computed

/-- Dispatch every supported pure source name, including compiler aliases,
through the checked builtin implementation and its actual packed inputs. -/
theorem builtin_preserves {name : String} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value} {source : Semantics.Value}
    (computed : Semantics.primitive? name sourceType sources = some (.value source))
    (related : ArgumentsRel arguments sources targets)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) final) :
    ∃ target, ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  have accepted := normalized_compiled compiled
  rw [pureBuiltin_name classified] at accepted
  rw [primitiveName_meaning, pureBuiltin_name classified] at computed
  exact canonical_preserves operation typeCompiled accepted computed related evaluated

private theorem call_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {name : String} {type : Ty} {arguments : List Expr}
    {span : Option Span} {source : Semantics.Value} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    (notFunction : functions.find? (·.name == name) = none)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .call name arguments, span⟩ initial (.value source) final) :
    ∃ values, Semantics.EvalExprs functions effects sourceEnvironment arguments initial (.value values) final ∧
      Semantics.primitive? name type values = some (.value source) := by
  generalize resultEq : Semantics.Result.value source = result at evaluated
  cases evaluated <;> simp_all
  rename_i middle otherName otherArguments values kind argumentsEvaluated called
  cases called with
  | function selected _ =>
      exact (notFunction _ (List.mem_of_find?_eq_some selected)
        (by simpa only [beq_iff_eq] using List.find?_some selected)).elim
  | primitive _ computed => exact ⟨values, argumentsEvaluated, computed⟩
  | external _ notPrimitive _ =>
      have known := pureBuiltin_known classified type values
      rw [notPrimitive] at known
      cases known

private theorem call_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {name : String} {type : Ty} {arguments : List Expr} {span : Option Span} {lowered : Lowered}
    (notSignature : signatures.find? (·.name == name) = none)
    (compiled : lowerExpression (fuel + 1) signatures scope ⟨type, .call name arguments, span⟩ = .ok lowered) :
    ∃ expected codes, lowerType (fuel + 1) type = .ok expected ∧
      arguments.mapM (lowerExpression fuel signatures scope) = .ok codes ∧
      lowerBuiltin scope name expected codes = .ok lowered := by
  simp only [lowerExpression] at compiled
  obtain ⟨expected, typeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨codes, argumentsCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  simp only [notSignature] at compiled
  obtain ⟨result, builtinCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  cases returned
  exact ⟨expected, codes, typeCompiled, argumentsCompiled, builtinCompiled⟩

/-- A source call to a pure builtin is compositional through the public
expression lowerer. The only induction premises concern its source arguments;
function resolution and the complete builtin dispatch are proved here. -/
theorem call {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {name : String} {arguments : List Expr} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    (notFunction : functions.find? (·.name == name) = none)
    (notSignature : signatures.find? (·.name == name) = none)
    (preserves : ∀ argument ∈ arguments, NormalExprPreserves functions effects signatures external argument)
    (type : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .call name arguments, span⟩ := by
  intro sourceEnvironment initial final source evaluated
  obtain ⟨values, argumentsEvaluated, computed⟩ := call_source classified notFunction evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨expected, codes, typeCompiled, argumentsCompiled, builtinCompiled⟩ :=
        call_components notSignature compiled
      obtain ⟨extension, targets, finalStore, related, argumentsEvaluation, finalHeap, finalExternal⟩ :=
        arguments_preserve preserves argumentsEvaluated argumentsCompiled environmentRelated heap externalRelated
      obtain ⟨target, resultRelated, resultEvaluation⟩ :=
        builtin_preserves classified typeCompiled builtinCompiled computed related argumentsEvaluation
      exact ⟨extension, target, finalStore, resultRelated, resultEvaluation, finalHeap, finalExternal⟩

end Solcore.Frontend.RustHull.PureCallCorrespondence
