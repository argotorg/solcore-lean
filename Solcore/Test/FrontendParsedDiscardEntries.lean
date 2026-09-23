import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionLocalFragmentProperties
import Solcore.Frontend.RuntimeFunctionPreparationFactorization
import Solcore.Core.LocalFragment
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.TypedLetReturnBody

/-! Original semicolon prefixes preserve source rows while hidden Core binders
strictly discard arbitrary actual values. Costs and paths have independent oracles. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace DiscardEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"DiscardEntry", by decide⟩], by decide⟩⟩, 17⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def table (type : Core.Ty) : TypeNameTable := [(["T"], type), (["Bool"], .bool)]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "discard-entry.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, content.utf8ByteSize⟩) && source.span.contains source.value.body.span) s!"original complete ranges changed: {content}"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent type leaf missing")
  | ⟨_, .tuple [left, right]⟩ =>
      let a ← meaning types left; let b ← meaning types right
      return ⟨.product a.type b.type, by rw [atSource]; exact .pair a.evidence b.evidence⟩
  | _ => throw (IO.userError "outside independent annotation grammar")
termination_by sizeOf source
private structure Parameters (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial params inputs
private def parameters (types : TypeNameTable) (initial : LocalTypeInputs)
    (params : List Syntax.FunctionParameter) : IO (Parameters types initial params) := do
  match atParams : params with
  | [] => return ⟨initial, by rw [atParams]; exact .nil⟩
  | ⟨span, .typed none name annotation⟩ :: rest =>
      check (span.contains name.span && span.contains annotation.span) "original parameter range changed"
      let m ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← parameters types (initial.bindFresh owner name.value m.type) rest
        return ⟨tail.inputs, by rw [atParams]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate parameter")
  | _ => throw (IO.userError "unsupported original parameter")
private structure Expression (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def expression (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Expression s source) := do
  match atSource : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "independent context row missing")
      | none => throw (IO.userError "independent name missing")
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s left; let b ← expression s right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        by rw [atSource]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← expression s left; let b ← expression s right
      if leftType : a.type = .word then
        if bt : b.type = .word then
          return ⟨.binary .wordSub a.resolved b.resolved, .binary .wordSub a.core b.core, .word,
            by rw [atSource]; exact .subtract a.resolution b.resolution,
            .binary a.lowered b.lowered,
            .binary (show Resolved.HasType s.context a.resolved .word from leftType ▸ a.typing)
              (show Resolved.HasType s.context b.resolved .word from bt ▸ b.typing)⟩
        else throw (IO.userError "right operand not Word")
      else throw (IO.userError "left operand not Word")
  | _ => throw (IO.userError "outside independent expression grammar")
termination_by sizeOf source
private structure Body (types : TypeNameTable) (s : LocalTypeInputs) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : TypedLetReturnTreeElaborates types owner s source core type
private def body (types : TypeNameTable) (s : LocalTypeInputs) (source : Syntax.Block) : IO (Body types s source) := do
  match atSource : source with
  | ⟨_, [⟨_, .returnStmt (some returned)⟩]⟩ =>
      let a ← expression s returned
      return ⟨a.core, a.type, by rw [atSource]; exact .single (.expression a.resolution
        (by simpa only [LocalTypeInputs.context_ids] using a.lowered) a.typing)⟩
  | ⟨span, ⟨ls, .letDecl name none (some initializer)⟩ :: rest⟩ =>
      check (ls.contains name.span && ls.contains initializer.span) "original none annotation spans changed"
      if unused : name.value ∉ s.names.map Prod.fst then
        let a ← expression s initializer
        let b ← body types (s.bindFresh owner name.value a.type) ⟨span, rest⟩
        return ⟨.letE a.core b.core, b.type, by rw [atSource]; exact .inferred unused a.resolution a.lowered a.typing b.evidence⟩
      else throw (IO.userError "ancestor name reused")
  | ⟨span, ⟨_, .expression source true⟩ :: rest⟩ =>
      let a ← expression s source; let b ← body types s ⟨span, rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0), b.type,
        by rw [atSource]; exact .discard a.resolution a.lowered a.typing b.evidence⟩
  | ⟨_, [⟨_, .ifThen guard yes (some no)⟩]⟩ =>
      let c ← expression s guard; let a ← body types s yes; let b ← body types s no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
          return ⟨.ifE c.core a.core b.core, a.type, by rw [atSource]; exact .conditional c.resolution c.lowered (ct ▸ c.typing) a.evidence (bt ▸ b.evidence)⟩
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "guard is not Bool")
  | _ => throw (IO.userError "outside independent body grammar")
termination_by sizeOf source
private structure Compilation (types : TypeNameTable) (source : Syntax.FunctionDecl) where
  compiled : CompiledRuntimeFunction
  evidence : RuntimeFunctionCompiles types owner source compiled
private def compile (types : TypeNameTable) (source : Syntax.FunctionDecl) : IO (Compilation types source) := do
  let ps ← parameters types .empty source.value.signature.parameters.elements
  let b ← body types ps.inputs source.value.body
  match atClause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [returned]⟩⟩ =>
      let m ← meaning types returned
      if same : m.type = b.type then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          return ⟨⟨ps.inputs, b.core, b.type⟩, ⟨⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [atClause]; exact .single (same ▸ m.evidence)⟩, ps.evidence, b.evidence⟩⟩
        else throw (IO.userError "header policy rejected")
      else throw (IO.userError "return contract differs")
  | _ => throw (IO.userError "return clause is not singleton")

private def mixed : Core.Expr := .letE (.var 2) (.letE (.var 3) (.ifE (.var 2)
  (.letE (.pair (.var 0) (.var 3)) (.var 1)) (.letE (.var 3) (.var 1))))
private theorem mixedPaths (x y : Core.Value) (c : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (if c then 17 else 13) ⟨.eval mixed [.bool c, y, x], k, store⟩ ⟨.ret x, k, store⟩ := by
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl)
      (.cons .bindLet (.cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))))))))))
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl)
      (.cons .bindLet (.cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .enterLet
        (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl)
          (.cons .applyPair (.cons .bindLet (.cons (.var rfl) .refl))))))))))))))))
private def spine : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var index) (spine n (index + 1))
private theorem spinePaths (n index : Nat) (env : Core.Environment) (value : Core.Value)
    (found : env[index]? = some value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3 * n + 1) ⟨.eval (spine n index) env, k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing index env with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      have tail := ih (index + 1) (value :: env) (by simpa using found)
      have path := Core.Steps.cons .enterLet (.cons (.var found) (.cons .bindLet tail))
      have arithmetic : 3 * (n + 1) + 1 = 3 * n + 1 + 1 + 1 + 1 := by omega
      rw [arithmetic]
      exact path
private theorem arithmeticPaths (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 8 ⟨.eval (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) [.bool true, w 2, w 9], k, store⟩
      ⟨.ret (w 9), k, store⟩ :=
  .cons .enterLet (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight
    (.cons (.var rfl) (.cons (.applyBinary rfl) (.cons .bindLet (.cons (.var rfl) .refl)))))))
private def text (body : String) := "function f(x:T,y:T,c:Bool) returns(T){" ++ body ++ "}"
private def verify (content : String) (x y : TypedRuntimeArgument) (c : Bool)
    (expectedCore : Core.Expr) (expectedValue : Core.Value) (cost : Nat)
    (paths : ∀ store k, Core.Steps cost ⟨.eval expectedCore [.bool c, y.value, x.value], k, store⟩
      ⟨.ret expectedValue, k, store⟩) : IO Unit := do
  let source ← parsed content; let proof ← compile (table x.type) source
  let args := [x, y, (⟨.bool, .bool c, .bool⟩ : TypedRuntimeArgument)]
  check (decide (proof.compiled.core = expectedCore ∧ proof.compiled.returnType = x.type ∧
    proof.compiled.inputs.names = [("c", ⟨owner, 2⟩), ("y", ⟨owner, 1⟩), ("x", ⟨owner, 0⟩)] ∧
    proof.compiled.inputs.context.values = [.bool, x.type, x.type])) "independent original parameter layout changed"
  let some prepared := prepareRuntimeFunction? (table x.type) owner source args | throw (IO.userError "actual preparation missing")
  check (decide (prepared.core = expectedCore ∧ prepared.returnType = x.type ∧
    prepared.inputs.ids = proof.compiled.inputs.ids ∧ prepared.inputs.names = proof.compiled.inputs.names ∧
    prepared.inputs.environment.values = [.bool c, y.value, x.value])) "hidden discard binder leaked into parameter records"
  if different : proof.compiled.core ≠ .var 2 then
    have _ : ¬ RuntimeFunctionCompiles (table x.type) owner source { proof.compiled with core := .var 2 } :=
      fun wrong => different (congrArg CompiledRuntimeFunction.core (proof.evidence.result_unique wrong))
    pure ()
  else throw (IO.userError "strict work unexpectedly vanished")
  for store in [[], [w 91, .cellRef .word 999]] do
    have _ := paths store [.unaryApply .wordNot]
    let start := Core.State.initial expectedCore [.bool c, y.value, x.value] store
    check (decide (evaluateTypedLetReturnTreeWithCost? owner prepared.inputs.names prepared.inputs.environment source.value.body =
      some (expectedValue, cost) ∧ cost ≤ typedLetReturnTreeFuelBound source.value.body)) "strict source value/cost changed"
    for fuel in List.range (cost + 3) do
      check (decide (runRuntimeFunction? (table x.type) owner source args fuel store =
        some (x.type, Core.runStateful fuel start))) "whole entry differs from fixed Core"
      check (match Core.runStateful fuel start with
        | .done value final => decide (cost ≤ fuel ∧ value = expectedValue ∧ final = store)
        | .outOfFuel _ => decide (fuel < cost)
        | _ => false) "strict fuel threshold changed"
    for spent in List.range cost do
      match exhausted : runRuntimeFunction? (table x.type) owner source args spent store with
      | some (type, .outOfFuel cp) =>
          have _ := runRuntimeFunction?_resume exhausted (cost - spent)
          check (decide (type = x.type ∧ Core.runStateful (cost - spent) cp = .done expectedValue store)) "actual checkpoint residual changed"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 cp | throw (IO.userError "second chunk missing")
            check (decide (Core.runStateful (cost - spent - 1) next = .done expectedValue store)) "three chunks lost hidden value"
          if spent > 0 then check (Core.runStateful (cost - spent) start != .done expectedValue store) "restart substituted for resume"
      | _ => throw (IO.userError "genuine entry checkpoint missing")
private def checkedOpaque (type : Core.Ty) (x y : Core.Value) (xt : Core.ValueHasType x type) (yt : Core.ValueHasType y type) : IO Unit := do
  for c in [false, true] do
    verify (text "x;let z=x;if(c){(z,y);return z;}else{y;return z;}") ⟨type, x, xt⟩ ⟨type, y, yt⟩ c
      mixed x (if c then 17 else 13) (mixedPaths x y c)
end DiscardEntries
open DiscardEntries

def frontendParsedDiscardEntryTests : IO Unit := do
  for depth in [1, 3, 10, 32] do
    let prefixText := String.join (List.replicate depth "x;")
    verify (text (prefixText ++ "return x;")) ⟨.word, w 9, .word⟩ ⟨.word, w 2, .word⟩ true
      (spine depth 2) (w 9) (3 * depth + 1) (spinePaths depth 2 [.bool true, w 2, w 9] (w 9) rfl)
  verify (text "x - y;return x;") ⟨.word, w 9, .word⟩ ⟨.word, w 2, .word⟩ true
    (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) (w 9) 8 arithmeticPaths
  checkedOpaque .word (w 9) (w 2) .word .word
  checkedOpaque (.cell .word) (.cellRef .word 700) (.cellRef .word 701) .cellRef .cellRef
  checkedOpaque (.function .word .word) (.closure .word .word (.var 0) []) (.closure .word .word (.var 1) [w 7])
    (.closure .nil (.var rfl)) (.closure (.cons .word .nil) (.var rfl))
  checkedOpaque .unit .unit .unit .unit .unit
  checkedOpaque .bool (.bool true) (.bool false) .bool .bool
  for c in [false, true] do
    for store in [[], [w 91]] do
      let values := [.bool c, w 2, w 9]
      let tail : Core.Expr := .letE (.var 3) (.ifE (.var 2)
        (.letE (.pair (.var 0) (.var 3)) (.var 1)) (.letE (.var 3) (.var 1)))
      check (decide (Core.runStateful 2 (.initial mixed values store) =
        .outOfFuel ⟨.ret (w 9), [.letBody tail values], store⟩ ∧
        Core.runStateful 3 (.initial mixed values store) = .outOfFuel ⟨.eval tail (w 9 :: values), [], store⟩))
        "actual hidden binder or saved original environment changed"
      check (decide (Core.runStateful 6 (.initial (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) values store) =
        .outOfFuel ⟨.ret (w 7), [.letBody (.var 3) values], store⟩)) "unused arithmetic head was skipped"
  for type in [Core.Ty.namedData ⟨90⟩, .product (.namedData ⟨90⟩) (.cell (.namedData ⟨13⟩))] do
    let source ← parsed (text "x;let z=x;if(c){(z,y);return z;}else{y;return z;}")
    let proof ← compile (table type) source
    check (decide (proof.compiled.core = mixed ∧ proof.compiled.returnType = type ∧
      Core.infer? proof.compiled.inputs.context.values (.var 2) = some type)) "nominal static or same-typed wrong-Core contrast changed"
    check ((elaborateTypedLetReturnBody? (table type) owner proof.compiled.inputs source.value.body).isNone) "old prefix adapter widened"
  for body in ["x;", "missing;return x;", "f(x);return x;", "x= y;return x;", "return x;y;",
      "if(c){x;return x;}else{missing;return x;}"] do
    let source ← parsed (text body)
    check ((compileRuntimeFunction? (table .word) owner source).isNone) "invalid written head/tail accepted"
  let source ← parsed (text "x;return x;")
  match source.value.body with
  | ⟨span, ⟨statementSpan, .expression expression true⟩ :: rest⟩ =>
      check (statementSpan.contains expression.span && decide (expression.span.endByte + 1 = statementSpan.endByte))
        "original explicit semicolon range changed"
      let falseFlag : Syntax.Block := ⟨span, ⟨statementSpan, .expression expression false⟩ :: rest⟩
      let proof ← compile (table .word) source
      check ((elaborateTypedLetReturnTree? (table .word) owner proof.compiled.inputs falseFlag).isNone) "missing flag was silently repaired"
  | _ => throw (IO.userError "original expression statement shape changed")
  let args : List TypedRuntimeArgument := [⟨.word, w 9, .word⟩, ⟨.word, w 2, .word⟩, ⟨.bool, .bool true, .bool⟩]
  for badArgs in [[], args.drop 1, args ++ [⟨.unit, .unit, .unit⟩], args.reverse] do
    check ((prepareRuntimeFunction? (table .word) owner source badArgs).isNone) "discard bypassed argument count/type/order"
  let skipped ← parsed (text "if(c){x;return x;}else{missing;return x;}")
  let some inputs := bindRuntimeParameters? (table .word) owner skipped.value.signature.parameters.elements args
    | throw (IO.userError "original skipped-arm arguments did not bind")
  check (decide (evaluateTypedLetReturnTreeWithCost? owner inputs.names inputs.environment skipped.value.body = some (w 9, 7) ∧
    compileRuntimeFunction? (table .word) owner skipped = none)) "raw selected success replaced whole written checking"
  for content in ["function f<T>(x:T) returns(T){x;return x;}", "function f(x:T,x:T) returns(T){x;return x;}",
      "function f(x:T) returns(Bool){x;return x;}"] do
    check ((compileRuntimeFunction? (table .word) owner (← parsed content)).isNone) "discard bypassed the whole header or parameter policy"

end Tests
