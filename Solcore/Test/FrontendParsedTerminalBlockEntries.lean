import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionLocalFragmentProperties
import Solcore.Frontend.RuntimeFunctionPreparationFactorization
import Solcore.Core.LocalFragmentExactInsertionProperties
import Solcore.Core.LocalFragmentInferenceInsertionProperties
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.TypedLetReturnBody

/-! Terminal wrappers retain original inner ranges and parameter records.
Independent Core paths fix positive costs, with no transition added by braces. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace TerminalBlockEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TerminalBlockEntry", by decide⟩], by decide⟩⟩, 17⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def table (type : Core.Ty) : TypeNameTable := [(["T"], type), (["Bool"], .bool)]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "terminal-block-entry.sol"⟩, content⟩
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
  | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
      let child ← body types s ⟨innerSpan, statements⟩
      return ⟨child.core, child.type, by rw [atSource]; exact .block child.evidence⟩
  | ⟨span, ⟨ls, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      check (ls.contains name.span && ls.contains initializer.span) "original initializer spans changed"
      if unused : name.value ∉ s.names.map Prod.fst then
        let a ← expression s initializer
        let b ← body types (s.bindFresh owner name.value a.type) ⟨span, rest⟩
        match atAnnotation : annotation with
        | none => return ⟨.letE a.core b.core, b.type, by rw [atSource, atAnnotation]; exact .inferred unused a.resolution a.lowered a.typing b.evidence⟩
        | some written =>
            let m ← meaning types written
            if same : m.type = a.type then
              return ⟨.letE a.core b.core, b.type, by rw [atSource, atAnnotation]; exact .binding (same ▸ m.evidence) unused a.resolution a.lowered a.typing b.evidence⟩
            else throw (IO.userError "written annotation disagreed")
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
private theorem arithmeticPaths (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 8 ⟨.eval (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) [.bool true, w 2, w 9], k, store⟩
      ⟨.ret (w 9), k, store⟩ :=
  .cons .enterLet (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight
    (.cons (.var rfl) (.cons (.applyBinary rfl) (.cons .bindLet (.cons (.var rfl) .refl)))))))
private def text (body : String) := "function f(x:T,y:T,c:Bool) returns(T){" ++ body ++ "}"

private def wrap : Nat → String → String
  | 0, content => content
  | n + 1, content => "{" ++ wrap n content ++ "}"
private def mixedText (annotated : Bool) : String :=
  "x;{let z" ++ (if annotated then ":T" else "") ++
    "=x;{if(c){{(z,y);{return z;}}}else{{y;{return z;}}}}}"
private def peel (types : TypeNameTable) (inputs : LocalTypeInputs) (source : Syntax.Block) : IO Syntax.Block := do
  match source with
  | ⟨outer, [⟨inner, .block statements⟩]⟩ =>
      check (outer.contains inner && decide (outer.startByte < inner.startByte ∧ inner.endByte < outer.endByte))
        "original terminal inner braces lost their distinct range"
      have _ := elaborateTypedLetReturnTree?_block types owner inputs outer inner statements
      return ← peel types inputs ⟨inner, statements⟩
  | _ => return source
termination_by sizeOf source
private def verify (content : String) (x y : TypedRuntimeArgument) (c : Bool)
    (expectedCore : Core.Expr) (value : Core.Value) (cost bound : Nat)
    (paths : ∀ store k, Core.Steps cost ⟨.eval expectedCore [.bool c, y.value, x.value], k, store⟩
      ⟨.ret value, k, store⟩) : IO Unit := do
  let source ← parsed content; let proof ← compile (table x.type) source
  have _ := proof.evidence.complete
  let args := [x, y, (⟨.bool, .bool c, .bool⟩ : TypedRuntimeArgument)]
  check (decide (proof.compiled.core = expectedCore ∧ proof.compiled.returnType = x.type ∧
    proof.compiled.inputs.names = [("c", ⟨owner, 2⟩), ("y", ⟨owner, 1⟩), ("x", ⟨owner, 0⟩)] ∧
    proof.compiled.inputs.context.values = [.bool, x.type, x.type])) "original parameter-only records changed"
  let some prepared := prepareRuntimeFunction? (table x.type) owner source args | throw (IO.userError "whole preparation missing")
  check (decide (prepared.core = expectedCore ∧ prepared.returnType = x.type ∧
    prepared.inputs.ids = proof.compiled.inputs.ids ∧ prepared.inputs.names = proof.compiled.inputs.names ∧
    prepared.inputs.environment.values = [.bool c, y.value, x.value])) "wrapper changed actual ordered inputs"
  let inner ← peel (table x.type) proof.compiled.inputs source.value.body
  let child ← body (table x.type) proof.compiled.inputs inner
  check (decide (child.core = expectedCore ∧ child.type = x.type ∧
    typedLetReturnTreeFuelBound source.value.body = bound ∧ typedLetReturnTreeFuelBound inner = bound))
    "wrapper introduced a Core binder or fuel overhead"
  check ((elaborateTypedLetReturnBody? (table x.type) owner proof.compiled.inputs source.value.body).isNone)
    "narrower prefix adapter widened"
  let wrong : Core.Expr := .letE .unit (proof.compiled.core.weakenAt 0)
  check (decide (Core.infer? proof.compiled.inputs.context.values wrong = some x.type)) "wrong Core lost the same type"
  if different : proof.compiled.core ≠ wrong then
    have _ : ¬ RuntimeFunctionCompiles (table x.type) owner source { proof.compiled with core := wrong } :=
      fun other => different (congrArg CompiledRuntimeFunction.core (proof.evidence.result_unique other))
    pure ()
  else throw (IO.userError "wrapper gained a hidden Core binder")
  for store in [[], [w 91, .cellRef .word 999]] do
    have _ := paths store [.unaryApply .wordNot]
    let start := Core.State.initial expectedCore [.bool c, y.value, x.value] store
    check (decide (evaluateTypedLetReturnTreeWithCost? owner prepared.inputs.names prepared.inputs.environment source.value.body =
      some (value, cost))) "source independent value/cost changed"
    for fuel in List.range (bound + 3) do
      let expected := Core.runStateful fuel start
      check (decide (runRuntimeFunction? (table x.type) owner source args fuel store = some (x.type, expected) ∧
        prepared.inputs.runTypedLetReturnTree? (table x.type) owner fuel inner store = some (x.type, expected)))
        "wrapper and original inner whole results or actual checkpoints differ"
      check (match expected with
        | .done v final => decide (cost ≤ fuel ∧ v = value ∧ final = store)
        | .outOfFuel _ => decide (fuel < cost)
        | _ => false) "independent exact threshold changed"
    for spent in List.range cost do
      match exhausted : runRuntimeFunction? (table x.type) owner source args spent store with
      | some (type, .outOfFuel cp) =>
          have _ := runRuntimeFunction?_resume exhausted (cost - spent)
          check (decide (type = x.type ∧ Core.runStateful (cost - spent) cp = .done value store)) "saved checkpoint residual changed"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 cp | throw (IO.userError "middle chunk missing")
            check (decide (Core.runStateful (cost - spent - 1) next = .done value store)) "three chunks lost captured values"
          if spent > 0 then check (Core.runStateful (cost - spent) start != .done value store) "restart replaced genuine resume"
      | _ => throw (IO.userError "real checkpoint missing")
private def checked (type : Core.Ty) (x y : Core.Value) (xt : Core.ValueHasType x type) (yt : Core.ValueHasType y type) : IO Unit := do
  for depth in [1, 4, 16] do
    for annotated in [false, true] do
      for c in [false, true] do
        verify (text (wrap depth (mixedText annotated))) ⟨type, x, xt⟩ ⟨type, y, yt⟩ c mixed x
          (if c then 17 else 13) 17 (mixedPaths x y c)
end TerminalBlockEntries
open TerminalBlockEntries

def frontendParsedTerminalBlockEntryTests : IO Unit := do
  checked .word (w 9) (w 2) .word .word
  checked .bool (.bool true) (.bool false) .bool .bool
  checked .unit .unit .unit .unit .unit
  checked (.cell .word) (.cellRef .word 700) (.cellRef .word 701) .cellRef .cellRef
  checked (.function .word .word) (.closure .word .word (.var 0) []) (.closure .word .word (.var 1) [w 7])
    (.closure .nil (.var rfl)) (.closure (.cons .word .nil) (.var rfl))
  let values := [.bool true, w 2, w 9]
  let tail : Core.Expr := .letE (.var 3) (.ifE (.var 2)
    (.letE (.pair (.var 0) (.var 3)) (.var 1)) (.letE (.var 3) (.var 1)))
  for store in [[], [w 91]] do
    check (decide (Core.runStateful 2 (.initial mixed values store) =
      .outOfFuel ⟨.ret (w 9), [.letBody tail values], store⟩ ∧
      Core.runStateful 3 (.initial mixed values store) = .outOfFuel ⟨.eval tail (w 9 :: values), [], store⟩))
      "terminal braces changed an explicit captured-environment checkpoint"
    check (decide (Core.runStateful 6 (.initial (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) values store) =
      .outOfFuel ⟨.ret (w 7), [.letBody (.var 3) values], store⟩)) "strict arithmetic was not evaluated before the terminal block"
  for depth in [1, 3, 20, 40] do
    verify (text (wrap depth "return x;")) ⟨.word, w 9, .word⟩ ⟨.word, w 2, .word⟩ true (.var 2) (w 9) 1 1
      (fun _ _ => .cons (.var rfl) .refl)
  for depth in [1, 5] do
    verify (text (wrap depth "x - y;{return x;}")) ⟨.word, w 9, .word⟩ ⟨.word, w 2, .word⟩ true
      (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) (w 9) 8 8 arithmeticPaths
  for type in [Core.Ty.namedData ⟨90⟩, .product (.namedData ⟨90⟩) (.cell (.namedData ⟨13⟩))] do
    let source ← parsed (text (wrap 8 (mixedText true))); let proof ← compile (table type) source
    check (decide (proof.compiled.core = mixed ∧ proof.compiled.returnType = type)) "nominal static compilation needed invented values"
  for invalid in ["{}", "{x;}", "{return x;}return y;", "{let z=x;return z;}return z;", "{let x=y;return x;}",
      "{if(c){{return x;}}else{{return missing;}}}"] do
    check ((compileRuntimeFunction? (table .word) owner (← parsed (text invalid))).isNone) "terminal wrapper bypassed whole shape or scope policy"
  let args : List TypedRuntimeArgument := [⟨.word, w 9, .word⟩, ⟨.word, w 2, .word⟩, ⟨.bool, .bool true, .bool⟩]
  let skipped ← parsed (text "{if(c){{return x;}}else{{return missing;}}}")
  let some inputs := bindRuntimeParameters? (table .word) owner skipped.value.signature.parameters.elements args
    | throw (IO.userError "original arguments did not bind")
  check (decide (evaluateTypedLetReturnTreeWithCost? owner inputs.names inputs.environment skipped.value.body = some (w 9, 4) ∧
    compileRuntimeFunction? (table .word) owner skipped = none)) "selected raw success replaced whole written checking"
  let good ← parsed (text "{{return x;}}")
  for badArgs in [[], args.drop 1, args ++ [⟨.unit, .unit, .unit⟩], args.reverse] do
    check ((prepareRuntimeFunction? (table .word) owner good badArgs).isNone) "wrapper bypassed argument gates"
  for content in ["function f<T>(x:T) returns(T){{return x;}}", "function f(x:T,x:T) returns(T){{return x;}}",
      "function f(x:T) returns(Bool){{return x;}}"] do
    check ((compileRuntimeFunction? (table .word) owner (← parsed content)).isNone) "wrapper bypassed original header or return gates"
  let cell : Core.Value := .cellRef .word 700
  have _ : Core.Steps 1 ⟨.eval (.var 0) [cell], [.unaryApply .wordNot], []⟩ ⟨.ret cell, [.unaryApply .wordNot], []⟩ :=
    .cons (.var rfl) .refl
  check (match Core.runStateful 1 ⟨.eval (.var 0) [cell], [.unaryApply .wordNot], []⟩ with
    | .fault _ _ => true | _ => false) "arbitrary continuation endpoint was mistaken for a complete run"
end Tests
