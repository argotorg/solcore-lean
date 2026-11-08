import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions
import Solcore.Core.Internal.LocalFragment
import Solcore.Core.Fuel
import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Frontend.Fragments.Internal.ReturnBodies
import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Frontend.Fragments.Internal.RuntimeParameters
import Solcore.Resolved.LocalScope

/-!
# Terminal body tests

Terminal blocks, terminal return bodies, tree evaluation, body invariance and terminal runtime entries.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedTerminalBlockEntries
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTerminalBlocks
/-! Original terminal block spans and independent source/Core paths. Wrappers
add no transitions, names or positional shifts, even around mixed prefixes. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace TerminalBlocks
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TerminalBlock", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (type : Core.Ty) : LocalTypeInputs := ⟨[
  ⟨"c", ⟨other, 999⟩, .bool⟩, ⟨"r", id 2, .word⟩, ⟨"x", id 7, type⟩, ⟨"x", id 3, .bool⟩], by
    change ([⟨other, 999⟩, id 2, id 7, id 3] : List Resolved.LocalId).Nodup; decide⟩
private def env (value : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(⟨other, 999⟩, .bool choice), (id 2, w 2), (id 7, value), (id 3, .bool false)]
private def stores : List Core.Store := [[.unit, w 40], [w 91, .cellRef .word 40, .bool false]]
private def parsed (content : String) (clean : Bool := true) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main, "terminal-block.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok body next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"complete block rejected: {content}")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty == clean && next.atEnd &&
    decide (body.span = ⟨file.id, 0, content.utf8ByteSize⟩)) s!"{content}: original block/range changed"
  return body
private structure Expression (s : LocalTypeInputs) (e : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.ids resolved core
  typing : Resolved.HasType s.context resolved type
  raw : LocalExpressionEvaluatesWithCost s.names e store source value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core e.values, k, store⟩ ⟨.ret value, k, store⟩
private def expression (s : LocalTypeInputs) (e : Resolved.Environment) (aligned : e.ids = s.ids)
    (store : Core.Store) (source : Syntax.Expr) : IO (Expression s e store source) := do
  match atSource : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | none => throw (IO.userError "independent name absent")
      | some binder =>
          match typed : s.context.lookup? binder, found : e.lookup? binder, indexed : Resolved.LocalScope.index? s.ids binder with
          | some type, some value, some index =>
              let position := Resolved.LocalScope.index?_iff.mp indexed
              return ⟨.var binder, .var index, type, value, 1,
                by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named), .var position,
                .var (Resolved.LocalScope.lookup?_iff.mp typed),
                by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
                fun _ => .cons (.var ((Resolved.LocalScope.lookup_iff_getElem? (aligned.symm ▸ position)).mp
                  (Resolved.LocalScope.lookup?_iff.mp found))) .refl⟩
          | _, _, _ => throw (IO.userError "independent row absent")
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, .unit, .unit, 1,
      by rw [atSource]; exact .unit, .unit, .unit, by rw [atSource]; exact .unit, fun _ => .cons .unit .refl⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s e aligned store left; let b ← expression s e aligned store right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type, .pair a.value b.value, a.cost + b.cost + 3,
        by rw [atSource]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing,
        by rw [atSource]; exact .pair a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core e.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← expression s e aligned store left; let b ← expression s e aligned store right
      match av : a.value, bv : b.value with
      | .word x, .word y =>
          if leftType : a.type = .word then
            if rightType : b.type = .word then
            return ⟨.binary .wordSub a.resolved b.resolved, .binary .wordSub a.core b.core, .word, .word (x.sub y), a.cost + b.cost + 3,
              by rw [atSource]; exact .subtract a.resolution b.resolution, .binary a.lowered b.lowered,
              .binary (show Resolved.HasType s.context a.resolved .word from leftType ▸ a.typing)
                (show Resolved.HasType s.context b.resolved .word from rightType ▸ b.typing),
              by rw [atSource]; exact .subtract (av ▸ a.raw) (bv ▸ b.raw), fun k => by
                have path := Core.Steps.cons .enterBinary ((av ▸ a.paths (.binaryRight .wordSub b.core e.values :: k)).trans
                  (.cons .enterBinaryRight ((bv ▸ b.paths _).trans (.cons (.applyBinary rfl) .refl))))
                simpa only [Nat.add_assoc] using path⟩
            else throw (IO.userError "right is not Word")
          else throw (IO.userError "left is not Word")
      | _, _ => throw (IO.userError "actual operand not Word")
  | _ => throw (IO.userError "outside independent expression script")
termination_by sizeOf source
private structure Certificate (s : LocalTypeInputs) (e : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  elaboration : TypedLetReturnTreeElaborates types owner s body core type
  raw : TypedLetReturnTreeEvaluatesWithCost owner s.names e store body value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core e.values, k, store⟩ ⟨.ret value, k, store⟩
private def certify (s : LocalTypeInputs) (e : Resolved.Environment) (aligned : e.ids = s.ids)
    (store : Core.Store) (body : Syntax.Block) : IO (Certificate s e store body) := do
  match atBody : body with
  | ⟨outer, [⟨inner, .block statements⟩]⟩ =>
      check (outer.contains inner && decide (outer.startByte < inner.startByte ∧ inner.endByte < outer.endByte) &&
        statements.all (fun statement => inner.contains statement.span)) "original inner span or child order changed"
      let child ← certify s e aligned store ⟨inner, statements⟩
      return ⟨child.core, child.type, child.value, child.cost,
        by rw [atBody]; exact .block child.elaboration, by rw [atBody]; exact .block child.raw, child.paths⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      return ⟨.unit, .unit, .unit, 1, by rw [atBody]; exact .single .bare,
        by rw [atBody]; exact .single .bare, fun _ => .cons .unit .refl⟩
  | ⟨_, [⟨_, .returnStmt (some source)⟩]⟩ =>
      let a ← expression s e aligned store source
      return ⟨a.core, a.type, a.value, a.cost,
        by rw [atBody]; exact .single (.expression a.resolution (by simpa only [LocalTypeInputs.context_ids] using a.lowered) a.typing),
        by rw [atBody]; exact .single (.expression a.raw), a.paths⟩
  | ⟨span, ⟨_, .expression source true⟩ :: rest⟩ =>
      let a ← expression s e aligned store source
      let b ← certify s e aligned store ⟨span, rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0), b.type, b.value, a.cost + b.cost + 2,
        by rw [atBody]; exact .discard a.resolution a.lowered a.typing b.elaboration,
        by rw [atBody]; exact .discard a.raw b.raw, fun k => by
          have shifted := (b.paths []).weakenAt_zero_localFragment b.elaboration.localFragment a.value k
          have path := Core.Steps.cons .enterLet
            ((a.paths (.letBody (b.core.weakenAt 0) e.values :: k)).trans (.cons .bindLet shifted))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨span, ⟨_, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      if unused : name.value ∉ s.names.map Prod.fst then
        let a ← expression s e aligned store initializer
        let next := s.bindFresh owner name.value a.type
        let b ← certify next ((Resolved.freshLocalId owner s.ids, a.value) :: e)
          (by simpa only [next, LocalTypeInputs.bindFresh_ids, Resolved.LocalScope.ids, List.map_cons]
            using congrArg (List.cons _) aligned) store ⟨span, rest⟩
        let rawTail := by simpa only [next, LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using b.raw
        let common := fun elaboration raw => (⟨.letE a.core b.core, b.type, b.value, a.cost + b.cost + 2, elaboration, raw, fun k => by
          have path := Core.Steps.cons .enterLet ((a.paths (.letBody b.core e.values :: k)).trans (.cons .bindLet (b.paths k)))
          simpa only [Resolved.LocalScope.values, List.map_cons, Nat.add_assoc] using path⟩ : Certificate s e store body)
        match atAnnotation : annotation with
        | none => return (common (by rw [atBody, atAnnotation]; exact .inferred unused a.resolution a.lowered a.typing b.elaboration)
            (by rw [atBody, atAnnotation]; exact .inferred a.raw (by simpa only [LocalTypeInputs.names_ids] using rawTail)))
        | some written =>
            match atWritten : written with
            | ⟨_, .named name none⟩ =>
                if meaning : types.lookup? (qualifiedTypeNameKey name) = some a.type then
                  return (common (by rw [atBody, atAnnotation, atWritten]; exact .binding (.named (TypeNameTable.lookup?_iff.mp meaning)) unused a.resolution a.lowered a.typing b.elaboration)
                    (by rw [atBody, atAnnotation]; exact .binding a.raw (by simpa only [LocalTypeInputs.names_ids] using rawTail)))
                else throw (IO.userError "written annotation disagrees")
            | _ => throw (IO.userError "outside independent annotation script")
      else throw (IO.userError "written name is already used")
  | ⟨_, [⟨_, .ifThen guard yes (some no)⟩]⟩ =>
      let c ← expression s e aligned store guard
      let a ← certify s e aligned store yes; let b ← certify s e aligned store no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
        have elaboration : TypedLetReturnTreeElaborates types owner s body (.ifE c.core a.core b.core) a.type := by
          rw [atBody]; exact .conditional c.resolution c.lowered (ct ▸ c.typing) a.elaboration (bt ▸ b.elaboration)
        match cv : c.value with
        | .bool true => return ⟨.ifE c.core a.core b.core, a.type, a.value, c.cost + a.cost + 2, elaboration,
            by rw [atBody]; exact .ifTrue (cv ▸ c.raw) a.raw, fun k => by
              have path := Core.Steps.cons .enterIf ((cv ▸ c.paths (.ifBranches a.core b.core e.values :: k)).trans (.cons .chooseTrue (a.paths k)))
              simpa only [Nat.add_assoc] using path⟩
        | .bool false => return ⟨.ifE c.core a.core b.core, a.type, b.value, c.cost + b.cost + 2, elaboration,
            by rw [atBody]; exact .ifFalse (cv ▸ c.raw) b.raw, fun k => by
              have path := Core.Steps.cons .enterIf ((cv ▸ c.paths (.ifBranches a.core b.core e.values :: k)).trans (.cons .chooseFalse (b.paths k)))
              simpa only [Nat.add_assoc] using path⟩
        | _ => throw (IO.userError "actual guard not Bool")
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "guard type not Bool")
  | _ => throw (IO.userError "outside independent body script")
termination_by sizeOf body
private structure Actual where
  type : Core.Ty
  value : Core.Value
  typed : Core.ValueHasType value type
private def supplied (a : Actual) (choice : Bool) : LocalInputs := ⟨[
  ⟨"c", ⟨other, 999⟩, .bool, .bool choice, .bool⟩, ⟨"r", id 2, .word, w 2, .word⟩,
  ⟨"x", id 7, a.type, a.value, a.typed⟩, ⟨"x", id 3, .bool, .bool false, .bool⟩], by
    change ([⟨other, 999⟩, id 2, id 7, id 3] : List Resolved.LocalId).Nodup; decide⟩
private def unwrap (body : Syntax.Block) : Syntax.Block :=
  match body with
  | ⟨_, [⟨inner, .block statements⟩]⟩ => unwrap ⟨inner, statements⟩
  | _ => body
termination_by sizeOf body
private def checked (content : String) (a : Actual) (choice : Bool) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let body ← parsed content; let actual := supplied a choice
  let s := actual.toTypeInputs; let e := actual.environment
  have _ : s = inputs a.type := rfl
  check (decide (e = env a.value choice ∧ actual.bindings.length = 4)) "original supplied rows changed"
  for store in stores do
    let cert ← certify s e rfl store body
    check (decide (cert.core = core ∧ cert.type = type ∧ cert.value = value ∧ cert.cost = cost)) "independent expectations changed"
    match body with
    | ⟨outer, [⟨inner, .block statements⟩]⟩ =>
        have _ := elaborateTypedLetReturnTree?_block types owner s outer inner statements
        pure ()
    | _ => pure ()
    check (decide (actual.checkTypedLetReturnTree? types owner body = some (core, type) ∧
      evaluateTypedLetReturnTreeWithCost? owner s.names e body = some (value, cost) ∧
      Core.infer? s.context.values core = some type ∧ typedLetReturnTreeFuelBound body = bound ∧ cost ≤ bound ∧
      typedLetReturnTreeFuelBound (unwrap body) = bound)) "wrapper changed exact Core/type/value/cost/bound"
    check ((elaborateTypedLetReturnBody? types owner s body).isNone) "old prefix adapter widened"
    let start := Core.State.initial core e.values store
    let run := fun fuel => actual.runTypedLetReturnTree? types owner fuel body store
    have _ := cert.paths [.letBody (.var 0) [w 17]]
    have _ := cert.raw.checked_toStepsWithContinuation cert.elaboration.complete rfl [.unaryApply .wordNot]
    for fuel in List.range (bound + 3) do
      check (decide (run fuel = some (type, Core.runStateful fuel start) ∧
        run fuel = actual.runTypedLetReturnTree? types owner fuel (unwrap body) store)) "wrapper altered the full same-fuel result"
      check (match run fuel with
        | some (_, .done v st) => decide (cost ≤ fuel ∧ v = value ∧ st = store)
        | some (_, .outOfFuel cp) => decide (fuel < cost ∧ cp.store = store)
        | _ => false) "exact threshold or own store changed"
    for spent in List.range cost do
      match exhausted : run spent with
      | some (_, .outOfFuel cp) =>
          have _ := actual.runTypedLetReturnTree?_resume exhausted (cost - spent)
          for remaining in [0, 1, cost - spent, cost - spent + 2] do
            check (decide (run (spent + remaining) = some (type, Core.runStateful remaining cp))) "genuine checkpoint replay changed"
          check (decide (Core.runStateful (cost - spent) cp = .done value store)) "exact residual cost changed"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 cp | throw (IO.userError "second chunk missing")
            check (decide (Core.runStateful (cost - spent - 1) next = .done value store)) "third chunk lost its continuation"
          if spent > 0 then check (Core.runStateful (cost - spent) start != .done value store) "restart impersonated resume"
      | _ => throw (IO.userError "checkpoint missing")
private def nominal (type : Core.Ty) (body : Syntax.Block) :
    IO (PLift (TypedLetReturnTreeElaborates types owner (inputs type) body (.var 2) type)) := do
  match atBody : body with
  | ⟨_, [⟨inner, .block statements⟩]⟩ =>
      let child ← nominal type ⟨inner, statements⟩
      return ⟨by rw [atBody]; exact .block child.down⟩
  | ⟨_, [⟨_, .returnStmt (some ⟨_, .identifier name⟩)⟩]⟩ =>
      if same : name.value = "x" then
        have named : LocalNameTable.Lookup (inputs type).names "x" (id 7) := .tail (by decide) (.tail (by decide) .head)
        return ⟨by rw [atBody]; exact .single (.expression (.identifier (same ▸ named))
          (.var (.tail (by change (⟨other, 999⟩ : Resolved.LocalId) ≠ id 7; decide) (.tail (by change id 2 ≠ id 7; decide) .head)))
          (.var (.tail (by change (⟨other, 999⟩ : Resolved.LocalId) ≠ id 7; decide) (.tail (by change id 2 ≠ id 7; decide) .head))))⟩
      else throw (IO.userError "nominal source spelling changed")
  | _ => throw (IO.userError "nominal original block shape changed")
termination_by sizeOf body
private def wrap : Nat → String → String
  | 0, content => content
  | n + 1, content => "{" ++ wrap n content ++ "}"
end TerminalBlocks
open TerminalBlocks
def frontendParsedTerminalBlockTests : IO Unit := do
  let a : Actual := ⟨.word, w 9, .word⟩
  for depth in [1, 2, 5, 16, 40] do
    checked (wrap depth "{return x;}") a true (.var 2) .word (w 9) 1 1
    checked (wrap depth "{let z=x;return z;}") a false (.letE (.var 2) (.var 0)) .word (w 9) 4 4
    checked (wrap depth "{x - r;return r;}") a true (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 2)) .word (w 2) 8 8
  checked "{{{return;}}}" a false .unit .unit .unit 1 1
  checked "{let z=x;{{return;}}}" a true (.letE (.var 2) .unit) .unit .unit 4 4
  checked "{let z: Word=x;{z;let q=z - r;{{return q;}}}}" a true
    (.letE (.var 2) (.letE (.var 0) (.letE (.binary .wordSub (.var 1) (.var 3)) (.var 0)))) .word (w 7) 14 14
  checked "{{(x,r);{let z=x;{return z;}}}}" a true (.letE (.pair (.var 2) (.var 1)) (.letE (.var 3) (.var 0))) .word (w 9) 11 11
  for choice in [false, true] do
    checked "{if(c){{x - r;{return x;}}}else{{return r;}}}" a choice
      (.ifE (.var 0) (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) (.var 1))
      .word (if choice then w 9 else w 2) (if choice then 11 else 4) 11
  for value in [⟨.cell .word, .cellRef .word 999, .cellRef⟩,
      ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩,
      ⟨.unit, .unit, .unit⟩, ⟨.product .unit (.cell .word), .pair .unit (.cellRef .word 19), .pair .unit .cellRef⟩] do
    checked "{{let z=x;{{return z;}}}}" value true (.letE (.var 2) (.var 0)) value.type value.value 4 4
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨99⟩) (.cell (.namedData ⟨13⟩)), .function .word (.namedData ⟨99⟩)] do
    let body ← parsed (wrap 12 "{return x;}"); let evidence := (← nominal type body).down
    have _ (definitions : Core.DataEnvironment) : Core.HasType (inputs type).context.values (.var 2) type definitions := .var rfl
    have _ : ¬ TypedLetReturnTreeElaborates types owner (inputs type) body (.letE .unit (.var 3)) type := by
      intro wrong; have impossible := evidence.result_unique wrong; cases impossible.1
    check (decide (elaborateTypedLetReturnTree? types owner (inputs type) body = some (.var 2, type) ∧
      Core.infer? (inputs type).context.values (.letE .unit (.var 3)) = some type)) "nominal or same-typed wrong-Core boundary changed"
  for store in stores do
    let actual := supplied a true; let e := actual.environment.values
    let body ← parsed "{{x - r;{return r;}}}"
    let cp : Core.State := ⟨.ret (w 7), [.letBody (.var 2) e], store⟩
    check (decide (actual.runTypedLetReturnTree? types owner 6 body store = some (.word, .outOfFuel cp) ∧
      Core.runStateful 2 cp = .done (w 2) store ∧ Core.runStateful 0 {cp with continuation := []} = .done (w 7) store))
      "wrappers changed the actual initializer checkpoint or lost the saved tail"
  for content in ["{{}}", "{{x;}}", "{{return x;}return x;}", "{{let z=x;return z;}return z;}",
      "{let z=x;{{let z=r;return z;}}}", "{{let x=r;return x;}}", "{{let z=missing;return x;}}",
      "{if(c){{let z=x;return z;}}else{{return z;}}}", "{{return x;return r;}}", "{{f(x);return x;}}"] do
    let body ← parsed content
    check ((elaborateTypedLetReturnTree? types owner (inputs .word) body).isNone) "invalid lexical boundary accepted"
    check (decide (elaborateTypedLetReturnTree? types owner (inputs .word) body =
      elaborateTypedLetReturnTree? types owner (inputs .word) (unwrap body))) "wrapper full Option equality lost rejection"
  let unterminated ← parsed "{{x}}" false
  check (match unterminated.value with | [⟨_, .block [⟨_, .expression _ false⟩]⟩] => true | _ => false)
    "diagnosed inner expression lost its original absent semicolon"
  check ((elaborateTypedLetReturnTree? types owner (inputs .word) unterminated).isNone) "diagnosed unterminated inner block accepted"
  let skipped ← parsed "{if(c){{return x;}}else{{missing;return x;}}}"
  check (decide (evaluateTypedLetReturnTreeWithCost? owner (inputs .word).names (env (w 9) true) skipped = some (w 9, 4) ∧
    elaborateTypedLetReturnTree? types owner (inputs .word) skipped = none)) "raw selection bypassed whole block checking"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTerminalBodyInvariance
/-! Parsed body identity changes preserve complete same-fuel machine results.
Store replay preserves actual values and thresholds, not the store-bearing
results or suspended states. Existing entry owner/store contracts also apply. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"TerminalBodyInvariance", by decide⟩], by decide⟩⟩, 29⟩
private def otherOwner : Resolved.DeclarationId := { owner with declarationIndex := 41 }
private def shift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 37 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have sameOwner := congrArg Resolved.LocalId.owner same
  have sameIndex := congrArg Resolved.LocalId.binderIndex same
  change left.binderIndex + 37 = right.binderIndex + 37 at sameIndex
  have originalIndex := Nat.add_right_cancel sameIndex
  cases left
  cases right
  simp_all [shift]
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def stores : List Core.Store :=
  [[.word (word 91), .bool true], [.unit, .cellRef .word 40, .bool false],
    [.closure .bool .bool (.var 0) [], .word Core.Word.maximum]]
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def arguments (choice : Bool) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, ⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
private def lt (left right : Core.Expr) : Core.Expr :=
  .letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1)))

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-terminal-invariance.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")
private def body (content : String) : IO Syntax.Block := do
  let some result ← parsed? (Syntax.Parser.block .allow) content
    | throw (IO.userError s!"{content}: expected complete diagnostic-free block")
  return result

private def checkBody (inputs : LocalInputs) (source : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let mapped := inputs.mapIds shift shiftInjective
  have _ := inputs.checkTerminalReturnBody?_mapIds shift shiftInjective source
  assertTrue (decide (mapped.ids = inputs.ids.map shift ∧ mapped.context.values = inputs.context.values ∧
    mapped.environment.values = inputs.environment.values ∧ mapped.names.map (·.1) = inputs.names.map (·.1)))
    "identity relabeling changed ordered values, types, spellings, or chosen IDs"
  if !inputs.bindings.isEmpty then
    assertTrue (decide (mapped.ids ≠ inputs.ids ∧ mapped.names ≠ inputs.names)) "identity map was accidentally trivial"
  assertTrue (decide (inputs.checkTerminalReturnBody? source = some (core, type) ∧
    mapped.checkTerminalReturnBody? source = some (core, type))) "exact body Core/type changed under injective relabeling"
  assertTrue (terminalReturnBodyFuelBound source == bound) "source bound changed"
  for initialStore in stores do
    let run := fun fuel => inputs.runTerminalReturnBody? fuel source initialStore
    let mappedRun := fun fuel => mapped.runTerminalReturnBody? fuel source initialStore
    for fuel in List.range (bound + 3) do
      have _ := inputs.runTerminalReturnBody?_mapIds shift shiftInjective fuel source initialStore
      assertTrue (decide (mappedRun fuel = run fuel ∧ run fuel = some (type, Core.runStateful fuel
        (Core.State.initial core inputs.environment.values initialStore)))) "mapped full same-fuel checkpoint/result changed"
      assertTrue (match run fuel with
        | some (actualType, .done actualValue finalStore) =>
            decide (cost ≤ fuel ∧ actualType = type ∧ actualValue = value ∧ finalStore = initialStore)
        | some (actualType, .outOfFuel checkpoint) =>
            decide (fuel < cost ∧ actualType = type ∧ checkpoint.store = initialStore)
        | _ => false) "store replay changed the actual value, exact cost, or its own store"
      for replacement in stores do
        have _ := inputs.runTerminalReturnBody?_done_store_iff fuel source initialStore replacement type value
        have _ := inputs.runTerminalReturnBody?_outOfFuel_store_iff fuel source initialStore replacement type
        if replacement != initialStore then
          assertTrue (decide (run fuel ≠ inputs.runTerminalReturnBody? fuel source replacement))
            "distinct stores were incorrectly erased from full results/states"
    for spent in List.range cost do
      let some (_, .outOfFuel checkpoint) := run spent | throw (IO.userError "genuine checkpoint disappeared")
      for remaining in List.range (cost - spent + 3) do
        let resumed := Core.runStateful remaining checkpoint
        assertTrue (decide (run (spent + remaining) = some (type, resumed) ∧
          mappedRun (spent + remaining) = some (type, resumed))) "mapped same-state resumption changed"
        assertTrue (match resumed with
          | .done actualValue finalStore => decide (cost - spent ≤ remaining ∧ actualValue = value ∧ finalStore = initialStore)
          | .outOfFuel residual => decide (remaining < cost - spent ∧ residual.store = initialStore)
          | _ => false) "resumption replaced the checkpoint's own store"
private def checkText (inputs : LocalInputs) (content : String) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  checkBody inputs (← body content) core type value cost bound

private def checkEntry (content : String) (supplied : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
    | throw (IO.userError "complete declaration did not parse")
  let some inputs := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements supplied
    | throw (IO.userError "actual ordered parameters did not bind")
  assertTrue (decide (inputs.environment.values = supplied.reverse.map (·.value))) "actual parameter values changed"
  checkBody inputs declaration.value.body core type value cost bound
  let singleton := match declaration.value.body.value with | [⟨_, .returnStmt _⟩] => true | _ => false
  if !singleton then
    assertTrue (returnBodyFuelBound declaration.value.body == 0) "original singleton bound broadened"
  let some compiled := compileRuntimeFunction? types owner declaration
    | throw (IO.userError "invariant terminal entry did not compile")
  let some prepared := prepareRuntimeFunction? types otherOwner declaration supplied
    | throw (IO.userError "relabeled actual terminal arguments did not prepare")
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ prepared.core = core ∧
    prepared.returnType = type ∧ prepared.inputs.environment.values = supplied.reverse.map (·.value)))
    "entry relabeling changed actual Core, return type, or argument values"
  for initialStore in stores do
    for fuel in List.range (bound + 3) do
      have _ := runRuntimeFunction?_owner_eq types owner otherOwner declaration supplied fuel initialStore
      let original := runRuntimeFunction? types owner declaration supplied fuel initialStore
      assertTrue (decide (original = runRuntimeFunction? types otherOwner declaration supplied fuel initialStore))
        "owner API stopped preserving complete same-fuel results"
      assertTrue (decide (original = inputs.runTerminalReturnBody? fuel declaration.value.body initialStore))
        "entry no longer agrees with its terminal body execution"
      for replacement in stores do
        have _ := runRuntimeFunction?_done_store_iff types owner declaration supplied fuel initialStore replacement type value
        have _ := runRuntimeFunction?_outOfFuel_store_iff types owner declaration supplied fuel initialStore replacement type
        let completed := decide (original = some (type, .done value initialStore))
        let replayed := decide (runRuntimeFunction? types owner declaration supplied fuel replacement =
          some (type, .done value replacement))
        assertTrue (completed == replayed) "store API lost its own-store completion observation"

private def checkRejected (inputs : LocalInputs) (content : String) : IO Unit := do
  let source ← body content
  let mapped := inputs.mapIds shift shiftInjective
  assertTrue ((inputs.checkTerminalReturnBody? source).isNone && (mapped.checkTerminalReturnBody? source).isNone)
    "injective IDs changed whole rejection of written syntax"
  for initialStore in stores do
    for fuel in [0, 1, 4, 13, terminalReturnBodyFuelBound source, 50] do
      assertTrue ((inputs.runTerminalReturnBody? fuel source initialStore).isNone &&
        (mapped.runTerminalReturnBody? fuel source initialStore).isNone) "store/identity change enabled a rejected body"

def frontendParsedTerminalBodyInvarianceTests : IO Unit := do
  checkText LocalInputs.empty "{ return; }" .unit .unit .unit 1 1
  for choice in [false, true] do
    let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
      "function parameters(c: Bool, t: Word, f: Word) returns (Word) { return t; }"
      | throw (IO.userError "parameter declaration did not parse")
    let some inputs := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements (arguments choice)
      | throw (IO.userError "actual typed arguments did not bind")
    checkText inputs " /* source */ { return ((t)); } " (.var 1) .word (.word (word 7)) 1 1
    for content in ["{ return c ? ~t : f; }", "{ if(c){return ~t;}else{return f;} }"] do
      checkText inputs content (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
        (.word (if choice then (word 7).bitNot else word 9)) (if choice then 6 else 4) 6
    checkText inputs "{ if(c){return t < f;}else{return t >= f;} }"
      (.ifE (.var 2) (lt (.var 1) (.var 0)) (.unary .boolNot (lt (.var 1) (.var 0))))
      .bool (.bool choice) (if choice then 14 else 16) 16
    checkText inputs "{ return c && t < f; }" (.ifE (.var 2) (lt (.var 1) (.var 0)) (.bool false))
      .bool (.bool choice) (if choice then 14 else 4) 14
    checkText inputs "{ if(c){return;}else{return;} }" (.ifE (.var 2) .unit .unit) .unit .unit 4 4
    for content in ["{}", "{ return missing; }", "{ return c ? t : missing; }", "{ return c ? missing : f; }",
        "{ if(c){return t;}else{return missing;} }", "{ if(c){return missing;}else{return f;} }",
        "{ if(c){return t;}else{return c;} }", "{ if(c){return c;}else{return f;} }",
        "{ if(t){return t;}else{return f;} }", "{ if(c){return t;} }",
        "{ return t; return f; }", "{ if(c){return t;}else{return f;} return t; }",
        "{ if(c){if(c){return t;}else{return f;}}else{return f;} }"] do checkRejected inputs content
    for invalid in [s!"{Core.wordModulus}", "t + c", "t(c)"] do
      checkRejected inputs ("{ if(c){return t;}else{return " ++ invalid ++ ";} }")
      checkRejected inputs ("{ if(c){return " ++ invalid ++ ";}else{return f;} }")
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cellLeft : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let cellRight : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 91, .cellRef⟩
  let closureLeft : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let closureRight : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, left, right) in [("Word", (⟨.word, .word Core.Word.maximum, .word⟩ : TypedRuntimeArgument),
      ⟨.word, .word (word (2 ^ 255)), .word⟩), ("Unit", unit, unit), ("Cell", cellLeft, cellRight), ("Fn", closureLeft, closureRight),
      ("Bool", (⟨.bool, .bool true, .bool⟩ : TypedRuntimeArgument), ⟨.bool, .bool false, .bool⟩)] do
    for choice in [false, true] do
      for content in ["{ return c ? t : f; }", "{ if(c){return t;}else{return f;} }"] do
        checkEntry (s!"function values(c: Bool, t: {name}, f: {name}) returns ({name}) " ++ content)
          [⟨.bool, .bool choice, .bool⟩, left, right] (.ifE (.var 2) (.var 1) (.var 0))
          left.type (if choice then left.value else right.value) 4 4
  for content in ["", "{ return t; } trailing", "{ if(c){return t;}else{return f;} } trailing"] do
    assertTrue (← parsed? (Syntax.Parser.block .allow) content).isNone "incomplete canonical body consumption accepted"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTerminalReturnBodies
/-! The common body interface preserves both original runners at every fuel.
Singleton and terminal-conditional profiles retain their own Core, costs and
actual values when accepted through the integrated runtime entry. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"TerminalReturnBody", by decide⟩], by decide⟩⟩, 28⟩
private def store : Core.Store := [.word (word 91), .bool true]
private def parsed_variant? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-terminal-return.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")
private def body_variant (content : String) : IO Syntax.Block := do
  let some result ← parsed_variant? (Syntax.Parser.block .allow) content
    | throw (IO.userError s!"{content}: expected complete diagnostic-free block")
  return result

private def checkBody_variant (inputs : LocalInputs) (source : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let singleton := match source.value with | [⟨_, .returnStmt _⟩] => true | _ => false
  let originalCheck := if singleton then inputs.checkReturnBody? source else inputs.checkConditionalReturnBody? source
  let excludedCheck := if singleton then inputs.checkConditionalReturnBody? source else inputs.checkReturnBody? source
  let originalRun := if singleton then inputs.runReturnBody? else inputs.runConditionalReturnBody?
  let excludedRun := if singleton then inputs.runConditionalReturnBody? else inputs.runReturnBody?
  let originalBound := if singleton then returnBodyFuelBound source else conditionalReturnBodyFuelBound source
  assertTrue (decide (inputs.checkTerminalReturnBody? source = some (core, type) ∧ originalCheck = some (core, type)))
    s!"wrong exact common/original Core and type: {reprStr (inputs.checkTerminalReturnBody? source)}"
  assertTrue (terminalReturnBodyFuelBound source == bound && originalBound == bound) "dispatch added source fuel"
  assertTrue excludedCheck.isNone "an existing separate checker broadened its shape"
  let initial := Core.State.initial core inputs.environment.values store
  let run := fun fuel => inputs.runTerminalReturnBody? fuel source store
  for fuel in List.range (bound + 3) do
    assertTrue (decide (run fuel = originalRun fuel source store ∧
      run fuel = some (type, Core.runStateful fuel initial))) "common runner changed the original full same-fuel result"
    assertTrue (excludedRun fuel source store).isNone "an existing runner broadened its shape"
    assertTrue (match run fuel with
      | some (actualType, .done actualValue finalStore) =>
          decide (cost ≤ fuel ∧ actualType = type ∧ actualValue = value ∧ finalStore = store)
      | some (actualType, .outOfFuel state) => decide (fuel < cost ∧ actualType = type ∧ state.store = store)
      | _ => false) "common runner added cost or changed actual values/stores"
  for spent in List.range cost do
    let some (_, .outOfFuel checkpoint) := run spent | throw (IO.userError "genuine checkpoint disappeared")
    for remaining in List.range (cost - spent + 3) do
      assertTrue (decide (run (spent + remaining) = some (type, Core.runStateful remaining checkpoint)))
        "same-state resumption changed a frame/environment or the full result"
  match source.value, core with
  | [⟨statementSpan, .returnStmt expression⟩], _ =>
      assertTrue (source.span.contains statementSpan) "original return span changed"
      match expression with
      | none => assertTrue (decide (core = .unit ∧ type = .unit ∧ cost = 1)) "bare return gained an operation"
      | some child =>
          for fuel in List.range (bound + 3) do
            assertTrue (decide (run fuel = inputs.run? fuel child store)) "expression return gained overhead"
  | [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩], .ifE conditionCore thenCore elseCore =>
      assertTrue (decide (inputs.check? condition = some (conditionCore, .bool) ∧
        inputs.checkReturnBody? thenBody = some (thenCore, type) ∧
        inputs.checkReturnBody? elseBody = some (elseCore, type))) "union recursively changed the original arm adapter"
      assertTrue (source.span.contains statementSpan && statementSpan.contains condition.span &&
        statementSpan.contains thenBody.span && statementSpan.contains elseBody.span &&
        decide (condition.span.endByte ≤ thenBody.span.startByte ∧ thenBody.span.endByte ≤ elseBody.span.startByte))
        "canonical spans or written branch order changed"
      let first : Core.State := ⟨.eval conditionCore inputs.environment.values,
        [.ifBranches thenCore elseCore inputs.environment.values], store⟩
      assertTrue (decide (run 1 = some (type, .outOfFuel first))) "conditional frame changed at the common boundary"
  | _, _ => throw (IO.userError "accepted something outside both terminal profiles")
private def checkText_variant (inputs : LocalInputs) (content : String) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  checkBody_variant inputs (← body_variant content) core type value cost bound

private def checkEntry_variant (content : String) (supplied : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let some declaration ← parsed_variant? (Syntax.Parser.functionDecl .module) content
    | throw (IO.userError "complete declaration did not parse")
  let some inputs := bindRuntimeParameters? types owner_variant declaration.value.signature.parameters.elements supplied
    | throw (IO.userError "actual declaration arguments did not bind")
  assertTrue (decide (inputs.environment.values = supplied.reverse.map (·.value))) "actual argument order changed"
  checkBody_variant inputs declaration.value.body core type value cost bound
  match declaration.value.body.value with
  | [⟨_, .returnStmt _⟩] => pure ()
  | _ => assertTrue (returnBodyFuelBound declaration.value.body == 0) "original singleton bound broadened"
  match accepted : compileRuntimeFunction? types owner_variant declaration with
  | none => throw (IO.userError "terminal entry stopped compiling")
  | some compiled =>
      let provenance := compileRuntimeFunction?_sound accepted
      let some prepared := prepareRuntimeFunction? types owner_variant declaration supplied
        | throw (IO.userError "actual terminal arguments did not prepare")
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ prepared.core = core ∧
        prepared.returnType = type ∧ prepared.inputs.environment.values = supplied.reverse.map (·.value)))
        "entry lost actual compilation projection"
      if matching : supplied.map (·.type) = compiled.inputs.context.values.reverse then
        for fuel in List.range (bound + 3) do
          have _ := provenance.run_eq supplied matching fuel store
          assertTrue (decide (runRuntimeFunction? types owner_variant declaration supplied fuel store =
            inputs.runTerminalReturnBody? fuel declaration.value.body store)) "entry changed terminal body behavior"
      else throw (IO.userError "actual terminal argument type order changed")

private theorem selectedPiecesEvaluate (inputs : LocalInputs) (blockSpan statementSpan : Syntax.SourceSpan)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block) (choice : Bool) (type : Core.Ty) (value : Core.Value)
    (conditionDone : inputs.run? 40 condition store = some (.bool, .done (.bool choice) store))
    (branchDone : inputs.runReturnBody? 40 (if choice then thenBody else elseBody) store = some (type, .done value store)) :
    TerminalReturnBodyEvaluates inputs.names inputs.environment store
      ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value store := by
  obtain ⟨_, _, conditionCosted, _⟩ := LocalInputs.run?_done_iff_typed_cost.mp conditionDone
  cases choice with
  | false =>
      change inputs.runReturnBody? 40 elseBody store = some (type, .done value store) at branchDone
      obtain ⟨_, _, branchCosted, _⟩ := LocalInputs.runReturnBody?_done_iff_typed_cost.mp branchDone
      exact .conditional (.ifFalse conditionCosted.erase branchCosted.erase)
  | true =>
      change inputs.runReturnBody? 40 thenBody store = some (type, .done value store) at branchDone
      obtain ⟨_, _, branchCosted, _⟩ := LocalInputs.runReturnBody?_done_iff_typed_cost.mp branchDone
      exact .conditional (.ifTrue conditionCosted.erase branchCosted.erase)

private def checkSkipped (inputs : LocalInputs) (choice : Bool) (invalid : String) : IO Unit := do
  let content := if choice then "{ if(c) { return t; } else { return " ++ invalid ++ "; } }"
    else "{ if(c) { return " ++ invalid ++ "; } else { return f; } }"
  let source ← body_variant content
  assertTrue (inputs.checkTerminalReturnBody? source).isNone "invalid unselected arm checked"
  assertTrue (inputs.checkConditionalReturnBody? source).isNone "common rejection differed from original conditional rejection"
  for fuel in [0, 4, terminalReturnBodyFuelBound source, 40] do
    assertTrue (inputs.runTerminalReturnBody? fuel source store).isNone "numeric bound bypassed whole-arm rejection"
  match source.value with
  | [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩] =>
      let expected := Core.Value.word (word (if choice then 7 else 9))
      if conditionDone : inputs.run? 40 condition store = some (.bool, .done (.bool choice) store) then
        if branchDone : inputs.runReturnBody? 40 (if choice then thenBody else elseBody) store = some (.word, .done expected store) then
          have _ := selectedPiecesEvaluate inputs source.span statementSpan condition thenBody elseBody
            choice .word expected conditionDone branchDone
          pure ()
        else throw (IO.userError "selected valid arm did not independently execute")
      else throw (IO.userError "actual condition selected the wrong branch")
  | _ => throw (IO.userError "skipped-arm fixture lost its canonical conditional")

private def checkRejected_variant (inputs : LocalInputs) (content : String) (zeroShapeBound : Bool) : IO Unit := do
  let source ← body_variant content
  assertTrue (inputs.checkTerminalReturnBody? source).isNone s!"{content}: unsupported body checked"
  assertTrue ((inputs.checkReturnBody? source).isNone && (inputs.checkConditionalReturnBody? source).isNone)
    "common rejection differed from the two original checker failures"
  if zeroShapeBound then assertTrue (terminalReturnBodyFuelBound source == 0) "unsupported outer shape gained a bound"
  for fuel in [0, 1, 4, 13, terminalReturnBodyFuelBound source, 50] do
    assertTrue ((inputs.runTerminalReturnBody? fuel source store).isNone &&
      (inputs.runReturnBody? fuel source store).isNone && (inputs.runConditionalReturnBody? fuel source store).isNone)
      "structural/type rejection or original runner agreement depended on fuel"

def frontendParsedTerminalReturnBodiesTests : IO Unit := do
  checkText_variant LocalInputs.empty " /* unit */ { return; } " .unit .unit .unit 1 1
  checkText_variant LocalInputs.empty "{ return ((0007)); }" (.word (word 7)) .word (.word (word 7)) 1 1
  checkEntry_variant "function bare() returns (Unit) { return; }" [] .unit .unit .unit 1 1
  for choice in [false, true] do
    let some declaration ← parsed_variant? (Syntax.Parser.functionDecl .module)
      "function parameters(c: Bool, t: Word, f: Word) returns (Word) { return t; }"
      | throw (IO.userError "actual parameter declaration did not parse")
    let some inputs := bindRuntimeParameters? types owner_variant declaration.value.signature.parameters.elements (arguments choice)
      | throw (IO.userError "typed Word parameters did not bind")
    checkText_variant inputs "{ return; }" .unit .unit .unit 1 1
    checkText_variant inputs "{ return t; }" (.var 1) .word (.word (word 7)) 1 1
    checkText_variant inputs "{ return ~t; }" (.unary .wordNot (.var 1)) .word (.word ((word 7).bitNot)) 3 3
    checkText_variant inputs "{ return t + f; }" (.binary .wordAdd (.var 1) (.var 0)) .word (.word (word 16)) 5 5
    checkText_variant inputs "{ return c ? t * f : f; }" (.ifE (.var 2) (.binary .wordMul (.var 1) (.var 0)) (.var 0))
      .word (.word (word (if choice then 63 else 9))) (if choice then 8 else 4) 8
    checkText_variant inputs "{ return c && t < f; }" (.ifE (.var 2) (lt (.var 1) (.var 0)) (.bool false))
      .bool (.bool choice) (if choice then 14 else 4) 14
    let simple := Core.Expr.ifE (.var 2) (.var 1) (.var 0)
    let simpleBody ← body_variant "{ if(c){return t;}else{return f;} }"
    let pending : Core.State := ⟨.ret (.bool choice), [.ifBranches (.var 1) (.var 0) inputs.environment.values], store⟩
    assertTrue (decide (inputs.runTerminalReturnBody? 2 simpleBody store = some (.word, .outOfFuel pending) ∧
      Core.runStateful 0 pending = .outOfFuel pending ∧
      Core.runStateful 1 pending = .outOfFuel ⟨.eval (if choice then .var 1 else .var 0) inputs.environment.values, [], store⟩ ∧
      Core.runStateful 0 { pending with continuation := [] } = .done (.bool choice) store))
      "pending conditional selection or dropped-frame counterexample changed"
    checkText_variant inputs " /* lead */ { if /* guard */ (c) { return ((t)); } else { return f; } }"
      simple .word (.word (word (if choice then 7 else 9))) 4 4
    checkEntry_variant "function choose(c: Bool, t: Word, f: Word) returns (Word) { if(c){return t;}else{return f;} }"
      (arguments choice) simple .word (.word (word (if choice then 7 else 9))) 4 4
    checkText_variant inputs "{ if(c){return t * f + t;}else{return f;} }"
      (.ifE (.var 2) (.binary .wordAdd (.binary .wordMul (.var 1) (.var 0)) (.var 1)) (.var 0))
      .word (.word (word (if choice then 70 else 9))) (if choice then 12 else 4) 12
    checkText_variant inputs "{ if(c){return t < f;}else{return t >= f;} }"
      (.ifE (.var 2) (lt (.var 1) (.var 0)) (.unary .boolNot (lt (.var 1) (.var 0))))
      .bool (.bool choice) (if choice then 14 else 16) 16
    checkText_variant inputs "{ if(c && t < f){return t + f;}else{return f;} }"
      (.ifE (.ifE (.var 2) (lt (.var 1) (.var 0)) (.bool false)) (.binary .wordAdd (.var 1) (.var 0)) (.var 0))
      .word (.word (word (if choice then 16 else 9))) (if choice then 21 else 7) 21
    checkText_variant inputs "{ if(c){return c ? t - f : f;}else{return c ? t : f;} }"
      (.ifE (.var 2) (.ifE (.var 2) (.binary .wordSub (.var 1) (.var 0)) (.var 0))
        (.ifE (.var 2) (.var 1) (.var 0))) .word
      (.word (if choice then (word 7).sub (word 9) else word 9)) (if choice then 11 else 7) 11
    for invalid in ["missing", "c", "t + c", "t(c)", s!"{Core.wordModulus}"] do
      checkSkipped inputs choice invalid
    for content in ["{}", "{ return t; return f; }", "{ t; return f; }", "{ return t; missing; }", "{ if(c){return t;} }",
        "{ t; if(c){return t;}else{return f;} }", "{ if(c){return t;}else{return f;} return t; }",
        "{ if(c){return t;}else{return f;} if(c){return f;}else{return t;} }",
        "{ { if(c){return t;}else{return f;} } }"] do checkRejected_variant inputs content true
    for content in ["{ return missing; }", "{ return t(c); }", "{ return c ? t : missing; }",
        "{ return c ? t : c; }", "{ if(t){return t;}else{return f;} }", "{ if(missing){return t;}else{return f;} }",
        "{ if(c){return t;}else{return c;} }", "{ if(c){return;}else{return t;} }",
        "{ if(c){}else{return f;} }", "{ if(c){return t;}else{} }",
        "{ if(c){t; return t;}else{return f;} }", "{ if(c){return t; f;}else{return f;} }",
        "{ if(c){return t; return f;}else{return f;} }", "{ if(c){return t;}else{return f; t;} }",
        "{ if(c){if(c){return t;}else{return f;}}else{return f;} }",
        "{ if(c){return t;}else{if(c){return t;}else{return f;}} }",
        "{ if(c){return t;}else{while(c){return f;}} }"] do checkRejected_variant inputs content false
    checkText_variant inputs "{ if(c){return;}else{return;} }" (.ifE (.var 2) .unit .unit) .unit .unit 4 4
  checkText_variant LocalInputs.empty "{ if(0 < 1){return;}else{return;} }"
    (.ifE (lt (.word (word 0)) (.word (word 1))) .unit .unit) .unit .unit 14 14
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cellLeft : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let cellRight : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 91, .cellRef⟩
  let closureLeft : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let closureRight : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, left, right) in [("Word", (⟨.word, .word Core.Word.maximum, .word⟩ : TypedRuntimeArgument),
      ⟨.word, .word (word (2 ^ 255)), .word⟩), ("Unit", unit, unit), ("Cell", cellLeft, cellRight), ("Fn", closureLeft, closureRight),
      ("Bool", (⟨.bool, .bool true, .bool⟩ : TypedRuntimeArgument), ⟨.bool, .bool false, .bool⟩)] do
    for choice in [false, true] do
      checkEntry_variant (s!"function expression(c: Bool, t: {name}, f: {name}) returns ({name})" ++
        " { return c ? t : f; }") [⟨.bool, .bool choice, .bool⟩, left, right]
        (.ifE (.var 2) (.var 1) (.var 0)) left.type (if choice then left.value else right.value) 4 4
      checkEntry_variant (s!"function values(c: Bool, t: {name}, f: {name}) returns ({name})" ++
        " { if(c){return t;}else{return f;} }") [⟨.bool, .bool choice, .bool⟩, left, right]
        (.ifE (.var 2) (.var 1) (.var 0)) left.type (if choice then left.value else right.value) 4 4
      checkEntry_variant "function units(c: Bool, u: Unit) returns (Unit) { if(c){return;}else{return u;} }"
        [⟨.bool, .bool choice, .bool⟩, unit] (.ifE (.var 1) .unit (.var 0)) .unit .unit 4 4
  for content in ["", "if(c){return t;}else{return f;}", "{ if(c){return t;}else{return f;} ",
      "{ if(c){return t}else{return f;} }", "{ if(c){return t;}else }", "{ if(c){return t;}else{return f;} } trailing"] do
    assertTrue (← parsed_variant? (Syntax.Parser.block .allow) content).isNone "malformed or incompletely consumed block accepted"
  assertTrue (← parsed_variant? (Syntax.Parser.functionDecl .module)
    "function trailing(c: Bool) returns (Unit) { if(c){return;}else{return;} } trailing").isNone
    "function helper accepted only a valid prefix"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTerminalReturnTreeEvaluation
/-! Fixture-supplied branch scripts certify actual parsed selected paths.
This is not a tree runner: no branch search, execution API or fuel policy is
introduced. Core correspondence always uses the actual whole checker result. -/

set_option autoImplicit false

namespace Tests
open Solcore Solcore.Frontend

private def owner_variant2 : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeEvaluation", by decide⟩], by decide⟩⟩, 9⟩
private def word_variant (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def inputs (c d : Bool) (type : Core.Ty) (x y : Core.Value)
    (xTyped : Core.ValueHasType x type) (yTyped : Core.ValueHasType y type) : LocalInputs :=
  let flags := (LocalInputs.empty.bindFresh owner_variant2 "c" .bool (.bool c) .bool).bindFresh owner_variant2 "d" .bool (.bool d) .bool
  (flags.bindFresh owner_variant2 "x" type x xTyped).bindFresh owner_variant2 "y" type y yTyped
private def stores_variant : List Core.Store := [[.word (word_variant 101), .cellRef .word 31],
  [.closure .bool .bool (.var 0) [], .bool false, .word Core.Word.maximum]]
private def body_variant2 (content : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-tree-evaluation.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "fixture did not parse as a block")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd)
    s!"block was diagnosed or partially consumed: {content}; {reprStr next.diagnostics}; atEnd={next.atEnd}"
  return source

private structure Reference (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  costed : LocalExpressionEvaluatesWithCost table environment store source value store 1
private def reference (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Reference table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "script referenced an unknown name")
      | some id =>
          match found : environment.lookup? id with
          | none => throw (IO.userError "script referenced a missing actual value")
          | some value => return ⟨value, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "script expected its actual identifier expression")
private structure ExpressionCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table environment store source value store cost
private def expressionCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) : IO (ExpressionCertificate table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ =>
      let ref ← reference table environment store source
      return ⟨ref.value, 1, ref.costed⟩
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let ref ← reference table environment store operand
      match actual : ref.value with
      | .word value => return ⟨.word value.bitNot, 3, by rw [sourceAt]; exact .bitNot (by simpa only [actual] using ref.costed)⟩
      | _ => throw (IO.userError "word certificate received a non-word value")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table environment store left
      let second ← reference table environment store right
      match firstAt : first.value, secondAt : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), 5, by
          rw [sourceAt]
          exact .subtract (by simpa only [firstAt] using first.costed) (by simpa only [secondAt] using second.costed)⟩
      | _, _ => throw (IO.userError "ordered subtraction certificate received a non-word")
  | _ => throw (IO.userError "expression is outside this fixture certificate vocabulary")
private structure LeafCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : ReturnBodyEvaluatesWithCost table environment store source value store cost
private def leafCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) : IO (LeafCertificate table environment store source) := do
  match sourceAt : source with
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .bare⟩
  | ⟨_, [⟨_, .returnStmt (some expression)⟩]⟩ =>
      let leaf ← expressionCertificate table environment store expression
      return ⟨leaf.value, leaf.cost, by rw [sourceAt]; exact .expression leaf.costed⟩
  | _ => throw (IO.userError "script did not end at a singleton return")

private theorem oldEmbeddings {table : LocalNameTable} {environment : Resolved.Environment}
    {store : Core.Store} {source : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment store source value store cost) :
    TerminalReturnTreeEvaluates table environment store source value store ∧
      TerminalReturnTreeEvaluatesWithCost table environment store source value store cost := by
  have oldRaw := evaluation.erase.returnTree
  have oldCost := evaluation.returnTree
  have unionRaw := (TerminalReturnBodyEvaluates.conditional evaluation.erase).returnTree
  have unionCost := (TerminalReturnBodyEvaluatesWithCost.conditional evaluation).returnTree
  have _ := oldRaw.deterministic unionRaw
  have _ := oldCost.deterministic unionCost
  exact ⟨oldRaw, unionCost⟩
private structure TreeCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  raw : TerminalReturnTreeEvaluates table environment store source value store
  costed : TerminalReturnTreeEvaluatesWithCost table environment store source value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) (choices : List Bool) : IO (TreeCertificate table environment store source) := do
  match choices with
  | [] =>
      let leaf ← leafCertificate table environment store source
      have _ := leaf.costed.returnTree
      have _ := leaf.costed.erase.returnTree
      return ⟨leaf.value, leaf.cost, .single leaf.costed.erase, .single leaf.costed⟩
  | choice :: rest =>
      match sourceAt : source with
      | ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
          let guard ← reference table environment store condition
          if agrees : guard.value = .bool choice then
            match choiceAt : choice with
            | true =>
                have conditionCost : LocalExpressionEvaluatesWithCost table environment store condition (.bool true) store 1 := by
                  simpa only [agrees, choiceAt] using guard.costed
                let child ← certify table environment store thenBody rest
                if rest.isEmpty then
                  let leaf ← leafCertificate table environment store thenBody
                  have _ := oldEmbeddings (ConditionalReturnBodyEvaluatesWithCost.ifTrue
                    (blockSpan := blockSpan) (statementSpan := statementSpan) (elseBody := elseBody) conditionCost leaf.costed)
                  pure ()
                return ⟨child.value, 1 + child.cost + 2, by rw [sourceAt]; exact .ifTrue conditionCost.erase child.raw,
                  by rw [sourceAt]; exact .ifTrue conditionCost child.costed⟩
            | false =>
                have conditionCost : LocalExpressionEvaluatesWithCost table environment store condition (.bool false) store 1 := by
                  simpa only [agrees, choiceAt] using guard.costed
                let child ← certify table environment store elseBody rest
                if rest.isEmpty then
                  let leaf ← leafCertificate table environment store elseBody
                  have _ := oldEmbeddings (ConditionalReturnBodyEvaluatesWithCost.ifFalse
                    (blockSpan := blockSpan) (statementSpan := statementSpan) (thenBody := thenBody) conditionCost leaf.costed)
                  pure ()
                return ⟨child.value, 1 + child.cost + 2, by rw [sourceAt]; exact .ifFalse conditionCost.erase child.raw,
                  by rw [sourceAt]; exact .ifFalse conditionCost child.costed⟩
          else throw (IO.userError "supplied branch script disagreed with actual condition value")
      | _ => throw (IO.userError "script expected an explicit if/else node")
termination_by choices.length

private theorem arbitraryContinuation {table : LocalNameTable} {environment : Resolved.Environment}
    {context : Resolved.Context} {store : Core.Store} {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (certificate : TreeCertificate table environment store source)
    (accepted : elaborateTerminalReturnTree? table context source = some (core, type))
    (sameIds : environment.ids = context.ids) (continuation : List Core.Frame) :
    Core.Steps certificate.cost ⟨.eval core environment.values, continuation, store⟩
      ⟨.ret certificate.value, continuation, store⟩ :=
  certificate.costed.checked_toStepsWithContinuation accepted sameIds continuation
private def checked (localInputs : LocalInputs) (store : Core.Store) (source : Syntax.Block)
    (choices : List Bool) (expected : Core.Expr) (value : Core.Value) (cost : Nat) : IO Unit := do
  let certificate ← certify localInputs.names localInputs.environment store source choices
  assertTrue (decide (certificate.value = value ∧ certificate.cost = cost)) "independent selected source cost/value changed"
  match accepted : elaborateTerminalReturnTree? localInputs.names localInputs.context source with
  | none => throw (IO.userError "whole tree checking failed")
  | some (core, type) =>
      let typing := elaborateTerminalReturnTree?_sound accepted
      have _ := typing.evaluates localInputs.sameIds localInputs.environmentTyped store
      have _ := certificate.raw.preserves_type typing localInputs.sameIds localInputs.environmentTyped
      have _ := certificate.raw.store_eq
      have _ := certificate.raw.exists_cost
      have _ := terminalReturnTreeEvaluates_iff_exists_cost.mp certificate.raw
      have _ := certificate.raw.deterministic certificate.costed.erase
      have _ := certificate.costed.store_eq
      have _ := certificate.costed.cost_pos
      have _ := certificate.costed.deterministic certificate.costed
      let correspondence := elaborateTerminalReturnTree?_evaluates_iff accepted localInputs.sameIds
      have coreEvaluation := correspondence.mp certificate.raw
      have _ := correspondence.mpr coreEvaluation
      have _ := certificate.costed.checked_toSteps accepted localInputs.sameIds
      have _ := arbitraryContinuation certificate accepted localInputs.sameIds
      assertTrue (decide (core = expected ∧ Core.infer? localInputs.context.values core = some type ∧
        Core.runStateful cost (.initial core localInputs.environment.values store) = .done value store))
        "actual checked Core did not have the certified path endpoint"
      -- runStateful inspects the next frame even at zero fuel; this head accepts every returned value.
      let continuation : List Core.Frame := [.letBody (.var 0) [.word (word_variant 17)], .unaryApply .wordNot]
      have _ := arbitraryContinuation certificate accepted localInputs.sameIds continuation
      assertTrue (decide (Core.runStateful cost ⟨.eval core localInputs.environment.values, continuation, store⟩ =
        .outOfFuel ⟨.ret value, continuation, store⟩)) "pending arbitrary continuation was executed, edited or discarded"
      if (Core.UnaryOp.wordNot.apply value).isNone then
        let faulty : List Core.Frame := [.unaryApply .wordNot, .binaryApply .wordSub (.word (word_variant 17))]
        have _ := arbitraryContinuation certificate accepted localInputs.sameIds faulty
        assertTrue (decide (Core.runStateful cost ⟨.eval core localInputs.environment.values, faulty, store⟩ =
          .fault (.invalidUnaryOperand .wordNot value) ⟨.ret value, faulty, store⟩))
          "fault observation at zero remaining fuel lost the certified endpoint or original continuation"

def frontendParsedTerminalReturnTreeEvaluationTests : IO Unit := do
  let source ← body_variant2 "{if(c){if(d){return ~x;}else{return x - y;}}else{return y;}}"
  let core : Core.Expr := .ifE (.var 3) (.ifE (.var 2) (.unary .wordNot (.var 1))
    (.binary .wordSub (.var 1) (.var 0))) (.var 0)
  let mirror ← body_variant2 "{if(c){return x;}else{if(d){return y;}else{if(c){return ~x;}else{return x - y;}}}}"
  let mirrorCore : Core.Expr := .ifE (.var 3) (.var 1) (.ifE (.var 2) (.var 0)
    (.ifE (.var 3) (.unary .wordNot (.var 1)) (.binary .wordSub (.var 1) (.var 0))))
  for c in [false, true] do
    for d in [false, true] do
      for (x, y) in [(word_variant 9, word_variant 2), (Core.Word.zero, Core.Word.maximum), (word_variant (2 ^ 255), word_variant 7)] do
        let actual := inputs c d .word (.word x) (.word y) .word .word
        for store in stores_variant do
          checked actual store source (if c then [true, d] else [false]) core
            (.word (if c then if d then x.bitNot else x.sub y else y)) (if c then if d then 9 else 11 else 4)
          checked actual store mirror (if c then [true] else if d then [false, true] else [false, false, false]) mirrorCore
            (.word (if c then x else if d then y else x.sub y)) (if c then 4 else if d then 7 else 14)
  let opaqueSource ← body_variant2 "{if(c){if(d){return x;}else{return y;}}else{return x;}}"
  let opaqueCore : Core.Expr := .ifE (.var 3) (.ifE (.var 2) (.var 1) (.var 0)) (.var 1)
  let closureLeft : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let closureRight : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (left, right) in [(closureLeft, closureRight),
      (⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩)] do
    if matching : right.type = left.type then
      for c in [false, true] do
        for d in [false, true] do
          for store in stores_variant do
            checked (inputs c d left.type left.value right.value left.valueTyped (matching ▸ right.valueTyped)) store opaqueSource
              (if c then [true, d] else [false]) opaqueCore (if c && !d then right.value else left.value) (if c then 7 else 4)
    else throw (IO.userError "opaque fixture supplied different types")
  let units ← body_variant2 "{if(c){if(d){return;}else{return;}}else{return;}}"
  for store in stores_variant do
    checked (inputs true false .unit .unit .unit .unit .unit) store units [true, false]
      (.ifE (.var 3) (.ifE (.var 2) .unit .unit) .unit) .unit 7
  let actual := inputs true true .word (.word (word_variant 9)) (.word (word_variant 2)) .word .word
  for invalid in ["{return missing;}", "{return c;}", "{}", "{if(d){return x;}}", "{return x;return y;}", "{return x();}"] do
    let skipped ← body_variant2 ("{if(c){if(d){return x;}else" ++ invalid ++ "}else{return y;}}")
    for store in stores_variant do
      let certificate ← certify actual.names actual.environment store skipped [true, true]
      have _ := certificate.raw.exists_cost
      have _ := certificate.raw.store_eq
      have _ := certificate.costed.cost_pos
      assertTrue (decide (certificate.value = .word (word_variant 9) ∧ certificate.cost = 7) &&
        (elaborateTerminalReturnTree? actual.names actual.context skipped).isNone) "raw skipped success was mistaken for whole acceptance"
  let untyped : Resolved.Environment := actual.environment.map fun entry => (entry.1, Core.Value.bool true)
  have aligned : untyped.ids = actual.context.ids := by
    simpa only [untyped, Resolved.LocalScope.ids, List.map_map, Function.comp_def] using actual.sameIds
  for store in stores_variant do
    let certificate ← certify actual.names untyped store opaqueSource [true, true]
    match accepted : elaborateTerminalReturnTree? actual.names actual.context opaqueSource with
    | none => throw (IO.userError "aligned raw contrast lost actual whole checking")
    | some (actualCore, type) =>
        let bridge := elaborateTerminalReturnTree?_evaluates_iff accepted aligned
        have _ := bridge.mp certificate.raw
        have _ := bridge.mpr (bridge.mp certificate.raw)
        have _ := certificate.costed.checked_toSteps accepted aligned
        have _ := arbitraryContinuation certificate accepted aligned
        assertTrue (decide (type = .word ∧ certificate.value = .bool true ∧ certificate.cost = 7 ∧ actualCore = opaqueCore ∧
          Core.runStateful 7 (.initial actualCore untyped.values store) = .done (.bool true) store))
          "raw identity-aligned correspondence incorrectly demanded runtime typing"
  let referenceBody ← body_variant2 "{return x;}"
  let reordered : Resolved.Environment := actual.environment.reverse
  for store in stores_variant do
    let certificate ← certify actual.names reordered store referenceBody []
    let some (actualCore, type) := elaborateTerminalReturnTree? actual.names actual.context referenceBody
      | throw (IO.userError "misalignment contrast lost actual checker provenance")
    have _ := certificate.raw.store_eq
    assertTrue (decide (reordered.ids ≠ actual.context.ids ∧ certificate.value = .word (word_variant 9) ∧
      type = .word ∧ actualCore = .var 1 ∧ Core.runStateful 1 (.initial actualCore reordered.values store) =
        .done (.bool true) store)) "reordered identities were treated as an aligned positional environment"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTerminalReturnTrees
/-! Recursive bodies are checked statically using actual parsed parameters.
No values, tree execution or costs are assumed by recursive entry compilation.
Source depth, unlike the depth of its lowered Core, controls the old body profile. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant3 : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"StaticReturnTrees", by decide⟩], by decide⟩⟩, 17⟩
private def types_variant : TypeNameTable := [(["Bool"], .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Unit"], .unit), (["Word"], .word), (["Fn"], .function .word (.namedData ⟨91⟩))]
private def parameterText : String := "c: Bool,d: Bool,x: Opaque,y: Opaque,u: Unit,w: Word,f: Fn"
private def parameterTypes : List Core.Ty :=
  [.bool, .bool, .namedData ⟨91⟩, .namedData ⟨91⟩, .unit, .word, .function .word (.namedData ⟨91⟩)]

private structure TreeFixture where
  content : String
  core : Core.Expr
  depth : Nat
private def leaf (expression : String) (core : Core.Expr) : TreeFixture :=
  ⟨"{return " ++ expression ++ ";}", core, 0⟩
private def node (condition : String) (core : Core.Expr) (left right : TreeFixture) : TreeFixture :=
  ⟨"{if(" ++ condition ++ ")" ++ left.content ++ "else" ++ right.content ++ "}",
    .ifE core left.core right.core, max left.depth right.depth + 1⟩
private def spine : Nat → Bool → TreeFixture → TreeFixture → TreeFixture
  | 0, _, selected, _ => selected
  | depth + 1, right, selected, other =>
      let nested := spine depth (!right) selected other
      if right then node "d" (.var 5) other nested else node "c" (.var 6) nested other
private def bury : Nat → Bool → String → String
  | 0, _, content => content
  | depth + 1, right, content =>
      let nested := bury depth (!right) content
      if right then "{if(d){return y;}else" ++ nested ++ "}"
      else "{if(c)" ++ nested ++ "else{return x;}}"
private def buriedCore : Nat → Bool → Core.Expr → Core.Expr
  | 0, _, core => core
  | depth + 1, right, core =>
      let nested := buriedCore depth (!right) core
      if right then .ifE (.var 5) (.var 3) nested else .ifE (.var 6) nested (.var 4)

private def parsed_variant2? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-static-return-trees.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"lexer invariant: {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")

private def staticInputs (source : Syntax.FunctionDecl) : IO LocalTypeInputs := do
  match accepted : declareRuntimeParameters? types_variant owner_variant3 source.value.signature.parameters.elements with
  | none => throw (IO.userError "complete static parameters failed without needing values")
  | some inputs =>
      have _ := declareRuntimeParameters?_sound accepted
      assertTrue (decide (inputs.context.values = parameterTypes.reverse ∧
        inputs.names.map Prod.fst = ["f", "w", "u", "y", "x", "d", "c"] ∧
        inputs.ids = (List.range 7).reverse.map (fun index => (⟨owner_variant3, index⟩ : Resolved.LocalId))))
        "original parameter spelling, position, type or generated identity changed"
      return inputs

private theorem excludeWrong {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Block} {core wrong : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates table context source core type) (different : wrong ≠ core) :
    ¬ TerminalReturnTreeElaborates table context source wrong type :=
  fun other => different (other.result_unique elaboration).1

private def compatibility (inputs : LocalTypeInputs) (source : Syntax.Block) : IO Unit := do
  match source with
  | ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =>
      have _ := elaborateTerminalReturnTree?_single inputs.names inputs.context returned blockSpan returnSpan
      have _ := elaborateTerminalReturnTree?_single_terminal inputs.names inputs.context returned blockSpan returnSpan
      assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context source =
        elaborateReturnBody? inputs.names inputs.context source ∧
        elaborateTerminalReturnTree? inputs.names inputs.context source =
          elaborateTerminalReturnBody? inputs.names inputs.context source)) "singleton Option equality lost rejection or exact Core"
  | ⟨blockSpan, [⟨ifSpan, .ifThen condition ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
      (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ =>
      have _ := elaborateTerminalReturnTree?_conditional_singletons inputs.names inputs.context condition thenReturned elseReturned
        blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan
      have _ := elaborateTerminalReturnTree?_conditional_singletons_terminal inputs.names inputs.context condition thenReturned elseReturned
        blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan
      assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context source =
        elaborateConditionalReturnBody? inputs.names inputs.context source ∧
        elaborateTerminalReturnTree? inputs.names inputs.context source =
          elaborateTerminalReturnBody? inputs.names inputs.context source)) "one-level Option equality lost an invalid arm"
  | _ => pure ()
  match accepted : elaborateReturnBody? inputs.names inputs.context source with
  | none => pure ()
  | some _ =>
      let old := elaborateReturnBody?_elaborates accepted
      have _ := old.returnTree
      have _ := old.hasType.returnTree
      have _ := old.returnTree_complete
  match accepted : elaborateConditionalReturnBody? inputs.names inputs.context source with
  | none => pure ()
  | some _ =>
      let old := elaborateConditionalReturnBody?_elaborates accepted
      have _ := old.returnTree
      have _ := old.hasType.returnTree
      have _ := old.returnTree_complete
  match accepted : elaborateTerminalReturnBody? inputs.names inputs.context source with
  | none => pure ()
  | some pair =>
      let old := elaborateTerminalReturnBody?_elaborates accepted
      have _ := old.returnTree
      have _ := old.hasType.returnTree
      have _ := old.returnTree_complete
      assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context source = some pair))
        "old successful elaboration lost its identical tree embedding"

private def checkTree (inputs : LocalTypeInputs) (source : Syntax.Block) (expected : Core.Expr)
    (type : Core.Ty) : IO Unit := do
  match accepted : elaborateTerminalReturnTree? inputs.names inputs.context source with
  | none => throw (IO.userError "finite recursive tree was rejected")
  | some (core, actualType) =>
      let elaboration := elaborateTerminalReturnTree?_elaborates accepted
      have _ := elaborateTerminalReturnTree?_iff.mp accepted
      let typing := elaborateTerminalReturnTree?_sound accepted
      have _ := elaboration.complete
      have _ := elaboration.hasType
      have _ := typing.elaborates_exact
      have _ := typing.elaborates
      have _ := terminalReturnTreeHasType_iff_elaborates_exact.mp typing
      have _ := terminalReturnTreeHasType_iff_elaborates.mp typing
      have _ := elaborateTerminalReturnTree?_core_hasType accepted
      have _ := elaboration.result_unique elaboration
      have _ := typing.type_unique typing
      assertTrue (decide (core = expected ∧ actualType = type ∧
        Core.infer? inputs.context.values expected = some type)) "recursive source lost exact ordered Core or result type"
      let wrong := match core with
        | .ifE condition left right =>
            if left != right then Core.Expr.ifE condition right left
            else .ifE (.unary .boolNot condition) left right
        | _ => .ifE (.bool true) core core
      if different : wrong ≠ core then
        have _ := excludeWrong elaboration different
        assertTrue (decide (Core.infer? inputs.context.values wrong = some actualType))
          "wrong-tree comparison was not independently equally typed"
      else throw (IO.userError "wrong-Core contrast accidentally equaled the actual tree")
      match sourceAt : source with
      | ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
          have shaped : elaborateTerminalReturnTree? inputs.names inputs.context
              ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, actualType) := by
            simpa only [sourceAt] using accepted
          have _ := elaborateTerminalReturnTree?_children shaped
          let otherSpan : Syntax.SourceSpan := ⟨⟨.main, "outer-ranges-only.sol"⟩, 900, 2⟩
          have _ := elaborateTerminalReturnTree?_spans inputs.names inputs.context condition thenBody elseBody
            blockSpan statementSpan otherSpan otherSpan
          assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context
            ⟨otherSpan, [⟨otherSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, actualType)))
            "outer ranges changed static meaning of original ordered children"
          match core with
          | .ifE conditionCore thenCore elseCore =>
              assertTrue (decide (elaborateLocalExpression? inputs.names inputs.context condition = some (conditionCore, .bool) ∧
                elaborateTerminalReturnTree? inputs.names inputs.context thenBody = some (thenCore, type) ∧
                elaborateTerminalReturnTree? inputs.names inputs.context elseBody = some (elseCore, type)))
                "ordered children did not use the original static inputs"
          | _ => throw (IO.userError "conditional source did not lower to ordered ifE")
          assertTrue (source.span.contains statementSpan && statementSpan.contains condition.span &&
            statementSpan.contains thenBody.span && statementSpan.contains elseBody.span &&
            decide (thenBody.span.endByte ≤ elseBody.span.startByte)) "own recursive child spans or written order changed"
      | ⟨_, [⟨_, .returnStmt _⟩]⟩ => pure ()
      | _ => throw (IO.userError "accepted tree lost its original whole-block shape")
  compatibility inputs source

private def checkFixture (fixture : TreeFixture) (type : Core.Ty) (annotation : String) : IO Unit := do
  let some block ← parsed_variant2? (Syntax.Parser.block .allow) fixture.content
    | throw (IO.userError "actual complete block failed to parse")
  let returns := if annotation.isEmpty then "" else s!" returns ({annotation})"
  let some source ← parsed_variant2? (Syntax.Parser.functionDecl .module)
      (s!"function tree({parameterText})" ++ returns ++ fixture.content)
    | throw (IO.userError "same text in its own complete declaration failed to parse")
  let inputs ← staticInputs source
  if headerAt : interpretRuntimeFunctionHeader? types_variant source.value.signature = some type then
    have _ := interpretRuntimeFunctionHeader?_iff.mp headerAt
    checkTree inputs block fixture.core type
    checkTree inputs source.value.body fixture.core type
    assertTrue (decide ((compileRuntimeFunction? types_variant owner_variant3 source).map (fun result => (result.core, result.returnType)) =
      some (fixture.core, type))) "value-free recursive entry compilation lost its exact body"
    if 1 < fixture.depth then
      assertTrue ((elaborateTerminalReturnBody? inputs.names inputs.context block).isNone &&
        (elaborateTerminalReturnBody? inputs.names inputs.context source.value.body).isNone) "recursive entry support expanded the old body adapter"
    else
      assertTrue (decide (elaborateTerminalReturnBody? inputs.names inputs.context block = some (fixture.core, type) ∧
        (compileRuntimeFunction? types_variant owner_variant3 source).map (fun result => (result.core, result.returnType)) =
          some (fixture.core, type))) "old source shapes lost their exact optional result"
  else throw (IO.userError "entry contrast had a bad header rather than a deeper body")

private def rejected (content : String) (entryCore : Option Core.Expr := none) : IO Unit := do
  let some block ← parsed_variant2? (Syntax.Parser.block .allow) content
    | throw (IO.userError s!"semantic tree rejection did not fully parse: {content}")
  let some source ← parsed_variant2? (Syntax.Parser.functionDecl .module)
      (s!"function invalid({parameterText}) returns (Opaque)" ++ content)
    | throw (IO.userError "invalid tree in whole declaration failed to parse")
  let inputs ← staticInputs source
  for ownBody in [block, source.value.body] do
    match failed : elaborateTerminalReturnTree? inputs.names inputs.context ownBody with
    | some _ => throw (IO.userError "a deeply unselected invalid child bypassed whole-tree checking")
    | none =>
        have _ := elaborateTerminalReturnTree?_eq_none_iff.mp failed
        compatibility inputs ownBody
    if entryCore.isSome then
      assertTrue (elaborateTypedLetReturnBody? types_variant owner_variant3 inputs ownBody).isNone "recursive entry changed the old prefix adapter"
  match entryCore with
  | none => assertTrue (compileRuntimeFunction? types_variant owner_variant3 source).isNone "invalid whole source entered runtime compilation"
  | some core => assertTrue (decide (Core.infer? parameterTypes.reverse core = some (.namedData ⟨91⟩) ∧
      (compileRuntimeFunction? types_variant owner_variant3 source).map (fun compiled =>
        (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) =
          some (core, .namedData ⟨91⟩, inputs.names, parameterTypes.reverse))) "nominal recursive entry changed exact Core or original parameter-only rows"

def frontendParsedTerminalReturnTreeTests : IO Unit := do
  let left := leaf "x" (.var 4)
  let right := leaf "y" (.var 3)
  checkFixture (node "c" (.var 6) left left) (.namedData ⟨91⟩) "Opaque"
  for depth in [0, 1, 2, 3, 5, 8, 16] do
    for direction in [false, true] do
      checkFixture (spine depth direction left right) (.namedData ⟨91⟩) "Opaque"
  for (leftDepth, rightDepth) in [(0, 7), (6, 1), (3, 5), (9, 2)] do
    checkFixture (node "c" (.var 6) (spine leftDepth false left right) (spine rightDepth true right left))
      (.namedData ⟨91⟩) "Opaque"
  let bare : TreeFixture := ⟨"{return;}", .unit, 0⟩
  for depth in [0, 1, 4, 9] do checkFixture (spine depth false bare (leaf "u" (.var 2))) .unit ""
  checkFixture (spine 5 true (leaf "c" (.var 6)) (leaf "!d" (.unary .boolNot (.var 5)))) .bool "Bool"
  let expressionLeaf := leaf "c ? x : y" (.ifE (.var 6) (.var 4) (.var 3))
  checkFixture expressionLeaf (.namedData ⟨91⟩) "Opaque"
  checkFixture (node "c && !d" (.ifE (.var 6) (.unary .boolNot (.var 5)) (.bool false))
    expressionLeaf (spine 3 true left right)) (.namedData ⟨91⟩) "Opaque"
  let arithmetic := leaf "w / (w + 1)" (.binary .wordDiv (.var 1)
    (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1))))
  checkFixture (spine 3 false arithmetic (leaf "w" (.var 1))) .word "Word"
  rejected "{return missing;}"
  rejected "{return f(w);}"
  for depth in [0, 2, 5] do
    for direction in [false, true] do
      let deep := bury depth direction "{let z: Opaque = x;return z;}"
      let core := buriedCore depth direction (.letE (.var 4) (.var 0))
      let equal := Core.Expr.binary .wordEq (.word .zero) (.word .zero)
      let content := if direction then "{if(0 == 0){return x;}else" ++ deep ++ "}"
        else "{if(0 != 0)" ++ deep ++ "else{return y;}}"
      rejected content (some (if direction then .ifE equal (.var 4) core else .ifE (.unary .boolNot equal) core (.var 3)))
  let some wrapped ← parsed_variant2? (Syntax.Parser.block .allow) "{{return x;}}"
    | throw (IO.userError "original terminal block leaf did not parse")
  assertTrue (terminalReturnTreeFuelBound wrapped == 0 && typedLetReturnTreeFuelBound wrapped == 1)
    "terminal wrappers changed the old unsupported bound or added a new transition"
  for depth in [0, 2, 5] do
    for direction in [false, true] do
      let deep := bury depth direction "{{return x;}}"
      let core := buriedCore depth direction (.var 4)
      let equal := Core.Expr.binary .wordEq (.word .zero) (.word .zero)
      let content := if direction then "{if(0 == 0){return x;}else" ++ deep ++ "}"
        else "{if(0 != 0)" ++ deep ++ "else{return y;}}"
      rejected content (some (if direction then .ifE equal (.var 4) core else .ifE (.unary .boolNot equal) core (.var 3)))
  for invalid in ["{return missing;}", "{return c;}", "{return;}",
      "{if(w){return x;}else{return y;}}", "{if(c){return x;}}", "{return x;return y;}",
      "{}", "{return f(w);}"] do
    for depth in [0, 2, 5] do
      for direction in [false, true] do
        let deep := bury depth direction invalid
        -- Constant comparison guards place the bad subtree on the unselected side.
        let content := if direction then "{if(0 == 0){return x;}else" ++ deep ++ "}"
          else "{if(0 != 0)" ++ deep ++ "else{return y;}}"
        rejected content
  for content in ["", "{return x;", "{return x}", "{if(c){return x;}else{return y;}} trailing"] do
    assertTrue (← parsed_variant2? (Syntax.Parser.block .allow) content).isNone "incomplete or diagnosed block acquired tree meaning"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTerminalRuntimeEntries
/-! Compile each complete declaration once without values, then supply actual
ordered arguments. Terminal entries preserve exact costs, genuine checkpoints,
independent provenance, owner changes, and each execution's own store. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant4 : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"TerminalRuntimeEntry", by decide⟩], by decide⟩⟩, 30⟩
private def otherOwner_variant : Resolved.DeclarationId := { owner_variant4 with declarationIndex := 52 }
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word value), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def types_variant2 : TypeNameTable := [(["Bool"], .bool), (["Word"], .word), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def parsed_variant3? (content : String) (location : Syntax.Parser.FunctionLocation := .module) :
    IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-terminal-entry.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private structure Entry where
  declaration : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  provenance : RuntimeFunctionCompiles types_variant2 owner_variant4 declaration compiled

private def compile (content : String) (core : Core.Expr) (type : Core.Ty)
    (parameterTypes : List Core.Ty) (bound : Nat) : IO Entry := do
  let some declaration ← parsed_variant3? content | throw (IO.userError s!"{content}: incomplete declaration")
  match accepted : compileRuntimeFunction? types_variant2 owner_variant4 declaration with
  | none => throw (IO.userError s!"{content}: terminal compilation failed")
  | some compiled =>
      let names ← declaration.value.signature.parameters.elements.mapM fun parameter => do
        let .typed none name _ := parameter.value | throw (IO.userError "unsupported parameter compiled")
        assertTrue (parameter.span.contains name.span && declaration.span.contains parameter.span)
          "parameter source positions escaped their declaration"
        pure name.value
      let expectedNames := (names.zipIdx.map fun (name, index) =>
        (name, (⟨owner_variant4, index⟩ : Resolved.LocalId))).reverse
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
        compiled.inputs.context.values = parameterTypes.reverse ∧ compiled.inputs.names = expectedNames ∧
        Core.infer? parameterTypes.reverse core = some type)) "wrong open Core, source IDs, or declared return type"
      assertTrue (terminalReturnTreeFuelBound declaration.value.body == bound &&
        typedLetReturnTreeFuelBound declaration.value.body == bound) "wrong old body or integrated entry bound"
      match declaration.value.body.value with
      | [⟨_, .returnStmt _⟩] =>
          assertTrue (returnBodyFuelBound declaration.value.body == bound) "singleton source bound changed"
      | [⟨span, .ifThen condition thenBody (some elseBody)⟩] =>
          assertTrue (returnBodyFuelBound declaration.value.body == 0 &&
            span.contains condition.span && span.contains thenBody.span && span.contains elseBody.span &&
            decide (condition.span.endByte ≤ thenBody.span.startByte ∧ thenBody.span.endByte ≤ elseBody.span.startByte))
            "original singleton bound or written arm positions changed"
      | _ => throw (IO.userError "compiled a non-terminal body shape")
      return ⟨declaration, compiled, compileRuntimeFunction?_sound accepted⟩

private def checkCase (entry : Entry) (arguments : List TypedRuntimeArgument)
    (value : Core.Value) (cost : Nat) : IO Unit := do
  let source := entry.declaration
  let compiled := entry.compiled
  let bound := typedLetReturnTreeFuelBound source.value.body
  assertTrue (decide (0 < cost ∧ cost ≤ bound)) "actual selected cost exceeded source budget"
  if matching : arguments.map (·.type) = compiled.inputs.context.values.reverse then
    let some prepared := prepareRuntimeFunction? types_variant2 owner_variant4 source arguments
      | throw (IO.userError "actual matching arguments did not prepare")
    have _ := entry.provenance.prepare_arguments arguments matching
    assertTrue (decide (prepared.core = compiled.core ∧ prepared.returnType = compiled.returnType ∧
      prepared.inputs.names = compiled.inputs.names ∧ prepared.inputs.context.values = compiled.inputs.context.values ∧
      prepared.inputs.environment.values = arguments.reverse.map (·.value) ∧
      prepared.inputs.checkTerminalReturnTree? source.value.body = some (compiled.core, compiled.returnType)))
      "preparation changed static projection, ordered actual values, or the original checked body"
    let expectedRows := (compiled.inputs.names.reverse.zip arguments).map fun (name, argument) =>
      (name.1, name.2, argument.type, argument.value)
    assertTrue (decide (prepared.inputs.bindings.map (fun row => (row.name, row.id, row.type, row.value)) =
      expectedRows.reverse)) "actual source positions were paired with different values"
    for initialStore in stores do
      have _ := entry.provenance.run_done_of_fuelBound arguments matching initialStore bound (Nat.le_refl _)
      let run := fun fuel => runRuntimeFunction? types_variant2 owner_variant4 source arguments fuel initialStore
      let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore
      for fuel in List.range (bound + 3) do
        have _ := entry.provenance.run_eq arguments matching fuel initialStore
        have _ := runRuntimeFunction?_owner_eq types_variant2 owner_variant4 otherOwner_variant source arguments fuel initialStore
        assertTrue (decide (run fuel = some (compiled.returnType, Core.runStateful fuel initial) ∧
          run fuel = prepared.inputs.runTerminalReturnTree? fuel source.value.body initialStore ∧
          run fuel = runRuntimeFunction? types_variant2 otherOwner_variant source arguments fuel initialStore))
          "entry wrapper or owner change altered the full same-fuel machine result"
        assertTrue (match run fuel with
          | some (type, .done result finalStore) =>
              decide (cost ≤ fuel ∧ type = compiled.returnType ∧ result = value ∧ finalStore = initialStore)
          | some (type, .outOfFuel checkpoint) =>
              decide (fuel < cost ∧ type = compiled.returnType ∧ checkpoint.store = initialStore)
          | _ => false) "wrong exact threshold, typed value, or own store"
        for replacement in stores do
          have _ := runRuntimeFunction?_done_store_iff types_variant2 owner_variant4 source arguments fuel initialStore replacement
            compiled.returnType value
          assertTrue ((decide (run fuel = some (compiled.returnType, .done value initialStore))) ==
            decide (runRuntimeFunction? types_variant2 owner_variant4 source arguments fuel replacement =
              some (compiled.returnType, .done value replacement))) "store replay changed completion observations"
          if replacement != initialStore then
            assertTrue (decide (run fuel ≠ runRuntimeFunction? types_variant2 owner_variant4 source arguments fuel replacement))
              "distinct own stores were erased from complete results/checkpoints"
      for spent in List.range cost do
        match exhausted : run spent with
        | some (type, .outOfFuel checkpoint) =>
            for remaining in List.range (cost - spent + 3) do
              have _ := runRuntimeFunction?_resume exhausted remaining
              let resumed := Core.runStateful remaining checkpoint
              assertTrue (decide (run (spent + remaining) = some (type, resumed))) "genuine checkpoint resumption changed"
              assertTrue (match resumed with
                | .done result finalStore => decide (cost - spent ≤ remaining ∧ result = value ∧ finalStore = initialStore)
                | .outOfFuel residual => decide (remaining < cost - spent ∧ residual.store = initialStore)
                | _ => false) "resumption changed the exact residual cost or checkpoint's store"
        | _ => throw (IO.userError "genuine pre-completion checkpoint disappeared")
      match compiled.core with
      | .ifE condition thenCore elseCore =>
          let environment := arguments.reverse.map (·.value)
          let expected : Core.State := ⟨.eval condition environment,
            [.ifBranches thenCore elseCore environment], initialStore⟩
          assertTrue (decide (run 1 = some (compiled.returnType, .outOfFuel expected))) "initial conditional frame changed"
      | _ => pure ()
  else throw (IO.userError "positive test supplied mismatching argument types")

private def rejectArguments (entry : Entry) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ entry.compiled.inputs.context.values.reverse))
    "negative actual arguments accidentally matched"
  assertTrue (prepareRuntimeFunction? types_variant2 owner_variant4 entry.declaration arguments).isNone "ordered argument guard bypassed"
  for store in stores do
    for fuel in [0, typedLetReturnTreeFuelBound entry.declaration.value.body, 60] do
      assertTrue (runRuntimeFunction? types_variant2 otherOwner_variant entry.declaration arguments fuel store).isNone
        "ample fuel or owner change bypassed actual argument guard"

private def reject (content : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let some source ← parsed_variant3? content location | throw (IO.userError s!"{content}: negative fixture did not fully parse")
  assertTrue (compileRuntimeFunction? types_variant2 owner_variant4 source).isNone s!"{content}: invalid whole entry compiled"
  for arguments in [[], [boolArg false], [boolArg true], [wordArg 7],
      [boolArg false, wordArg 7, wordArg 9], [boolArg true, wordArg 7, wordArg 9]] do
    assertTrue (prepareRuntimeFunction? types_variant2 owner_variant4 source arguments).isNone "rejected entry prepared actual arguments"
    for store in stores do
      for fuel in [0, typedLetReturnTreeFuelBound source.value.body, 60] do
        assertTrue (runRuntimeFunction? types_variant2 owner_variant4 source arguments fuel store).isNone
          "whole header/parameter/arm rejection depended on fuel or selected value"

private def discardedPrefix : IO Unit := do
  let some source ← parsed_variant3? "function invalid(c: Bool,t: Word,f: Word) returns (Word){t; if(c){return t;}else{return f;}}"
    | throw (IO.userError "original discarded-prefix declaration did not parse")
  let tail : Core.Expr := .ifE (.var 3) (.var 2) (.var 1)
  let core : Core.Expr := .letE (.var 1) tail
  let some compiled := compileRuntimeFunction? types_variant2 owner_variant4 source
    | throw (IO.userError "valid strict expression prefix did not compile")
  let names : LocalNameTable := [("f", ⟨owner_variant4, 2⟩), ("t", ⟨owner_variant4, 1⟩), ("c", ⟨owner_variant4, 0⟩)]
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = .word ∧
    compiled.inputs.names = names ∧ compiled.inputs.context.values = [.word, .word, .bool] ∧
    elaborateTerminalReturnTree? compiled.inputs.names compiled.inputs.context source.value.body = none ∧
    terminalReturnTreeFuelBound source.value.body = 0 ∧ typedLetReturnTreeFuelBound source.value.body = 7))
    "discard prefix changed parameter-only records or the old adapter boundary"
  match source.value.body.value with
  | [⟨statementSpan, .expression expression true⟩, conditional] =>
      assertTrue (statementSpan.contains expression.span &&
        decide (statementSpan.endByte ≤ conditional.span.startByte)) "discard source order or semicolon changed"
  | _ => throw (IO.userError "original strict prefix AST changed")
  for choice in [false, true] do
    let arguments := [boolArg choice, wordArg 7, wordArg 9]
    let environment := [.word (word 9), .word (word 7), .bool choice]
    let value := Core.Value.word (word (if choice then 7 else 9))
    let some prepared := prepareRuntimeFunction? types_variant2 owner_variant4 source arguments
      | throw (IO.userError "original ordered arguments did not prepare")
    assertTrue (decide (prepared.core = core ∧ prepared.returnType = .word ∧
      prepared.inputs.names = names ∧ prepared.inputs.environment.values = environment ∧
      prepared.inputs.bindings.length = 3)) "discard added a source binding or reordered actual arguments"
    for store in stores do
      have paths (k : List Core.Frame) : Core.Steps 7
          ⟨.eval core environment, k, store⟩ ⟨.ret value, k, store⟩ := by
        cases choice <;>
          exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet
            (.cons .enterIf (.cons (.var rfl)
              (.cons (by first | exact .chooseFalse | exact .chooseTrue) (.cons (.var rfl) .refl))))))
      have _ := paths []
      let run := fun fuel => runRuntimeFunction? types_variant2 owner_variant4 source arguments fuel store
      for fuel in List.range 10 do
        assertTrue (decide (run fuel = some (.word, Core.runStateful fuel (Core.State.initial core environment store)) ∧
          run fuel = prepared.inputs.runTypedLetReturnTree? types_variant2 owner_variant4 fuel source.value.body store))
          "strict prefix entry disagreed with the original Core/body runner"
        assertTrue (match run fuel with
          | some (.word, .done result finalStore) => decide (7 ≤ fuel ∧ result = value ∧ finalStore = store)
          | some (.word, .outOfFuel checkpoint) => decide (fuel < 7 ∧ checkpoint.store = store)
          | _ => false) "discard prefix did not retain its exact seven-step cost"
      assertTrue (decide (run 2 = some (.word, .outOfFuel
        ⟨.ret (.word (word 7)), [.letBody tail environment], store⟩) ∧
        run 3 = some (.word, .outOfFuel ⟨.eval tail (.word (word 7) :: environment), [], store⟩)))
        "discard's hidden Core value or original saved environment changed"
      for spent in List.range 7 do
        let some (.word, .outOfFuel checkpoint) := run spent
          | throw (IO.userError "discard checkpoint disappeared")
        for remaining in List.range (10 - spent) do
          assertTrue (decide (run (spent + remaining) = some (.word, Core.runStateful remaining checkpoint)))
            "discard checkpoint did not resume exactly"

def frontendParsedTerminalRuntimeEntriesTests : IO Unit := do
  discardedPrefix
  let bare ← compile "function bare(){return;}" .unit .unit [] 1
  checkCase bare [] .unit 1
  let units ← compile "function units(c: Bool){if(c){return;}else{return;}}"
    (.ifE (.var 0) .unit .unit) .unit [.bool] 4
  for choice in [false, true] do checkCase units [boolArg choice] .unit 4
  let nested ← compile "function nested(c: Bool,t: Word,f: Word) returns (Word){if(c){if(c){return t;}else{return f;}}else{return f;}}"
    (.ifE (.var 2) (.ifE (.var 2) (.var 1) (.var 0)) (.var 0)) .word [.bool, .word, .word] 7
  for choice in [false, true] do
    checkCase nested [boolArg choice, wordArg 7, wordArg 9] (.word (word (if choice then 7 else 9))) (if choice then 7 else 4)
  let short ← compile "function short(c: Bool,t: Word,f: Word) returns (Word){if(c){return ~t;}else{return f;}}"
    (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word [.bool, .word, .word] 6
  let compare ← compile "function compare(c: Bool,t: Word,f: Word) returns (Bool){if(c){return t < f;}else{return t >= f;}}"
    (.ifE (.var 2) (lt (.var 1) (.var 0)) (.unary .boolNot (lt (.var 1) (.var 0)))) .bool [.bool, .word, .word] 16
  for left in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
    for right in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
      for choice in [false, true] do
        let arguments := [boolArg choice, wordArg left, wordArg right]
        checkCase short arguments (.word (if choice then (word left).bitNot else word right)) (if choice then 6 else 4)
        let less := decide (word left < word right)
        checkCase compare arguments (.bool (if choice then less else !less)) (if choice then 14 else 16)
  for arguments in [[], [boolArg true], [wordArg 7, boolArg false, wordArg 9],
      [boolArg true, wordArg 7, boolArg false], [boolArg true, wordArg 7, wordArg 9, wordArg 1]] do
    rejectArguments short arguments
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cellLeft : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let cellRight : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 91, .cellRef⟩
  let closureLeft : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let closureRight : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, left, right) in [("Word", wordArg 7, wordArg 9), ("Bool", boolArg true, boolArg false),
      ("Unit", unit, unit), ("Cell", cellLeft, cellRight), ("Fn", closureLeft, closureRight)] do
    for body in ["{return c ? t : f;}", "{if(c){return t;}else{return f;}}"] do
      let entry ← compile (s!"function values(c: Bool,t: {name},f: {name}) returns ({name})" ++ body)
        (.ifE (.var 2) (.var 1) (.var 0)) left.type [.bool, left.type, right.type] 4
      for choice in [false, true] do
        checkCase entry [boolArg choice, left, right] (if choice then left.value else right.value) 4
  let nominal ← compile "function nominal(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return x;}}"
    (.ifE (.var 1) (.var 0) (.var 0)) (.namedData ⟨91⟩) [.bool, .namedData ⟨91⟩] 4
  for argument in [unit, wordArg 7, boolArg false, cellLeft, closureLeft] do
    rejectArguments nominal [boolArg true, argument]
  for body in ["{}", "{if(c){return t;}}", "{if(c){return t;}else{return f;}return t;}",
      "{if(c){return t;return f;}else{return f;}}",
      "{if(t){return t;}else{return f;}}",
      "{if(c){return t;}else{return c;}}", "{if(c){return;}else{return f;}}"] do
    reject ("function invalid(c: Bool,t: Word,f: Word) returns (Word)" ++ body)
  for invalid in ["missing", "c", "t + c", "t(c)", s!"{Core.wordModulus}"] do
    reject ("function skipped(c: Bool,t: Word,f: Word) returns (Word){if(c){return t;}else{return " ++ invalid ++ ";}}")
    reject ("function skipped(c: Bool,t: Word,f: Word) returns (Word){if(c){return " ++ invalid ++ ";}else{return f;}}")
  for header in ["function wrong(c: Bool)", "function wrong(c: Bool) returns (Bool)",
      "function wrong(c: Bool) returns ()", "function wrong(c: Bool) returns (Word,Bool)",
      "function wrong(c: Bool) returns (Unknown)", "function wrong<T>(c: Bool) returns (Word)",
      "function wrong(c: Bool) returns (Word) where Word: Eq", "function wrong(c: Bool,c: Bool) returns (Word)",
      "function wrong(comptime c: Bool) returns (Word)", "function wrong(c: Unknown) returns (Word)"] do
    reject (header ++ "{if(c){return 7;}else{return 9;}}")
  reject "function wrong(c: Bool) public returns (Word){if(c){return 7;}else{return 9;}}" .contract
  for content in ["", "function f(c: Bool)", "function f(c: Bool){if(c){return;}else{return;}",
      "function f(c: Bool){if(c){return}else{return;}}", "function f(c: Bool){if(c){return;}else{return;}} trailing"] do
    assertTrue (← parsed_variant3? content).isNone "malformed or partially consumed declaration accepted"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendTerminalBlockProperties
/-! Original terminal wrappers have no hidden binder or machine transition.
Independent mixed bodies separate static types, raw values and genuine states. -/
set_option autoImplicit false
namespace Tests.FrontendTerminalBlock
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TerminalBlock", by decide⟩], by decide⟩⟩, 0⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 9 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "terminal-block.sol"⟩, 23, 4⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def wrap (outer : Syntax.SourceSpan) (body : Syntax.Block) : Syntax.Block :=
  ⟨outer, [⟨body.span, .block body.value⟩]⟩
private def nested : List Syntax.SourceSpan → Syntax.Block → Syntax.Block
  | [], body => body
  | outer :: rest, body => wrap outer (nested rest body)
private theorem wrapped {types : TypeNameTable} {own : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (evidence : TypedLetReturnTreeElaborates types own inputs body core type) (spans : List Syntax.SourceSpan) :
    TypedLetReturnTreeElaborates types own inputs (nested spans body) core type := by
  induction spans with
  | nil => exact evidence
  | cons outer rest ih => exact .block ih
private theorem replay {own : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initial final : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evidence : TypedLetReturnTreeEvaluatesWithCost own table environment initial body value final cost)
    (spans : List Syntax.SourceSpan) :
    TypedLetReturnTreeEvaluatesWithCost own table environment initial (nested spans body) value final cost := by
  induction spans with
  | nil => exact evidence
  | cons outer rest ih => exact .block ih
private theorem checked (types : TypeNameTable) (own : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (spans : List Syntax.SourceSpan) (body : Syntax.Block) :
    elaborateTypedLetReturnTree? types own inputs (nested spans body) = elaborateTypedLetReturnTree? types own inputs body := by
  induction spans with
  | nil => rfl
  | cons outer rest ih => exact (elaborateTypedLetReturnTree?_block types own inputs outer _ _).trans ih
private theorem runs (inputs : LocalInputs) (types : TypeNameTable) (own : Resolved.DeclarationId)
    (spans : List Syntax.SourceSpan) (body : Syntax.Block) (fuel : Nat) (store : Core.Store) :
    inputs.runTypedLetReturnTree? types own fuel (nested spans body) store = inputs.runTypedLetReturnTree? types own fuel body store := by
  simp only [LocalInputs.runTypedLetReturnTree?, LocalInputs.checkTypedLetReturnTree?, checked]
private def static (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"seed", id 7, type⟩, ⟨"c", ⟨other, 99⟩, .bool⟩, ⟨"seed", id 2, type⟩], by change [id 7, ⟨other, 99⟩, id 2].Nodup; decide⟩
private def values (value shadow : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(id 7, value), (⟨other, 99⟩, .bool choice), (id 2, shadow)]
private def actual (type : Core.Ty) (value shadow : Core.Value) (choice : Bool)
    (typed : Core.ValueHasType value type) (shadowTyped : Core.ValueHasType shadow type) : LocalInputs :=
  ⟨[⟨"seed", id 7, type, value, typed⟩, ⟨"c", ⟨other, 99⟩, .bool, .bool choice, .bool⟩,
    ⟨"seed", id 2, type, shadow, shadowTyped⟩], by change [id 7, ⟨other, 99⟩, id 2].Nodup; decide⟩
private def branch : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") (returned "x") (some (returned "x"))⟩]⟩
private def mixed : Syntax.Block := ⟨span,
  ⟨span, .letDecl ⟨span, "x"⟩ none (some (ref "seed"))⟩ :: ⟨span, .expression (ref "x") true⟩ :: branch.value⟩
private def branchCore : Core.Expr := .ifE (.var 3) (.var 1) (.var 1)
private def core : Core.Expr := .letE (.var 0) (.letE (.var 0) branchCore)
private theorem elaborated (types : TypeNameTable) (type : Core.Ty) :
    TypedLetReturnTreeElaborates types owner (static type) mixed core type := by
  have leaf : ReturnBodyElaborates ((static type).bindFresh owner "x" type).names
      ((static type).bindFresh owner "x" type).context (returned "x") (.var 0) type :=
    .expression (.identifier .head) (.var .head) (.var .head)
  have conditional : TypedLetReturnTreeElaborates types owner ((static type).bindFresh owner "x" type)
      branch (.ifE (.var 2) (.var 0) (.var 0)) type :=
    .conditional (.identifier (.tail (by change "x" ≠ "c"; decide) (.tail (by change "seed" ≠ "c"; decide) .head)))
      (.var (.tail (by change id 8 ≠ ⟨other, 99⟩; decide) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head)))
      (.var (.tail (by change id 8 ≠ ⟨other, 99⟩; decide) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head)))
      (.single leaf) (.single leaf)
  have tail := TypedLetReturnTreeElaborates.discard (inputs := (static type).bindFresh owner "x" type)
    (blockSpan := span) (statementSpan := span) (expression := ref "x") (rest := branch.value)
    (.identifier .head) (.var .head) (.var .head) conditional
  simpa [mixed, core, branchCore, Core.Expr.weakenAt] using
    (TypedLetReturnTreeElaborates.inferred (inputs := static type) (name := ⟨span, "x"⟩)
      (initializer := ref "seed") (letSpan := span) (by change "x" ∉ ["seed", "c", "seed"]; decide)
      (.identifier .head) (.var .head) (.var .head) tail)
private theorem counted (type : Core.Ty) (value shadow : Core.Value) (choice : Bool) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (static type).names (values value shadow choice) store mixed value store 10 := by
  apply TypedLetReturnTreeEvaluatesWithCost.inferred (owner := owner) (table := (static type).names)
    (environment := values value shadow choice) (initializer := ref "seed") (name := ⟨span, "x"⟩)
    (blockSpan := span) (letSpan := span) (initializerCost := 1) (tailCost := 7) (.identifier .head .head)
  apply TypedLetReturnTreeEvaluatesWithCost.discard (expression := ref "x") (expressionCost := 1) (tailCost := 4) (.identifier .head .head)
  have guard : LocalExpressionEvaluatesWithCost (("x", id 8) :: (static type).names)
      ((id 8, value) :: values value shadow choice) store (ref "c") (.bool choice) store 1 :=
    .identifier (.tail (by change "x" ≠ "c"; decide) (.tail (by change "seed" ≠ "c"; decide) .head))
      (.tail (by change id 8 ≠ ⟨other, 99⟩; decide) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head))
  cases choice
  · exact .ifFalse guard (.single (.expression (.identifier .head .head)))
  · exact .ifTrue guard (.single (.expression (.identifier .head .head)))
private theorem path (value shadow : Core.Value) (choice : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 10 ⟨.eval core [value, .bool choice, shadow], k, store⟩ ⟨.ret value, k, store⟩ := by
  apply CostStepComposition.letE (valueCost := 1) (bodyCost := 7) (.cons (.var rfl) .refl)
  apply CostStepComposition.letE (valueCost := 1) (bodyCost := 4) (.cons (.var rfl) .refl)
  cases choice
  · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
  · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)

theorem arbitrary_original_ranges_keep_value_free_mixed_provenance
    (spans : List Syntax.SourceSpan) (types : TypeNameTable) (type : Core.Ty) (definitions : Core.DataEnvironment) :
    TypedLetReturnTreeElaborates types owner (static type) (nested spans mixed) core type ∧
    TypedLetReturnTreeHasType types owner (static type) (nested spans mixed) type ∧
    Core.HasType [type, .bool, type] core type definitions ∧
    Resolved.freshLocalId owner (static type).ids = id 8 ∧ ¬ ((static type).names.map Prod.fst).Nodup :=
  ⟨wrapped (elaborated types type) spans, (wrapped (elaborated types type) spans).hasType,
    .letE (.var rfl) (.letE (.var rfl) (.ifE (.var rfl) (.var rfl) (.var rfl))), rfl,
    by change ¬ ["seed", "c", "seed"].Nodup; decide⟩

theorem raw_values_and_every_continuation_keep_exactly_ten_steps
    (spans : List Syntax.SourceSpan) (type : Core.Ty) (value shadow : Core.Value) (choice : Bool)
    (store : Core.Store) (k : List Core.Frame) :
    TypedLetReturnTreeEvaluatesWithCost owner (static type).names (values value shadow choice) store (nested spans mixed) value store 10 ∧
    evaluateTypedLetReturnTreeWithCost? owner (static type).names (values value shadow choice) (nested spans mixed) = some (value, 10) ∧
    Core.Steps 10 ⟨.eval core [value, .bool choice, shadow], k, store⟩ ⟨.ret value, k, store⟩ ∧
    Core.Evaluates [value, .bool choice, shadow] store core value store :=
  ⟨replay (counted type value shadow choice store) spans,
    evaluateTypedLetReturnTreeWithCost?_complete (replay (counted type value shadow choice store) spans), path value shadow choice store k,
    (elaborateTypedLetReturnTree?_evaluates_iff (wrapped (elaborated [] type) spans).complete rfl).mp
      (replay (counted type value shadow choice store) spans).erase⟩

theorem whole_option_and_actual_full_states_are_equal_not_just_values
    (spans : List Syntax.SourceSpan) (types : TypeNameTable) (own : Resolved.DeclarationId)
    (inputs : LocalInputs) (body : Syntax.Block) (fuel : Nat) (store : Core.Store) :
    elaborateTypedLetReturnTree? types own inputs.toTypeInputs (nested spans body) = elaborateTypedLetReturnTree? types own inputs.toTypeInputs body ∧
    inputs.runTypedLetReturnTree? types own fuel (nested spans body) store = inputs.runTypedLetReturnTree? types own fuel body store :=
  ⟨checked types own inputs.toTypeInputs spans body, runs inputs types own spans body fuel store⟩

theorem actual_typed_callers_have_exact_thresholds (spans : List Syntax.SourceSpan) (type : Core.Ty)
    (value shadow : Core.Value) (choice : Bool) (typed : Core.ValueHasType value type)
    (shadowTyped : Core.ValueHasType shadow type) (store : Core.Store) (fuel : Nat) :
    (actual type value shadow choice typed shadowTyped).runTypedLetReturnTree? [] owner fuel (nested spans mixed) store =
      some (type, Core.runStateful fuel (Core.State.initial core [value, .bool choice, shadow] store)) ∧
    (Core.runStateful fuel (Core.State.initial core [value, .bool choice, shadow] store) = .done value store ↔ 10 ≤ fuel) :=
  ⟨LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (wrapped (elaborated [] type) spans).complete, rfl⟩,
    (path value shadow choice store []).runStateful_done_iff⟩

private def checkpoint (value shadow : Core.Value) (choice : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody branchCore [value, value, .bool choice, shadow]], store⟩
private def early (value shadow : Core.Value) (choice : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (.letE (.var 0) branchCore) [value, .bool choice, shadow]], store⟩
theorem wrappers_preserve_the_actual_pre_binding_checkpoint (spans : List Syntax.SourceSpan)
    (word shadow : Core.Word) (choice : Bool) (store : Core.Store) :
    (actual .word (.word word) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner 2 mixed store =
      some (.word, .outOfFuel (early (.word word) (.word shadow) choice store)) ∧
    (actual .word (.word word) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner 2 (nested spans mixed) store =
      some (.word, .outOfFuel (early (.word word) (.word shadow) choice store)) := by
  have original : (actual .word (.word word) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner 2 mixed store =
      some (.word, .outOfFuel (early (.word word) (.word shadow) choice store)) :=
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (elaborated [] .word).complete, rfl⟩
  exact ⟨original, (runs _ [] owner spans mixed 2 store).trans original⟩

theorem identical_saved_states_resume_without_restarting (spans : List Syntax.SourceSpan)
    (value shadow : Core.Word) (choice : Bool) (store : Core.Store) (additional : Nat) :
    (actual .word (.word value) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner 5 (nested spans mixed) store =
      some (.word, .outOfFuel (checkpoint (.word value) (.word shadow) choice store)) ∧
    Core.Steps 5 (checkpoint (.word value) (.word shadow) choice store) (Core.State.final (.word value) store) ∧
    (actual .word (.word value) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner (5 + additional) (nested spans mixed) store =
      some (.word, Core.runStateful additional (checkpoint (.word value) (.word shadow) choice store)) := by
  have stopped : (actual .word (.word value) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner 5 (nested spans mixed) store =
      some (.word, .outOfFuel (checkpoint (.word value) (.word shadow) choice store)) :=
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (wrapped (elaborated [] .word) spans).complete, rfl⟩
  exact ⟨stopped, ((path (.word value) (.word shadow) choice store []).residual_of_outOfFuel (spent := 5) rfl).2,
    LocalInputs.runTypedLetReturnTree?_resume stopped additional⟩

theorem nominal_static_acceptance_is_not_actual_inhabitation (spans : List Syntax.SourceSpan) (nominal : Core.DataTypeId) :
    elaborateTypedLetReturnTree? [] owner (static (.namedData nominal)) (nested spans mixed) = some (core, .namedData nominal) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(wrapped (elaborated [] _) spans).complete, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem opaque_cells_and_closures_need_no_dereference (location : Core.Location) (word : Core.Word)
    (spans : List Syntax.SourceSpan) (store : Core.Store) :
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    Core.ValueHasType (.closure .bool .word (.var 1) [.word word]) (.function .bool .word) ∧
    TypedLetReturnTreeEvaluatesWithCost owner (static (.cell .word)).names (values (.cellRef .word location) .unit true)
      store (nested spans mixed) (.cellRef .word location) store 10 ∧
    Core.Steps 10 ⟨.eval core [.closure .bool .word (.var 1) [.word word], .bool false, .unit], [], store⟩
      (Core.State.final (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨.cellRef, .closure (.cons .word .nil) (.var rfl), replay (counted _ _ _ true store) spans, path _ _ false store []⟩

theorem opaque_actual_inputs_complete_without_accessing_stored_contents
    (location : Core.Location) (word : Core.Word) (spans : List Syntax.SourceSpan) (store : Core.Store) :
    (actual (.cell .word) (.cellRef .word location) (.cellRef .word location) true .cellRef .cellRef).runTypedLetReturnTree?
      [] owner 10 (nested spans mixed) store = some (.cell .word, .done (.cellRef .word location) store) ∧
    (actual (.function .bool .word) (.closure .bool .word (.var 1) [.word word]) (.closure .bool .word (.var 1) [.word word]) false
      (.closure (.cons .word .nil) (.var rfl)) (.closure (.cons .word .nil) (.var rfl))).runTypedLetReturnTree?
      [] owner 10 (nested spans mixed) store = some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (wrapped (elaborated [] _) spans).complete, rfl⟩,
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (wrapped (elaborated [] _) spans).complete, rfl⟩⟩

theorem same_typed_replacement_is_not_original_provenance (spans : List Syntax.SourceSpan) (type : Core.Ty) :
    Core.HasType [type, .bool, type] (.var 2) type ∧
    ¬ TypedLetReturnTreeElaborates [] owner (static type) (nested spans mixed) (.var 2) type := by
  refine ⟨.var rfl, ?_⟩
  intro competing
  cases (competing.result_unique (wrapped (elaborated [] type) spans)).1

theorem owner_type_store_and_raw_lookup_transport_remain_distinct
    (spans : List Syntax.SourceSpan) (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (word shadow : Core.Word) (choice : Bool) (store replacement : Core.Store) (fuel : Nat) (extras : TypeNameTable)
    (rightOwner : Resolved.DeclarationId) (table : LocalNameTable) (environment : Resolved.Environment)
    (agreement : ∀ name, ((static .word).names.lookup? name).bind (values (.word word) (.word shadow) choice).lookup? =
      (table.lookup? name).bind environment.lookup?) :
    ((actual .word (.word word) (.word shadow) choice .word .word).mapIds (ownerLocalIdMap mapping)
      (ownerLocalIdMap_injective mapping injective)).runTypedLetReturnTree? [] (mapping owner) fuel (nested spans mixed) store =
      (actual .word (.word word) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner fuel (nested spans mixed) store ∧
    elaborateTypedLetReturnTree? extras owner (static .word) (nested spans mixed) = some (core, .word) ∧
    TypedLetReturnTreeEvaluatesWithCost rightOwner table environment replacement (nested spans mixed) (.word word) replacement 10 := by
  exact ⟨LocalInputs.runTypedLetReturnTree?_mapOwner _ mapping injective [] owner fuel _ store,
    elaborateTypedLetReturnTree?_some_of_extends (TypeNameTable.Extends.append_right [] extras)
      (wrapped (elaborated [] .word) spans).complete,
    (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff agreement).mp
      ((replay (counted .word (.word word) (.word shadow) choice store) spans).change_store replacement)⟩

theorem terminal_shape_does_not_enable_nonterminal_blocks_or_empty_returns
    (outer inner : Syntax.SourceSpan) (spans : List Syntax.SourceSpan) :
    elaborateTypedLetReturnTree? [] owner (static .word) (nested spans ⟨inner, []⟩) = none ∧
    elaborateTypedLetReturnTree? [] owner (static .word) ⟨outer, ⟨inner, .block mixed.value⟩ :: (returned "x").value⟩ = none ∧
    elaborateTypedLetReturnBody? [] owner (static .word) (wrap outer mixed) = none ∧
    (wrap outer ⟨inner, mixed.value⟩).value = [⟨inner, .block mixed.value⟩] := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [checked]; simp only [elaborateTypedLetReturnTree?]
  · simp only [returned, elaborateTypedLetReturnTree?]
  · simp only [wrap, mixed, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?]

private def badBranch : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") (returned "seed") (some (returned "missing"))⟩]⟩
theorem unselected_missing_is_raw_success_but_not_whole_success (spans : List Syntax.SourceSpan)
    (value shadow : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluates owner (static .word).names (values value shadow true) store (nested spans badBranch) value store ∧
    elaborateTypedLetReturnTree? [] owner (static .word) (nested spans badBranch) = none := by
  have raw : TypedLetReturnTreeEvaluatesWithCost owner (static .word).names (values value shadow true) store badBranch value store 4 :=
    .ifTrue (condition := ref "c") (conditionCost := 1) (branchCost := 1)
      (.identifier (.tail (by change "seed" ≠ "c"; decide) .head) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head))
      (.single (.expression (.identifier .head .head)))
  refine ⟨(replay raw spans).erase, ?_⟩
  rw [checked]
  apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
  rintro ⟨_, typing⟩
  cases typing with
  | single child => cases child
  | conditional _ _ other =>
      cases other with
      | single child => cases child with
        | expression expression => cases expression with
          | identifier named _ =>
              have impossible := LocalNameTable.lookup?_iff.mpr named
              change none = some _ at impossible
              cases impossible

theorem wrapping_does_not_reset_scope_or_allow_shadowing (spans : List Syntax.SourceSpan) :
    elaborateTypedLetReturnTree? [] owner (static .word) (nested spans (returned "x")) = none ∧
    elaborateTypedLetReturnTree? [] owner (static .word)
      (nested spans ⟨span, ⟨span, .letDecl ⟨span, "seed"⟩ none (some (ref "seed"))⟩ :: (returned "seed").value⟩) = none := by
  constructor
  · rw [checked]
    simp [returned, ref, elaborateTypedLetReturnTree?, elaborateReturnBody?, elaborateLocalExpression?,
      resolveLocalExpression?, static, LocalTypeInputs.names, LocalNameTable.lookup?]
  · rw [checked]
    simp [elaborateTypedLetReturnTree?, static, LocalTypeInputs.names]

end Tests.FrontendTerminalBlock
end

section
-- leanmerge: from Solcore.Test.FrontendTerminalBodyInvarianceProperties
/-! Identity transport preserves whole suspended states, whereas store replay
preserves observations carrying their own stores. Merging IDs is explicitly
excluded and can change both the selected Bool and its exact cost. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalBodyInvariance

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "body-invariance.sol"⟩, 5, 23⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"BodyInvariance", by decide⟩], by decide⟩⟩, 0⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩
private def single := returned (ref "v")
private def body : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") single
  (some (returned ⟨span, .unary ⟨span, .logicalNot⟩ (ref "v")⟩))⟩]⟩
private def inputs (choice flag : Bool) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh owner "v" .bool (.bool flag) .bool
private def core : Core.Expr := .ifE (.var 1) (.var 0) (.unary .boolNot (.var 0))
private theorem names_ne : "v" ≠ "c" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private def required (choice : Bool) := if choice then 4 else 6
private def result (choice flag : Bool) : Core.Value := .bool (if choice then flag else !flag)
private theorem singleElab (choice flag : Bool) :
    ReturnBodyElaborates (inputs choice flag).names (inputs choice flag).context single (.var 0) .bool :=
  .expression (.identifier .head) (.var .head) (.var .head)
private theorem elaborated (choice flag : Bool) :
    ConditionalReturnBodyElaborates (inputs choice flag).names (inputs choice flag).context body core .bool :=
  .intro (.identifier (.tail names_ne .head)) (.var (.tail ids_ne .head)) (.var (.tail ids_ne .head))
    (singleElab choice flag) (.expression (.logicalNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))
private theorem terminalElab (choice flag : Bool) :
    TerminalReturnBodyElaborates (inputs choice flag).names (inputs choice flag).context body core .bool :=
  .conditional (elaborated choice flag)
private theorem checked (choice flag : Bool) :
    (inputs choice flag).checkTerminalReturnBody? body = some (core, .bool) := (terminalElab choice flag).complete
private theorem conditionCost (choice flag : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      store (ref "c") (.bool choice) store 1 := .identifier (.tail names_ne .head) (.tail ids_ne .head)
private theorem valueCost (choice flag : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      store (ref "v") (.bool flag) store 1 := .identifier .head .head
private theorem costed (choice flag : Bool) (store : Core.Store) :
    ConditionalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      store body (result choice flag) store (required choice) := by
  cases choice
  · exact .ifFalse (conditionCost false flag store) (.expression (.logicalNot (valueCost false flag store)))
  · exact .ifTrue (conditionCost true flag store) (.expression (valueCost true flag store))

theorem injective_elaboration_transport_retains_exact_core_for_all_three_profiles
    (choice flag : Bool) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    ReturnBodyElaborates (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) single (.var 0) .bool ∧
    ConditionalReturnBodyElaborates (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) body core .bool ∧
    TerminalReturnBodyElaborates (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) body core .bool :=
  ⟨(singleElab choice flag).mapIds mapping injective, (elaborated choice flag).mapIds mapping injective,
    (terminalElab choice flag).mapIds mapping injective⟩

theorem injective_checkers_and_entire_same_fuel_results_agree
    (choice flag : Bool) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (fuel : Nat) (store : Core.Store) :
    ((inputs choice flag).mapIds mapping injective).checkConditionalReturnBody? body = some (core, .bool) ∧
    ((inputs choice flag).mapIds mapping injective).checkTerminalReturnBody? body = some (core, .bool) ∧
    ((inputs choice flag).mapIds mapping injective).runConditionalReturnBody? fuel body store =
      (inputs choice flag).runConditionalReturnBody? fuel body store ∧
    ((inputs choice flag).mapIds mapping injective).runTerminalReturnBody? fuel body store =
      (inputs choice flag).runTerminalReturnBody? fuel body store :=
  ⟨((inputs choice flag).checkConditionalReturnBody?_mapIds mapping injective body).trans (elaborated choice flag).complete,
    ((inputs choice flag).checkTerminalReturnBody?_mapIds mapping injective body).trans (checked choice flag),
    (inputs choice flag).runConditionalReturnBody?_mapIds mapping injective fuel body store,
    (inputs choice flag).runTerminalReturnBody?_mapIds mapping injective fuel body store⟩

theorem optional_component_checkers_retain_exact_successful_core
    (choice flag : Bool) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    elaborateReturnBody? (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) single = some (.var 0, .bool) ∧
    elaborateConditionalReturnBody? (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) body = some (core, .bool) ∧
    elaborateTerminalReturnBody? (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) body = some (core, .bool) :=
  ⟨(elaborateReturnBody?_mapIds mapping injective _ _ _).trans (singleElab choice flag).complete,
    (elaborateConditionalReturnBody?_mapIds mapping injective _ _ _).trans (elaborated choice flag).complete,
    (elaborateTerminalReturnBody?_mapIds mapping injective _ _ _).trans (terminalElab choice flag).complete⟩

private def shifted (id : Resolved.LocalId) : Resolved.LocalId := ⟨id.owner, id.binderIndex + 7⟩
private theorem shiftedInjective : Function.Injective shifted := by
  intro ⟨leftOwner, leftIndex⟩ ⟨rightOwner, rightIndex⟩ same
  simp only [shifted, Resolved.LocalId.mk.injEq] at same
  obtain ⟨rfl, indexes⟩ := same
  cases Nat.add_right_cancel indexes
  rfl
private def checkpoint (choice flag : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.var 0) (.unary .boolNot (.var 0)) [.bool flag, .bool choice]], store⟩
private theorem exhausted (choice flag : Bool) (store : Core.Store) :
    (inputs choice flag).runTerminalReturnBody? 2 body store = some (.bool, .outOfFuel (checkpoint choice flag store)) := by
  rw [LocalInputs.runTerminalReturnBody?, checked]; cases choice <;> rfl

theorem nontrivial_identity_shift_preserves_the_actual_whole_checkpoint
    (choice flag : Bool) (store : Core.Store) :
    shifted ⟨owner, 0⟩ ≠ ⟨owner, 0⟩ ∧
    ((inputs choice flag).mapIds shifted shiftedInjective).runTerminalReturnBody? 2 body store =
      some (.bool, .outOfFuel (checkpoint choice flag store)) :=
  ⟨by decide, ((inputs choice flag).runTerminalReturnBody?_mapIds shifted shiftedInjective 2 body store).trans
    (exhausted choice flag store)⟩

theorem singleton_actual_typed_values_replay_through_the_old_store_api_and_terminal_wrapper
    (type : Core.Ty) (value : Core.Value) (valueTyped : Core.ValueHasType value type)
    (first replacement : Core.Store) :
    let supplied := LocalInputs.empty.bindFresh owner "v" type value valueTyped
    ReturnBodyEvaluates supplied.names supplied.environment replacement single value replacement ∧
    ReturnBodyEvaluatesWithCost supplied.names supplied.environment replacement single value replacement 1 ∧
    TerminalReturnBodyEvaluates supplied.names supplied.environment replacement single value replacement ∧
    TerminalReturnBodyEvaluatesWithCost supplied.names supplied.environment replacement single value replacement 1 := by
  intro supplied
  have original : ReturnBodyEvaluatesWithCost supplied.names supplied.environment first single value first 1 :=
    .expression (.identifier .head .head)
  have common : TerminalReturnBodyEvaluatesWithCost supplied.names supplied.environment first single value first 1 := .single original
  exact ⟨original.erase.change_store replacement, original.change_store replacement,
    common.erase.change_store replacement, common.change_store replacement⟩

theorem conditional_raw_and_exact_cost_replay_keep_the_selected_bool_and_cost
    (choice flag : Bool) (first replacement : Core.Store) :
    ConditionalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment
      replacement body (result choice flag) replacement ∧
    ConditionalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      replacement body (result choice flag) replacement (required choice) ∧
    TerminalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment
      replacement body (result choice flag) replacement ∧
    TerminalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      replacement body (result choice flag) replacement (required choice) := by
  have original := costed choice flag first
  have common : TerminalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      first body (result choice flag) first (required choice) := .conditional original
  exact ⟨original.erase.change_store replacement, original.change_store replacement,
    common.erase.change_store replacement, common.change_store replacement⟩

theorem replay_equivalences_preserve_initial_final_store_equality
    (choice flag : Bool) (initialStore finalStore replacement : Core.Store) :
    (ReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment initialStore single (.bool flag) finalStore ↔
      finalStore = initialStore ∧ ReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment
        replacement single (.bool flag) replacement) ∧
    (ReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment initialStore single (.bool flag) finalStore 1 ↔
      finalStore = initialStore ∧ ReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
        replacement single (.bool flag) replacement 1) ∧
    (ConditionalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment initialStore body (result choice flag) finalStore ↔
      finalStore = initialStore ∧ ConditionalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment
        replacement body (result choice flag) replacement) ∧
    (ConditionalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      initialStore body (result choice flag) finalStore (required choice) ↔
      finalStore = initialStore ∧ ConditionalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
        replacement body (result choice flag) replacement (required choice)) ∧
    (TerminalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment initialStore body (result choice flag) finalStore ↔
      finalStore = initialStore ∧ TerminalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment
        replacement body (result choice flag) replacement) ∧
    (TerminalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      initialStore body (result choice flag) finalStore (required choice) ↔
      finalStore = initialStore ∧ TerminalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
        replacement body (result choice flag) replacement (required choice)) :=
  ⟨returnBodyEvaluates_store_iff, returnBodyEvaluatesWithCost_store_iff,
    conditionalReturnBodyEvaluates_store_iff, conditionalReturnBodyEvaluatesWithCost_store_iff,
    terminalReturnBodyEvaluates_store_iff, terminalReturnBodyEvaluatesWithCost_store_iff⟩

theorem completion_and_exhaustion_presence_agree_without_equating_stored_states
    (choice flag : Bool) (fuel : Nat) (first replacement : Core.Store) :
    ((inputs choice flag).runConditionalReturnBody? fuel body first = some (.bool, .done (result choice flag) first) ↔
      (inputs choice flag).runConditionalReturnBody? fuel body replacement = some (.bool, .done (result choice flag) replacement)) ∧
    ((∃ checkpoint, (inputs choice flag).runConditionalReturnBody? fuel body first = some (.bool, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, (inputs choice flag).runConditionalReturnBody? fuel body replacement = some (.bool, .outOfFuel checkpoint)) ∧
    ((inputs choice flag).runTerminalReturnBody? fuel body first = some (.bool, .done (result choice flag) first) ↔
      (inputs choice flag).runTerminalReturnBody? fuel body replacement = some (.bool, .done (result choice flag) replacement)) ∧
    ((∃ checkpoint, (inputs choice flag).runTerminalReturnBody? fuel body first = some (.bool, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, (inputs choice flag).runTerminalReturnBody? fuel body replacement = some (.bool, .outOfFuel checkpoint)) :=
  ⟨(inputs choice flag).runConditionalReturnBody?_done_store_iff fuel body first replacement .bool (result choice flag),
    (inputs choice flag).runConditionalReturnBody?_outOfFuel_store_iff fuel body first replacement .bool,
    (inputs choice flag).runTerminalReturnBody?_done_store_iff fuel body first replacement .bool (result choice flag),
    (inputs choice flag).runTerminalReturnBody?_outOfFuel_store_iff fuel body first replacement .bool⟩

theorem differing_nonempty_stores_change_full_checkpoints_even_when_fuel_agrees
    (choice flag : Bool) (tail : Core.Store) :
    (inputs choice flag).runTerminalReturnBody? 2 body (.unit :: tail) =
      some (.bool, .outOfFuel (checkpoint choice flag (.unit :: tail))) ∧
    (inputs choice flag).runTerminalReturnBody? 2 body (.bool true :: tail) =
      some (.bool, .outOfFuel (checkpoint choice flag (.bool true :: tail))) ∧
    (inputs choice flag).runTerminalReturnBody? 2 body (.unit :: tail) ≠
      (inputs choice flag).runTerminalReturnBody? 2 body (.bool true :: tail) := by
  refine ⟨exhausted choice flag _, exhausted choice flag _, ?_⟩
  rw [exhausted, exhausted]
  intro same
  have stored := congrArg (fun state : Core.State => state.store)
    (Core.StatefulRunResult.outOfFuel.inj (Prod.mk.inj (Option.some.inj same)).2)
  cases stored

private def missingArm : Syntax.Block :=
  ⟨span, [⟨span, .ifThen (ref "c") single (some (returned (ref "missing")))⟩]⟩

theorem invalid_unselected_arm_remains_absent_under_identity_and_store_changes
    (flag : Bool) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (fuel : Nat) (first replacement : Core.Store) :
    ConditionalReturnBodyEvaluatesWithCost (inputs true flag).names (inputs true flag).environment
      first missingArm (.bool flag) first 4 ∧
    (inputs true flag).checkTerminalReturnBody? missingArm = none ∧
    ((inputs true flag).mapIds mapping injective).checkConditionalReturnBody? missingArm = none ∧
    ((inputs true flag).mapIds mapping injective).runTerminalReturnBody? fuel missingArm replacement = none := by
  have rejected : (inputs true flag).checkTerminalReturnBody? missingArm = none := by
    simp [LocalInputs.checkTerminalReturnBody?, elaborateTerminalReturnBody?, elaborateConditionalReturnBody?,
      missingArm, single, returned, ref, elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?,
      inputs, LocalInputs.names, LocalInputs.context, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  have absent : (inputs true flag).runTerminalReturnBody? fuel missingArm replacement = none := by
    simp only [LocalInputs.runTerminalReturnBody?, rejected, bind, Option.bind_none]
  exact ⟨.ifTrue (conditionCost true flag first) (.expression (valueCost true flag first)), rejected,
    ((inputs true flag).checkConditionalReturnBody?_mapIds mapping injective missingArm).trans rejected,
    ((inputs true flag).runTerminalReturnBody?_mapIds mapping injective fuel missingArm replacement).trans absent⟩

private def collapse (_ : Resolved.LocalId) : Resolved.LocalId := ⟨owner, 0⟩

theorem merging_two_bool_ids_changes_first_lookup_selected_value_and_cost
    (store : Core.Store) :
    ¬ Function.Injective collapse ∧
    ConditionalReturnBodyEvaluatesWithCost (inputs false true).names (inputs false true).environment store body (.bool false) store 6 ∧
    ConditionalReturnBodyEvaluatesWithCost (LocalNameTable.mapIds collapse (inputs false true).names)
      (Resolved.LocalScope.mapIds collapse (inputs false true).environment) store body (.bool true) store 4 ∧
    elaborateConditionalReturnBody? (LocalNameTable.mapIds collapse (inputs false true).names)
      (Resolved.LocalScope.mapIds collapse (inputs false true).context) body =
        some (.ifE (.var 0) (.var 0) (.unary .boolNot (.var 0)), .bool) := by
  have condition : LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds collapse (inputs false true).names)
      (Resolved.LocalScope.mapIds collapse (inputs false true).environment) store (ref "c") (.bool true) store 1 :=
    .identifier (.tail names_ne .head) .head
  have value : ReturnBodyEvaluatesWithCost (LocalNameTable.mapIds collapse (inputs false true).names)
      (Resolved.LocalScope.mapIds collapse (inputs false true).environment) store single (.bool true) store 1 :=
    .expression (.identifier .head .head)
  have mapped : ConditionalReturnBodyElaborates (LocalNameTable.mapIds collapse (inputs false true).names)
      (Resolved.LocalScope.mapIds collapse (inputs false true).context) body
      (.ifE (.var 0) (.var 0) (.unary .boolNot (.var 0))) .bool :=
    .intro (.identifier (.tail names_ne .head)) (.var .head) (.var .head)
      (.expression (.identifier .head) (.var .head) (.var .head))
      (.expression (.logicalNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))
  refine ⟨?_, costed false true store, .ifTrue condition value, mapped.complete⟩
  intro injective
  exact ids_ne (injective (a₁ := ⟨owner, 1⟩) (a₂ := ⟨owner, 0⟩) rfl)

end Tests.FrontendTerminalBodyInvariance
end

section
-- leanmerge: from Solcore.Test.FrontendTerminalReturnBodyProperties
/-! The nonrecursive union preserves each original profile's full observations.
Independent fixtures retain actual inputs and do not turn conditional arms into
recursive terminal bodies or accept function entries with ill-scoped bodies. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalReturnBody

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "terminal-union.sol"⟩, 29, 8⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TerminalUnion", by decide⟩], by decide⟩⟩, 0⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (value : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt value⟩]⟩
private def branch (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") yes (some no)⟩]⟩
private def complement : Syntax.Expr := ⟨span, .unary ⟨span, .bitNot⟩ (ref "w")⟩
private def conditional := branch (returned (some complement)) (returned (some (ref "w")))
private def core : Core.Expr := .ifE (.var 1) (.unary .wordNot (.var 0)) (.var 0)
private def inputs (choice : Bool) (word : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh owner "w" .word (.word word) .word
private theorem names_ne : "w" ≠ "c" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private def required (choice : Bool) : Nat := if choice then 6 else 4
private def result (choice : Bool) (word : Core.Word) : Core.Value := .word (if choice then word.bitNot else word)
private theorem conditionCost (choice : Bool) (word : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store (ref "c") (.bool choice) store 1 := .identifier (.tail names_ne .head) (.tail ids_ne .head)
private theorem valueCost (choice : Bool) (word : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store (ref "w") (.word word) store 1 := .identifier .head .head
private theorem conditionalTyped (choice : Bool) (word : Core.Word) :
    ConditionalReturnBodyHasType (inputs choice word).names (inputs choice word).context conditional .word :=
  .intro (.identifier (.tail names_ne .head) (.tail ids_ne .head))
    (.expression (.bitNot (.identifier .head .head))) (.expression (.identifier .head .head))
private theorem conditionalElaborated (choice : Bool) (word : Core.Word) :
    ConditionalReturnBodyElaborates (inputs choice word).names (inputs choice word).context conditional core .word :=
  .intro (.identifier (.tail names_ne .head)) (.var (.tail ids_ne .head)) (.var (.tail ids_ne .head))
    (.expression (.bitNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))
    (.expression (.identifier .head) (.var .head) (.var .head))
private theorem conditionalCost (choice : Bool) (word : Core.Word) (store : Core.Store) :
    ConditionalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store conditional (result choice word) store (required choice) := by
  cases choice
  · exact .ifFalse (conditionCost false word store) (.expression (valueCost false word store))
  · exact .ifTrue (conditionCost true word store) (.expression (.bitNot (valueCost true word store)))
private theorem elaborated (choice : Bool) (word : Core.Word) :
    TerminalReturnBodyElaborates (inputs choice word).names (inputs choice word).context conditional core .word :=
  .conditional (conditionalElaborated choice word)
private theorem checked (choice : Bool) (word : Core.Word) :
    (inputs choice word).checkTerminalReturnBody? conditional = some (core, .word) := (elaborated choice word).complete
private theorem costed (choice : Bool) (word : Core.Word) (store : Core.Store) :
    TerminalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store conditional (result choice word) store (required choice) := .conditional (conditionalCost choice word store)

theorem bare_return_embeddings_and_original_runner_agree_at_every_fuel
    (supplied : LocalInputs) (store : Core.Store) (fuel : Nat) :
    TerminalReturnBodyHasType supplied.names supplied.context (returned none) .unit ∧
    TerminalReturnBodyElaborates supplied.names supplied.context (returned none) .unit .unit ∧
    TerminalReturnBodyEvaluates supplied.names supplied.environment store (returned none) .unit store ∧
    TerminalReturnBodyEvaluatesWithCost supplied.names supplied.environment store (returned none) .unit store 1 ∧
    supplied.runTerminalReturnBody? fuel (returned none) store = supplied.runReturnBody? fuel (returned none) store ∧
    terminalReturnBodyFuelBound (returned none) = 1 :=
  ⟨.single .bare, .single .bare, .single .bare, .single .bare,
    supplied.runTerminalReturnBody?_single fuel none span span store, rfl⟩

theorem singleton_expression_raw_and_cost_projection_do_not_admit_a_conditional_derivation
    (table : LocalNameTable) (environment : Resolved.Environment) (source : Syntax.Expr)
    (initialStore finalStore : Core.Store) (value : Core.Value) (cost : Nat) :
    (TerminalReturnBodyEvaluates table environment initialStore (returned (some source)) value finalStore ↔
      ReturnBodyEvaluates table environment initialStore (returned (some source)) value finalStore) ∧
    (TerminalReturnBodyEvaluatesWithCost table environment initialStore (returned (some source)) value finalStore cost ↔
      ReturnBodyEvaluatesWithCost table environment initialStore (returned (some source)) value finalStore cost) := by
  constructor
  · constructor
    · intro evaluation; cases evaluation with | single child => exact child | conditional child => cases child
    · exact TerminalReturnBodyEvaluates.single
  · constructor
    · intro evaluation; cases evaluation with | single child => exact child | conditional child => cases child
    · exact TerminalReturnBodyEvaluatesWithCost.single

theorem arbitrary_actual_typed_expression_values_keep_one_step_and_all_outer_frames
    (type : Core.Ty) (value : Core.Value) (valueTyped : Core.ValueHasType value type)
    (store : Core.Store) (fuel : Nat) (continuation : List Core.Frame) :
    let supplied := LocalInputs.empty.bindFresh owner "w" type value valueTyped
    supplied.runTerminalReturnBody? fuel (returned (some (ref "w"))) store =
      supplied.runReturnBody? fuel (returned (some (ref "w"))) store ∧
    Core.Steps 1 ⟨.eval (.var 0) [value], continuation, store⟩ ⟨.ret value, continuation, store⟩ ∧
    (supplied.runTerminalReturnBody? fuel (returned (some (ref "w"))) store =
      some (type, .done value store) ↔ 1 ≤ fuel) := by
  intro supplied
  have elaboration : TerminalReturnBodyElaborates supplied.names supplied.context
      (returned (some (ref "w"))) (.var 0) type := .single (.expression (.identifier .head) (.var .head) (.var .head))
  have check : supplied.checkTerminalReturnBody? (returned (some (ref "w"))) = some (.var 0, type) := elaboration.complete
  have evaluation : TerminalReturnBodyEvaluatesWithCost supplied.names supplied.environment store
      (returned (some (ref "w"))) value store 1 := .single (.expression (.identifier .head .head))
  refine ⟨supplied.runTerminalReturnBody?_single fuel (some (ref "w")) span span store,
    evaluation.checked_toStepsWithContinuation check supplied.sameIds continuation, ?_⟩
  simpa only [LocalInputs.runTerminalReturnBody?, check, bind, Option.bind_some, pure,
    Option.some.injEq, Prod.mk.injEq, true_and] using evaluation.checked_runStateful_done_iff
      (fuel := fuel) check supplied.sameIds

theorem conditional_embedding_keeps_the_original_core_type_value_store_and_cost
    (choice : Bool) (word : Core.Word) (store : Core.Store) (fuel : Nat) :
    TerminalReturnBodyHasType (inputs choice word).names (inputs choice word).context conditional .word ∧
    TerminalReturnBodyElaborates (inputs choice word).names (inputs choice word).context conditional core .word ∧
    TerminalReturnBodyEvaluates (inputs choice word).names (inputs choice word).environment
      store conditional (result choice word) store ∧
    TerminalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store conditional (result choice word) store (required choice) ∧
    Core.Steps (required choice) (Core.State.initial core [.word word, .bool choice] store)
      (Core.State.final (result choice word) store) ∧
    (inputs choice word).runTerminalReturnBody? fuel conditional store =
      (inputs choice word).runConditionalReturnBody? fuel conditional store :=
  ⟨.conditional (conditionalTyped choice word), elaborated choice word,
    .conditional (conditionalCost choice word store).erase, costed choice word store,
    (costed choice word store).checked_toSteps (checked choice word) (inputs choice word).sameIds,
    (inputs choice word).runTerminalReturnBody?_conditional fuel (ref "c")
      (returned (some complement)) (returned (some (ref "w"))) span span store⟩

theorem conditional_projection_retains_selected_arm_costs_without_recursive_union_arms
    (choice : Bool) (word : Core.Word) (initialStore finalStore : Core.Store) (value : Core.Value) (cost : Nat) :
    (TerminalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      initialStore conditional value finalStore cost ↔
      ConditionalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
        initialStore conditional value finalStore cost) := by
  constructor
  · intro evaluation; cases evaluation with | single child => cases child | conditional child => exact child
  · exact TerminalReturnBodyEvaluatesWithCost.conditional

theorem common_all_fuel_boundaries_and_continuation_paths_add_no_wrapper_steps
    (choice : Bool) (word : Core.Word) (store : Core.Store) (fuel : Nat) (continuation : List Core.Frame) :
    ((inputs choice word).runTerminalReturnBody? fuel conditional store =
      some (.word, .done (result choice word) store) ↔ required choice ≤ fuel) ∧
    ((∃ checkpoint, (inputs choice word).runTerminalReturnBody? fuel conditional store =
      some (.word, .outOfFuel checkpoint)) ↔ fuel < required choice) ∧
    Core.Steps (required choice) ⟨.eval core [.word word, .bool choice], continuation, store⟩
      ⟨.ret (result choice word), continuation, store⟩ := by
  refine ⟨?_, ?_, (costed choice word store).checked_toStepsWithContinuation
    (checked choice word) (inputs choice word).sameIds continuation⟩
  · simpa only [LocalInputs.runTerminalReturnBody?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using (costed choice word store).checked_runStateful_done_iff
        (fuel := fuel) (checked choice word) (inputs choice word).sameIds
  · simpa only [LocalInputs.runTerminalReturnBody?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using (costed choice word store).checked_runStateful_outOfFuel_iff
        (fuel := fuel) (checked choice word) (inputs choice word).sameIds

private def deciding (choice : Bool) (word : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.unary .wordNot (.var 0)) (.var 0) [.word word, .bool choice]], store⟩

theorem common_runner_resumes_the_same_genuine_conditional_checkpoint
    (choice : Bool) (word : Core.Word) (store : Core.Store) (additional : Nat) :
    (inputs choice word).runTerminalReturnBody? 2 conditional store = some (.word, .outOfFuel (deciding choice word store)) ∧
    Core.Steps (required choice - 2) (deciding choice word store) (Core.State.final (result choice word) store) ∧
    (inputs choice word).runTerminalReturnBody? (2 + additional) conditional store =
      some (.word, Core.runStateful additional (deciding choice word store)) := by
  have exhausted : (inputs choice word).runTerminalReturnBody? 2 conditional store =
      some (.word, .outOfFuel (deciding choice word store)) := by
    rw [LocalInputs.runTerminalReturnBody?, checked]; cases choice <;> rfl
  have actual : Core.runStateful 2 (Core.State.initial core [.word word, .bool choice] store) =
      .outOfFuel (deciding choice word store) := by cases choice <;> rfl
  exact ⟨exhausted, ((costed choice word store).checked_residual_of_outOfFuel
    (checked choice word) (inputs choice word).sameIds actual).2,
    LocalInputs.runTerminalReturnBody?_resume exhausted additional⟩

theorem bounds_dispatch_to_existing_profiles_but_old_entry_bound_remains_singleton_only :
    terminalReturnBodyFuelBound (returned none) = returnBodyFuelBound (returned none) ∧
    terminalReturnBodyFuelBound conditional = conditionalReturnBodyFuelBound conditional ∧
    terminalReturnBodyFuelBound conditional = 6 ∧ returnBodyFuelBound conditional = 0 :=
  ⟨rfl, rfl, by simp [conditional, branch, returned, complement, ref, terminalReturnBodyFuelBound,
    conditionalReturnBodyFuelBound, returnBodyFuelBound, localExpressionFuelBound], rfl⟩

theorem common_bound_completes_with_the_actual_selected_typed_value
    (choice : Bool) (word : Core.Word) (store : Core.Store) :
    required choice ≤ terminalReturnBodyFuelBound conditional ∧
    Core.ValueHasType (result choice word) .word ∧
    (inputs choice word).runTerminalReturnBody? 6 conditional store = some (.word, .done (result choice word) store) := by
  have bound := bounds_dispatch_to_existing_profiles_but_old_entry_bound_remains_singleton_only.2.2.1
  have enough := (costed choice word store).cost_le_fuelBound
  have actual := (common_all_fuel_boundaries_and_continuation_paths_add_no_wrapper_steps choice word store 6 []).1.mpr
    (by simpa only [bound] using enough)
  obtain ⟨value, valueTyped, completed⟩ := LocalInputs.runTerminalReturnBody?_done_of_fuelBound
    (.conditional (conditionalTyped choice word)) store 6 (by simp only [bound, Nat.le_refl])
  rw [actual] at completed
  cases completed
  exact ⟨enough, valueTyped, actual⟩

private def missingArm := branch (returned (some (ref "w"))) (returned (some (ref "missing")))
private def nested := branch conditional (returned none)

theorem raw_skipped_arm_success_does_not_certify_common_whole_checking
    (word : Core.Word) (store : Core.Store) (fuel : Nat) :
    TerminalReturnBodyEvaluatesWithCost (inputs true word).names (inputs true word).environment
      store missingArm (.word word) store 4 ∧
    (inputs true word).checkTerminalReturnBody? missingArm = none ∧
    (inputs true word).runTerminalReturnBody? fuel missingArm store = none := by
  have rejected : (inputs true word).checkTerminalReturnBody? missingArm = none := by
    simp [LocalInputs.checkTerminalReturnBody?, elaborateTerminalReturnBody?, elaborateConditionalReturnBody?,
      missingArm, branch, returned, elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?, ref,
      inputs, LocalInputs.names, LocalInputs.context, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  exact ⟨.conditional (.ifTrue (conditionCost true word store) (.expression (valueCost true word store))),
    rejected, by simp only [LocalInputs.runTerminalReturnBody?, rejected, bind, Option.bind_none]⟩

theorem nested_statement_conditionals_are_not_recursively_accepted
    (word : Core.Word) (store : Core.Store) (fuel : Nat) :
    TerminalReturnBodyEvaluates (inputs false word).names (inputs false word).environment store nested .unit store ∧
    (inputs false word).checkTerminalReturnBody? nested = none ∧
    (inputs false word).runTerminalReturnBody? fuel nested store = none := by
  have rejected : (inputs false word).checkTerminalReturnBody? nested = none := by
    simp [LocalInputs.checkTerminalReturnBody?, elaborateTerminalReturnBody?, elaborateConditionalReturnBody?,
      nested, branch, conditional, returned, elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?, ref,
      inputs, LocalInputs.names, LocalInputs.context, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  exact ⟨.conditional (.ifFalse (conditionCost false word store).erase .bare), rejected,
    by simp only [LocalInputs.runTerminalReturnBody?, rejected, bind, Option.bind_none]⟩

private def declaration : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "unchanged"⟩, none, ⟨span, []⟩, ⟨none, none⟩, none, none⟩, conditional⟩⟩

theorem original_singleton_rejects_and_ill_scoped_function_entry_still_rejects
    (choice : Bool) (word : Core.Word) :
    (inputs choice word).checkReturnBody? conditional = none ∧
    compileRuntimeFunction? [] owner declaration = none := by
  refine ⟨rfl, ?_⟩
  apply compileRuntimeFunction?_eq_none_iff.mpr
  intro ⟨candidate, accepted⟩
  have sameInputs : candidate.inputs = .empty := accepted.parameters.result_unique .nil
  have checked := accepted.body.complete
  rw [sameInputs] at checked
  simp [elaborateTypedLetReturnTree?, declaration, conditional,
    branch, ref, elaborateLocalExpression?, resolveLocalExpression?, LocalTypeInputs.empty,
    LocalTypeInputs.names, LocalTypeInputs.context, LocalNameTable.lookup?] at checked

end Tests.FrontendTerminalReturnBody
end

section
-- leanmerge: from Solcore.Test.FrontendTerminalReturnTreeEvaluationProperties
/-! Recursive selected paths retain actual values, stores and pending frames.
Identity alignment is separate from value typing; no tree runner is introduced. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalReturnTreeEvaluation

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeEvaluation", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "tree-evaluation.sol"⟩, 71, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (value : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt value⟩]⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block :=
  ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def names : LocalNameTable := [("y", id 2), ("x", id 1), ("c", id 0)]
private def context (type : Core.Ty) : Resolved.Context := [(id 2, type), (id 1, type), (id 0, .bool)]
private def environment (choice : Bool) (left right : Core.Value) : Resolved.Environment :=
  [(id 2, right), (id 1, left), (id 0, .bool choice)]
private def x := returned (some (ref "x"))
private def y := returned (some (ref "y"))
private def bare := returned none
private def spine : Nat → Syntax.Block
  | 0 => x
  | depth + 1 => branch (ref "c") (spine depth) y
private def core : Nat → Core.Expr
  | 0 => .var 1
  | depth + 1 => .ifE (.var 2) (core depth) (.var 0)
private theorem xElab (type : Core.Ty) : ReturnBodyElaborates names (context type) x (.var 1) type :=
  .expression (.identifier (.tail (by decide) .head))
    (.var (.tail (by change id 2 ≠ id 1; decide) .head)) (.var (.tail (by decide) .head))
private theorem yElab (type : Core.Ty) : ReturnBodyElaborates names (context type) y (.var 0) type :=
  .expression (.identifier .head) (.var .head) (.var .head)
private theorem elaborated (depth : Nat) (type : Core.Ty) :
    TerminalReturnTreeElaborates names (context type) (spine depth) (core depth) type := by
  induction depth with
  | zero => exact .single (xElab type)
  | succ depth ih =>
    exact .conditional (.identifier (.tail (by decide) (.tail (by decide) .head)))
      (.var (.tail (by change id 2 ≠ id 0; decide) (.tail (by change id 1 ≠ id 0; decide) .head)))
      (.var (.tail (by decide) (.tail (by decide) .head))) ih (.single (yElab type))
private theorem conditionCost (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store (ref "c") (.bool choice) store 1 :=
  .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem xCost (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store (ref "x") left store 1 :=
  .identifier (.tail (by decide) .head) (.tail (by decide) .head)
private theorem yCost (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store (ref "y") right store 1 := .identifier .head .head
private theorem trueCost (depth : Nat) (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) left store (3 * depth + 1) := by
  induction depth with
  | zero => exact .single (.expression (xCost true left right store))
  | succ depth ih =>
    have arithmetic : 1 + (3 * depth + 1) + 2 = 3 * (depth + 1) + 1 := by omega
    simpa only [arithmetic, spine, branch] using TerminalReturnTreeEvaluatesWithCost.ifTrue (conditionCost true left right store) ih
private theorem falseCost (depth : Nat) (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost names (environment false left right) store (spine (depth + 1)) right store 4 :=
  .ifFalse (conditionCost false left right store) (.single (.expression (yCost false left right store)))

theorem every_true_level_costs_three_while_false_stops_at_the_first_node
    (depth : Nat) (type : Core.Ty) (left right : Core.Value) (store : Core.Store) (continuation : List Core.Frame) :
    TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) left store (3 * depth + 1) ∧
    TerminalReturnTreeEvaluatesWithCost names (environment false left right) store (spine (depth + 1)) right store 4 ∧
    Core.Steps (3 * depth + 1) ⟨.eval (core depth) [right, left, .bool true], continuation, store⟩ ⟨.ret left, continuation, store⟩ ∧
    Core.Steps 4 (Core.State.initial (core (depth + 1)) [right, left, .bool false] store) (Core.State.final right store) :=
  ⟨trueCost depth left right store, falseCost depth left right store,
    (trueCost depth left right store).checked_toStepsWithContinuation (elaborated depth type).complete rfl continuation,
    (falseCost depth left right store).checked_toSteps (elaborated (depth + 1) type).complete rfl⟩

theorem a_leaf_has_one_step_even_when_the_unused_condition_is_false (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost names (environment false left right) store (spine 0) left store 1 :=
  .single (.expression (xCost false left right store))

theorem raw_and_counted_derivations_determine_values_stores_and_the_exact_positive_cost
    (depth : Nat) (left right rawValue countedValue : Core.Value) (store rawStore countedStore : Core.Store) (cost : Nat)
    (raw : TerminalReturnTreeEvaluates names (environment true left right) store (spine depth) rawValue rawStore)
    (counted : TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) countedValue countedStore cost) :
    rawValue = left ∧ rawStore = store ∧ countedValue = left ∧ countedStore = store ∧ cost = 3 * depth + 1 ∧ 0 < cost ∧
    (∃ witness, TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) rawValue rawStore witness) ∧
    (TerminalReturnTreeEvaluates names (environment true left right) store (spine depth) left store ↔
      ∃ witness, TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) left store witness) := by
  have original := trueCost depth left right store
  have same := counted.deterministic original
  exact ⟨(raw.deterministic original.erase).1, raw.store_eq, same.1, counted.store_eq, same.2.2,
    counted.cost_pos, raw.exists_cost, terminalReturnTreeEvaluates_iff_exists_cost⟩

theorem typed_existence_and_preservation_use_the_actual_supplied_value_proofs
    (depth : Nat) (choice : Bool) (type : Core.Ty) (left right value : Core.Value)
    (leftTyped : Core.ValueHasType left type) (rightTyped : Core.ValueHasType right type)
    (store finalStore : Core.Store)
    (raw : TerminalReturnTreeEvaluates names (environment choice left right) store (spine depth) value finalStore) :
    (∃ result, TerminalReturnTreeEvaluates names (environment choice left right) store (spine depth) result store ∧
      Core.ValueHasType result type) ∧ Core.ValueHasType value type ∧ finalStore = store := by
  have typing := (elaborated depth type).hasType
  have supplied : Core.EnvironmentHasTypes (environment choice left right).values (context type).values :=
    .cons rightTyped (.cons leftTyped (.cons .bool .nil))
  exact ⟨typing.evaluates rfl supplied store, raw.preserves_type typing rfl supplied⟩

theorem opaque_existing_cells_and_closures_leave_even_incompatible_outer_frames_pending
    (depth : Nat) (location : Core.Location) (body : Core.Expr) (captured : Core.Environment)
    (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps (3 * depth + 1)
      ⟨.eval (core depth) [.unit, .cellRef .word location, .bool true], .unaryApply .boolNot :: continuation, store⟩
      ⟨.ret (.cellRef .word location), .unaryApply .boolNot :: continuation, store⟩ ∧
    Core.Steps (3 * depth + 1)
      ⟨.eval (core depth) [.unit, .closure .bool .word body captured, .bool true], continuation, store⟩
      ⟨.ret (.closure .bool .word body captured), continuation, store⟩ :=
  ⟨(trueCost depth (.cellRef .word location) .unit store).checked_toStepsWithContinuation
      (elaborated depth (.cell .word)).complete rfl _,
    (trueCost depth (.closure .bool .word body captured) .unit store).checked_toStepsWithContinuation
      (elaborated depth (.function .bool .word)).complete rfl continuation⟩

theorem aligned_untyped_payloads_still_have_raw_core_correspondence_without_type_safety
    (depth : Nat) (store finalStore : Core.Store) (value : Core.Value) :
    elaborateTerminalReturnTree? names (context .word) (spine depth) = some (core depth, .word) ∧
    (TerminalReturnTreeEvaluates names (environment true (.bool true) (.bool false)) store (spine depth) value finalStore ↔
      Core.Evaluates [.bool false, .bool true, .bool true] store (core depth) value finalStore) ∧
    Core.Evaluates [.bool false, .bool true, .bool true] store (core depth) (.bool true) store ∧
    ¬ Core.ValueHasType (.bool true) .word := by
  have accepted := (elaborated depth .word).complete
  exact ⟨accepted, elaborateTerminalReturnTree?_evaluates_iff accepted rfl,
    (elaborateTerminalReturnTree?_evaluates_iff accepted rfl).mp (trueCost depth (.bool true) (.bool false) store).erase,
    by intro impossible; cases impossible⟩

theorem typed_values_do_not_replace_the_missing_identity_alignment (store : Core.Store) :
    let table : LocalNameTable := [("x", id 0), ("y", id 1)]
    let scope : Resolved.Context := [(id 0, .bool), (id 1, .bool)]
    let swapped : Resolved.Environment := [(id 1, .bool false), (id 0, .bool true)]
    elaborateTerminalReturnTree? table scope x = some (.var 0, .bool) ∧
    swapped.ids ≠ scope.ids ∧ Core.EnvironmentHasTypes swapped.values scope.values ∧
    TerminalReturnTreeEvaluates table swapped store x (.bool true) store ∧
    Core.Evaluates swapped.values store (.var 0) (.bool false) store ∧
    ¬ Core.Evaluates swapped.values store (.var 0) (.bool true) store := by
  intro table scope swapped
  have exact : TerminalReturnTreeElaborates table scope x (.var 0) .bool :=
    .single (.expression (.identifier .head) (.var .head) (.var .head))
  exact ⟨exact.complete, by decide, .cons .bool (.cons .bool .nil),
    .single (.expression (.identifier .head (.tail (by decide) .head))), .var rfl,
    by intro impossible; cases impossible with | var found => cases found⟩

private def twoNames : LocalNameTable := ("d", id 3) :: names
private def twoEnvironment (outer inner : Bool) (word : Core.Word) : Resolved.Environment :=
  (id 3, .bool inner) :: environment outer (.word word) (.word .zero)
private def asymmetric := branch (ref "c")
  (branch (ref "d") (returned (some ⟨span, .unary ⟨span, .bitNot⟩ (ref "x")⟩)) x) y
private def asymmetricCost (outer inner : Bool) : Nat := if outer then if inner then 9 else 7 else 4
private def asymmetricValue (outer inner : Bool) (word : Core.Word) : Core.Value :=
  .word (if outer then if inner then word.bitNot else word else .zero)
theorem asymmetric_paths_count_only_the_selected_conditions_and_word_operation
    (outer inner : Bool) (word : Core.Word) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost twoNames (twoEnvironment outer inner word) store asymmetric
      (asymmetricValue outer inner word) store (asymmetricCost outer inner) := by
  have c : LocalExpressionEvaluatesWithCost twoNames (twoEnvironment outer inner word) store (ref "c") (.bool outer) store 1 :=
    .identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
  have d : LocalExpressionEvaluatesWithCost twoNames (twoEnvironment outer inner word) store (ref "d") (.bool inner) store 1 := .identifier .head .head
  have selectedX : LocalExpressionEvaluatesWithCost twoNames (twoEnvironment outer inner word) store (ref "x") (.word word) store 1 :=
    .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
  have selectedY : LocalExpressionEvaluatesWithCost twoNames (twoEnvironment outer inner word) store (ref "y") (.word .zero) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  cases outer
  · exact .ifFalse c (.single (.expression selectedY))
  · cases inner
    · exact .ifTrue c (.ifFalse d (.single (.expression selectedX)))
    · exact .ifTrue c (.ifTrue d (.single (.expression (.bitNot selectedX))))

private def bad : Nat → Syntax.Block
  | 0 => returned (some (ref "missing"))
  | depth + 1 => branch (ref "c") bare (bad depth)
private theorem badUntyped (depth : Nat) : ¬ ∃ type, TerminalReturnTreeHasType names (context .word) (bad depth) type := by
  induction depth with
  | zero =>
    rintro ⟨type, typing⟩
    cases typing with
    | single leaf =>
      cases leaf with
      | expression typed =>
        obtain ⟨resolved, resolution, _⟩ := typed.resolves
        have accepted := resolution.complete
        simp [resolveLocalExpression?, ref, names, LocalNameTable.lookup?] at accepted
  | succ depth ih =>
    rintro ⟨type, typing⟩
    cases typing with
    | single leaf => cases leaf
    | conditional _ _ no => exact ih ⟨type, no⟩
theorem a_skipped_arbitrarily_deep_invalid_arm_has_raw_cost_four_but_no_whole_acceptance
    (depth : Nat) (store : Core.Store) :
    TerminalReturnTreeEvaluates names (environment false .unit .unit) store (branch (ref "c") (bad depth) bare) .unit store ∧
    TerminalReturnTreeEvaluatesWithCost names (environment false .unit .unit) store (branch (ref "c") (bad depth) bare) .unit store 4 ∧
    elaborateTerminalReturnTree? names (context .word) (branch (ref "c") (bad depth) bare) = none := by
  refine ⟨.ifFalse (conditionCost false .unit .unit store).erase (.single .bare),
    .ifFalse (conditionCost false .unit .unit store) (.single .bare), ?_⟩
  apply elaborateTerminalReturnTree?_eq_none_iff.mpr
  rintro ⟨type, typing⟩
  cases typing with
  | single leaf => cases leaf
  | conditional _ yes _ => exact badUntyped depth ⟨type, yes⟩

theorem all_old_raw_and_cost_profiles_embed_with_no_extra_steps_or_acceptance_premise
    (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluates names (environment choice left right) store x left store ∧
    TerminalReturnTreeEvaluatesWithCost names (environment choice left right) store x left store 1 ∧
    TerminalReturnTreeEvaluates names (environment choice left right) store (spine 1) (if choice then left else right) store ∧
    TerminalReturnTreeEvaluatesWithCost names (environment choice left right) store (spine 1) (if choice then left else right) store 4 ∧
    TerminalReturnTreeEvaluates names (environment choice left right) store bare .unit store ∧
    TerminalReturnTreeEvaluatesWithCost names (environment choice left right) store bare .unit store 1 := by
  have leaf : ReturnBodyEvaluatesWithCost names (environment choice left right) store x left store 1 :=
    .expression (xCost choice left right store)
  have conditional : ConditionalReturnBodyEvaluatesWithCost names (environment choice left right) store (spine 1)
      (if choice then left else right) store 4 := by
    cases choice
    · exact .ifFalse (conditionCost false left right store) (.expression (yCost false left right store))
    · exact .ifTrue (conditionCost true left right store) (.expression (xCost true left right store))
  have terminal : TerminalReturnBodyEvaluatesWithCost names (environment choice left right) store bare .unit store 1 := .single .bare
  have terminalRaw : TerminalReturnBodyEvaluates names (environment choice left right) store bare .unit store := .single .bare
  exact ⟨leaf.erase.returnTree, leaf.returnTree, conditional.erase.returnTree, conditional.returnTree,
    terminalRaw.returnTree, terminal.returnTree⟩

end Tests.FrontendTerminalReturnTreeEvaluation
end

section
-- leanmerge: from Solcore.Test.FrontendTerminalReturnTreeProperties
/-! Arbitrary-depth static trees retain every original branch and positional
reference. The raw skip contrast below uses only the old conditional judgment. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalReturnTree

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ReturnTree", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "return-tree.sol"⟩, 61, 7⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (source : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt source⟩]⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block :=
  ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def names : LocalNameTable := [("y", id 2), ("x", id 1), ("c", id 0)]
private def context (type : Core.Ty) : Resolved.Context := [(id 2, type), (id 1, type), (id 0, .bool)]
private def x := returned (some (ref "x"))
private def y := returned (some (ref "y"))
private def bare := returned none
private theorem xTyped (type : Core.Ty) : LocalExpressionHasType names (context type) (ref "x") type :=
  .identifier (.tail (by decide) .head) (.tail (by decide) .head)
private theorem yTyped (type : Core.Ty) : LocalExpressionHasType names (context type) (ref "y") type := .identifier .head .head
private theorem guardTyped (type : Core.Ty) : LocalExpressionHasType names (context type) (ref "c") .bool :=
  .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem guardResolves : ResolvesLocalExpression names (ref "c") (.var (id 0)) :=
  .identifier (.tail (by decide) (.tail (by decide) .head))
private theorem guardLowers (type : Core.Ty) : Resolved.Lowers (Resolved.LocalScope.ids (context type)) (.var (id 0)) (.var 2) :=
  .var (.tail (by change id 2 ≠ id 0; decide) (.tail (by change id 1 ≠ id 0; decide) .head))
private theorem guardResolvedType (type : Core.Ty) : Resolved.HasType (context type) (.var (id 0)) .bool :=
  .var (.tail (by decide) (.tail (by decide) .head))
private theorem xElab (type : Core.Ty) : ReturnBodyElaborates names (context type) x (.var 1) type :=
  .expression (.identifier (.tail (by decide) .head)) (.var (.tail (by change id 2 ≠ id 1; decide) .head)) (.var (.tail (by decide) .head))
private theorem yElab (type : Core.Ty) : ReturnBodyElaborates names (context type) y (.var 0) type :=
  .expression (.identifier .head) (.var .head) (.var .head)
private def spine : Nat → Syntax.Block → Syntax.Block → Syntax.Block
  | 0, first, _ => first
  | depth + 1, first, side => branch (ref "c") (spine depth first side) side
private def spineCore : Nat → Core.Expr → Core.Expr → Core.Expr
  | 0, first, _ => first
  | depth + 1, first, side => .ifE (.var 2) (spineCore depth first side) side
private theorem spineTyped (depth : Nat) (payload result : Core.Ty) {first side : Syntax.Block}
    (firstTyped : ReturnBodyHasType names (context payload) first result)
    (sideTyped : ReturnBodyHasType names (context payload) side result) :
    TerminalReturnTreeHasType names (context payload) (spine depth first side) result := by
  induction depth with
  | zero => exact .single firstTyped
  | succ depth ih => exact .conditional (guardTyped payload) ih (.single sideTyped)
private theorem spineElab (depth : Nat) (payload result : Core.Ty) {first side : Syntax.Block} {firstCore sideCore : Core.Expr}
    (firstElab : ReturnBodyElaborates names (context payload) first firstCore result)
    (sideElab : ReturnBodyElaborates names (context payload) side sideCore result) :
    TerminalReturnTreeElaborates names (context payload) (spine depth first side) (spineCore depth firstCore sideCore) result := by
  induction depth with
  | zero => exact .single firstElab
  | succ depth ih => exact .conditional guardResolves (guardLowers payload) (guardResolvedType payload) ih (.single sideElab)

theorem arbitrary_depth_keeps_independent_typing_and_exact_unshifted_positions
    (depth : Nat) (type : Core.Ty) (definitions : Core.DataEnvironment) :
    TerminalReturnTreeHasType names (context type) (spine depth x y) type ∧
    TerminalReturnTreeElaborates names (context type) (spine depth x y) (spineCore depth (.var 1) (.var 0)) type ∧
    elaborateTerminalReturnTree? names (context type) (spine depth x y) = some (spineCore depth (.var 1) (.var 0), type) ∧
    Core.HasType [type, type, .bool] (spineCore depth (.var 1) (.var 0)) type definitions := by
  have exactTree := spineElab depth type type (xElab type) (yElab type)
  refine ⟨spineTyped depth type type (.expression (xTyped type)) (.expression (yTyped type)), exactTree, exactTree.complete, ?_⟩
  clear exactTree
  induction depth with
  | zero => exact .var rfl
  | succ depth ih => exact .ifE (.var rfl) ih (.var rfl)

theorem bare_unit_leaves_are_not_replaced_by_unit_typed_variable_leaves (depth : Nat) :
    TerminalReturnTreeHasType names (context .unit) (spine depth bare x) .unit ∧
    elaborateTerminalReturnTree? names (context .unit) (spine depth bare x) = some (spineCore depth .unit (.var 1), .unit) :=
  ⟨spineTyped depth .unit .unit .bare (.expression (xTyped .unit)), (spineElab depth .unit .unit .bare (xElab .unit)).complete⟩

theorem nominal_tree_checking_requires_no_runtime_inhabitant (depth : Nat) (dataType : Core.DataTypeId) :
    elaborateTerminalReturnTree? names (context (.namedData dataType)) (spine depth x y) =
      some (spineCore depth (.var 1) (.var 0), .namedData dataType) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData dataType) := by
  refine ⟨(spineElab depth _ _ (xElab _) (yElab _)).complete, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ =>
      simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def asymmetric := branch (ref "c") x (spine 2 x y)
private def asymmetricCore : Core.Expr := .ifE (.var 2) (.var 1) (.ifE (.var 2) (.ifE (.var 2) (.var 1) (.var 0)) (.var 0))
private theorem asymmetricElab (type : Core.Ty) : TerminalReturnTreeElaborates names (context type) asymmetric asymmetricCore type :=
  .conditional guardResolves (guardLowers type) (guardResolvedType type) (.single (xElab type)) (spineElab 2 type type (xElab type) (yElab type))
theorem asymmetric_child_inversion_retains_both_original_ordered_subtrees (type : Core.Ty) :
    elaborateTerminalReturnTree? names (context type) asymmetric = some (asymmetricCore, type) ∧
    ∃ conditionCore thenCore elseCore,
      elaborateLocalExpression? names (context type) (ref "c") = some (conditionCore, .bool) ∧
      elaborateTerminalReturnTree? names (context type) x = some (thenCore, type) ∧
      elaborateTerminalReturnTree? names (context type) (spine 2 x y) = some (elseCore, type) ∧
      asymmetricCore = .ifE conditionCore thenCore elseCore :=
  ⟨(asymmetricElab type).complete, elaborateTerminalReturnTree?_children (asymmetricElab type).complete⟩

theorem typing_and_a_same_typed_wrong_core_do_not_replace_exact_source_provenance (type : Core.Ty)
    {candidate : Core.Expr} {candidateType : Core.Ty}
    (accepted : elaborateTerminalReturnTree? names (context type) asymmetric = some (candidate, candidateType)) :
    candidate = asymmetricCore ∧ candidateType = type ∧ Core.HasType (context type).values candidate candidateType ∧
    Core.HasType (context type).values (.var 1) type ∧
    TerminalReturnTreeHasType names (context type) asymmetric candidateType ∧
    ¬ TerminalReturnTreeElaborates names (context type) asymmetric (.var 1) type := by
  have exact := elaborateTerminalReturnTree?_elaborates accepted
  have same := exact.result_unique (asymmetricElab type)
  refine ⟨same.1, same.2, elaborateTerminalReturnTree?_core_hasType accepted, .var rfl,
    elaborateTerminalReturnTree?_sound accepted, ?_⟩
  intro wrong
  have changed := (wrong.result_unique (asymmetricElab type)).1
  cases changed

theorem independent_source_typing_supplies_all_static_existence_interfaces (depth : Nat) (type : Core.Ty) :
    (∃ result, TerminalReturnTreeElaborates names (context type) (spine depth x y) result type) ∧
    (∃ result, elaborateTerminalReturnTree? names (context type) (spine depth x y) = some (result, type)) ∧
    (TerminalReturnTreeHasType names (context type) (spine depth x y) type ↔
      ∃ result, TerminalReturnTreeElaborates names (context type) (spine depth x y) result type) ∧
    (TerminalReturnTreeHasType names (context type) (spine depth x y) type ↔
      ∃ result, elaborateTerminalReturnTree? names (context type) (spine depth x y) = some (result, type)) := by
  have typing : TerminalReturnTreeHasType names (context type) (spine depth x y) type :=
    spineTyped depth type type (.expression (xTyped type)) (.expression (yTyped type))
  exact ⟨typing.elaborates_exact, typing.elaborates,
    terminalReturnTreeHasType_iff_elaborates_exact, terminalReturnTreeHasType_iff_elaborates⟩

private theorem oldConditional (type : Core.Ty) : ConditionalReturnBodyElaborates names (context type) (spine 1 x y)
    (.ifE (.var 2) (.var 1) (.var 0)) type :=
  .intro guardResolves (guardLowers type) (guardResolvedType type) (xElab type) (yElab type)
theorem all_three_old_profiles_embed_without_adding_or_replacing_core (type : Core.Ty) :
    TerminalReturnTreeHasType names (context type) x type ∧
    TerminalReturnTreeElaborates names (context type) x (.var 1) type ∧
    elaborateTerminalReturnTree? names (context type) x = some (.var 1, type) ∧
    TerminalReturnTreeHasType names (context type) (spine 1 x y) type ∧
    TerminalReturnTreeElaborates names (context type) (spine 1 x y) (.ifE (.var 2) (.var 1) (.var 0)) type ∧
    elaborateTerminalReturnTree? names (context type) (spine 1 x y) = some (.ifE (.var 2) (.var 1) (.var 0), type) ∧
    TerminalReturnTreeHasType names (context type) bare .unit ∧
    TerminalReturnTreeElaborates names (context type) bare .unit .unit ∧
    elaborateTerminalReturnTree? names (context type) bare = some (.unit, .unit) := by
  have terminal : TerminalReturnBodyElaborates names (context type) bare .unit .unit := .single .bare
  exact ⟨(xElab type).hasType.returnTree, (xElab type).returnTree, (xElab type).returnTree_complete,
    (oldConditional type).hasType.returnTree, (oldConditional type).returnTree, (oldConditional type).returnTree_complete,
    terminal.hasType.returnTree, terminal.returnTree, terminal.returnTree_complete⟩

theorem full_optional_agreement_is_retained_on_exact_old_shapes
    (table : LocalNameTable) (scope : Resolved.Context) (condition : Syntax.Expr) (first side : Option Syntax.Expr) :
    elaborateTerminalReturnTree? table scope (returned first) = elaborateReturnBody? table scope (returned first) ∧
    elaborateTerminalReturnTree? table scope (returned first) = elaborateTerminalReturnBody? table scope (returned first) ∧
    elaborateTerminalReturnTree? table scope (branch condition (returned first) (returned side)) =
      elaborateConditionalReturnBody? table scope (branch condition (returned first) (returned side)) ∧
    elaborateTerminalReturnTree? table scope (branch condition (returned first) (returned side)) =
      elaborateTerminalReturnBody? table scope (branch condition (returned first) (returned side)) :=
  ⟨elaborateTerminalReturnTree?_single table scope first span span,
    elaborateTerminalReturnTree?_single_terminal table scope first span span,
    elaborateTerminalReturnTree?_conditional_singletons table scope condition first side span span span span span span,
    elaborateTerminalReturnTree?_conditional_singletons_terminal table scope condition first side span span span span span span⟩

theorem outer_spans_and_alternative_typing_leave_the_deep_core_and_type_fixed
    (depth : Nat) (type otherType : Core.Ty) (blockSpan ifSpan : Syntax.SourceSpan)
    (other : TerminalReturnTreeHasType names (context type) (spine (depth + 1) x y) otherType) :
    otherType = type ∧ elaborateTerminalReturnTree? names (context type)
      ⟨blockSpan, [⟨ifSpan, .ifThen (ref "c") (spine depth x y) (some y)⟩]⟩ =
        some (spineCore (depth + 1) (.var 1) (.var 0), type) := by
  have exact := spineElab (depth + 1) type type (xElab type) (yElab type)
  exact ⟨other.type_unique exact.hasType,
    (elaborateTerminalReturnTree?_spans names (context type) (ref "c") (spine depth x y) y blockSpan ifSpan span span).trans
      (elaborateTerminalReturnTree?_iff.mpr exact)⟩

private inductive Bad where | missing | guard | mismatch | statements
private def badBase : Bad → Syntax.Block
  | .missing => returned (some (ref "missing"))
  | .guard => branch (ref "x") bare bare
  | .mismatch => branch (ref "c") bare x
  | .statements => ⟨span, [⟨span, .returnStmt none⟩, ⟨span, .returnStmt none⟩]⟩
private def badSpine : Nat → Bad → Syntax.Block
  | 0, bad => badBase bad
  | depth + 1, bad => branch (ref "c") bare (badSpine depth bad)
private theorem badBaseUntyped (bad : Bad) : ¬ ∃ type, TerminalReturnTreeHasType names (context .word) (badBase bad) type := by
  rintro ⟨type, typing⟩
  cases bad
  · cases typing with
    | single child =>
      cases child with
      | expression expressionTyped =>
        obtain ⟨resolved, resolution, _⟩ := expressionTyped.resolves
        have checked := resolution.complete
        simp [resolveLocalExpression?, ref, names, LocalNameTable.lookup?] at checked
  · cases typing with
    | single child => cases child
    | conditional guard _ _ => cases guard.type_unique (xTyped .word)
  · cases typing with
    | single child => cases child
    | conditional _ thenTyped elseTyped =>
      cases thenTyped with
      | single child =>
        cases child
        cases elseTyped with
        | single child =>
          cases child with
          | expression expressionTyped => cases expressionTyped.type_unique (xTyped .word)
  · cases typing with | single child => cases child
private theorem badUntyped (depth : Nat) (bad : Bad) : ¬ ∃ type, TerminalReturnTreeHasType names (context .word) (badSpine depth bad) type := by
  induction depth with
  | zero => exact badBaseUntyped bad
  | succ depth ih =>
    rintro ⟨type, typing⟩
    cases typing with
    | single child => cases child
    | conditional _ _ elseTyped => exact ih ⟨type, elseTyped⟩

theorem every_deep_missing_guard_mismatch_and_extra_statement_failure_remains_rejected (depth : Nat) (bad : Bad) :
    elaborateTerminalReturnTree? names (context .word) (badSpine depth bad) = none ∧
    ¬ ∃ type, TerminalReturnTreeHasType names (context .word) (badSpine depth bad) type :=
  ⟨elaborateTerminalReturnTree?_eq_none_iff.mpr (badUntyped depth bad), badUntyped depth bad⟩

theorem the_old_raw_skipped_arm_judgment_does_not_certify_the_new_recursive_checker
    (depth : Nat) (bad : Bad) (store : Core.Store) :
    ConditionalReturnBodyEvaluates names [(id 2, .word .zero), (id 1, .word .zero), (id 0, .bool false)] store
      (branch (ref "c") (badSpine depth bad) bare) .unit store ∧
    elaborateTerminalReturnTree? names (context .word) (branch (ref "c") (badSpine depth bad) bare) = none := by
  refine ⟨.ifFalse (.identifier (.tail (by decide) (.tail (by decide) .head))
    (.tail (by decide) (.tail (by decide) .head))) .bare, ?_⟩
  apply elaborateTerminalReturnTree?_eq_none_iff.mpr
  rintro ⟨type, typing⟩
  cases typing with
  | single child => cases child
  | conditional _ thenTyped _ => exact badUntyped depth bad ⟨type, thenTyped⟩

theorem the_old_terminal_adapter_still_rejects_every_genuinely_deep_good_tree (depth : Nat) (type : Core.Ty) :
    elaborateTerminalReturnTree? names (context type) (spine (depth + 2) x y) =
      some (spineCore (depth + 2) (.var 1) (.var 0), type) ∧
    elaborateTerminalReturnBody? names (context type) (spine (depth + 2) x y) = none := by
  refine ⟨(spineElab _ type type (xElab type) (yElab type)).complete, ?_⟩
  have guardChecked : elaborateLocalExpression? names (context type) (ref "c") = some (.var 2, .bool) :=
    elaborateLocalExpression?_complete guardResolves (guardLowers type) (guardResolvedType type)
  simp [spine, branch, elaborateTerminalReturnBody?, elaborateConditionalReturnBody?, guardChecked, elaborateReturnBody?]

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Flag"], .bool)]
private def entry (depth : Nat) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "deep"⟩, none,
    ⟨span, [parameter "c" "Flag", parameter "x" "Payload", parameter "y" "Payload"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation "Payload"]⟩⟩, none⟩, spine (depth + 2) x y⟩⟩
private def inputs (type : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh owner "c" .bool).bindFresh owner "x" type).bindFresh owner "y" type
theorem a_valid_header_and_complete_parameters_compile_the_exact_deep_tree
    (depth : Nat) (type : Core.Ty) :
    RuntimeFunctionHeader (types type) (entry depth).value.signature type ∧
    RuntimeParametersDeclare (types type) owner (entry depth).value.signature.parameters.elements (inputs type) ∧
    compileRuntimeFunction? (types type) owner (entry depth) =
      some ⟨inputs type, spineCore (depth + 2) (.var 1) (.var 0), type⟩ := by
  have declared : RuntimeParametersDeclare (types type) owner (entry depth).value.signature.parameters.elements (inputs type) :=
    .cons (.named (.tail (by decide) .head)) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "x" ∉ ["c"]; decide) (.cons (.named .head) (by change "y" ∉ ["x", "c"]; decide) .nil))
  have compilation : RuntimeFunctionCompiles (types type) owner (entry depth)
      ⟨inputs type, spineCore (depth + 2) (.var 1) (.var 0), type⟩ :=
    ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, declared, TypedLetReturnBodyElaborates.returnTree <| .terminal (spineElab _ type type (xElab type) (yElab type))⟩
  exact ⟨compilation.header, declared, compilation.complete⟩

end Tests.FrontendTerminalReturnTree
end

section
-- leanmerge: from Solcore.Test.FrontendTerminalRuntimeEntryProperties
/-! Independent terminal-entry contracts use actual arguments, unequal selected
costs and real suspended environments. Static compilation invents no values. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalRuntimeEntry

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "terminal-entry.sol"⟩, 7, 31⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TerminalEntry", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩
private def yes := returned ⟨span, .unary ⟨span, .bitNot⟩ (ref "t")⟩
private def branch (no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") yes (some no)⟩]⟩
private def body := branch (returned (ref "f"))
private def declaration (source : Syntax.Block) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "choose"⟩, none,
    ⟨span, [parameter "c" "Bool", parameter "t" "Word", parameter "f" "Word"]⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation "Word"]⟩⟩, none⟩, source⟩⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def staticInputs := ((LocalTypeInputs.empty.bindFresh owner "c" .bool).bindFresh
  owner "t" .word).bindFresh owner "f" .word
private def inputs (choice : Bool) (left right : Core.Word) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh
    owner "t" .word (.word left) .word).bindFresh owner "f" .word (.word right) .word
private def arguments (choice : Bool) (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, ⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private def core : Core.Expr := .ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)
private def compiled : CompiledRuntimeFunction := ⟨staticInputs, core, .word⟩
private def prepared (choice : Bool) (left right : Core.Word) : PreparedRuntimeFunction :=
  ⟨inputs choice left right, core, .word⟩
private def required (choice : Bool) : Nat := if choice then 6 else 4
private def result (choice : Bool) (left right : Core.Word) : Core.Value :=
  .word (if choice then left.bitNot else right)
private theorem header : RuntimeFunctionHeader types (declaration body).value.signature .word :=
  ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
private theorem bodyElab : TerminalReturnBodyElaborates staticInputs.names staticInputs.context body core .word :=
  .conditional (.intro (.identifier (.tail (by decide) (.tail (by decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) .head)))
    (.expression (.bitNot (.identifier (.tail (by decide) .head)))
      (.unary (.var (.tail (by decide) .head))) (.unary (.var (.tail (by decide) .head))))
    (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem compiles : RuntimeFunctionCompiles types owner (declaration body) compiled :=
  ⟨header, .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "t" ∉ ["c"]; simp)
      (.cons (.named (.tail (by decide) .head)) (by change "f" ∉ ["t", "c"]; simp) .nil)), TypedLetReturnBodyElaborates.returnTree <| .terminal bodyElab.returnTree⟩
private theorem prepares (choice : Bool) (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration body) (arguments choice left right) (prepared choice left right) :=
  ⟨header, .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "t" ∉ ["c"]; simp)
      (.cons (.named (.tail (by decide) .head)) (by change "f" ∉ ["t", "c"]; simp) .nil)), TypedLetReturnBodyElaborates.returnTree <| .terminal bodyElab.returnTree⟩
private theorem conditionCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store (ref "c") (.bool choice) store 1 :=
  .identifier (.tail (show "f" ≠ "c" by decide) (.tail (show "t" ≠ "c" by decide) .head))
    (.tail (show id 2 ≠ id 0 by decide) (.tail (show id 1 ≠ id 0 by decide) .head))
private theorem yesCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    ReturnBodyEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store yes (.word left.bitNot) store 3 :=
  .expression (.bitNot (.identifier (.tail (show "f" ≠ "t" by decide) .head)
    (.tail (show id 2 ≠ id 1 by decide) .head)))
private theorem noCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    ReturnBodyEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store (returned (ref "f")) (.word right) store 1 := .expression (.identifier .head .head)
private theorem costed (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost types owner (declaration body) (arguments choice left right)
      store .word (result choice left right) store (required choice) := by
  apply RuntimeFunctionEvaluatesWithCost.intro (prepares choice left right)
  apply TypedLetReturnBodyEvaluatesWithCost.returnTree
  apply TypedLetReturnBodyEvaluatesWithCost.terminal
  apply TerminalReturnBodyEvaluatesWithCost.returnTree
  apply TerminalReturnBodyEvaluatesWithCost.conditional
  cases choice
  · exact .ifFalse (conditionCost false left right store) (noCost false left right store)
  · exact .ifTrue (conditionCost true left right store) (yesCost true left right store)

theorem annotation_only_compilation_and_actual_preparation_retain_exact_core
    (choice : Bool) (left right : Core.Word) :
    RuntimeFunctionCompiles types owner (declaration body) compiled ∧
    compileRuntimeFunction? types owner (declaration body) = some compiled ∧
    RuntimeFunctionPrepares types owner (declaration body) (arguments choice left right) (prepared choice left right) ∧
    prepareRuntimeFunction? types owner (declaration body) (arguments choice left right) = some (prepared choice left right) ∧
    (prepared choice left right).toCompiled = compiled ∧
    (inputs choice left right).environment = [(id 2, .word right), (id 1, .word left), (id 0, .bool choice)] :=
  ⟨compiles, compiles.complete, prepares choice left right, (prepares choice left right).complete, rfl, rfl⟩

theorem compilation_factorization_keeps_the_actual_argument_values_at_every_fuel
    (choice : Bool) (left right : Core.Word) (fuel : Nat) (store : Core.Store) :
    (prepareRuntimeFunction? types owner (declaration body) (arguments choice left right)).map
      PreparedRuntimeFunction.toCompiled = some compiled ∧
    runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel store =
      some (.word, Core.runStateful fuel (Core.State.initial core [.word right, .word left, .bool choice] store)) := by
  constructor
  · simpa only [compiles.complete, bind, Option.bind_some, show
      (arguments choice left right).map (·.type) = compiled.inputs.context.values.reverse from rfl, ↓reduceIte]
      using prepareRuntimeFunction?_factorization types owner (declaration body) (arguments choice left right)
  · exact compiles.run_eq (arguments choice left right) rfl fuel store

theorem independent_selected_costs_have_the_same_exact_compiled_paths
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost types owner (declaration body) (arguments choice left right)
      store .word (result choice left right) store (required choice) ∧
    Core.Steps (required choice) (Core.State.initial core [.word right, .word left, .bool choice] store)
      (Core.State.final (result choice left right) store) :=
  ⟨costed choice left right store, (costed choice left right store).compiled_toSteps compiles⟩

theorem all_entry_and_compiled_fuel_thresholds_keep_six_versus_four_steps
    (choice : Bool) (left right : Core.Word) (fuel : Nat) (store : Core.Store) :
    (runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel store =
      some (.word, .done (result choice left right) store) ↔ required choice ≤ fuel) ∧
    ((∃ suspended, runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel store =
      some (.word, .outOfFuel suspended)) ↔ fuel < required choice) ∧
    (Core.runStateful fuel (Core.State.initial core [.word right, .word left, .bool choice] store) =
      .done (result choice left right) store ↔ required choice ≤ fuel) ∧
    ((∃ suspended, Core.runStateful fuel (Core.State.initial core [.word right, .word left, .bool choice] store) =
      .outOfFuel suspended) ↔ fuel < required choice) :=
  ⟨(costed choice left right store).run_done_iff, (costed choice left right store).run_outOfFuel_iff,
    (costed choice left right store).compiled_run_done_iff compiles,
    (costed choice left right store).compiled_run_outOfFuel_iff compiles⟩

private theorem bound : terminalReturnBodyFuelBound body = 6 := by
  simp [body, branch, returned, yes, ref, terminalReturnBodyFuelBound,
    conditionalReturnBodyFuelBound, returnBodyFuelBound, localExpressionFuelBound]

theorem terminal_bound_is_six_while_the_unchanged_singleton_bound_is_zero
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    terminalReturnBodyFuelBound body = 6 ∧ returnBodyFuelBound body = 0 ∧ required choice ≤ 6 ∧
    (∃ value, Core.ValueHasType value .word ∧
      runRuntimeFunction? types owner (declaration body) (arguments choice left right) 6 store = some (.word, .done value store)) ∧
    (∃ value, Core.ValueHasType value .word ∧
      runRuntimeFunction? types owner (declaration body) (arguments choice left right) 6 store = some (.word, .done value store) ∧
      Core.runStateful 6 (Core.State.initial core [.word right, .word left, .bool choice] store) = .done value store) := by
  have treeBound : typedLetReturnTreeFuelBound body = 6 := by
    simp [body, branch, returned, yes, ref, typedLetReturnTreeFuelBound,
      returnBodyFuelBound, localExpressionFuelBound]
  have enough : typedLetReturnTreeFuelBound (declaration body).value.body ≤ 6 := by
    change typedLetReturnTreeFuelBound body ≤ 6
    rw [treeBound]; exact Nat.le_refl 6
  refine ⟨bound, rfl, ?_, (prepares choice left right).hasType.run_done_of_fuelBound store 6 enough,
    compiles.run_done_of_fuelBound (arguments choice left right) rfl store 6 enough⟩
  simpa only [show (declaration body).value.body = body from rfl, treeBound]
    using (costed choice left right store).cost_le_fuelBound

theorem a_same_typed_hand_built_core_does_not_supply_compilation_provenance :
    Core.HasType staticInputs.context.values (.word .zero) .word ∧
    ¬ RuntimeFunctionCompiles types owner (declaration body) { compiled with core := .word .zero } := by
  refine ⟨.word, ?_⟩
  intro forged
  have same := congrArg CompiledRuntimeFunction.core (compiles.result_unique forged)
  cases same

private def checkpoint (choice : Bool) (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.unary .wordNot (.var 1)) (.var 0)
    [.word right, .word left, .bool choice]], store⟩
private theorem exhausted (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    runRuntimeFunction? types owner (declaration body) (arguments choice left right) 2 store =
      some (.word, .outOfFuel (checkpoint choice left right store)) := by
  rw [runRuntimeFunction?, (prepares choice left right).complete]; cases choice <;> rfl

theorem owner_relabeling_keeps_the_complete_actual_checkpoint
    (choice : Bool) (left right : Core.Word) (otherOwner : Resolved.DeclarationId) (store : Core.Store) :
    runRuntimeFunction? types otherOwner (declaration body) (arguments choice left right) 2 store =
      some (.word, .outOfFuel (checkpoint choice left right store)) :=
  (runRuntimeFunction?_owner_eq types otherOwner owner (declaration body) (arguments choice left right) 2 store).trans
    (exhausted choice left right store)

theorem resumption_runs_the_real_checkpoint_and_retains_its_exact_remaining_path
    (choice : Bool) (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? types owner (declaration body) (arguments choice left right) 2 store =
      some (.word, .outOfFuel (checkpoint choice left right store)) ∧
    2 < required choice ∧ Core.Steps (required choice - 2) (checkpoint choice left right store)
      (Core.State.final (result choice left right) store) ∧
    runRuntimeFunction? types owner (declaration body) (arguments choice left right) (2 + additional) store =
      some (.word, Core.runStateful additional (checkpoint choice left right store)) := by
  have residual := (costed choice left right store).residual_of_outOfFuel (exhausted choice left right store)
  exact ⟨exhausted choice left right store, residual.1, residual.2,
    runRuntimeFunction?_resume (exhausted choice left right store) additional⟩

theorem store_replay_preserves_values_and_costs_but_keeps_each_own_store
    (choice : Bool) (left right : Core.Word) (first replacement : Core.Store) (fuel : Nat) :
    RuntimeFunctionEvaluatesWithCost types owner (declaration body) (arguments choice left right)
      replacement .word (result choice left right) replacement (required choice) ∧
    (runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel first =
      some (.word, .done (result choice left right) first) ↔
      runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel replacement =
        some (.word, .done (result choice left right) replacement)) ∧
    ((∃ suspended, runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel first =
      some (.word, .outOfFuel suspended)) ↔
      ∃ suspended, runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel replacement =
        some (.word, .outOfFuel suspended)) :=
  ⟨(costed choice left right first).change_store replacement,
    runRuntimeFunction?_done_store_iff types owner (declaration body) (arguments choice left right) fuel
      first replacement .word (result choice left right),
    runRuntimeFunction?_outOfFuel_store_iff types owner (declaration body) (arguments choice left right) fuel first replacement .word⟩

theorem differing_nonempty_stores_give_distinct_actual_checkpoints
    (choice : Bool) (left right : Core.Word) (tail : Core.Store) :
    runRuntimeFunction? types owner (declaration body) (arguments choice left right) 2 (.unit :: tail) ≠
      runRuntimeFunction? types owner (declaration body) (arguments choice left right) 2 (.bool true :: tail) := by
  rw [exhausted, exhausted]
  intro same
  have stored := congrArg (fun state : Core.State => state.store)
    (Core.StatefulRunResult.outOfFuel.inj (Prod.mk.inj (Option.some.inj same)).2)
  cases stored

private def selectBody : Syntax.Block :=
  ⟨span, [⟨span, .ifThen (ref "c") (returned (ref "t")) (some (returned (ref "f")))⟩]⟩
private def valueTypes (argument : TypedRuntimeArgument) : TypeNameTable :=
  [(["Bool"], .bool), (["Word"], argument.type)]
private def supplied (choice : Bool) (argument : TypedRuntimeArgument) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, argument, argument]
private def valueInputs (choice : Bool) (argument : TypedRuntimeArgument) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh
    owner "t" argument.type argument.value argument.valueTyped).bindFresh
      owner "f" argument.type argument.value argument.valueTyped

theorem arbitrary_typed_values_are_returned_without_invocation_or_allocation
    (choice : Bool) (argument : TypedRuntimeArgument) (store : Core.Store) (fuel : Nat) :
    RuntimeFunctionEvaluatesWithCost (valueTypes argument) owner (declaration selectBody) (supplied choice argument)
      store argument.type argument.value store 4 ∧
    (runRuntimeFunction? (valueTypes argument) owner (declaration selectBody) (supplied choice argument) fuel store =
      some (argument.type, .done argument.value store) ↔ 4 ≤ fuel) := by
  let candidate : PreparedRuntimeFunction := ⟨valueInputs choice argument, .ifE (.var 2) (.var 1) (.var 0), argument.type⟩
  have preparation : RuntimeFunctionPrepares (valueTypes argument) owner (declaration selectBody)
      (supplied choice argument) candidate :=
    ⟨⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩,
      .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
        (.cons (.named (.tail (by decide) .head)) (by change "t" ∉ ["c"]; simp)
          (.cons (.named (.tail (by decide) .head)) (by change "f" ∉ ["t", "c"]; simp) .nil)),
      TypedLetReturnBodyElaborates.returnTree <| .terminal <| .conditional (.identifier (.tail (show "f" ≠ "c" by decide) (.tail (show "t" ≠ "c" by decide) .head)))
        (.var (.tail (show id 2 ≠ id 0 by decide) (.tail (show id 1 ≠ id 0 by decide) .head)))
        (.var (.tail (show id 2 ≠ id 0 by decide) (.tail (show id 1 ≠ id 0 by decide) .head)))
        (.single (.expression (.identifier (.tail (show "f" ≠ "t" by decide) .head))
          (.var (.tail (show id 2 ≠ id 1 by decide) .head)) (.var (.tail (show id 2 ≠ id 1 by decide) .head))))
        (.single (.expression (.identifier .head) (.var .head) (.var .head)))⟩
  have condition : LocalExpressionEvaluatesWithCost candidate.inputs.names candidate.inputs.environment
      store (ref "c") (.bool choice) store 1 :=
    .identifier (.tail (show "f" ≠ "c" by decide) (.tail (show "t" ≠ "c" by decide) .head))
      (.tail (show id 2 ≠ id 0 by decide) (.tail (show id 1 ≠ id 0 by decide) .head))
  have yesValue : ReturnBodyEvaluatesWithCost candidate.inputs.names candidate.inputs.environment
      store (returned (ref "t")) argument.value store 1 :=
    .expression (.identifier (.tail (show "f" ≠ "t" by decide) .head) (.tail (show id 2 ≠ id 1 by decide) .head))
  have noValue : ReturnBodyEvaluatesWithCost candidate.inputs.names candidate.inputs.environment
      store (returned (ref "f")) argument.value store 1 := .expression (.identifier .head .head)
  have evaluated : RuntimeFunctionEvaluatesWithCost (valueTypes argument) owner (declaration selectBody)
      (supplied choice argument) store argument.type argument.value store 4 := by
    apply RuntimeFunctionEvaluatesWithCost.intro preparation
    apply TypedLetReturnBodyEvaluatesWithCost.returnTree
    apply TypedLetReturnBodyEvaluatesWithCost.terminal
    apply TerminalReturnBodyEvaluatesWithCost.returnTree
    apply TerminalReturnBodyEvaluatesWithCost.conditional
    cases choice
    · exact .ifFalse condition noValue
    · exact .ifTrue condition yesValue
  exact ⟨evaluated, evaluated.run_done_iff⟩

private def missing := branch (returned (ref "missing"))

theorem raw_selected_success_does_not_accept_an_unresolved_unselected_arm
    (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    TerminalReturnBodyEvaluatesWithCost (inputs true left right).names (inputs true left right).environment
      store missing (.word left.bitNot) store 6 ∧
    prepareRuntimeFunction? types owner (declaration missing) (arguments true left right) = none ∧
    runRuntimeFunction? types owner (declaration missing) (arguments true left right) fuel store = none := by
  have bodyRejected : (inputs true left right).checkTypedLetReturnTree? types owner missing = none := by
    simp [LocalInputs.checkTypedLetReturnTree?, elaborateTypedLetReturnTree?, LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context,
      missing, branch, yes, returned, ref, elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?,
      inputs, LocalInputs.names, LocalInputs.context, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  have noPreparation : ¬ ∃ candidate, RuntimeFunctionPrepares types owner (declaration missing)
      (arguments true left right) candidate := by
    rintro ⟨candidate, accepted⟩
    have same := (prepares true left right).parameters.result_unique accepted.parameters
    have checked := accepted.body.complete
    rw [← same] at checked
    change (inputs true left right).checkTypedLetReturnTree? types owner missing = some _ at checked
    rw [bodyRejected] at checked
    cases checked
  have rejected := prepareRuntimeFunction?_eq_none_iff.mpr noPreparation
  exact ⟨.conditional (.ifTrue (conditionCost true left right store) (yesCost true left right store)), rejected,
    by simp only [runRuntimeFunction?, rejected, bind, Option.bind_none]⟩

end Tests.FrontendTerminalRuntimeEntry
end
