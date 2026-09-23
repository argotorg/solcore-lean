import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionLocalFragmentProperties
import Solcore.Frontend.RuntimeFunctionPreparationFactorization
import Solcore.Core.LocalFragment
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluatorProperties

/-! Exact parsed entry provenance feeds structural insertion laws. Independent
Core paths fix costs; transported suspended states need not be identical. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace LocalFragmentEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LocalFragmentEntry", by decide⟩], by decide⟩⟩, 17⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def table (type : Core.Ty) : TypeNameTable := [(["T"], type), (["Bool"], .bool)]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "local-fragment-entry.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, content.utf8ByteSize⟩) && source.span.contains source.value.body.span) "original complete ranges changed"
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
private def core : Core.Expr := .letE (.var 2) (.ifE (.var 1)
  (.letE (.var 2) (.pair (.var 1) (.var 0))) (.pair (.var 2) (.var 0)))
private def cost (c : Bool) : Nat := if c then 14 else 11
private def result (x y : Core.Value) (c : Bool) : Core.Value := if c then .pair x y else .pair y x
private theorem paths (x y : Core.Value) (c : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (cost c) ⟨.eval core [.bool c, y, x], k, store⟩ ⟨.ret (result x y c), k, store⟩ := by
  cases c <;> simp only [cost, result, Bool.false_eq_true, ↓reduceIte]
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterIf (.cons (.var rfl)
      (.cons .chooseFalse (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl))))))))))
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterIf (.cons (.var rfl)
      (.cons .chooseTrue (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterPair (.cons (.var rfl)
        (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))))))))))
private def content := "function choose(x: T,y: T,c: Bool) returns((T,T)){let z=x;if(c){let q=y;return (z,q);}else{return (y,z);}}"
private def verify (x y : TypedRuntimeArgument) (same : y.type = x.type) (c : Bool) : IO Unit := do
  let source ← parsed content; let proof ← compile (table x.type) source
  check (decide (proof.compiled.core = core ∧ proof.compiled.returnType = .product x.type x.type ∧
    proof.compiled.inputs.names = [("c", ⟨owner, 2⟩), ("y", ⟨owner, 1⟩), ("x", ⟨owner, 0⟩)] ∧
    proof.compiled.inputs.context.values = [.bool, x.type, x.type])) "independent Core/type/parameter layout changed"
  let fragment := proof.evidence.localFragment
  have _ := compileRuntimeFunction?_localFragment proof.evidence.complete
  let args := [x, y, (⟨.bool, .bool c, .bool⟩ : TypedRuntimeArgument)]
  have _ : args.map (·.type) = [x.type, x.type, .bool] := by simp only [args, List.map_cons, List.map_nil, same]
  match accepted : prepareRuntimeFunction? (table x.type) owner source args with
  | none => throw (IO.userError "typed actual preparation failed")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound accepted
      have _ := preparation.localFragment
      have _ := prepareRuntimeFunction?_localFragment accepted
      check (decide (prepared.core = core ∧ prepared.returnType = .product x.type x.type ∧
        prepared.inputs.ids = proof.compiled.inputs.ids ∧ prepared.inputs.names = proof.compiled.inputs.names ∧
        prepared.inputs.environment.values = [.bool c, y.value, x.value])) "original arguments/parameter-only record changed"
      have _ := preparation.compiles.result_unique proof.evidence
      let forged : PreparedRuntimeFunction := { prepared with core := .letE (.lambda .word .word (.var 0)) (prepared.core.weakenAt 0) }
      have _ : ¬ RuntimeFunctionPrepares (table x.type) owner source args forged := by
        intro impossible
        cases impossible.localFragment with
        | letE nonlocal _ => cases nonlocal
      if exactCore : proof.compiled.core = core then
        have localCore : core.LocalFragment := exactCore ▸ fragment
        for store in [[], [w 91, .cellRef .word 999]] do
          let original := Core.State.initial core [.bool c, y.value, x.value] store
          let expected := result x.value y.value c
          for split in [0, 1, 2, 3] do
            let leading := [.bool c, y.value, x.value].take split
            let suffix := [.bool c, y.value, x.value].drop split
            have full : leading ++ suffix = [.bool c, y.value, x.value] := List.take_append_drop split _
            for inserted in [Core.Value.unit, .cellRef .word 707, .closure .word .word (.var 90) [], .pair (w 7) .unit] do
              let shifted := Core.State.initial (core.weakenAt leading.length) (leading ++ inserted :: suffix) store
              have path : Core.Steps (cost c) (.initial core (leading ++ suffix) store) (.final expected store) := by
                simpa only [full, Core.State.initial, Core.State.final, expected] using paths x.value y.value c store []
              have moved := localCore.steps_insert leading suffix inserted path []
              have _ := localCore.steps_reflect_insert leading suffix inserted moved []
              have _ := (localCore.steps_insert_iff leading suffix inserted).mpr path
              have _ := (localCore.evaluates_insert_iff leading suffix inserted).mpr (Core.steps_from_initial_sound path)
              have _ := (localCore.evaluates_insert_iff leading suffix inserted).mp (Core.steps_from_initial_sound moved)
              for k in [[], [.letBody (.var 0) [w 9]], [.unaryApply .wordNot]] do
                have _ := localCore.steps_insert leading suffix inserted path k
                pure ()
              for fuel in List.range (cost c + 3) do
                check (decide (runRuntimeFunction? (table x.type) owner source args fuel store =
                  some (.product x.type x.type, Core.runStateful fuel original)))
                  "whole runtime entry differs from the original machine"
                check (match Core.runStateful fuel original, Core.runStateful fuel shifted with
                  | .done a st, .done b tt => decide (cost c ≤ fuel ∧ a = expected ∧ b = expected ∧ st = store ∧ tt = store)
                  | .outOfFuel _, .outOfFuel _ => decide (fuel < cost c)
                  | _, _ => false) "transported threshold/value/own store changed"
              for spent in List.range (cost c) do
                match left : Core.runStateful spent original, right : Core.runStateful spent shifted with
                | .outOfFuel lc, .outOfFuel rc =>
                    have _ := (paths x.value y.value c store []).residual_of_outOfFuel left
                    have _ := moved.residual_of_outOfFuel right
                    have _ := Core.runStateful_resume left (cost c - spent)
                    have _ := Core.runStateful_resume right (cost c - spent)
                    check (decide (Core.runStateful (cost c - spent) lc = .done expected store ∧
                      Core.runStateful (cost c - spent) rc = .done expected store)) "genuine saved states or exact residual changed"
                    if spent = 2 then check (decide (lc ≠ rc)) "saved environments were incorrectly equated"
                    if spent = cost c - 1 then check (decide (lc = rc)) "final value-only frames did not coalesce"
                | _, _ => throw (IO.userError "genuine paired checkpoints missing")
          check (decide (Core.runStateful 2 original = .outOfFuel ⟨.ret x.value,
            [.letBody (.ifE (.var 1) (.letE (.var 2) (.pair (.var 1) (.var 0))) (.pair (.var 2) (.var 0))) [.bool c, y.value, x.value]], store⟩))
            "explicit old-scope let frame changed"
      else throw (IO.userError "exact independent Core changed")
private theorem typedInsertion {source : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} {types : TypeNameTable}
    (evidence : RuntimeFunctionCompiles types owner source compiled) (leading suffix : Core.Context) (inserted : Core.Ty)
    (definitions : Core.DataEnvironment) :
    Core.infer? (leading ++ inserted :: suffix) (compiled.core.weakenAt leading.length) definitions =
      Core.infer? (leading ++ suffix) compiled.core definitions :=
  evidence.localFragment.infer_insert leading suffix inserted definitions
private theorem forgedNotLocal (body : Core.Expr) :
    ¬ (Core.Expr.letE (.lambda .word .word (.var 0)) body).LocalFragment := by
  intro localBody
  cases localBody with
  | letE value _ => cases value
private theorem copyPaths (value : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 4 ⟨.eval (.letE (.var 0) (.var 1)) [value], k, store⟩ ⟨.ret value, k, store⟩ :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))
private def discardedCopy : IO Unit := do
  let source ← parsed "function f(x:T) returns(T){x;return x;}"
  let proof ← compile (table .word) source
  check (decide (proof.compiled.core = .letE (.var 0) (.var 1) ∧ proof.compiled.returnType = .word ∧
    proof.compiled.inputs.names = [("x", ⟨owner, 0⟩)])) "original discard copy provenance changed"
  have _ := proof.evidence.localFragment
  for store in [[], [w 91]] do
    for fuel in List.range 7 do
      have _ := copyPaths (w 9) store []
      check (match runRuntimeFunction? (table .word) owner source [⟨.word, w 9, .word⟩] fuel store with
        | some (.word, .done value final) => decide (4 ≤ fuel ∧ value = w 9 ∧ final = store)
        | some (.word, .outOfFuel checkpoint) => decide (fuel < 4 ∧ Core.runStateful (4 - fuel) checkpoint = .done (w 9) store)
        | _ => false) "original discarded copy is not strict cost four"
end LocalFragmentEntries
open LocalFragmentEntries

def frontendParsedLocalFragmentEntryTests : IO Unit := do
  discardedCopy
  verify ⟨.word, w 9, .word⟩ ⟨.word, w 2, .word⟩ rfl true
  verify ⟨.word, w 9, .word⟩ ⟨.word, w 2, .word⟩ rfl false
  for c in [false, true] do
    verify ⟨.cell .word, .cellRef .word 900, .cellRef⟩ ⟨.cell .word, .cellRef .word 901, .cellRef⟩ rfl c
    verify ⟨.function .word .word, .closure .word .word (.var 0) [], .closure .nil (.var rfl)⟩
      ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩ rfl c
  let source ← parsed content
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨99⟩) (.cell (.namedData ⟨13⟩)), .word] do
    let proof ← compile (table type) source
    let fragment := proof.evidence.localFragment
    for inserted in [Core.Ty.unit, .namedData ⟨101⟩, .function (.namedData ⟨7⟩) (.cell .word)] do
      have _ := typedInsertion proof.evidence [.bool] [type, type] inserted
      have forward := (fragment.hasType_insert_iff [] proof.compiled.inputs.context.values inserted).mpr proof.evidence.core_hasType
      have _ := (fragment.hasType_insert_iff [] proof.compiled.inputs.context.values inserted).mp forward
      check (decide (Core.infer? (inserted :: proof.compiled.inputs.context.values) (proof.compiled.core.weakenAt 0) =
        some (.product type type))) "value-free nominal type insertion changed"
    let forged : CompiledRuntimeFunction := { proof.compiled with core := .letE (.lambda .word .word (.var 0)) (proof.compiled.core.weakenAt 0) }
    have _ : ¬ RuntimeFunctionCompiles (table type) owner source forged := fun impossible => forgedNotLocal _ impossible.localFragment
    check (decide (Core.infer? forged.inputs.context.values forged.core = some forged.returnType)) "same-typed forged record contrast became trivial"
  for text in ["function f(x:T,c:Bool) returns(T){if(c){return x;}else{return missing;}}",
      "function f(x:T,x:T) returns(T){return x;}",
      "function f(x:T) returns(Bool){return x;}", "function f<T>(x:T) returns(T){return x;}"] do
    check ((compileRuntimeFunction? (table .word) owner (← parsed text)).isNone) "whole guard or unchanged statement boundary disappeared"
  have _ : Core.HasType [.cell .word] (.loadCell (.var 0)) .word := .loadCell (.var rfl) .word
  have _ : ¬ (Core.Expr.loadCell (.var 0)).LocalFragment := by intro impossible; cases impossible
  let invalid ← parsed "function f(x:T,c:Bool) returns(T){if(c){return x;}else{return missing;}}"
  let some actual := bindRuntimeParameters? (table .word) owner invalid.value.signature.parameters.elements
    [⟨.word, w 9, .word⟩, ⟨.bool, .bool true, .bool⟩] | throw (IO.userError "original invalid body parameter binding failed")
  check (decide (evaluateTypedLetReturnTreeWithCost? owner actual.names actual.environment invalid.value.body = some (w 9, 4) ∧
    compileRuntimeFunction? (table .word) owner invalid = none)) "raw selected success replaced whole-source membership evidence"

end Tests
