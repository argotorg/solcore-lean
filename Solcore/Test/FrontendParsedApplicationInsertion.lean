import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalFunctionApplicationProperties
import Solcore.Frontend.LocalFunctionApplicationExactInsertionProperties

/-! Parsed source provenance is independent of the static and runtime insertion
contexts. Nominal checking supplies no actual values; the small runtime grid
uses explicit identity closures and manually counted child transitions. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedApplicationInsertion
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Insertion", by decide⟩], by decide⟩⟩, 49⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def foreign : Resolved.LocalId := ⟨{ owner with declarationIndex := 77 }, 301⟩
private def names : LocalNameTable := [("f", id 7), ("c", foreign), ("x", id 2), ("g", id 19), ("y", id 3), ("f", id 80)]
private def context (input output : Core.Ty) : Resolved.Context :=
  [(id 90, .unit), (id 7, .function input output), (foreign, .bool), (id 2, input),
    (id 19, .function input output), (id 3, input), (id 7, .bool)]
private def fnCore (conditional : Bool) : Core.Expr :=
  if conditional then .ifE (.var 2) (.var 1) (.var 4) else .var 1
private def argCore (conditional : Bool) : Core.Expr :=
  if conditional then .ifE (.var 2) (.var 3) (.var 5) else .var 3
private def target (fc ac : Bool) := Core.Expr.apply (fnCore fc) (argCore ac)
private def childCost (conditional : Bool) : Nat := if conditional then 4 else 1
private def cost (fc ac : Bool) := childCost fc + childCost ac + 1 + 3
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main, "application-insertion.sol"⟩, text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing failed")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError s!"expression did not parse: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) "original expression span or diagnostics changed"
  return source
private structure Child (ctx : Resolved.Context) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names source resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : Resolved.HasType ctx resolved type
private def child (ctx : Resolved.Context) (source : Syntax.Expr) : IO (Child ctx source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some type, some index => return ⟨.var localId, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _, _ => throw (IO.userError "original context row absent")
      | none => throw (IO.userError "original name absent")
  | ⟨_, .group inner⟩ =>
      let a ← child ctx inner
      return ⟨a.resolved, a.core, a.type, by rw [original]; exact .group a.resolution, a.lowered, a.typing⟩
  | ⟨_, .conditional condition _ yes _ no⟩ =>
      let c ← child ctx condition; let a ← child ctx yes; let b ← child ctx no
      if ct : c.type = .bool then
        if bt : b.type = a.type then return ⟨.ifE c.resolved a.resolved b.resolved,
          .ifE c.core a.core b.core, a.type, by rw [original]; exact .conditional c.resolution a.resolution b.resolution,
          .ifE c.lowered a.lowered b.lowered, .ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole arm types differ")
      else throw (IO.userError "guard not Bool")
  | _ => throw (IO.userError "outside independent child fixture")
termination_by sizeOf source
private structure Certified (input output : Core.Ty) (fc ac : Bool) where
  source : Syntax.Expr
  evidence : LocalFunctionApplicationElaborates names (context input output) source (target fc ac) output
private theorem manualTyping (input output : Core.Ty) (fc ac : Bool) (definitions : Core.DataEnvironment) :
    Core.HasType (context input output).values (target fc ac) output definitions := by
  cases fc <;> cases ac <;>
    exact .apply (by first | exact .var rfl | exact .ifE (.var rfl) (.var rfl) (.var rfl))
      (by first | exact .var rfl | exact .ifE (.var rfl) (.var rfl) (.var rfl))
private def staticCheck (input output : Core.Ty) (fc ac : Bool) (text : String) : IO (Certified input output fc ac) := do
  let source ← parsed text; let ctx := context input output
  match original : source with
  | ⟨_, .call callee ⟨argsSpan, [argument]⟩⟩ =>
      check (source.span.contains callee.span && source.span.contains argsSpan && argsSpan.contains argument.span &&
        decide (callee.span.endByte ≤ argsSpan.startByte ∧ argsSpan.startByte < argument.span.startByte ∧
          argument.span.endByte < argsSpan.endByte)) "original delimiter/order changed"
      let f ← child ctx callee; let a ← child ctx argument
      if expected : f.type = .function input output ∧ a.type = input ∧
          f.core = fnCore fc ∧ a.core = argCore ac then
        have evidence : LocalFunctionApplicationElaborates names ctx source (target fc ac) output := by
          rw [original]
          simpa only [target, expected.2.2.1, expected.2.2.2] using
            LocalFunctionApplicationElaborates.call f.resolution f.lowered (expected.1 ▸ f.typing)
              a.resolution a.lowered (expected.2.1 ▸ a.typing)
        check (decide (elaborateLocalFunctionApplication? names ctx source = some (target fc ac, output) ∧
          elaborateLocalExpression? names ctx source = none ∧ names.lookup? "f" = some (id 7) ∧
          ctx.lookup? (id 7) = some (.function input output))) "exact original static provenance/first match changed"
        for cutoff in List.range 8 do
          let leading := ctx.values.take cutoff; let suffix := ctx.values.drop cutoff
          for inserted in [Core.Ty.unit, .word, .namedData ⟨999⟩, .function (.namedData ⟨2⟩) (.namedData ⟨3⟩)] do
            have typing (definitions) : Core.HasType (leading ++ suffix) (target fc ac) output definitions := by
              simpa only [leading, suffix, List.take_append_drop] using manualTyping input output fc ac definitions
            have lifted (definitions) := (evidence.core_hasType_insert_iff leading suffix inserted).mpr (typing definitions)
            have _ (definitions) := (evidence.core_hasType_insert_iff leading suffix inserted).mp (lifted definitions)
            have _ (requestedType definitions) := evidence.core_hasType_insert_iff leading suffix inserted
              (requestedType := requestedType) (definitions := definitions)
            check (decide (Core.infer? (leading ++ inserted :: suffix) ((target fc ac).weakenAt leading.length) = some output))
              "type insertion changed the independent assigned result"
        return ⟨source, evidence⟩
      else throw (IO.userError "independent expected child Core/type differs")
  | _ => throw (IO.userError "original root is not one-argument call")
private def identity (type : Core.Ty) : Core.Value := .closure type type (.var 0) [.bool true]
private def values (type : Core.Ty) (x y : Core.Value) (choice : Bool) : Core.Environment :=
  [.unit, identity type, .bool choice, x, identity type, y, .bool false]
private def result (x y : Core.Value) (choice ac : Bool) := if ac && !choice then y else x
private theorem manualEvaluation (type : Core.Ty) (x y : Core.Value) (choice fc ac : Bool) (store : Core.Store) :
    Core.Evaluates (values type x y choice) store (target fc ac) (result x y choice ac) store := by
  have fn : Core.Evaluates (values type x y choice) store (fnCore fc) (identity type) store := by
    cases fc <;> cases choice <;> first | exact .var rfl | exact .ifTrue (.var rfl) (.var rfl) | exact .ifFalse (.var rfl) (.var rfl)
  have arg : Core.Evaluates (values type x y choice) store (argCore ac) (result x y choice ac) store := by
    cases ac <;> cases choice <;> first | exact .var rfl | exact .ifTrue (.var rfl) (.var rfl) | exact .ifFalse (.var rfl) (.var rfl)
  exact .apply fn arg (.var rfl)
private theorem manualPath (type : Core.Ty) (x y : Core.Value) (choice fc ac : Bool)
    (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (cost fc ac) ⟨.eval (target fc ac) (values type x y choice), k, store⟩
      ⟨.ret (result x y choice ac), k, store⟩ := by
  have fn (frames) : Core.Steps (childCost fc) ⟨.eval (fnCore fc) (values type x y choice), frames, store⟩
      ⟨.ret (identity type), frames, store⟩ := by
    cases fc <;> cases choice <;>
      first | exact .cons (.var rfl) .refl
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl)))
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons (.var rfl) .refl)))
  have arg (frames) : Core.Steps (childCost ac) ⟨.eval (argCore ac) (values type x y choice), frames, store⟩
      ⟨.ret (result x y choice ac), frames, store⟩ := by
    cases ac <;> cases choice <;>
      first | exact .cons (.var rfl) .refl
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl)))
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons (.var rfl) .refl)))
  exact CostStepComposition.apply (fn _) (arg _) (.cons (.var rfl) .refl)
private def actualSmoke (type : Core.Ty) (x y : Core.Value) (choice fc ac : Bool) (text : String) : IO Unit := do
  let original ← staticCheck type type fc ac text
  let env := values type x y choice; let expected := result x y choice ac
  for store in [[], [.word (Core.Word.ofNatModulo 71), .bool true]] do
    for cutoff in List.range 8 do
      let leading := env.take cutoff; let suffix := env.drop cutoff
      have same : leading ++ suffix = env := List.take_append_drop cutoff env
      have raw : Core.Evaluates (leading ++ suffix) store (target fc ac) expected store := by
        simpa only [same] using manualEvaluation type x y choice fc ac store
      have path : Core.Steps (cost fc ac) (.initial (target fc ac) (leading ++ suffix) store) (.final expected store) := by
        simpa only [same, Core.State.initial, Core.State.final, env, expected] using manualPath type x y choice fc ac store []
      for inserted in [Core.Value.bool true, .cellRef .word 93, .closure .word .bool (.var 19) [.cellRef .bool 31], .unit] do
        have lifted := (original.evidence.core_evaluates_insert_iff leading suffix inserted).mpr raw
        have _ := (original.evidence.core_evaluates_insert_iff leading suffix inserted).mp lifted
        have paired : ∃ n, n = cost fc ac ∧ ∀ k,
            Core.Steps n ⟨.eval (target fc ac) (leading ++ suffix), k, store⟩ ⟨.ret expected, k, store⟩ ∧
            Core.Steps n ⟨.eval ((target fc ac).weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩
              ⟨.ret expected, k, store⟩ := by
          obtain ⟨n, paths⟩ := original.evidence.core_insertion_paths leading suffix inserted raw
          exact ⟨n, (path.final_unique (paths []).1).1.symm, paths⟩
        have _ := paired
        have insertedPath := original.evidence.core_steps_insert leading suffix inserted path []
        have _ := original.evidence.core_steps_reflect_insert leading suffix inserted insertedPath []
        have _ := (original.evidence.core_steps_insert_iff leading suffix inserted).mpr path
        have _ := (original.evidence.core_steps_insert_iff leading suffix inserted).mp insertedPath
        let pending : List Core.Frame := [.letBody .unit []]
        have _ := original.evidence.core_steps_insert leading suffix inserted path pending
        have _ := original.evidence.core_steps_reflect_insert leading suffix inserted insertedPath pending
        check (decide (leading ++ suffix = env ∧
          Core.runStateful (cost fc ac) (.initial ((target fc ac).weakenAt leading.length) (leading ++ inserted :: suffix) store) =
            .done expected store)) "actual insertion changed literal value/store/cost"
        check (decide (Core.runStateful (cost fc ac)
          ⟨.eval ((target fc ac).weakenAt leading.length) (leading ++ inserted :: suffix), pending, store⟩ =
            .outOfFuel ⟨.ret expected, pending, store⟩)) "retained continuation endpoint was mistaken for closed completion"
        for fuel in List.range (cost fc ac + 2) do
          have _ := insertedPath.runStateful_done_iff (fuel := fuel)
          match Core.runStateful fuel (.initial ((target fc ac).weakenAt leading.length) (leading ++ inserted :: suffix) store) with
          | .done value finalStore => check (decide (cost fc ac ≤ fuel ∧ value = expected ∧ finalStore = store)) "wrong inserted completion"
          | .outOfFuel _ => check (decide (fuel < cost fc ac)) "wrong inserted exhaustion threshold"
          | .fault _ _ => throw (IO.userError "unused inserted value was executed")
end ParsedApplicationInsertion
open ParsedApplicationInsertion
def frontendParsedApplicationInsertionTests : IO Unit := do
  let fixtures := [(false, false, "f(x)"), (false, false, "((f))(((x)))"),
    (true, false, "(c ? f : g)(x)"), (false, true, "f(c ? x : y)"),
    (true, true, "(c ? (f) : g)(c ? x : (y))"), (false, false, "f /* call */ ( /* arg */ x )")]
  for input in [Core.Ty.unit, .word, .namedData ⟨7⟩, .function (.namedData ⟨2⟩) (.namedData ⟨3⟩)] do
    for output in [Core.Ty.unit, .bool, .namedData ⟨8⟩, .cell .word] do
      for (fc, ac, text) in fixtures do
        let _ ← staticCheck input output fc ac text
  for choice in [false, true] do
    for (fc, ac, text) in fixtures do
      actualSmoke .unit .unit .unit choice fc ac text
      actualSmoke .word (.word (Core.Word.ofNatModulo 9)) (.word (Core.Word.ofNatModulo 14)) choice fc ac text
  for text in ["(lam(z: Word){return z;})(x)", "f(f(x))", "(f(x))"] do
    let source ← parsed text
    check (decide (elaborateLocalFunctionApplication? names (context .word .word) source = none ∧
      elaborateLocalExpression? names (context .word .word) source = none)) "outside child/root profile acquired insertion provenance"
end Tests
