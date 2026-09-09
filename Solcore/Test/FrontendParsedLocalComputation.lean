import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalComputationProperties
import Solcore.Frontend.LocalComputationEvaluationProperties
import Solcore.Frontend.LocalComputationExecutionProperties
import Solcore.Frontend.LocalComputationInsertionProperties

/-! Original parsed children supply independent exact static and raw evidence.
Manual Core paths, not checker outputs, fix each runtime value and cost. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalComputation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Computation", by decide⟩], by decide⟩⟩, 50⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def fid : Resolved.LocalId := ⟨{ owner with declarationIndex := 91 }, 302⟩
private def names : LocalNameTable := [("x", id 7), ("f", fid), ("c", id 14), ("y", id 9), ("f", id 88)]
private def context (a b : Core.Ty) : Resolved.Context :=
  [(id 7, a), (fid, .function a b), (id 14, .bool), (id 9, a), (fid, .bool)]
private def identity (type : Core.Ty) : Core.Value := .closure type type (.var 0) [.bool true]
private def environment (type : Core.Ty) (x y : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(id 7, x), (fid, identity type), (id 14, .bool choice), (id 9, y), (fid, .bool false)]
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main, "local-computation.sol"⟩, text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError s!"original expression did not parse: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) s!"original complete span changed: {text}"
  return source
private structure Pure (ctx : Resolved.Context) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names source resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : Resolved.HasType ctx resolved type
private def pureChild (ctx : Resolved.Context) (source : Syntax.Expr) : IO (Pure ctx source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some type, some index => return ⟨.var localId, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _, _ => throw (IO.userError "original context missing")
      | none => throw (IO.userError "original name missing")
  | ⟨_, .group inner⟩ =>
      let a ← pureChild ctx inner
      return ⟨a.resolved, a.core, a.type, by rw [original]; exact .group a.resolution, a.lowered, a.typing⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, .unit, by rw [original]; exact .unit, .unit, .unit⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← pureChild ctx left; let b ← pureChild ctx right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        by rw [original]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← pureChild ctx left; let b ← pureChild ctx right
      if ta : a.type = .word then
        if bt : b.type = .word then return ⟨.binary .wordSub a.resolved b.resolved, .binary .wordSub a.core b.core, .word,
          by rw [original]; exact .subtract a.resolution b.resolution, .binary a.lowered b.lowered,
          .binary (show Resolved.HasType ctx a.resolved .word from ta ▸ a.typing)
            (show Resolved.HasType ctx b.resolved .word from bt ▸ b.typing)⟩
        else throw (IO.userError "right Word mismatch")
      else throw (IO.userError "left Word mismatch")
  | ⟨_, .conditional condition _ yes _ no⟩ =>
      let c ← pureChild ctx condition; let a ← pureChild ctx yes; let b ← pureChild ctx no
      if ct : c.type = .bool then
        if bt : b.type = a.type then return ⟨.ifE c.resolved a.resolved b.resolved, .ifE c.core a.core b.core, a.type,
          by rw [original]; exact .conditional c.resolution a.resolution b.resolution,
          .ifE c.lowered a.lowered b.lowered, .ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole arms differ")
      else throw (IO.userError "guard mismatch")
  | _ => throw (IO.userError "outside pure certificate")
termination_by sizeOf source
private structure Static (ctx : Resolved.Context) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : LocalComputationElaborates names ctx source core type
  typing : LocalComputationHasType names ctx source type
private def staticChild (ctx : Resolved.Context) (source : Syntax.Expr) : IO (Static ctx source) := do
  match original : source with
  | ⟨_, .call callee ⟨argsSpan, [argument]⟩⟩ =>
      check (source.span.contains callee.span && source.span.contains argsSpan && argsSpan.contains argument.span &&
        decide (callee.span.endByte ≤ argsSpan.startByte)) "original call delimiter/order changed"
      let f ← pureChild ctx callee; let a ← pureChild ctx argument
      match shape : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core, output,
            by rw [original]; exact .application (.call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)),
            by rw [original]; exact .application (.call (f.resolution.reflects_type (shape ▸ f.typing)) (a.resolution.reflects_type (same ▸ a.typing)))⟩
          else throw (IO.userError "argument mismatch")
      | _ => throw (IO.userError "callee not Function")
  | _ =>
      let p ← pureChild ctx source
      return ⟨p.core, p.type, .pure p.resolution p.lowered p.typing, .pure (p.resolution.reflects_type p.typing)⟩
private def staticCheck (input output : Core.Ty) (text : String) (core : Core.Expr) (type : Core.Ty) (application : Bool) : IO Unit := do
  let source ← parsed text; let ctx := context input output; let p ← staticChild ctx source
  have _ := elaborateLocalComputation?_iff.mp (elaborateLocalComputation?_iff.mpr p.elaboration)
  have _ := localComputationHasType_iff_elaborates.mp p.typing
  have _ := localComputationHasType_iff_elaborates.mpr ⟨p.core, p.elaboration⟩
  have _ := p.elaboration.core_hasType
  check (decide (p.core = core ∧ p.type = type ∧ elaborateLocalComputation? names ctx source = some (core, type) ∧
    elaborateLocalExpression? names ctx source = (if application then none else some (core, type)) ∧
    elaborateLocalFunctionApplication? names ctx source = (if application then some (core, type) else none) ∧
    names.lookup? "f" = some fid ∧ ctx.lookup? fid = some (.function input output))) "exact static union or old boundary differs"
private structure PureCost (env : Resolved.Environment) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, LocalExpressionEvaluatesWithCost names env store source value store cost
private def pureCost (env : Resolved.Environment) (source : Syntax.Expr) : IO (PureCost env source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : env.lookup? localId with
          | some value => return ⟨value, 1, fun _ => by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | none => throw (IO.userError "actual value missing")
      | none => throw (IO.userError "actual name missing")
  | ⟨_, .group inner⟩ =>
      let a ← pureCost env inner
      return ⟨a.value, a.cost, fun s => by rw [original]; exact .group (a.evidence s)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, fun _ => by rw [original]; exact .unit⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← pureCost env left; let b ← pureCost env right
      return ⟨.pair a.value b.value, a.cost+b.cost+3, fun s => by rw [original]; exact .pair (a.evidence s) (b.evidence s)⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← pureCost env left; let b ← pureCost env right
      match av : a.value, bv : b.value with
      | .word x, .word y => return ⟨.word (x.sub y), a.cost+b.cost+3,
          fun s => by rw [original]; exact .subtract (av ▸ a.evidence s) (bv ▸ b.evidence s)⟩
      | _, _ => throw (IO.userError "raw subtraction needs Words")
  | ⟨_, .conditional condition _ yes _ no⟩ =>
      let c ← pureCost env condition
      match selected : c.value with
      | .bool true =>
          let a ← pureCost env yes
          return ⟨a.value, c.cost+a.cost+2, fun s => by rw [original]; exact .ifTrue (selected ▸ c.evidence s) (a.evidence s)⟩
      | .bool false =>
          let b ← pureCost env no
          return ⟨b.value, c.cost+b.cost+2, fun s => by rw [original]; exact .ifFalse (selected ▸ c.evidence s) (b.evidence s)⟩
      | _ => throw (IO.userError "raw guard needs Bool")
  | _ => throw (IO.userError "outside independent raw fixture")
termination_by sizeOf source
private structure Actual (env : Resolved.Environment) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  raw : ∀ store, LocalComputationEvaluates names env store source value store
  costed : ∀ store, LocalComputationEvaluatesWithCost names env store source value store cost
private def actual (env : Resolved.Environment) (source : Syntax.Expr) : IO (Actual env source) := do
  match original : source with
  | ⟨_, .call callee ⟨_, [argument]⟩⟩ =>
      let f ← pureCost env callee; let a ← pureCost env argument
      match shape : f.value with
      | .closure _ _ (.var 0) _ => return ⟨a.value, f.cost+a.cost+1+3,
          fun s => by rw [original]; exact .application (.call (shape ▸ (f.evidence s).erase) (a.evidence s).erase (.var rfl)),
          fun s => by rw [original]; exact .application (.call (shape ▸ f.evidence s) (a.evidence s) (.cons (.var rfl) .refl))⟩
      | _ => throw (IO.userError "not the independently supplied identity body")
  | _ =>
      let p ← pureCost env source
      return ⟨p.value, p.cost, fun s => .pure (p.evidence s).erase, fun s => .pure (p.evidence s)⟩
private def exercise (type : Core.Ty) (x y : Core.Value) (choice : Bool) (text : String)
    (core : Core.Expr) (resultType : Core.Ty) (value : Core.Value) (cost : Nat)
    (manual : ∀ store k, Core.Steps cost ⟨.eval core (environment type x y choice).values, k, store⟩ ⟨.ret value, k, store⟩) : IO Unit := do
  let source ← parsed text; let ctx := context type type; let env := environment type x y choice
  let p ← staticChild ctx source; let r ← actual env source
  if exactResult : p.core = core ∧ p.type = resultType ∧ r.value = value ∧ r.cost = cost then
    have e : LocalComputationElaborates names ctx source core resultType := by simpa only [exactResult.1, exactResult.2.1] using p.elaboration
    have ids : env.ids = ctx.ids := rfl
    for store in [[], [.bool true, .word (Core.Word.ofNatModulo 71)]] do
      have raw : LocalComputationEvaluates names env store source value store := exactResult.2.2.1 ▸ r.raw store
      have counted : LocalComputationEvaluatesWithCost names env store source value store cost := by
        simpa only [exactResult.2.2.1, exactResult.2.2.2] using r.costed store
      have _ := localComputationEvaluates_iff_exists_cost.mp raw
      have _ := localComputationEvaluates_iff_exists_cost.mpr ⟨cost, counted⟩
      have coreRaw := (e.evaluates_iff ids).mp raw
      have _ := (e.evaluates_iff ids).mpr coreRaw
      have _ := counted.deterministic ((e.evaluatesWithCost_iff_steps ids).mpr (manual store []))
      have _ := (e.evaluatesWithCost_iff_steps ids).mp counted
      let pending : List Core.Frame := [.letBody .unit []]
      have _ := counted.toStepsWithContinuation e ids pending
      for cutoff in [0, 2] do
        let leading := env.values.take cutoff; let suffix := env.values.drop cutoff
        have same : leading ++ suffix = env.values := List.take_append_drop cutoff env.values
        let leftTypes := ctx.values.take cutoff; let rightTypes := ctx.values.drop cutoff
        for insertedType in [Core.Ty.namedData ⟨999⟩, .function (.namedData ⟨7⟩) (.namedData ⟨8⟩)] do
          have typed : Core.HasType (leftTypes ++ rightTypes) core resultType := by simpa only [leftTypes, rightTypes, List.take_append_drop] using e.core_hasType
          have added := (e.core_hasType_insert_iff leftTypes rightTypes insertedType).mpr typed
          have _ := (e.core_hasType_insert_iff leftTypes rightTypes insertedType).mp added
        for inserted in [Core.Value.cellRef .word 99, .closure .bool .word (.var 19) [.unit], .bool false] do
          have originalRaw : Core.Evaluates (leading ++ suffix) store core value store := by rw [same]; exact coreRaw
          have changed := (e.core_evaluates_insert_iff leading suffix inserted).mpr originalRaw
          have _ := (e.core_evaluates_insert_iff leading suffix inserted).mp changed
          have paired : ∀ k, Core.Steps cost ⟨.eval core (leading ++ suffix), k, store⟩ ⟨.ret value, k, store⟩ ∧
              Core.Steps cost ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩ ⟨.ret value, k, store⟩ := by
            obtain ⟨n, paths⟩ := e.core_insertion_paths leading suffix inserted originalRaw
            have count : n = cost := ((paths []).1.final_unique (by simpa only [same, env, Core.State.final] using manual store [])).1
            exact count ▸ paths
          for fuel in List.range (cost+2) do
            have _ := (paired []).2.runStateful_done_iff (fuel := fuel)
            match Core.runStateful fuel (.initial (core.weakenAt leading.length) (leading ++ inserted :: suffix) store) with
            | .done v s => check (decide (cost ≤ fuel ∧ v = value ∧ s = store)) "manual value/store/cost differs"
            | .outOfFuel _ => check (decide (fuel < cost)) "exact threshold differs"
            | .fault _ _ => throw (IO.userError "unused inserted value executed")
          check (decide (Core.runStateful cost ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix), pending, store⟩ =
            .outOfFuel ⟨.ret value, pending, store⟩)) "pending endpoint was treated as final"
  else throw (IO.userError "independent static/raw expected result differs")
end ParsedLocalComputation
open ParsedLocalComputation
def frontendParsedLocalComputationTests : IO Unit := do
  for a in [Core.Ty.unit, .word, .namedData ⟨7⟩, .function (.namedData ⟨8⟩) (.namedData ⟨9⟩)] do
    for b in [Core.Ty.bool, .unit, .namedData ⟨11⟩] do
      staticCheck a b "x" (.var 0) a false
      staticCheck a b "((x))" (.var 0) a false
      staticCheck a b "()" .unit .unit false
      staticCheck a b "(x,())" (.pair (.var 0) .unit) (.product a .unit) false
      staticCheck a b "c ? x : y" (.ifE (.var 2) (.var 0) (.var 3)) a false
      for text in ["f(x)", "((f))(((x)))"] do staticCheck a b text (.apply (.var 1) (.var 0)) b true
      staticCheck a b "(c ? f : f)(c ? x : y)" (.apply (.ifE (.var 2) (.var 1) (.var 1)) (.ifE (.var 2) (.var 0) (.var 3))) b true
  staticCheck .word .word "x - y" (.binary .wordSub (.var 0) (.var 3)) .word false
  for (type, x, y) in [(Core.Ty.unit, Core.Value.unit, Core.Value.unit),
      (.word, .word (Core.Word.ofNatModulo 17), .word (Core.Word.ofNatModulo 5))] do
    for choice in [false, true] do
      exercise type x y choice "x" (.var 0) type x 1 (fun _ _ => .cons (.var rfl) .refl)
      exercise type x y choice "()" .unit .unit .unit 1 (fun _ _ => .cons .unit .refl)
      exercise type x y choice "(x,())" (.pair (.var 0) .unit) (.product type .unit) (.pair x .unit) 5
        (fun _ _ => .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .unit (.cons .applyPair .refl)))))
      exercise type x y choice "c ? x : y" (.ifE (.var 2) (.var 0) (.var 3)) type (if choice then x else y) 4
        (by
          intro s k
          cases choice with
          | false => exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons (.var rfl) .refl)))
          | true => exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl))))
      for text in ["f(x)", "((f))(((x)))"] do
        exercise type x y choice text (.apply (.var 1) (.var 0)) type x 6
          (fun _ _ => .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (.cons (.var rfl) .refl))))))
      exercise type x y choice "(c ? f : f)(c ? x : y)" (.apply (.ifE (.var 2) (.var 1) (.var 1)) (.ifE (.var 2) (.var 0) (.var 3)))
        type (if choice then x else y) 12 (by
          intro s k
          cases choice <;> apply CostStepComposition.apply (functionCost := 4) (argumentCost := 4) (bodyCost := 1)
          all_goals
            first
            | exact .cons (.var rfl) .refl
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl)))
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons (.var rfl) .refl))))
  exercise .word (.word (Core.Word.ofNatModulo 17)) (.word (Core.Word.ofNatModulo 5)) true "x - y"
    (.binary .wordSub (.var 0) (.var 3)) .word (.word (Core.Word.ofNatModulo 12)) 5
    (fun _ _ => .cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight (.cons (.var rfl) (.cons (.applyBinary rfl) .refl)))))
  for text in ["f(f(x))", "(f(x))", "x + f(x)", "(lam(z: Word){return z;})(x)"] do
    let source ← parsed text
    check (decide (elaborateLocalComputation? names (context .word .word) source = none)) "union became a recursive expression profile"
end Tests
