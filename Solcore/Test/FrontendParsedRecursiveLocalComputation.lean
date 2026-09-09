import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Frontend.RuntimeComputationFunctionCompilation
import Solcore.Frontend.RuntimeApplicationFunctionCompilation
import Solcore.Frontend.LocalComputationProperties
/-! Original syntax carries independent static and raw evidence. Value-free
nominal cases are separate from actual values and their hand-written Core paths. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveLocalComputation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Recursive",by decide⟩],by decide⟩⟩,53⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("f",foreign),("g",id 9),("maker",id 12),("y",id 14),("c",id 15),("p",id 20),("f",id 88)]
private def context (a b c : Core.Ty) : Resolved.Context := [(id 7,a),(foreign,.function b c),(id 9,.function a b),
  (id 12,.function a (.function a b)),(id 14,a),(id 15,.bool),(id 20,.function (.product a .unit) b),(foreign,.bool)]
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.bool true]
private def environment (a : Core.Ty) (x y : Core.Value) : Resolved.Environment := [(id 7,x),(foreign,identity a),
  (id 9,identity a),(id 12,.closure a (.function a a) (.var 1) [identity a]),(id 14,y),(id 15,.bool true),
  (id 20,.closure (.product a .unit) a (.first (.var 0)) []),(foreign,.bool false)]
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def grouped : Nat → String → String | 0,s => s | n+1,s => "(" ++ grouped n s ++ ")"
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-computation.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError s!"parse: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩)) "original full expression span"
  return source
private structure Pure (ctx : Resolved.Context) (s : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names s resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : Resolved.HasType ctx resolved type
private def pureChild (ctx : Resolved.Context) (s : Syntax.Expr) : IO (Pure ctx s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some t,some n => return ⟨.var localId,.var n,t,by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original row")
      | _ => throw (IO.userError "original name")
  | ⟨_,.group inner⟩ =>
      let a ← pureChild ctx inner; return ⟨a.resolved,a.core,a.type,by rw [shape]; exact .group a.resolution,a.lowered,a.typing⟩
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,.unit,.unit,by rw [shape]; exact .unit,.unit,.unit⟩
  | ⟨span,.tuple ⟨tupleSpan,[left,right]⟩⟩ =>
      check (span.contains tupleSpan && tupleSpan.contains left.span && tupleSpan.contains right.span && decide (left.span.endByte ≤ right.span.startByte)) "tuple child spans/order"
      let a ← pureChild ctx left; let b ← pureChild ctx right
      return ⟨.pair a.resolved b.resolved,.pair a.core b.core,.product a.type b.type,
        by rw [shape]; exact .pair a.resolution b.resolution,.pair a.lowered b.lowered,.pair a.typing b.typing⟩
  | ⟨_,.binary left ⟨_,.subtract⟩ right⟩ =>
      let a ← pureChild ctx left; let b ← pureChild ctx right
      if atWord : a.type = .word then
        if btWord : b.type = .word then return ⟨.binary .wordSub a.resolved b.resolved,.binary .wordSub a.core b.core,.word,
          by rw [shape]; exact .subtract a.resolution b.resolution,.binary a.lowered b.lowered,
          .binary (show Resolved.HasType ctx a.resolved .word from atWord ▸ a.typing) (show Resolved.HasType ctx b.resolved .word from btWord ▸ b.typing)⟩
        else throw (IO.userError "right Word")
      else throw (IO.userError "left Word")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← pureChild ctx guard; let a ← pureChild ctx yes; let b ← pureChild ctx no
      if gt : g.type = .bool then
        if same : b.type = a.type then return ⟨.ifE g.resolved a.resolved b.resolved,.ifE g.core a.core b.core,a.type,
          by rw [shape]; exact .conditional g.resolution a.resolution b.resolution,
          .ifE g.lowered a.lowered b.lowered,.ifE (gt ▸ g.typing) a.typing (same ▸ b.typing)⟩
        else throw (IO.userError "whole arms")
      else throw (IO.userError "Bool guard")
  | _ => throw (IO.userError "outside independent pure fixture")
termination_by sizeOf s
private structure Static (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates names ctx s core type
  typing : RecursiveLocalComputationHasType names ctx s type
private def statics (ctx : Resolved.Context) (s : Syntax.Expr) : IO (Static ctx s) := do
  match shape : s with
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span && decide (span.startByte < inner.span.startByte ∧ inner.span.endByte < span.endByte)) "original group not erased from AST"
      let c ← statics ctx inner
      return ⟨c.core,c.type,by rw [shape]; exact .group c.elaboration,by rw [shape]; exact .group c.typing⟩
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte ≤ argsSpan.startByte)) "original call children/spans/order"
      let f ← statics ctx fn; let a ← statics ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,
            by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "function type")
  | _ => let p ← pureChild ctx s; return ⟨p.core,p.type,.pure p.resolution p.lowered p.typing,.pure (p.resolution.reflects_type p.typing)⟩
termination_by sizeOf s
private def staticCheck (a b c : Core.Ty) (text : String) (core : Core.Expr) (type : Core.Ty) (old : Bool := false) : IO Unit := do
  let s ← parsed text; let ctx := context a b c; let p ← statics ctx s
  have _ := elaborateRecursiveLocalComputation?_iff.mp (elaborateRecursiveLocalComputation?_iff.mpr p.elaboration)
  have _ := recursiveLocalComputationHasType_iff_elaborates.mp p.typing
  have _ := recursiveLocalComputationHasType_iff_elaborates.mpr ⟨p.core,p.elaboration⟩
  have _ := p.elaboration.core_hasType
  check (decide (p.core = core ∧ p.type = type ∧ elaborateRecursiveLocalComputation? names ctx s = some (core,type) ∧
    elaborateLocalComputation? names ctx s = (if old then some (core,type) else none) ∧
    names.lookup? "f" = some foreign ∧ ctx.lookup? foreign = some (.function b c))) "exact independent static result or old boundary"
private structure PureCost (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, LocalExpressionEvaluatesWithCost names env store s value store cost
private def pureCost (env : Resolved.Environment) (s : Syntax.Expr) : IO (PureCost env s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : env.lookup? localId with
          | some v => return ⟨v,1,fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _ => throw (IO.userError "actual row missing")
      | _ => throw (IO.userError "actual name missing")
  | ⟨_,.group inner⟩ =>
      let a ← pureCost env inner; return ⟨a.value,a.cost,fun store => by rw [shape]; exact .group (a.evidence store)⟩
  | _ => throw (IO.userError "outside actual pure fixture")
termination_by sizeOf s
private structure Actual (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost names env store s value store cost
private def actual (env : Resolved.Environment) (s : Syntax.Expr) : IO (Actual env s) := do
  match shape : s with
  | ⟨_,.group inner⟩ =>
      let a ← actual env inner; return ⟨a.value,a.cost,fun store => by rw [shape]; exact .group (a.evidence store)⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← actual env fn; let a ← actual env arg
      match closure : f.value with
      | .closure _ _ (.var index) captured =>
          match found : (a.value::captured)[index]? with
          | some v => return ⟨v,f.cost+a.cost+1+3,fun store => by
              rw [shape]; exact .application (closure ▸ f.evidence store) (a.evidence store) (.cons (.var found) .refl)⟩
          | _ => throw (IO.userError "actual body index")
      | _ => throw (IO.userError "outside independent actual body")
  | _ => let p ← pureCost env s; return ⟨p.value,p.cost,fun store => .pure (p.evidence store)⟩
termination_by sizeOf s
private def exercise (type : Core.Ty) (x y : Core.Value) (text : String) (core : Core.Expr) (value : Core.Value) (cost : Nat)
    (manual : ∀ store k, Core.Steps cost ⟨.eval core (environment type x y).values,k,store⟩ ⟨.ret value,k,store⟩)
    (legacyPure : Bool := false) : IO Unit := do
  let s ← parsed text; let ctx := context type type type; let env := environment type x y
  let p ← statics ctx s; let r ← actual env s
  if exactResult : p.core = core ∧ p.type = type ∧ r.value = value ∧ r.cost = cost then
    have e : RecursiveLocalComputationElaborates names ctx s core type := by simpa only [exactResult.1,exactResult.2.1] using p.elaboration
    have ids : env.ids = ctx.ids := rfl
    have fragment := e.core_fragment
    have _ := fragment.weakenAt 3
    for store in [[],[.bool true,.word (Core.Word.ofNatModulo 71)]] do
      have counted : RecursiveLocalComputationEvaluatesWithCost names env store s value store cost := by simpa only [exactResult.2.2.1,exactResult.2.2.2] using r.evidence store
      have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨cost,counted⟩
      have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mp raw
      have coreRaw := (e.evaluates_iff ids).mp raw
      have _ := (e.evaluates_iff ids).mpr coreRaw
      have _ := counted.deterministic ((e.evaluatesWithCost_iff_steps ids).mpr (manual store []))
      have _ := (e.evaluatesWithCost_iff_steps ids).mp counted
      let pending : List Core.Frame := [.letBody .unit []]
      have _ := counted.toStepsWithContinuation e ids pending
      if legacyPure then
        let old ← pureChild ctx s; let oldCost ← pureCost env s
        have oldElab : LocalComputationElaborates names ctx s old.core old.type := .pure old.resolution old.lowered old.typing
        have oldCounted : LocalComputationEvaluatesWithCost names env store s oldCost.value store oldCost.cost := .pure (oldCost.evidence store)
        have _ := elaborateRecursiveLocalComputation?_iff.mpr oldElab.toRecursiveLocalComputation
        have _ := counted.deterministic oldCounted.toRecursiveLocalComputation
        check (decide (old.core = core ∧ old.type = type ∧ elaborateLocalComputation? names ctx s = some (core,type))) "pure/group overlap or old success changed"
      for fuel in List.range (cost+2) do
        have _ := (manual store []).runStateful_done_iff (fuel := fuel)
        match Core.runStateful fuel (.initial core env.values store) with
        | .done v t => check (decide (cost ≤ fuel ∧ v = value ∧ t = store)) "literal actual result/cost"
        | .outOfFuel cp => check (decide (fuel < cost ∧ Core.runStateful (cost-fuel) cp = .done value store)) "genuine checkpoint residual"
        | .fault _ _ => throw (IO.userError "actual smoke fault")
      for cutoff in [0,1,3,8] do
        let leading := env.values.take cutoff; let suffix := env.values.drop cutoff
        have same : leading ++ suffix = env.values := List.take_append_drop cutoff env.values
        for inserted in [Core.Value.cellRef .word 99,.closure .bool .word (.var 19) [.unit]] do
          have original : Core.Evaluates (leading ++ suffix) store core value store := by rw [same]; exact coreRaw
          have changed := (fragment.evaluates_insert_iff leading suffix inserted).mpr original
          have _ := (fragment.evaluates_insert_iff leading suffix inserted).mp changed
          have paired : ∀ k, Core.Steps cost ⟨.eval core (leading++suffix),k,store⟩ ⟨.ret value,k,store⟩ ∧
              Core.Steps cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),k,store⟩ ⟨.ret value,k,store⟩ := by
            obtain ⟨n,paths⟩ := fragment.insertion_paths leading suffix inserted original
            have fixedCost : n = cost := ((paths []).1.final_unique (by simpa only [same,env,Core.State.final] using manual store [])).1
            exact fixedCost ▸ paths
          have _ := (paired pending).2
          check (decide (Core.runStateful cost ⟨.eval (core.weakenAt cutoff) (leading++inserted::suffix),pending,store⟩ =
            .outOfFuel ⟨.ret value,pending,store⟩)) "inserted caller pending endpoint"
  else throw (IO.userError "independent static/raw/manual expectations disagree")
private theorem invoke {env : Core.Environment} {fn arg : Core.Expr} {a b : Core.Ty} {body : Core.Expr}
    {captured : Core.Environment} {v result : Core.Value} {fc ac : Nat}
    (f : ∀ store k, Core.Steps fc ⟨.eval fn env,k,store⟩ ⟨.ret (.closure a b body captured),k,store⟩)
    (x : ∀ store k, Core.Steps ac ⟨.eval arg env,k,store⟩ ⟨.ret v,k,store⟩)
    (resultPath : ∀ store, Core.Steps 1 (.initial body (v::captured) store) (.final result store)) :
    ∀ store k, Core.Steps (fc+ac+1+3) ⟨.eval (.apply fn arg) env,k,store⟩ ⟨.ret result,k,store⟩ :=
  fun store _ => CostStepComposition.apply (f store _) (x store _) (resultPath store)
end ParsedRecursiveLocalComputation
open ParsedRecursiveLocalComputation
def frontendParsedRecursiveLocalComputationTests : IO Unit := do
  for a in [Core.Ty.unit,.word,.namedData ⟨7⟩,.function (.namedData ⟨8⟩) (.namedData ⟨9⟩)] do
    for b in [Core.Ty.bool,.unit,.namedData ⟨11⟩] do
      for c in [Core.Ty.word,.cell .word,.function (.namedData ⟨12⟩) (.namedData ⟨13⟩)] do
        for depth in [0,3,17,40] do
          for (s,core,t) in [("f(g(x))",.apply (.var 1) (call 2 0),c),
              ("(maker(x))(y)",.apply (call 3 0) (.var 4),b),
              ("f((maker(x))(y))",.apply (.var 1) (.apply (call 3 0) (.var 4)),c),
              ("f(p((x,())))",.apply (.var 1) (.apply (.var 6) (.pair (.var 0) .unit)),c),
              ("(c ? f : f)(g(c ? x : y))",.apply (.ifE (.var 5) (.var 1) (.var 1)) (.apply (.var 2) (.ifE (.var 5) (.var 0) (.var 4))),c)] do
            staticCheck a b c (grouped depth s) core t
        staticCheck a b c "((x))" (.var 0) a true
        staticCheck a b c "g(x)" (call 2 0) b true
  staticCheck .word .word .word "f(g(x - y))" (.apply (.var 1) (.apply (.var 2) (.binary .wordSub (.var 0) (.var 4)))) .word
  for (type,x,y) in [(Core.Ty.unit,Core.Value.unit,Core.Value.unit),(.word,.word (Core.Word.ofNatModulo 17),.word (Core.Word.ofNatModulo 5))] do
    let leaf (index : Nat) (v : Core.Value) (found : (environment type x y).values[index]? = some v) :
        ∀ store k, Core.Steps 1 ⟨.eval (.var index) (environment type x y).values,k,store⟩ ⟨.ret v,k,store⟩ := fun _ _ => .cons (.var found) .refl
    let gx := invoke (leaf 2 (identity type) rfl) (leaf 0 x rfl) (fun _ => .cons (.var rfl) .refl)
    let fx := invoke (leaf 1 (identity type) rfl) gx (fun _ => .cons (.var rfl) .refl)
    let maker := invoke (leaf 3 (.closure type (.function type type) (.var 1) [identity type]) rfl) (leaf 0 x rfl) (fun _ => .cons (.var rfl) .refl)
    let applied := invoke maker (leaf 4 y rfl) (fun _ => .cons (.var rfl) .refl)
    exercise type x y "((x))" (.var 0) x 1 (leaf 0 x rfl) true
    exercise type x y "g(x)" (call 2 0) x 6 gx
    for depth in [0,5,23] do
      exercise type x y (grouped depth "f(g(x))") (.apply (.var 1) (call 2 0)) x 11 fx
      exercise type x y (grouped depth "(maker(x))(y)") (.apply (call 3 0) (.var 4)) y 11 applied
    exercise type x y "f((maker(x))(y))" (.apply (.var 1) (.apply (call 3 0) (.var 4))) y 16
      (invoke (leaf 1 (identity type) rfl) applied (fun _ => .cons (.var rfl) .refl))
  for text in ["f(g(x)) + x","(g(x),x)","c ? f(g(x)) : x","!g(x)","f()","f(x,y)","f(g(Missing))",
      "x(y)","f(c)","g(c ? x : Missing)","(lam(z: Word){return z;})(x)"] do
    let s ← parsed text
    check ((elaborateRecursiveLocalComputation? names (context .word .word .word) s).isNone) "outside recursive-call profile"
  let sourceText := "function example(f:F,g:F,x:A) returns(A){return f(g(x));}"
  let file : Syntax.SourceFile := ⟨⟨.main,"unchanged-entry.sol"⟩,sourceText⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "whole lexer")
  let .ok decl next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "whole parser")
  let ts : TypeNameTable := [(["F"],.function .word .word),(["A"],.word)]
  let some inputs := declareRuntimeParameters? ts owner decl.value.signature.parameters.elements | throw (IO.userError "valid original parameters")
  let [⟨_,.returnStmt (some expression)⟩] := decl.value.body.value | throw (IO.userError "original singleton body")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (interpretRuntimeFunctionHeader? ts decl.value.signature = some .word) &&
    decide (inputs.names = [("x",⟨owner,2⟩),("g",⟨owner,1⟩),("f",⟨owner,0⟩)] ∧ inputs.context =
      [(⟨owner,2⟩,.word),(⟨owner,1⟩,.function .word .word),(⟨owner,0⟩,.function .word .word)] ∧
      elaborateRecursiveLocalComputation? inputs.names inputs.context expression = some (.apply (.var 2) (call 1 0),.word)) &&
    (elaborateLocalComputationReturnTree? ts owner inputs decl.value.body).isNone &&
    (compileRuntimeFunction? ts owner decl).isNone && (compileRuntimeApplicationFunction? ts owner decl).isNone &&
    (compileRuntimeComputationFunction? ts owner decl).isNone) "valid original header/rows and recursive child did not retain old body/entry boundary"
end Tests
