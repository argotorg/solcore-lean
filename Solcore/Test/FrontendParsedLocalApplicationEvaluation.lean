import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties
import Solcore.Core.Safety

/-! Parsed call children and actual closure bodies supply independent evidence.
Expected Core, values, costs and checkpoints are fixed before correspondence. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalApplicationEvaluation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def own : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ApplicationEvaluation", by decide⟩], by decide⟩⟩, 17⟩
private def id (n : Nat) : Resolved.LocalId := ⟨own,n⟩
private def foreign : Resolved.LocalId := ⟨{ own with declarationIndex := 9 },999⟩
private def names : LocalNameTable := [("f",id 7),("f",id 99),("x",id 2),("c",foreign),("g",id 4),("y",id 3)]
private def ctx (input output x : Core.Ty) : Resolved.Context :=
  [(id 2,x),(id 7,.function input output),(foreign,.bool),(id 4,.function input output),(id 3,.word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def env (f g x : Core.Value) (c : Bool) : Resolved.Environment :=
  [(id 2,x),(id 7,f),(foreign,.bool c),(id 4,g),(id 3,w 9)]
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"application-evaluation.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original expression did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩)) s!"original full expression range changed: {text}"
  return source
private structure Child (context : Resolved.Context) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names source resolved
  lowered : Resolved.Lowers context.ids resolved core
  typing : Resolved.HasType context resolved type
private def child (context : Resolved.Context) (source : Syntax.Expr) : IO (Child context source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match typed : context.lookup? localId, indexed : Resolved.LocalScope.index? context.ids localId with
          | some type, some index => return ⟨.var localId,.var index,type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original context row missing")
      | none => throw (IO.userError "original name missing")
  | ⟨_,.group inner⟩ =>
      let a ← child context inner
      return ⟨a.resolved,a.core,a.type,by rw [original]; exact .group a.resolution,a.lowered,a.typing⟩
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,.unit,.unit,by rw [original]; exact .unit,.unit,.unit⟩
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
      let a ← child context left; let b ← child context right
      return ⟨.pair a.resolved b.resolved,.pair a.core b.core,.product a.type b.type,
        by rw [original]; exact .pair a.resolution b.resolution,.pair a.lowered b.lowered,.pair a.typing b.typing⟩
  | ⟨_,.binary left ⟨_,.subtract⟩ right⟩ =>
      let a ← child context left; let b ← child context right
      if ta : a.type = .word then
        if bt : b.type = .word then return ⟨.binary .wordSub a.resolved b.resolved,.binary .wordSub a.core b.core,.word,
          by rw [original]; exact .subtract a.resolution b.resolution,.binary a.lowered b.lowered,
          .binary (show Resolved.HasType context a.resolved .word from ta ▸ a.typing)
            (show Resolved.HasType context b.resolved .word from bt ▸ b.typing)⟩
        else throw (IO.userError "right word type differs")
      else throw (IO.userError "left word type differs")
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← child context condition; let a ← child context yes; let b ← child context no
      if ct : c.type = .bool then
        if bt : b.type = a.type then return ⟨.ifE c.resolved a.resolved b.resolved,.ifE c.core a.core b.core,a.type,
          by rw [original]; exact .conditional c.resolution a.resolution b.resolution,
          .ifE c.lowered a.lowered b.lowered,.ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole branch types differ")
      else throw (IO.userError "whole guard type differs")
  | _ => throw (IO.userError "outside independent static child grammar")
termination_by sizeOf source
private structure Application (context : Resolved.Context) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates names context source core type
private def application (context : Resolved.Context) (source : Syntax.Expr) : IO (Application context source) := do
  match original : source with
  | ⟨_,.call callee ⟨span,[argument]⟩⟩ =>
      check (source.span.contains callee.span && source.span.contains span && span.contains argument.span &&
        decide (callee.span.endByte ≤ span.startByte)) "original call ranges/order changed"
      let f ← child context callee; let a ← child context argument
      match shape : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,by
            rw [original]; exact .call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)⟩
          else throw (IO.userError "single argument type differs")
      | _ => throw (IO.userError "callee is not Function")
  | _ => throw (IO.userError "not a root single-argument call")
private structure Raw (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : LocalExpressionEvaluatesWithCost names environment s source value s cost
private def raw (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) : IO (Raw environment s source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : environment.lookup? localId with
          | some value => return ⟨value,1,by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | none => throw (IO.userError "actual value missing")
      | none => throw (IO.userError "actual name missing")
  | ⟨_,.group inner⟩ =>
      let a ← raw environment s inner
      return ⟨a.value,a.cost,by rw [original]; exact .group a.evidence⟩
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,1,by rw [original]; exact .unit⟩
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
      let a ← raw environment s left; let b ← raw environment s right
      return ⟨.pair a.value b.value,a.cost+b.cost+3,by rw [original]; exact .pair a.evidence b.evidence⟩
  | ⟨_,.binary left ⟨_,.subtract⟩ right⟩ =>
      let a ← raw environment s left; let b ← raw environment s right
      match av : a.value, bv : b.value with
      | .word x,.word y => return ⟨.word (x.sub y),a.cost+b.cost+3,by rw [original]; exact .subtract (av ▸ a.evidence) (bv ▸ b.evidence)⟩
      | _,_ => throw (IO.userError "actual subtraction operands differ")
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← raw environment s condition
      match cv : c.value with
      | .bool true =>
          let a ← raw environment s yes
          return ⟨a.value,c.cost+a.cost+2,by rw [original]; exact .ifTrue (cv ▸ c.evidence) a.evidence⟩
      | .bool false =>
          let b ← raw environment s no
          return ⟨b.value,c.cost+b.cost+2,by rw [original]; exact .ifFalse (cv ▸ c.evidence) b.evidence⟩
      | _ => throw (IO.userError "actual condition is not Bool")
  | _ => throw (IO.userError "selected unsupported child")
termination_by sizeOf source
private structure Body (body : Core.Expr) (actual : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  path : Core.Steps cost (.initial body actual s) (.final value final)
private def bodyPath (body : Core.Expr) (actual : Core.Environment) (s : Core.Store) : IO (Body body actual s) := do
  match original : body, values : actual with
  | .var index,_ =>
      match found : actual[index]? with
      | some value => return ⟨value,s,1,by rw [original]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "actual closure body variable missing")
  | .pair (.var 0) (.var 1),left :: right :: _ => return ⟨.pair left right,s,5,by
      rw [original,values]; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl))))⟩
  | .newCell .word (.var 0),value :: _ => return ⟨.cellRef .word s.length,s ++ [value],3,by
      rw [original,values]; exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))⟩
  | .loadCell (.var 0),.cellRef type location :: _ =>
      match found : s.read? location with
      | some value => return ⟨value,s,3,by rw [original,values]; exact .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell found) .refl))⟩
      | none => throw (IO.userError "actual cell is not allocated")
  | _,_ => throw (IO.userError "outside hand-built actual body paths")
private structure Counted (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : LocalFunctionApplicationEvaluatesWithCost names environment s source value final cost
private def counted (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) : IO (Counted environment s source) := do
  match original : source with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
      let f ← raw environment s callee; let a ← raw environment s argument
      match shape : f.value with
      | .closure _ _ body captured =>
          let b ← bodyPath body (a.value :: captured) s
          return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,by rw [original]; exact .call (shape ▸ f.evidence) a.evidence b.path⟩
      | _ => throw (IO.userError "actual callee is not a closure")
  | _ => throw (IO.userError "not exactly one original argument")
private def verify (text : String) (input output xtype : Core.Ty) (f g x : Core.Value) (c : Bool)
    (expected : Core.Expr) (value : Core.Value) (cost : Nat) (s final : Core.Store) : IO Unit := do
  let source ← parsed text
  let original ← application (ctx input output xtype) source
  let actual ← counted (env f g x c) s source
  check (decide (original.core = expected ∧ original.type = output ∧ actual.value = value ∧ actual.final = final ∧ actual.cost = cost ∧
    elaborateLocalExpression? names (ctx input output xtype) source = none))
    "independent original Core/value/store/cost expectation changed"
  have aligned : (env f g x c).ids = (ctx input output xtype).ids := rfl
  let p := actual.evidence.toSteps original.evidence aligned
  have _ := actual.evidence.erase.deterministic actual.evidence.erase
  have _ := actual.evidence.erase.exists_cost
  have _ := actual.evidence.cost_pos
  have _ := actual.evidence.cost_unique actual.evidence
  let ce := (original.evidence.evaluates_iff aligned).mp actual.evidence.erase
  have _ := (elaborateLocalFunctionApplication?_evaluates_iff original.evidence.complete aligned).mpr ce
  let restored := (original.evidence.evaluatesWithCost_iff_steps aligned).mpr p
  have _ := actual.evidence.deterministic restored
  have _ := (elaborateLocalFunctionApplication?_evaluatesWithCost_iff_steps original.evidence.complete aligned).mpr p
  have _ := (localFunctionApplicationEvaluates_iff_exists_cost).mpr ⟨actual.cost,actual.evidence⟩
  have uniform := (original.evidence.evaluates_iff_exists_uniform_steps aligned).mp actual.evidence.erase
  have _ := (original.evidence.evaluates_iff_exists_uniform_steps aligned).mpr uniform
  for k in [[],[.letBody (.var 0) [w 19]],[.unaryApply .wordNot]] do
    have _ := actual.evidence.toStepsWithContinuation original.evidence aligned k
    pure ()
  let k : List Core.Frame := [.unaryApply .wordNot]
  check (match Core.runStateful cost ⟨.eval expected (env f g x c).values,k,s⟩ with
    | .outOfFuel checkpoint => decide (checkpoint = ⟨.ret value,k,final⟩)
    | .fault error checkpoint => decide (error = .invalidUnaryOperand .wordNot value ∧ checkpoint = ⟨.ret value,k,final⟩)
    | _ => false) "fixed-cost arbitrary continuation endpoint was mistaken for completion"
  for fuel in List.range (cost+3) do
    check (match Core.runStateful fuel (.initial expected (env f g x c).values s) with
      | .done v t => decide (cost ≤ fuel ∧ v = value ∧ t = final)
      | .outOfFuel _ => decide (fuel < cost)
      | _ => false) "closed exact path threshold changed"
  for spent in List.range cost do
    match stopped : Core.runStateful spent (.initial original.core (env f g x c).values s) with
    | .outOfFuel checkpoint =>
        have _ := p.residual_of_outOfFuel stopped
        have _ := Core.runStateful_resume stopped (cost-spent)
        check (decide (Core.runStateful (cost-spent) checkpoint = .done value final)) "actual saved continuation or residual changed"
    | _ => throw (IO.userError "genuine checkpoint missing")
private def fn : Core.Value := .closure .word (.product .word .word) (.pair (.var 0) (.var 1)) [w 7]
private def gn : Core.Value := .closure .word (.product .word .word) (.var 1) [.pair (w 2) (w 9)]
private def mixed : Core.Expr := .apply (.ifE (.var 2) (.var 1) (.var 3)) (.binary .wordSub (.var 0) (.var 4))
private def selected : IO Unit := do
  let source ← parsed "(c ? f : g)(x - y)"
  match source.value with
  | .call callee ⟨span,[⟨argumentSpan,.binary left op right⟩]⟩ =>
      check (decide (callee.span.startByte = 0 ∧ callee.span.endByte = 11 ∧ span.startByte = 11 ∧ span.endByte = 18 ∧
        argumentSpan.startByte = 12 ∧ argumentSpan.endByte = 17 ∧ left.span.startByte = 12 ∧ right.span.startByte = 16 ∧
        op.span.startByte = 14 ∧ op.value = .subtract)) "original nested byte ranges or subtraction spelling changed"
  | _ => throw (IO.userError "original conditional callee/subtraction argument changed shape")
  have ft : Core.ValueHasType fn (.function .word (.product .word .word)) := .closure (.cons .word .nil) (.pair (.var rfl) (.var rfl))
  have gt : Core.ValueHasType gn (.function .word (.product .word .word)) := .closure (.cons (.pair .word .word) .nil) (.var rfl)
  for c in [false,true] do
    have _ : Core.EnvironmentHasTypes (env fn gn (w 14) c).values (ctx .word (.product .word .word) .word).values :=
      .cons .word (.cons ft (.cons .bool (.cons gt (.cons .word .nil))))
    for s in [[],[w 91]] do
      let f := if c then fn else gn
      verify "(c ? f : g)(x - y)" .word (.product .word .word) .word fn gn (w 14) c mixed
        (if c then .pair (w 5) (w 7) else .pair (w 2) (w 9)) (if c then 17 else 13) s s
      check (decide (Core.runStateful 5 (.initial mixed (env fn gn (w 14) c).values s) =
        .outOfFuel ⟨.ret f,[.applyArgument (.binary .wordSub (.var 0) (.var 4)) (env fn gn (w 14) c).values],s⟩)) "function-first caller frame changed"
      let body := if c then Core.Expr.pair (.var 0) (.var 1) else .var 1
      let captured := if c then [w 7] else [.pair (w 2) (w 9)]
      check (decide (Core.runStateful 11 (.initial mixed (env fn gn (w 14) c).values s) =
        .outOfFuel ⟨.ret (w 5),[.applyClosure .word (.product .word .word) body captured],s⟩)) "strict argument or actual captures changed"
private def identity (type : Core.Ty) : Core.Value := .closure type type (.var 0) []
private theorem faultExcludesPath {start stopped : Core.State} {fuel : Nat} {error : Core.MachineFault}
    (fault : Core.runStateful fuel start = .fault error stopped) :
    ¬ ∃ cost value final, Core.Steps cost start (.final value final) := by
  rintro ⟨cost,value,final,path⟩
  by_cases enough : cost ≤ fuel
  · have done := path.runStateful_done_iff.mpr enough
    rw [fault] at done; cases done
  · obtain ⟨checkpoint,exhausted⟩ := path.runStateful_outOfFuel_iff.mpr (Nat.lt_of_not_ge enough)
    rw [fault] at exhausted; cases exhausted
private def effects : IO Unit := do
  for s in [[],[w 23]] do
    verify "f(())" .unit .unit .word (identity .unit) (identity .unit) (w 14) true (.apply (.var 1) .unit) .unit 6 s s
    verify "f((x,y))" (.product .word .word) (.product .word .word) .word (identity (.product .word .word)) (identity (.product .word .word))
      (w 14) true (.apply (.var 1) (.pair (.var 0) (.var 4))) (.pair (w 14) (w 9)) 10 s s
    let allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
    have _ : Core.ValueHasType allocator (.function .word (.cell .word)) := .closure .nil (.newCell (.var rfl) .word)
    verify "f(x)" .word (.cell .word) .word allocator allocator (w 14) true (.apply (.var 1) (.var 0)) (.cellRef .word s.length) 8 s (s ++ [w 14])
  let reader : Core.Value := .closure (.cell .word) .word (.loadCell (.var 0)) []
  have rt : Core.ValueHasType reader (.function (.cell .word) .word) := .closure .nil (.loadCell (.var rfl) .word)
  have _ : Core.EnvironmentHasTypes (env reader reader (.cellRef .word 0) true).values (ctx (.cell .word) .word (.cell .word)).values :=
    .cons .cellRef (.cons rt (.cons .bool (.cons rt (.cons .word .nil))))
  verify "f(x)" (.cell .word) .word (.cell .word) reader reader (.cellRef .word 0) true (.apply (.var 1) (.var 0)) (w 23) 8 [w 23] [w 23]
  check (decide (Core.runStateful 7 (.initial (.apply (.var 1) (.var 0)) (env reader reader (.cellRef .word 0) true).values []) =
    .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩)) "structural value typing fabricated allocated cells"
  let source ← parsed "f(x)"
  let original ← application (ctx (.cell .word) .word (.cell .word)) source
  if exactCore : original.core = .apply (.var 1) (.var 0) then
    have fault : Core.runStateful 7 (.initial original.core (env reader reader (.cellRef .word 0) true).values []) =
        .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩ := by rw [exactCore]; rfl
    have _ : ¬ ∃ value final, LocalFunctionApplicationEvaluates names (env reader reader (.cellRef .word 0) true) [] source value final := by
      rintro ⟨value,final,evaluation⟩
      obtain ⟨cost,evidence⟩ := evaluation.exists_cost
      exact faultExcludesPath fault ⟨cost,value,final,evidence.toSteps original.evidence rfl⟩
    pure ()
  else throw (IO.userError "reader exact Core changed")
private def contrasts : IO Unit := do
  for text in ["(c ? f : missing)(x)","f(c ? x : missing)"] do
    let source ← parsed text
    let actual ← counted (env (identity .word) (identity .word) (w 14) true) [] source
    check (decide (actual.value = w 14 ∧ actual.cost = 9 ∧ actual.final = [] ∧
      elaborateLocalFunctionApplication? names (ctx .word .word .word) source = none)) "raw selected success was mistaken for whole acceptance"
    have _ := actual.evidence.erase
    pure ()
end ParsedLocalApplicationEvaluation
open ParsedLocalApplicationEvaluation
def frontendParsedLocalApplicationEvaluationTests : IO Unit := do
  selected; effects; contrasts
end Tests
