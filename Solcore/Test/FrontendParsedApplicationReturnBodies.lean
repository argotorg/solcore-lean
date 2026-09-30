import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalApplication
import Solcore.Frontend.ReturnBody
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Core.FuelResumptionProperties

/-! Original complete blocks and independent child/body witnesses retain the
same Core, actual stores, costs and saved states as their return-call child. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedApplicationReturnBodies
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ApplicationRunner",by decide⟩],by decide⟩⟩,19⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 3},999⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def inputs (output : Core.Ty) (f shadow : Core.Value)
    (ft : Core.ValueHasType f (.function .word output)) (gt : Core.ValueHasType shadow (.function .word output)) (x : Nat) : LocalInputs :=
  ⟨[⟨"x",id 2,.word,w x,.word⟩,⟨"f",id 7,.function .word output,f,ft⟩,
    ⟨"g",id 91,.function .word output,shadow,gt⟩,⟨"c",foreign,.bool,.bool true,.bool⟩],by
      change [id 2,id 7,id 91,foreign].Nodup; decide⟩
private def parsed (text : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"application-runner.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing failed")
  let .ok source next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original block did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩)) "original full byte range changed"
  return source
private structure Child (s : LocalInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.context.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def child (s : LocalInputs) (source : Syntax.Expr) : IO (Child s source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some localId =>
          match typed : s.context.lookup? localId, indexed : Resolved.LocalScope.index? s.context.ids localId with
          | some type, some index => return ⟨.var localId,.var index,type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original context row missing")
      | none => throw (IO.userError "original name missing")
  | ⟨_,.group inner⟩ =>
      let a ← child s inner
      return ⟨a.resolved,a.core,a.type,by rw [original]; exact .group a.resolution,a.lowered,a.typing⟩
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← child s condition; let a ← child s yes; let b ← child s no
      if ct : c.type = .bool then
        if bt : b.type = a.type then return ⟨.ifE c.resolved a.resolved b.resolved,.ifE c.core a.core b.core,a.type,
          by rw [original]; exact .conditional c.resolution a.resolution b.resolution,
          .ifE c.lowered a.lowered b.lowered,.ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole branch types differ")
      else throw (IO.userError "guard is not Bool")
  | _ => throw (IO.userError "outside independent static child certificate")
termination_by sizeOf source
private structure Application (s : LocalInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates s.names s.context source core type
private def application (s : LocalInputs) (source : Syntax.Expr) : IO (Application s source) := do
  match original : source with
  | ⟨_,.call callee ⟨span,[argument]⟩⟩ =>
      check (source.span.contains callee.span && source.span.contains span && span.contains argument.span &&
        decide (callee.span.endByte ≤ span.startByte)) "original call ranges/order changed"
      let f ← child s callee; let a ← child s argument
      match shape : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,by
            rw [original]; exact .call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)⟩
          else throw (IO.userError "argument type differs")
      | _ => throw (IO.userError "callee is not Function")
  | _ => throw (IO.userError "not exactly one original argument")
private structure Raw (s : LocalInputs) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : LocalExpressionEvaluatesWithCost s.names s.environment store source value store cost
private def raw (s : LocalInputs) (store : Core.Store) (source : Syntax.Expr) : IO (Raw s store source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some localId =>
          match found : s.environment.lookup? localId with
          | some value => return ⟨value,1,by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | none => throw (IO.userError "actual value missing")
      | none => throw (IO.userError "actual name missing")
  | ⟨_,.group inner⟩ =>
      let a ← raw s store inner
      return ⟨a.value,a.cost,by rw [original]; exact .group a.evidence⟩
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← raw s store condition
      match cv : c.value with
      | .bool true =>
          let a ← raw s store yes
          return ⟨a.value,c.cost+a.cost+2,by rw [original]; exact .ifTrue (cv ▸ c.evidence) a.evidence⟩
      | .bool false =>
          let b ← raw s store no
          return ⟨b.value,c.cost+b.cost+2,by rw [original]; exact .ifFalse (cv ▸ c.evidence) b.evidence⟩
      | _ => throw (IO.userError "actual guard is not Bool")
  | _ => throw (IO.userError "selected unsupported child")
termination_by sizeOf source
private def readBody : Core.Expr := .loadCell (.var 1)
private def writeBody : Core.Expr := .letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))
private def reader : Core.Value := .closure .word .word readBody [.cellRef .word 0]
private def writer : Core.Value := .closure .word .word writeBody [.cellRef .word 0]
private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
private theorem readerTyped : Core.ValueHasType reader (.function .word .word) :=
  .closure (.cons .cellRef .nil) (.loadCell (.var rfl))
private theorem writerTyped : Core.ValueHasType writer (.function .word .word) :=
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))
private theorem allocatorTyped : Core.ValueHasType allocator (.function .word (.cell .word)) := .closure .nil (.newCell (.var rfl))
private structure Body (body : Core.Expr) (actual : Core.Environment) (store : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  path : ∀ k, Core.Steps cost ⟨.eval body actual,k,store⟩ ⟨.ret value,k,final⟩
private def bodyPath (body : Core.Expr) (actual : Core.Environment) (store : Core.Store) : IO (Body body actual store) := do
  match original : body, values : actual, saved : store with
  | .loadCell (.var 1),arg :: .cellRef .word 0 :: [],[old] => return ⟨old,store,3,by
      intro k; rw [original,values]; exact .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell (by rw [saved]; rfl)) .refl))⟩
  | .letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2)),arg :: .cellRef .word 0 :: [],[old] => return ⟨arg,[arg],10,by
      intro k; rw [original,values,saved]
      exact .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
        (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet
        (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))))))))⟩
  | .newCell .word (.var 0),arg :: [],_ => return ⟨.cellRef .word store.length,store ++ [arg],3,by
      intro k; rw [original,values]; exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))⟩
  | _,_,_ => throw (IO.userError "outside independent actual body path")
private structure Counted (s : LocalInputs) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : LocalFunctionApplicationEvaluatesWithCost s.names s.environment store source value final cost
private def counted (s : LocalInputs) (store : Core.Store) (source : Syntax.Expr) : IO (Counted s store source) := do
  match original : source with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
      let f ← raw s store callee; let a ← raw s store argument
      match shape : f.value with
      | .closure _ _ body captured =>
          let b ← bodyPath body (a.value :: captured) store
          return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,by rw [original]; exact .call (shape ▸ f.evidence) a.evidence (b.path [])⟩
      | _ => throw (IO.userError "actual callee is not a closure")
  | _ => throw (IO.userError "not a single argument call")
private structure Returned (body : Syntax.Block) where
  blockSpan : Syntax.SourceSpan
  returnSpan : Syntax.SourceSpan
  source : Syntax.Expr
  shape : body = ⟨blockSpan,[⟨returnSpan,.returnStmt (some source)⟩]⟩
private def returned (body : Syntax.Block) : IO (Returned body) := do
  match original : body with
  | ⟨b,[⟨r,.returnStmt (some source)⟩]⟩ =>
      check (b.contains r && r.contains source.span && decide (b.startByte < r.startByte ∧ source.span.endByte < r.endByte))
        "original body/return/child spans changed"
      return ⟨b,r,source,original⟩
  | _ => throw (IO.userError "not original singleton expression return")
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def verify (s : LocalInputs) (text : String) (core : Core.Expr) (type : Core.Ty) (value : Core.Value)
    (cost : Nat) (store final : Core.Store) : IO Unit := do
  let body ← parsed text; let r ← returned body
  let original ← application s r.source; let actual ← counted s store r.source
  if staticEq : original.core = core ∧ original.type = type then
    if actualEq : actual.value = value ∧ actual.final = final ∧ actual.cost = cost then
      have child : LocalFunctionApplicationElaborates s.names s.context r.source core type := by simpa only [staticEq.1,staticEq.2] using original.evidence
      have e : LocalFunctionApplicationEvaluatesWithCost s.names s.environment store r.source value final cost := by
        simpa only [actualEq.1,actualEq.2.1,actualEq.2.2] using actual.evidence
      have elaboration : LocalApplicationReturnBodyElaborates s.names s.context body core type := by rw [r.shape]; exact .application child
      have typing : LocalApplicationReturnBodyHasType s.names s.context body type := by rw [r.shape]; exact .application child.hasType
      have rawBody : LocalApplicationReturnBodyEvaluates s.names s.environment store body value final := by rw [r.shape]; exact .application e.erase
      have costed : LocalApplicationReturnBodyEvaluatesWithCost s.names s.environment store body value final cost := by rw [r.shape]; exact .application e
      have checkEq : s.checkApplicationReturnBody? body = s.checkApplication? r.source := by
        exact (congrArg s.checkApplicationReturnBody? r.shape).trans (s.checkApplicationReturnBody?_return _ _ _)
      have runEq (fuel) : s.runApplicationReturnBody? fuel body store = s.runApplication? fuel r.source store := by
        exact (congrArg (fun b => s.runApplicationReturnBody? fuel b store) r.shape).trans (s.runApplicationReturnBody?_return _ _ _ _ _)
      have checked := LocalInputs.checkApplicationReturnBody?_iff_elaborates.mpr elaboration
      have _ := elaborateLocalApplicationReturnBody?_sound elaboration.complete
      have _ := elaborateLocalApplicationReturnBody?_iff.mp elaboration.complete
      have _ := elaboration.hasType
      have _ := localApplicationReturnBodyHasType_iff_elaborates.mpr ⟨core,elaboration⟩
      have _ := elaboration.result_unique (elaborateLocalApplicationReturnBody?_sound elaboration.complete)
      have _ := typing.type_unique elaboration.hasType
      have _ := elaborateLocalApplicationReturnBody?_core_hasType elaboration.complete
      have _ := elaboration.core_hasType
      have _ := typing.elaborates_exact
      have _ := rawBody.deterministic costed.erase
      have _ := rawBody.exists_cost
      have _ := localApplicationReturnBodyEvaluates_iff_exists_cost.mpr ⟨cost,costed⟩
      have _ := (elaboration.evaluates_iff s.sameIds).mpr ((elaboration.evaluates_iff s.sameIds).mp rawBody)
      let path := costed.toStepsWithContinuation elaboration s.sameIds []
      have _ := costed.deterministic ((elaboration.evaluatesWithCost_iff_steps s.sameIds).mpr path)
      have _ := costed.toStepsWithContinuation elaboration s.sameIds [.loadCellApply]
      have done := (LocalInputs.runApplicationReturnBody?_done_iff_typed_cost (fuel := cost)).mpr ⟨typing,cost,costed,Nat.le_refl cost⟩
      have _ := LocalInputs.runApplicationReturnBody?_done_iff_typed_cost.mp done
      check (decide (s.checkApplicationReturnBody? body = some (core,type) ∧ s.checkApplicationReturnBody? body = s.checkApplication? r.source ∧
        s.checkReturnBody? body = none ∧ s.checkTypedLetReturnTree? [] owner body = none)) "independent Core/type or full checker equality changed"
      for fuel in List.range (cost+3) do
        have _ := LocalInputs.runApplication?_done_iff_of_cost child.hasType e (fuel := fuel)
        have _ := LocalInputs.runApplication?_outOfFuel_iff_of_cost child.hasType e (fuel := fuel)
        check (decide (s.runApplicationReturnBody? fuel body store = s.runApplication? fuel r.source store ∧
          s.runReturnBody? fuel body store = none)) "return changed full child outcome or old body gate"
        check (match s.runApplicationReturnBody? fuel body store with
          | some (tag,.done v t) => decide (tag = type ∧ cost ≤ fuel ∧ v = value ∧ t = final)
          | some (tag,.outOfFuel _) => decide (tag = type ∧ fuel < cost)
          | _ => false) "fixed independent result/store/cost changed"
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial core s.environment.values store) with
        | .outOfFuel checkpoint =>
            have bodyStop := LocalInputs.runApplicationReturnBody?_eq_some_iff.mpr ⟨core,checked,stopped⟩
            have childStop : s.runApplication? spent r.source store = some (type,.outOfFuel checkpoint) := (runEq spent).symm.trans bodyStop
            have _ := LocalInputs.runApplication?_residual_of_outOfFuel e childStop
            for additional in [0,1,cost-spent,cost+2] do
              have _ := LocalInputs.runApplication?_resume childStop additional
              check (decide (s.runApplicationReturnBody? spent body store = some (type,.outOfFuel checkpoint) ∧
                s.runApplicationReturnBody? (spent+additional) body store = some (type,Core.runStateful additional checkpoint))) "identical original checkpoint/full resumption changed"
            check (decide (Core.runStateful (cost-spent) checkpoint = .done value final)) "exact saved residual changed"
        | _ => throw (IO.userError "original genuine checkpoint missing")
    else throw (IO.userError "independent actual expectation changed")
  else throw (IO.userError "independent source expectation changed")
private def fixtures : IO Unit := do
  let r := inputs .word reader writer readerTyped writerTyped 14
  let wr := inputs .word writer reader writerTyped readerTyped 14
  let a := inputs (.cell .word) allocator allocator allocatorTyped allocatorTyped 14
  let body ← parsed "{return f(x);}"; let ret ← returned body
  check (decide (ret.returnSpan.startByte = 1 ∧ ret.returnSpan.endByte = 13 ∧ ret.source.span.startByte = 8 ∧ ret.source.span.endByte = 12)) "original return keyword/semicolon/child ranges changed"
  for old in [23,91] do
    verify r "{return f(x);}" target .word (w old) 8 [w old] [w old]
    verify wr "{return f(x);}" target .word (w 14) 15 [w old] [w 14]
    verify a "{return f(x);}" target (.cell .word) (.cellRef .word 1) 8 [w old] [w old,w 14]
  verify r "{return (c ? f : g)(x);}" (.apply (.ifE (.var 3) (.var 1) (.var 2)) (.var 0)) .word (w 23) 11 [w 23] [w 23]
  verify r "{return f(x);}" target .word (.bool true) 8 [.bool true] [.bool true]
  have _ : ¬ Core.ValueHasType (.bool true) .word := by intro h; cases h
  have et : Core.RuntimeEnvironmentHasTypes [.word] r.environment.values r.context.values := .cons .word
    (.cons (.closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl)))
    (.cons (.closure (.cons (.cellRef rfl) .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))) (.cons .bool .nil)))
  have st : Core.StoreHasTypes [.word] [w 23] := Core.StoreHasTypes.nil.allocate .word .word
  let app ← application r ret.source
  let finite ← counted r [w 23] ret.source
  have _ := LocalInputs.runApplication?_runtime_has_exact_cost app.evidence.hasType et st
    ⟨finite.value, finite.final, finite.evidence.erase⟩
  for store in [[],[w 23],[.bool true]] do
    let cp : Core.State := ⟨.eval (.var 0) r.environment.values,[.applyClosure .word .word readBody [.cellRef .word 0]],store⟩
    if checked : r.checkApplication? ret.source = some (target,.word) then
      have stopped : r.runApplication? 3 ret.source store = some (.word,.outOfFuel cp) := LocalInputs.runApplication?_eq_some_iff.mpr ⟨target,checked,rfl⟩
      for additional in [0,4,5,9] do
        have _ := LocalInputs.runApplication?_resume stopped additional
        check (decide (r.runApplicationReturnBody? 3 body store = some (.word,.outOfFuel cp) ∧
          r.runApplicationReturnBody? (3+additional) body store = some (.word,Core.runStateful additional cp))) "fault/done resumption did not retain identical child state"
    else throw (IO.userError "original reader rejected")
  check (decide (r.runApplicationReturnBody? 7 body [] = some (.word,
    .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩))) "return wrapper suppressed missing-cell fault"
  have runtimeEq (fuel) : r.runApplicationReturnBody? fuel body [w 23] = r.runApplication? fuel ret.source [w 23] :=
    (congrArg (fun b => r.runApplicationReturnBody? fuel b [w 23]) ret.shape).trans (r.runApplicationReturnBody?_return _ _ _ _ _)
  for fuel in [0,3,8,20] do
    have bodyNeverFaults (error : Core.MachineFault) (state : Core.State) :
        r.runApplicationReturnBody? fuel body [w 23] ≠ some (.word,.fault error state) := by
      rw [runtimeEq]; exact LocalInputs.runApplication?_runtime_never_faults et st ret.source fuel .word error state
    have _ := bodyNeverFaults
    if completed : r.runApplicationReturnBody? fuel body [w 23] = some (.word,.done (w 23) [w 23]) then
      have _ := LocalInputs.runApplication?_runtime_done_sound et st ((runtimeEq fuel).symm.trans completed)
      pure ()
    else pure ()
  let rejected ← parsed "{return (c ? f : missing)(x);}"; let rr ← returned rejected
  let rawChild ← counted r [w 23] rr.source
  have _ : LocalApplicationReturnBodyEvaluatesWithCost r.names r.environment [w 23] rejected rawChild.value rawChild.final rawChild.cost :=
    Eq.mp (congrArg (fun b => LocalApplicationReturnBodyEvaluatesWithCost r.names r.environment [w 23] b rawChild.value rawChild.final rawChild.cost) rr.shape.symm)
      (.application rawChild.evidence)
  check (decide (rawChild.value = w 23 ∧ rawChild.cost = 11 ∧ r.checkApplicationReturnBody? rejected = none)) "raw selected success bypassed whole body acceptance"
  for (text,old) in [("{return;}",some (Core.Expr.unit,Core.Ty.unit)),("{return x;}",some (.var 0,.word)),
      ("{}",none),("{return f(x);return x;}",none),("{f(x);return x;}",none),
      ("{if(c){return x;}else{return x;}}",none),("{{return f(x);}}",none),("{return f(f(x));}",none)] do
    let bad ← parsed text
    check (decide (r.checkApplicationReturnBody? bad = none ∧ r.checkReturnBody? bad = old)) "new exclusion or old singleton acceptance changed"
    have _ := elaborateLocalApplicationReturnBody?_eq_none_iff (table := r.names) (context := r.context) (body := bad)
    for fuel in [0,3,20] do
      have _ := LocalInputs.runApplicationReturnBody?_eq_none_iff (inputs := r) (body := bad) fuel [w 23]
      check (decide (r.runApplicationReturnBody? fuel bad [w 23] = none)) "unsupported whole body became present"
  let bare ← parsed "{return;}"; let pureReturn ← parsed "{return x;}"
  check (decide (r.runReturnBody? 1 bare [w 23] = some (.unit,.done .unit [w 23]) ∧
    r.runReturnBody? 1 pureReturn [w 23] = some (.word,.done (w 14) [w 23]))) "old successful singleton runners changed"
end ParsedApplicationReturnBodies
open ParsedApplicationReturnBodies
def frontendParsedApplicationReturnBodyTests : IO Unit := fixtures
end Tests
