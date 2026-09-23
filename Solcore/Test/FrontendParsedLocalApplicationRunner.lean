import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties

/-! One actual input record supplies every projection. Original source and
hand-built closure-body paths fix the expected result before either runner. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalApplicationRunner
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ApplicationRunner",by decide⟩],by decide⟩⟩,19⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 3},999⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def inputs (output : Core.Ty) (f shadow : Core.Value)
    (ft : Core.ValueHasType f (.function .word output)) (gt : Core.ValueHasType shadow (.function .word output)) (x : Nat) : LocalInputs :=
  ⟨[⟨"x",id 2,.word,w x,.word⟩,⟨"f",id 7,.function .word output,f,ft⟩,
    ⟨"f",id 91,.function .word output,shadow,gt⟩,⟨"c",foreign,.bool,.bool true,.bool⟩],by
      change [id 2,id 7,id 91,foreign].Nodup; decide⟩
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"application-runner.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing failed")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original expression did not parse")
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
  .closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word)
private theorem writerTyped : Core.ValueHasType writer (.function .word .word) :=
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))
private theorem allocatorTyped : Core.ValueHasType allocator (.function .word (.cell .word)) := .closure .nil (.newCell (.var rfl) .word)
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
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def verify (s : LocalInputs) (text : String) (type : Core.Ty) (value : Core.Value)
    (cost : Nat) (store final : Core.Store)
    (runtime : Option (PLift (Core.RuntimeEnvironmentHasTypes [.word] s.environment.values s.context.values ∧
      Core.StoreHasTypes [.word] store)) := none) : IO Unit := do
  let source ← parsed text
  let original ← application s source
  let actual ← counted s store source
  if staticEq : original.core = target ∧ original.type = type then
    if actualEq : actual.value = value ∧ actual.final = final ∧ actual.cost = cost then
      have elaboration : LocalFunctionApplicationElaborates s.names s.context source target type := by
        simpa only [staticEq.1,staticEq.2] using original.evidence
      have evaluation : LocalFunctionApplicationEvaluatesWithCost s.names s.environment store source value final cost := by
        simpa only [actualEq.1,actualEq.2.1,actualEq.2.2] using actual.evidence
      let path := evaluation.toSteps elaboration s.sameIds
      have checked := LocalInputs.checkApplication?_iff_elaborates.mpr elaboration
      have whole := LocalInputs.checkApplication?_iff_hasType.mp ⟨target,checked⟩
      have _ := LocalInputs.checkApplication?_iff_hasType.mpr whole
      have done := (LocalInputs.runApplication?_done_iff_of_cost whole evaluation (fuel := cost)).mpr (Nat.le_refl cost)
      have _ := LocalInputs.runApplication?_done_iff_typed_evaluation.mpr ⟨whole,evaluation.erase⟩
      have _ := LocalInputs.runApplication?_done_iff_typed_evaluation.mp ⟨cost,done⟩
      have _ := LocalInputs.runApplication?_done_iff_typed_cost.mp done
      have _ := LocalInputs.runApplication?_done_iff_typed_cost.mpr ⟨whole,cost,evaluation,Nat.le_refl cost⟩
      match runtime with
      | some proof =>
          have _ := LocalInputs.runApplication?_runtime_done_sound proof.down.1 proof.down.2 done
          have identified : ∃ future, Core.WorldExtends [.word] future ∧ Core.StoreHasTypes future final ∧
              Core.RuntimeValueHasType future value type := by
            obtain ⟨fw,fs,v,n,extension,st,vt,e,_⟩ := LocalInputs.runApplication?_runtime_has_exact_cost whole proof.down.1 proof.down.2
            obtain ⟨rfl,rfl,rfl⟩ := e.deterministic evaluation
            exact ⟨fw,extension,st,vt⟩
          have _ := identified
          for fuel in List.range (cost+3) do
            have _ := LocalInputs.runApplication?_runtime_never_faults proof.down.1 proof.down.2 source fuel type
            pure ()
      | none => pure ()
      check (decide (s.checkApplication? source = some (target,type) ∧ s.check? source = none)) "new checker exactness or old pure boundary changed"
      for fuel in List.range (cost+3) do
        have _ := LocalInputs.runApplication?_outOfFuel_iff_of_cost whole evaluation (fuel := fuel)
        check (decide (s.run? fuel source store = none)) "new call entered old pure runner"
        check (match result : s.runApplication? fuel source store with
          | some (tag,.done v t) => decide (tag = type ∧ cost ≤ fuel ∧ v = value ∧ t = final)
          | some (tag,.outOfFuel _) => decide (tag = type ∧ fuel < cost)
          | _ => false) "checked full result/type tag or exact cost changed"
        match result : s.runApplication? fuel source store with
        | some (tag,.done v t) =>
            have _ := LocalInputs.runApplication?_done_sound result
            have _ := LocalInputs.runApplication?_eq_some_iff.mp result
            pure ()
        | _ => pure ()
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial target s.environment.values store) with
        | .outOfFuel checkpoint =>
            have _ := path.residual_of_outOfFuel stopped
            have suspended := LocalInputs.runApplication?_eq_some_iff.mpr ⟨target,checked,stopped⟩
            have _ := LocalInputs.runApplication?_residual_of_outOfFuel evaluation suspended
            for additional in [0,1,cost-spent,cost+2] do
              have _ := LocalInputs.runApplication?_resume suspended additional
              check (decide (s.runApplication? (spent+additional) source store =
                some (type,Core.runStateful additional checkpoint))) "full-result resumption changed"
            check (decide (s.runApplication? spent source store = some (type,.outOfFuel checkpoint) ∧
              Core.runStateful (cost-spent) checkpoint = .done value final)) "original full checkpoint/residual changed"
        | _ => throw (IO.userError "genuine checked checkpoint missing")
    else throw (IO.userError "independent expected value/store/cost changed")
  else throw (IO.userError "independent source Core/type changed")
private def fixtures : IO Unit := do
  let r := inputs .word reader writer readerTyped writerTyped 14
  let writerInputs := inputs .word writer reader writerTyped readerTyped 14
  let a := inputs (.cell .word) allocator allocator allocatorTyped allocatorTyped 14
  check (decide (r.names = [("x",id 2),("f",id 7),("f",id 91),("c",foreign)] ∧
    r.environment.values = [w 14,reader,writer,.bool true])) "one actual record lost duplicate first-match/order"
  let source ← parsed "f(x)"
  match source.value with
  | .call f ⟨span,[x]⟩ => check (decide (f.span.startByte = 0 ∧ f.span.endByte = 1 ∧ span.startByte = 1 ∧
      span.endByte = 4 ∧ x.span.startByte = 2 ∧ x.span.endByte = 3)) "original argument byte ranges changed"
  | _ => throw (IO.userError "original singleton call changed")
  for old in [23,91] do
    have st : Core.StoreHasTypes [.word] [w old] := Core.StoreHasTypes.nil.allocate .word .word
    have rt : Core.RuntimeValueHasType [.word] reader (.function .word .word) := .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl) .word)
    have wt : Core.RuntimeValueHasType [.word] writer (.function .word .word) := .closure (.cons (.cellRef rfl) .nil)
      (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))
    have atyped : Core.RuntimeValueHasType [.word] allocator (.function .word (.cell .word)) := .closure .nil (.newCell (.var rfl) .word)
    verify r "f(x)" .word (w old) 8 [w old] [w old] (some ⟨⟨.cons .word (.cons rt (.cons wt (.cons .bool .nil))),st⟩⟩)
    verify writerInputs "f(x)" .word (w 14) 15 [w old] [w 14] (some ⟨⟨.cons .word (.cons wt (.cons rt (.cons .bool .nil))),st⟩⟩)
    verify a "f(x)" (.cell .word) (.cellRef .word 1) 8 [w old] [w old,w 14]
      (some ⟨⟨.cons .word (.cons atyped (.cons atyped (.cons .bool .nil))),st⟩⟩)
    check (decide (writerInputs.runApplication? 11 source [w old] = some (.word,
      .outOfFuel ⟨.ret .unit,[.letBody (.loadCell (.var 2)) [w 14,.cellRef .word 0]],[w 14]⟩))) "writer checkpoint lost updated store or actual captures"
  verify r "(f)(x)" .word (w 23) 8 [w 23] [w 23]
  verify r "f(x)" .word (.bool true) 8 [.bool true] [.bool true]
  have _ : ¬ Core.ValueHasType (.bool true) .word := by intro h; cases h
  have _ : ¬ Core.StoreHasTypes [.word] [.bool true] := by
    intro h; obtain ⟨v,found,_,typed⟩ := h.read (location := 0) rfl
    have eq : v = .bool true := (Option.some.inj found).symm
    subst v; cases typed
  for store in [[],[w 23],[.bool true]] do
    let checkpoint : Core.State := ⟨.eval (.var 0) r.environment.values,[.applyClosure .word .word readBody [.cellRef .word 0]],store⟩
    check (decide (r.runApplication? 3 source store = some (.word,.outOfFuel checkpoint))) "original genuine cp3 changed"
    if checked : r.checkApplication? source = some (target,.word) then
      have stopped : r.runApplication? 3 source store = some (.word,.outOfFuel checkpoint) :=
        LocalInputs.runApplication?_eq_some_iff.mpr ⟨target,checked,rfl⟩
      for additional in [0,4,5,9] do
        have _ := LocalInputs.runApplication?_resume stopped additional
        check (decide (r.runApplication? (3+additional) source store = some (.word,Core.runStateful additional checkpoint))) "fault/exhaustion resumption lost original tag"
    else throw (IO.userError "original reader check failed")
    if store.isEmpty then
      check (decide (r.runApplication? 7 source store = some (.word,
        .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩) ∧
        Core.runStateful 4 checkpoint = .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩)) "missing store fault was hidden or restart used"
      check (match r.runApplication? 4 source store with
        | some (.word,.outOfFuel _) => true | _ => false) "restart was confused with saved cp3 plus four steps"
    else
      let some value := store[0]? | throw (IO.userError "original allocated payload missing")
      check (decide (Core.runStateful 5 checkpoint = .done value store)) "saved actual store was not used on resumption"
  let rejected ← parsed "(c ? f : missing)(x)"
  let actual ← counted r [w 23] rejected
  check (decide (actual.value = w 23 ∧ actual.final = [w 23] ∧ actual.cost = 11 ∧ r.checkApplication? rejected = none)) "raw selected success bypassed whole checking"
  for fuel in [0,3,11,30] do
    have _ := LocalInputs.runApplication?_eq_none_iff (inputs := r) (source := rejected) fuel [w 23]
    check (decide (r.runApplication? fuel rejected [w 23] = none)) "whole failure depended on fuel"
end ParsedLocalApplicationRunner
open ParsedLocalApplicationRunner
def frontendParsedLocalApplicationRunnerTests : IO Unit := fixtures
end Tests
