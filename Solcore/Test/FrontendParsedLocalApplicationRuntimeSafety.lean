import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties

/-! Original parsed children, independent actual world/store witnesses, and
hand-built captured-body paths precede every runtime safety observation. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalApplicationRuntimeSafety
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def own : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RuntimeSafety",by decide⟩],by decide⟩⟩,17⟩
private def id (n : Nat) : Resolved.LocalId := ⟨own,n⟩
private def foreign : Resolved.LocalId := ⟨{own with declarationIndex := 2},999⟩
private def names : LocalNameTable := [("f",id 7),("f",id 91),("x",id 2),("c",foreign),("g",id 4)]
private def ctx (output : Core.Ty) : Resolved.Context :=
  [(id 2,.word),(id 7,.function .word output),(foreign,.bool),(id 4,.function .word output)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def env (f g : Core.Value) (x : Nat) (c : Bool) : Resolved.Environment :=
  [(id 2,w x),(id 7,f),(foreign,.bool c),(id 4,g)]
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"runtime-safety.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing failed")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original expression did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩)) "original complete byte range changed"
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
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original context row missing")
      | none => throw (IO.userError "original name missing")
  | ⟨_,.group inner⟩ =>
      let a ← child context inner
      return ⟨a.resolved,a.core,a.type,by rw [original]; exact .group a.resolution,a.lowered,a.typing⟩
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← child context condition; let a ← child context yes; let b ← child context no
      if ct : c.type = .bool then
        if bt : b.type = a.type then return ⟨.ifE c.resolved a.resolved b.resolved,.ifE c.core a.core b.core,a.type,
          by rw [original]; exact .conditional c.resolution a.resolution b.resolution,
          .ifE c.lowered a.lowered b.lowered,.ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole branch types differ")
      else throw (IO.userError "whole guard is not Bool")
  | _ => throw (IO.userError "outside independent child certificate")
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
          else throw (IO.userError "argument type differs")
      | _ => throw (IO.userError "callee is not Function")
  | _ => throw (IO.userError "not exactly one original argument")
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
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← raw environment s condition
      match cv : c.value with
      | .bool true =>
          let a ← raw environment s yes
          return ⟨a.value,c.cost+a.cost+2,by rw [original]; exact .ifTrue (cv ▸ c.evidence) a.evidence⟩
      | .bool false =>
          let b ← raw environment s no
          return ⟨b.value,c.cost+b.cost+2,by rw [original]; exact .ifFalse (cv ▸ c.evidence) b.evidence⟩
      | _ => throw (IO.userError "actual guard is not Bool")
  | _ => throw (IO.userError "selected unsupported child")
termination_by sizeOf source
private def readBody : Core.Expr := .loadCell (.var 1)
private def writeBody : Core.Expr := .letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))
private def reader : Core.Value := .closure .word .word readBody [.cellRef .word 0]
private def writer : Core.Value := .closure .word .word writeBody [.cellRef .word 0]
private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
private structure Body (body : Core.Expr) (actual : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  path : ∀ k, Core.Steps cost ⟨.eval body actual,k,s⟩ ⟨.ret value,k,final⟩
private def bodyPath (body : Core.Expr) (actual : Core.Environment) (s : Core.Store) : IO (Body body actual s) := do
  match original : body, values : actual, store : s with
  | .loadCell (.var 1),arg :: .cellRef .word 0 :: [],[old] => return ⟨old,s,3,by
      intro k; rw [original,values]; exact .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell (by rw [store]; rfl)) .refl))⟩
  | .letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2)),arg :: .cellRef .word 0 :: [],[old] => return ⟨arg,[arg],10,by
      intro k; rw [original,values,store]
      exact .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
        (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet
        (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))))))))⟩
  | .newCell .word (.var 0),arg :: [],_ => return ⟨.cellRef .word s.length,s ++ [arg],3,by
      intro k; rw [original,values]; exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))⟩
  | _,_,_ => throw (IO.userError "outside independent actual body path")
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
          return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,by rw [original]; exact .call (shape ▸ f.evidence) a.evidence (b.path [])⟩
      | _ => throw (IO.userError "actual callee is not a closure")
  | _ => throw (IO.userError "not a single argument call")
private theorem storeTyped (n : Nat) : Core.StoreHasTypes [.word] [w n] :=
  Core.StoreHasTypes.nil.allocate .word .word
private theorem readerTyped : Core.RuntimeValueHasType [.word] reader (.function .word .word) :=
  .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl))
private theorem writerTyped : Core.RuntimeValueHasType [.word] writer (.function .word .word) :=
  .closure (.cons (.cellRef rfl) .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))
private def verify (text : String) (output : Core.Ty) (f g : Core.Value) (x : Nat) (c : Bool)
    (expected : Core.Expr) (value : Core.Value) (cost : Nat) (s final : Core.Store)
    (world : Core.StoreTyping) (et : Core.RuntimeEnvironmentHasTypes world (env f g x c).values (ctx output).values)
    (st : Core.StoreHasTypes world s) : IO Unit := do
  let source ← parsed text
  let original ← application (ctx output) source
  let actual ← counted (env f g x c) s source
  if exactStatic : original.core = expected ∧ original.type = output then
    if exactRaw : actual.value = value ∧ actual.final = final ∧ actual.cost = cost then
      have elaboration : LocalFunctionApplicationElaborates names (ctx output) source expected output := by
        simpa only [exactStatic.1,exactStatic.2] using original.evidence
      have evaluation : LocalFunctionApplicationEvaluatesWithCost names (env f g x c) s source value final cost := by
        simpa only [exactRaw.1,exactRaw.2.1,exactRaw.2.2] using actual.evidence
      have aligned : (env f g x c).ids = (ctx output).ids := rfl
      have _ := evaluation.erase.preserves_runtime_type elaboration aligned et st
      have _ := elaboration.hasType.runtime_evaluates aligned et st ⟨value, final, evaluation.erase⟩
      have identified : ∃ finalWorld, Core.WorldExtends world finalWorld ∧ Core.RuntimeStoreHasTypes finalWorld final ∧
          Core.RuntimeValueHasType finalWorld value output := by
        obtain ⟨fw,fs,v,n,ext,typed,vt,e,_,_⟩ := elaboration.runtime_typed_execution aligned et st ⟨value, final, evaluation.erase⟩
        obtain ⟨rfl,rfl,rfl⟩ := e.deterministic evaluation
        exact ⟨fw,ext,typed,vt⟩
      let path := evaluation.toSteps elaboration aligned
      have kt : Core.ContinuationHasType world [.pairApply (w 7)] output (.product .word output) := .cons (.pairApply .word) .nil
      have _ := elaboration.runtime_state_hasType et st kt
      check (decide (Core.runStateful cost ⟨.eval expected (env f g x c).values,[.pairApply (w 7)],s⟩ =
        .outOfFuel ⟨.ret value,[.pairApply (w 7)],final⟩)) "typed endpoint was confused with closed completion"
      for fuel in List.range (cost+3) do
        have _ := elaboration.runtime_run_never_faults et st kt fuel (.expectedCell value) (.final value final)
        check (match completed : Core.runStateful fuel (.initial expected (env f g x c).values s) with
          | .done v t => decide (cost ≤ fuel ∧ v = value ∧ t = final)
          | .outOfFuel _ => decide (fuel < cost)
          | _ => false) "actual closed typed execution threshold changed"
        match completed : Core.runStateful fuel (.initial expected (env f g x c).values s) with
        | .done v t =>
            have _ := elaborateLocalFunctionApplication?_runtime_run_done_sound elaboration.complete aligned et st completed
            pure ()
        | _ => pure ()
      for spent in List.range (cost+1) do
        match stopped : Core.runStateful spent ⟨.eval expected (env f g x c).values,[.pairApply (w 7)],s⟩ with
        | .outOfFuel checkpoint =>
            have _ := elaboration.runtime_checkpoint_hasType et st kt stopped
            have _ := elaboration.runtime_checkpoint_never_faults et st kt stopped (cost+1-spent) (.expectedCell value) checkpoint
            have _ := Core.runStateful_resume stopped (cost+1-spent)
            check (decide (Core.runStateful (cost+1-spent) checkpoint = .done (.pair (w 7) value) final)) "typed actual continuation/checkpoint changed"
        | _ => throw (IO.userError "typed continuation checkpoint missing")
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial expected (env f g x c).values s) with
        | .outOfFuel checkpoint =>
            have _ := path.residual_of_outOfFuel stopped
            check (decide (Core.runStateful (cost-spent) checkpoint = .done value final)) "closed exact residual changed"
        | _ => throw (IO.userError "genuine closed checkpoint missing")
      check (decide (elaborateLocalExpression? names (ctx output) source = none)) "old pure expression gate changed"
    else throw (IO.userError "independent raw value/store/cost changed")
  else throw (IO.userError "independent original Core/type changed")
private def mixed : Core.Expr := .apply (.ifE (.var 2) (.var 1) (.var 3)) (.var 0)
private def selected : IO Unit := do
  let source ← parsed "(c ? f : g)(x)"
  match source.value with
  | .call callee ⟨span,[argument]⟩ => check (decide (callee.span.startByte = 0 ∧ callee.span.endByte = 11 ∧
      span.startByte = 11 ∧ span.endByte = 14 ∧ argument.span.startByte = 12 ∧ argument.span.endByte = 13)) "original child byte ranges changed"
  | _ => throw (IO.userError "original root call changed")
  for x in [14,9] do
    for old in [23,91] do
      for c in [true,false] do
        let actual := env reader writer x c
        have et : Core.RuntimeEnvironmentHasTypes [.word] actual.values (ctx .word).values :=
          .cons .word (.cons readerTyped (.cons .bool (.cons writerTyped .nil)))
        verify "(c ? f : g)(x)" .word reader writer x c mixed (w (if c then old else x)) (if c then 11 else 18)
          [w old] (if c then [w old] else [w x]) [.word] et (storeTyped old)
        if !c then
          check (decide (Core.runStateful 14 (.initial mixed actual.values [w old]) =
            .outOfFuel ⟨.ret .unit,[.letBody (.loadCell (.var 2)) [w x,.cellRef .word 0]],[w x]⟩)) "actual updated store/captured environment at cp14 changed"
          check (decide (Core.runStateful 15 (.initial mixed actual.values [w old]) =
            .outOfFuel ⟨.eval (.loadCell (.var 2)) [.unit,w x,.cellRef .word 0],[],[w x]⟩)) "post-let reread did not retain original reference"
private def allocation : IO Unit := do
  for old in [23,91] do
    have ft : Core.RuntimeValueHasType [.word] allocator (.function .word (.cell .word)) := .closure .nil (.newCell (.var rfl))
    have et : Core.RuntimeEnvironmentHasTypes [.word] (env allocator allocator 14 true).values (ctx (.cell .word)).values :=
      .cons .word (.cons ft (.cons .bool (.cons ft .nil)))
    have _ : Core.StoreHasTypes [.word,.word] [w old,w 14] := (storeTyped old).allocate .word .word
    have _ : Core.RuntimeValueHasType [.word,.word] (.cellRef .word 1) (.cell .word) := .cellRef rfl
    verify "f(x)" (.cell .word) allocator allocator 14 true (.apply (.var 1) (.var 0)) (.cellRef .word 1) 8
      [w old] [w old,w 14] [.word] et (storeTyped old)
private def boundaries : IO Unit := do
  have _ : Core.ValueHasType reader (.function .word .word) := readerTyped.erase
  have _ : Core.RuntimeEnvironmentHasTypes [.word] (env reader writer 14 true).values (ctx .word).values :=
    .cons .word (.cons readerTyped (.cons .bool (.cons writerTyped .nil)))
  have _ : ¬ Core.RuntimeValueHasType [] (.cellRef .word 0) (.cell .word) := by intro h; cases h; contradiction
  have _ : ¬ Core.RuntimeValueHasType [.bool] (.cellRef .word 0) (.cell .word) := by intro h; cases h; contradiction
  have _ : ¬ Core.StoreHasTypes [.word] [] := by intro h; have := h.length_eq; contradiction
  have _ : ¬ Core.StoreHasTypes [.word] [.bool true] := by
    intro h; obtain ⟨v,found,_,typed⟩ := h.read (location := 0) rfl
    have eq : v = .bool true := (Option.some.inj found).symm
    subst v; cases typed
  check (decide (Core.runStateful 10 (.initial mixed (env reader writer 14 true).values []) =
    .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩)) "runtime typed reference fabricated allocated storage"
  check (decide (Core.runStateful 11 (.initial mixed (env reader writer 14 true).values [.bool true]) =
    .done (.bool true) [.bool true])) "equal store lengths fabricated payload typing"
  check (decide (Core.runStateful 11 ⟨.eval mixed (env reader writer 14 true).values,[.loadCellApply],[w 23]⟩ =
    .fault (.expectedCell (w 23)) ⟨.ret (w 23),[.loadCellApply],[w 23]⟩)) "untyped pending continuation was declared safe"
  let source ← parsed "(c ? f : missing)(x)"
  let actual ← counted (env reader writer 14 true) [w 23] source
  check (decide (actual.value = w 23 ∧ actual.final = [w 23] ∧ actual.cost = 11 ∧
    elaborateLocalFunctionApplication? names (ctx .word) source = none)) "raw selected success bypassed whole static typing"
  have _ := actual.evidence.erase
  pure ()
end ParsedLocalApplicationRuntimeSafety
open ParsedLocalApplicationRuntimeSafety
def frontendParsedLocalApplicationRuntimeSafetyTests : IO Unit := do
  selected; allocation; boundaries
end Tests
