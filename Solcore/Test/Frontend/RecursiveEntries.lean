import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Frontend.LocalComputation
import Solcore.Core.Safety

/-!
# Recursive entry tests

Recursive comparisons, tuples and identity renaming, with their entries and migrations.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveIdentityEffects
/-! Original parsed children, independent raw costs and literal Core paths retain
actual captures and ordered allocation/write/read. No body fresh-ID law is used. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveIdentityEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveIdentityEffects",by decide⟩],by decide⟩⟩,127⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def mapping (i : Resolved.LocalId) : Resolved.LocalId :=
  ⟨{i.owner with declarationIndex := i.owner.declarationIndex+10},i.binderIndex+100⟩
private theorem injective : Function.Injective mapping := by
  rintro ⟨⟨lm,ld⟩,li⟩ ⟨⟨rm,rd⟩,ri⟩ same
  simpa [mapping] using same
private theorem not_surjective : ¬ Function.Surjective mapping := by
  intro h; obtain ⟨i,same⟩ := h (id 0)
  have h := congrArg Resolved.LocalId.binderIndex same
  simp [mapping,id] at h
private def names : LocalNameTable := [("x",id 7),("c",id 15),("a",foreign),("w",id 9),("r",id 20),("a",id 88)]
private def context : Resolved.Context := [(id 7,.word),(id 15,.bool),(foreign,.function .word .word),(id 9,.function .word .word),(id 20,.function .word .word),(foreign,.bool)]
private def allocator : Core.Value := .closure .word .word (.letE (.newCell .word (.var 0)) (.var 1)) [.bool false]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def readFrame (l : Nat) : Core.Frame := .applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def writeFrame (l : Nat) : Core.Frame := .applyClosure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def environment (c : Core.Value) (w r : Nat) : Resolved.Environment :=
  [(id 7,.word (Core.Word.ofNatModulo 14)),(id 15,c),(foreign,allocator),(id 9,writer w),(id 20,reader r),(foreign,.bool true)]
private def first : Core.Expr := .apply (.var 4) (.apply (.var 3) (.apply (.var 2) (.var 0)))
private def read : Core.Expr := .apply (.var 4) (.var 0)
private def branch : Core.Expr := .ifE (.var 1) (.unary .wordNot read) (.binary .wordAdd read (.var 0))
private def core : Core.Expr := .pair first branch
private def wrap : Nat → String → String | 0,s => s | n+1,s => "("++wrap n s++")"
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-identity-effects.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError "parser")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "original full source bytes"
  return s
private structure Static (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : RecursiveLocalComputationElaborates names context s core type
private def statics (s : Syntax.Expr) : IO (Static s) := do
  match shape : s with
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span) "original group"
      let a ← statics inner; return ⟨a.core,a.type,by rw [shape]; exact .group a.evidence⟩
  | ⟨span,.tuple ⟨ts,[left,right]⟩⟩ =>
      check (span.contains ts && ts.contains left.span && ts.contains right.span && decide (left.span.endByte<right.span.startByte)) "original pair/order"
      let a ← statics left; let b ← statics right
      return ⟨.pair a.core b.core,.product a.type b.type,by rw [shape]; exact .pair a.evidence b.evidence⟩
  | ⟨span,.call fn ⟨args,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains args && args.contains arg.span && decide (fn.span.endByte≤args.startByte)) "original call/order"
      let f ← statics fn; let a ← statics arg
      match ft : f.type with
      | .function input output =>
        if same : a.type=input then
          return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
        else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static function")
  | ⟨span,.unary ⟨os,.bitNot⟩ inner⟩ =>
      check (span.contains os && span.contains inner.span && decide (os.endByte=os.startByte+1 ∧ os.endByte≤inner.span.startByte)) "original unary/order"
      let a ← statics inner
      if same : a.type=.word then return ⟨.unary .wordNot a.core,.word,by rw [shape]; exact .bitNot (same ▸ a.evidence)⟩ else throw (IO.userError "static Word")
  | ⟨span,.binary left ⟨os,.add⟩ right⟩ =>
      check (span.contains left.span && span.contains os && span.contains right.span && decide (left.span.endByte≤os.startByte ∧ os.endByte≤right.span.startByte)) "original binary/order"
      let a ← statics left; let b ← statics right
      if same : a.type=.word ∧ b.type=.word then return ⟨.binary .wordAdd a.core b.core,.word,
        by rw [shape]; exact .binary .add (by simpa only [Core.BinaryOp.leftType,same.1] using a.evidence) (by simpa only [Core.BinaryOp.rightType,Core.BinaryOp.leftType,same.2] using b.evidence)⟩ else throw (IO.userError "static operands")
  | ⟨span,.conditional condition q yes colon no⟩ =>
      check (span.contains condition.span && span.contains yes.span && span.contains no.span && span.contains q && span.contains colon &&
        decide (condition.span.endByte≤q.startByte ∧ q.endByte=q.startByte+1 ∧ q.endByte≤yes.span.startByte ∧ yes.span.endByte≤colon.startByte ∧ colon.endByte=colon.startByte+1 ∧ colon.endByte≤no.span.startByte)) "original conditional/order"
      let c ← statics condition; let a ← statics yes; let b ← statics no
      if same : c.type=.bool ∧ b.type=a.type then return ⟨.ifE c.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (same.1 ▸ c.evidence) a.evidence (same.2 ▸ b.evidence)⟩ else throw (IO.userError "all branches static")
  | ⟨_,.identifier name⟩ => match named : names.lookup? name.value with
    | some i => match typed : context.lookup? i, index : Resolved.LocalScope.index? context.ids i with
      | some t,some n => return ⟨.var n,t,by
          rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp index)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | _ => throw (IO.userError "static name")
  | _ => throw (IO.userError "static fixture shape")
termination_by sizeOf s
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .pair a b =>
        let l ← path n a env s; let r ← path n b env l.final
        return ⟨.pair l.value r.value,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; simpa only [Nat.add_assoc] using Core.Steps.cons .enterPair ((l.evidence _).trans (.cons .enterPairRight ((r.evidence _).trans (.cons .applyPair .refl))))⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell found) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match found : s.read? l, written : s.write? l v with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual missing write")
      | _,_ => throw (IO.userError "manual write reference")
    | .unary op a =>
        let l ← path n a env s
        match applied : op.apply l.value with | some v => return ⟨v,l.final,l.cost+2,fun _ => by rw [shape]; exact CostStepComposition.unary (l.evidence _) applied⟩ | none => throw (IO.userError "manual unary payload")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩ | none => throw (IO.userError "manual binary payload")
    | .ifE c a b =>
        let condition ← path n c env s
        match cv : condition.value with
        | .bool true => let r ← path n a env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (cv ▸ condition.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (cv ▸ condition.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual condition")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : RecursiveLocalComputationEvaluatesWithCost names env s e value final cost
private def raw (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw env s e) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : names.lookup? name.value with
    | some i => match found : env.lookup? i with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.group inner⟩ => let a ← raw env s inner; return ⟨a.value,a.final,a.cost,by rw [shape]; exact .group a.evidence⟩
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
      let a ← raw env s left; let b ← raw env a.final right
      return ⟨.pair a.value b.value,b.final,a.cost+b.cost+3,by rw [shape]; exact .pair a.evidence b.evidence⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← raw env s fn; let a ← raw env f.final arg
      match fv : f.value with
      | .closure _ _ b captured =>
          let r ← path 60 b (a.value::captured) a.final
          return ⟨r.value,r.final,f.cost+a.cost+r.cost+3,by rw [shape]; exact .application (fv ▸ f.evidence) a.evidence (r.evidence [])⟩
      | _ => throw (IO.userError "raw closure")
  | ⟨_,.unary ⟨_,.bitNot⟩ inner⟩ =>
      let a ← raw env s inner
      match av : a.value with | .word w => return ⟨.word w.bitNot,a.final,a.cost+2,by rw [shape]; exact .bitNot (av ▸ a.evidence)⟩ | _ => throw (IO.userError "raw Word")
  | ⟨_,.binary left ⟨_,.add⟩ right⟩ =>
      let a ← raw env s left; let b ← raw env a.final right
      match applied : Core.BinaryOp.wordAdd.apply a.value b.value with
      | some v => return ⟨v,b.final,a.cost+b.cost+3,by rw [shape]; exact .binary .add a.evidence b.evidence applied⟩
      | _ => throw (IO.userError "raw addition")
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← raw env s condition
      match cv : c.value with
      | .bool true => let a ← raw env c.final yes; return ⟨a.value,a.final,c.cost+a.cost+2,by rw [shape]; exact .ifTrue (cv ▸ c.evidence) a.evidence⟩
      | .bool false => let b ← raw env c.final no; return ⟨b.value,b.final,c.cost+b.cost+2,by rw [shape]; exact .ifFalse (cv ▸ c.evidence) b.evidence⟩
      | _ => throw (IO.userError "raw condition")
  | _ => throw (IO.userError "raw fixture shape")
termination_by sizeOf e
private def exercise (depth : Nat) (c : Bool) (w r : Nat) (base : Core.Word) (final : Core.Store) : IO Unit := do
  let e ← parsed (wrap depth "(r(w(a(x))), c ? ~r(x) : r(x) + x)")
  let p ← statics e; let env := environment (.bool c) w r; let store : Core.Store := [.word (Core.Word.ofNatModulo 41),.word (Core.Word.ofNatModulo 99)]
  let m ← path 60 core env.values store; let a ← raw env store e
  let cost := if c then 48 else 50
  let value := Core.Value.pair (.word base) (.word (if c then base.bitNot else base+Core.Word.ofNatModulo 14))
  if fixed : p.core=core ∧ p.type=.product .word .word ∧ a.value=value ∧ a.final=final ∧ a.cost=cost ∧ m.value=value ∧ m.final=final ∧ m.cost=cost then
    have original : RecursiveLocalComputationElaborates names context e core (.product .word .word) := by simpa only [fixed.1,fixed.2.1] using p.evidence
    have typed := recursiveLocalComputationHasType_iff_elaborates.mpr ⟨_,original⟩
    have relabeled := (recursiveLocalComputationElaborates_mapIds_iff mapping injective).mpr original
    have _ := (recursiveLocalComputationElaborates_mapIds_iff mapping injective).mp relabeled
    have _ := (recursiveLocalComputationHasType_mapIds_iff mapping injective).mpr typed
    have costed : RecursiveLocalComputationEvaluatesWithCost names env store e value final cost := by simpa only [fixed.2.2.1,fixed.2.2.2.1,fixed.2.2.2.2.1] using a.evidence
    have renamedCost := (recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mpr costed
    have _ := (recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mp renamedCost
    have ordinary := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨cost,costed⟩
    have _ := (recursiveLocalComputationEvaluates_mapIds_iff mapping injective).mpr ordinary
    have literal : ∀ k, Core.Steps cost ⟨.eval core env.values,k,store⟩ ⟨.ret value,k,final⟩ := by simpa only [fixed.2.2.2.2.2.1,fixed.2.2.2.2.2.2.1,fixed.2.2.2.2.2.2.2] using m.evidence
    have _ := costed.deterministic ((original.evaluatesWithCost_iff_steps rfl).mpr (literal []))
    have accepted := (elaborateRecursiveLocalComputation?_mapIds mapping injective names context e).trans (elaborateRecursiveLocalComputation?_iff.mpr original)
    have values : (Resolved.LocalScope.mapIds mapping env).values=env.values := Resolved.LocalScope.values_mapIds mapping env
    have mappedLiteral := renamedCost.toStepsWithContinuation relabeled (by rfl) []
    have completeRecord : ∀ fuel, (elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping context) e).map
        (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds mapping env).values store)))=
        some (.product .word .word,Core.runStateful fuel (.initial core env.values store)) := by intro fuel; rw [accepted,Option.map_some,values]
    check (decide (elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping context) e=some (core,.product .word .word))) "mapped exact checker"
    let arg := Core.Value.word (Core.Word.ofNatModulo 14)
    let checkpoints : List (Nat × Core.State) := [
      (16,⟨.ret (.cellRef .word 2),[.letBody (.var 1) [arg,.bool false],writeFrame w,readFrame r,.pairRight branch env.values],store++[arg]⟩),
      (25,⟨.ret .unit,[.letBody (.loadCell (.var 2)) [arg,.cellRef .word w],readFrame r,.pairRight branch env.values],final⟩),
      (33,⟨.ret (.word base),[.pairRight branch env.values],final⟩),
      (36,⟨.ret (.bool c),[.ifBranches (.unary .wordNot read) (.binary .wordAdd read (.var 0)) env.values,.pairApply (.word base)],final⟩)]
    for (spent,cp) in checkpoints do
      if genuine : Core.runStateful spent (.initial core env.values store)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        check (decide (Core.runStateful spent (.initial core (Resolved.LocalScope.mapIds mapping env).values store)=.outOfFuel cp ∧
          Core.runStateful (cost-spent) cp=.done value final)) "literal allocation/write/first-pair/conditional checkpoint"
      else throw (IO.userError "literal checkpoint is not genuine")
    for fuel in List.range (cost+2) do
      have _ := (literal []).runStateful_done_iff (fuel := fuel)
      have _ := mappedLiteral.runStateful_done_iff (fuel := fuel)
      have _ := completeRecord fuel
      check (decide (((elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping context) e).map (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds mapping env).values store)))) =
        some (.product .word .word,Core.runStateful fuel (.initial core env.values store)))) "exact optional Core/tag/value/store run"
      match exhausted : Core.runStateful fuel (.initial core env.values store) with
      | .done v s => check (decide (cost≤fuel ∧ v=value ∧ s=final)) "independent fixed completion"
      | .outOfFuel cp =>
          have _ := (literal []).residual_of_outOfFuel exhausted
          for more in [0,1,cost-fuel,cost+2] do
            check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core (Resolved.LocalScope.mapIds mapping env).values store))) "genuine full resumed state"
      | .fault _ _ => throw (IO.userError "unexpected fault")
    let k := [Core.Frame.pairApply (.cellRef .word 700)]
    have _ := costed.toStepsWithContinuation original rfl k
    check (decide (Core.runStateful (cost+1) ⟨.eval core (Resolved.LocalScope.mapIds mapping env).values,k,store⟩=.done (.pair (.cellRef .word 700) value) final)) "literal pending caller capture"
  else throw (IO.userError "independent source/Core/value/store/cost disagree")
private def skipped : IO Unit := do
  let e ← parsed "c ? r(w(a(x))) : Missing"
  let env := environment (.bool true) 2 2; let store : Core.Store := [.word (Core.Word.ofNatModulo 41),.word (Core.Word.ofNatModulo 99)]
  let a ← raw env store e
  if fixed : a.value=.word (Core.Word.ofNatModulo 14) ∧ a.final=store++[.word (Core.Word.ofNatModulo 14)] ∧ a.cost=35 then
    have counted : RecursiveLocalComputationEvaluatesWithCost names env store e (.word (Core.Word.ofNatModulo 14)) (store++[.word (Core.Word.ofNatModulo 14)]) 35 := by simpa only [fixed.1,fixed.2.1,fixed.2.2] using a.evidence
    have _ := (recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mpr counted
    have _ := (recursiveLocalComputationEvaluates_mapIds_iff mapping injective).mpr (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,a.evidence⟩)
    have _ := elaborateRecursiveLocalComputation?_mapIds mapping injective names context e
    check (decide (elaborateRecursiveLocalComputation? names context e=none ∧ elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping context) e=none)) "unselected unknown remains whole static rejection"
  else throw (IO.userError "raw skipped unknown exact cost")
private def faults : IO Unit := do
  let e ← parsed "(r(w(a(x))), c ? ~r(x) : r(x) + x)"; let p ← statics e
  let arg := Core.Value.word (Core.Word.ofNatModulo 14)
  for mode in List.range 4 do
    let w := if mode=0 then 700 else 2; let r := if mode=1 then 700 else if mode=3 then 0 else 2
    let c := if mode=2 then arg else Core.Value.bool true
    let env := environment c w r
    let store : Core.Store := [if mode=3 then .bool false else .word (Core.Word.ofNatModulo 41),.word (Core.Word.ofNatModulo 99)]
    let final := store++[arg]
    let tail : List Core.Frame := [.pairRight branch env.values]
    let writeK : List Core.Frame := [.storeCellValue (.var 0) [arg,.cellRef .word w],.letBody (.loadCell (.var 2)) [arg,.cellRef .word w],readFrame r]++tail
    let ifK : List Core.Frame := [.ifBranches (.unary .wordNot read) (.binary .wordAdd read (.var 0)) env.values,.pairApply arg]
    let unaryK : List Core.Frame := [.unaryApply .wordNot,.pairApply (.bool false)]
    let (threshold,before,failed,error) : Nat × Core.State × Core.State × Core.MachineFault :=
      if mode=0 then (22,⟨.eval (.var 1) [arg,.cellRef .word w],writeK,final⟩,⟨.ret (.cellRef .word w),writeK,final⟩,.invalidCellLocation 700)
      else if mode=1 then (32,⟨.eval (.var 1) [arg,.cellRef .word r],.loadCellApply::tail,final⟩,⟨.ret (.cellRef .word r),.loadCellApply::tail,final⟩,.invalidCellLocation 700)
      else if mode=2 then (36,⟨.eval (.var 1) env.values,ifK,final⟩,⟨.ret arg,ifK,final⟩,.expectedBool arg)
      else (46,⟨.ret (.cellRef .word 0),.loadCellApply::unaryK,final⟩,⟨.ret (.bool false),unaryK,final⟩,.invalidUnaryOperand .wordNot (.bool false))
    if fixed : p.core=core ∧ p.type=.product .word .word then
      have original : RecursiveLocalComputationElaborates names context e core (.product .word .word) := by simpa only [fixed.1,fixed.2] using p.evidence
      have _ := (recursiveLocalComputationElaborates_mapIds_iff mapping injective).mpr original
      have _ := elaborateRecursiveLocalComputation?_mapIds mapping injective names context e
      check (decide (Core.runStateful (threshold-1) (.initial core env.values store)=.outOfFuel before ∧
        Core.runStateful 1 before=.fault error failed)) "independent literal fault boundary preserves prior effects"
      for fuel in List.range (threshold+3) do
        let actual := Core.runStateful fuel (.initial core env.values store)
        check (decide ((elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping context) e).map
          (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds mapping env).values store)))=some (.product .word .word,actual))) "fault full mapped checker/run record"
        match actual with
        | .fault err st => check (decide (threshold≤fuel ∧ err=error ∧ st=failed)) "first fault cost/state"
        | .outOfFuel cp => check (decide (fuel<threshold ∧ Core.runStateful (threshold-fuel) cp=.fault error failed ∧
            Core.runStateful 1 cp=Core.runStateful (fuel+1) (.initial core (Resolved.LocalScope.mapIds mapping env).values store))) "genuine fault resumption"
        | .done _ _ => throw (IO.userError "unexpected bad-payload completion")
    else throw (IO.userError "bad actual store changed original static evidence")
end ParsedRecursiveIdentityEffects
open ParsedRecursiveIdentityEffects in
def frontendParsedRecursiveIdentityEffectTests : IO Unit := do
  have _ := not_surjective
  check (decide ((LocalNameTable.mapIds mapping names).lookup? "a"=some ⟨{owner with declarationIndex := 101},402⟩ ∧
    (Resolved.LocalScope.mapIds mapping context).ids=[mapping (id 7),mapping (id 15),mapping foreign,mapping (id 9),mapping (id 20),mapping foreign])) "foreign owner, sparse indices, first duplicate and duplicate ID retained"
  for depth in [0,2] do
    for c in [false,true] do
      exercise depth c 2 2 (Core.Word.ofNatModulo 14) [.word (Core.Word.ofNatModulo 41),.word (Core.Word.ofNatModulo 99),.word (Core.Word.ofNatModulo 14)]
      exercise depth c 0 1 (Core.Word.ofNatModulo 99) [.word (Core.Word.ofNatModulo 14),.word (Core.Word.ofNatModulo 99),.word (Core.Word.ofNatModulo 14)]
  skipped
  faults
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveNegatedComparisonEntries
/-! Independent original declaration certificates and manual paths retain actual captures, stores and whole results. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveNegatedComparisonEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveNegatedComparisonEntries",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-negated-comparison-entries.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) ("complete original bytes: "++text)
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span && decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original header and parameter ranges"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside named fixture")
private structure Parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span && decide (name.span.endByte≤annotation.span.startByte)) "original parameter fields/order"
      let m ← meaning types annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters types (s.bindFresh owner name.value arg.type)
            (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,
            by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate original parameter")
      else throw (IO.userError "original argument type mismatch")
  | _,_ => throw (IO.userError "original parameter arity")
private structure Path (core : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [original]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual var missing")
    | .letE head tail =>
        let a ← path n head env s; let b ← path n tail (a.value::env) a.final
        return ⟨b.value,b.final,a.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.letE (a.evidence _) (b.evidence _)⟩
    | .apply fn arg =>
        let f ← path n fn env s; let a ← path n arg env f.final
        match fv : f.value with
        | .closure _ _ body captured =>
            let b ← path n body (a.value::captured) a.final
            return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.apply (fv ▸ f.evidence _) (a.evidence _) (b.evidence [])⟩
        | _ => throw (IO.userError "manual callee shape")
    | .unary op operand =>
        let a ← path n operand env s
        match applied : op.apply a.value with
        | some v => return ⟨v,a.final,a.cost+2,fun _ => by rw [original]; exact CostStepComposition.unary (a.evidence _) applied⟩
        | none => throw (IO.userError "manual unary shape")
    | .binary op left right =>
        let a ← path n left env s; let b ← path n right env a.final
        match applied : op.apply a.value b.value with
        | some v => return ⟨v,b.final,a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.binary (a.evidence _) (b.evidence _) applied⟩
        | none => throw (IO.userError "manual binary shape")
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [original]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual load missing")
        | _ => throw (IO.userError "manual reference shape")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Certificate (Elaborates : Core.Expr → Core.Ty → Prop) (Evaluates : Core.Value → Core.Store → Nat → Prop) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : Elaborates core type
  raw : Evaluates value final cost
private abbrev Child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) :=
  Certificate (RecursiveLocalComputationElaborates s.names s.context source) (RecursiveLocalComputationEvaluatesWithCost s.names env store source)
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (source.span.contains fn.span && source.span.contains argsSpan && argsSpan.contains arg.span &&
        decide (fn.span.endByte ≤ argsSpan.startByte)) "original recursive child order"
      let f ← child s env store fn; let a ← child s env f.final arg
      match ft : f.type, fv : f.value with
      | .function input output,.closure _ _ body captured =>
          if same : a.type=input then
            let b ← path 100 body (a.value::captured) a.final
            return ⟨.apply f.core a.core,output,b.value,b.final,f.cost+a.cost+b.cost+3,
              by rw [original]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
              by rw [original]; exact .application (fv ▸ f.raw) a.raw (b.evidence [])⟩
          else throw (IO.userError "static argument differs")
      | _,_ => throw (IO.userError "static or actual Function differs")
  | ⟨_,.binary left ⟨opSpan,op⟩ right⟩ =>
      check (source.span.contains left.span && source.span.contains right.span && source.span.contains opSpan &&
        decide (left.span.endByte≤opSpan.startByte ∧ opSpan.endByte≤right.span.startByte)) "original comparison child/operator order"
      let l ← child s env store left; let r ← child s env l.final right
      if typed : l.type=.word ∧ r.type=.word then
        match lv : l.value, rv : r.value with
        | .word a,.word b =>
            match which : op with
            | .notEqual => return ⟨.unary .boolNot (.binary .wordEq l.core r.core),.bool,.bool (!(a==b)),r.final,l.cost+r.cost+5,
                by rw [original,which]; exact .notEqual (typed.1 ▸ l.elaboration) (typed.2 ▸ r.elaboration),
                by rw [original,which]; exact .notEqual (lv ▸ l.raw) (rv ▸ r.raw)⟩
            | .lessEqual => return ⟨.unary .boolNot (.binary .wordGt l.core r.core),.bool,.bool (!(decide (a>b))),r.final,l.cost+r.cost+5,
                by rw [original,which]; exact .lessEqual (typed.1 ▸ l.elaboration) (typed.2 ▸ r.elaboration),
                by rw [original,which]; exact .lessEqual (lv ▸ l.raw) (rv ▸ r.raw)⟩
            | _ => throw (IO.userError "outside two negated comparisons")
        | _,_ => throw (IO.userError "actual comparison operands are not Word")
      else throw (IO.userError "original comparison operands are not Word")
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨.var i,t,v,store,1,
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original row missing")
      | none => throw (IO.userError "original actual name missing")
  | _ => throw (IO.userError "outside fixture expression")
termination_by sizeOf source
private abbrev Tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) :=
  Certificate (RecursiveComputationReturnTreeElaborates types owner s source) (RecursiveComputationReturnTreeEvaluatesWithCost owner s.names env store source)
private def tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) : IO (Tree types s env store source) := do
  check (source.value.all fun statement => source.span.contains statement.span) "original statement spans"
  match original : source with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
      let a ← child s env store e
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .expression a.elaboration,by rw [original]; exact .expression a.raw⟩
  | _ => throw (IO.userError "outside original singleton return body")
private def header (types : TypeNameTable) (source : Syntax.FunctionDecl) (output : Core.Ty) : IO (PLift (RuntimeFunctionHeader types source.value.signature output)) := do
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.1=output then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧
            source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          return ⟨⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.2.down)⟩⟩
        else throw (IO.userError "original header policy")
      else throw (IO.userError "original return meaning")
  | _ => throw (IO.userError "original singleton return clause")
private def bodySource (body : String) : IO Syntax.FunctionDecl := parsed ("function comparison(f:F,g:G,x:X,y:Y) returns(R){"++body++"}")
private def verify (source : Syntax.FunctionDecl) (f g x y : TypedRuntimeArgument) (output : Core.Ty) (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO PreparedRuntimeFunction := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["Y"],y.type),(["R"],output),(["Word"],.word)]
  let args := [f,g,x,y]; let ps ← parameters types .empty .empty source.value.signature.parameters.elements args
  let inputs := ps.actual; let env := inputs.environment.values
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body; let manual ← path 100 core env s
  have erased : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  check (decide (env=[y.value,x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("y",⟨owner,3⟩,y.type,y.value),("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
  check (decide (b.value=value ∧ b.final=final ∧ b.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent raw/Core value/store/cost"
  if fixed : b.core=core ∧ b.type=output then
    let compiled : CompiledRuntimeFunction := ⟨ps.statics,core,output⟩; let prepared : PreparedRuntimeFunction := ⟨inputs,core,output⟩
    have preparation : RecursiveComputationFunctionPrepares types owner source args prepared := ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have compilation : RecursiveComputationFunctionCompiles types owner source compiled := ⟨h.down,ps.declared,by simpa only [compiled,prepared,erased] using preparation.body⟩
    have compiledSome := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
    have preparedSome := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr preparation
    have matching : args.map (·.type)=ps.statics.context.values.reverse := by
      have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
      simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
    have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some compiled := by
      rw [prepareComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte]
    have whole (fuel) (store) : runRecursiveComputationFunction? types owner source args fuel store = some (output,Core.runStateful fuel (.initial core [y.value,x.value,g.value,f.value] store)) := by
      rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte,args,List.reverse_cons,List.reverse_nil]; rfl
    have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
    have _ := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation b.raw b.elaboration ids []
    check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old entry remains None"
    for fuel in List.range (cost+2) do
      have _ := whole fuel s
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial core env s)) ∧ runRuntimeComputationFunction? types owner source args fuel s=none)) "whole full result/tag"
      match exhausted : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact completion"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel exhausted; have _ := Core.runStateful_resume exhausted 2
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧ runRecursiveComputationFunction? types owner source args (fuel+2) s=some (output,Core.runStateful 2 cp))) "genuine saved state/residual/full resume"
      | .fault _ _ => throw (IO.userError "independent successful path faulted")
    return prepared
  else throw (IO.userError "independent exact Core/type")
private def reader (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word location],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word location],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def arg (value : Nat) : TypedRuntimeArgument := ⟨.word,w value,.word⟩
end RecursiveNegatedComparisonEntries
open RecursiveNegatedComparisonEntries
def frontendParsedRecursiveNegatedComparisonEntryTests : IO Unit := do
  let left := Core.Expr.apply (.var 3) (.var 1); let right := Core.Expr.apply (.var 2) (.var 0)
  let f := reader 0; let g := writer 0; let x := arg 11; let y := arg 14
  for le in [false,true] do
    let source ← bodySource (if le then "return f(x) <= g(y);" else "return f(x) != g(y);")
    let op := if le then Core.BinaryOp.wordGt else .wordEq
    let core := Core.Expr.unary .boolNot (.binary op left right)
    for (old,rhs) in [(23,14),(14,23),(14,14),(0,2^256-1),(2^256-1,0),(2^255,2^255),(2^256-1,2^255)] do
      discard <| verify source f g x (arg rhs) .bool core [w old] [w rhs] (.bool (if le then old≤rhs else old≠rhs)) 28
    discard <| verify source g f x y .bool core [w 23] [w 11] (.bool le) 28
    discard <| verify source (reader 1) g x y .bool core [w 23,w 7] [w 14,w 7] (.bool true) 28
    discard <| verify source g (reader 1) y x .bool core [w 23,w 7] [w 14,w 7] (.bool (!le)) 28
    discard <| verify source f g y x .bool core [w 23] [w 11] (.bool (!le)) 28
  let source ← bodySource "return f(x) != g(y);"
  let core := Core.Expr.unary .boolNot (.binary .wordEq left right)
  let prepared ← verify source f g x y .bool core [w 23] [w 14] (.bool true) 28
  let env := prepared.inputs.environment.values
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],.word),(["Y"],.word),(["R"],.bool),(["Word"],.word)]
  let run := runRecursiveComputationFunction? types owner source [f,g,x,y]
  let unary : List Core.Frame := [.unaryApply .boolNot]
  let between : Core.State := ⟨.ret (w 23),.binaryRight .wordEq right env::unary,[w 23]⟩
  let last : Core.State := ⟨.ret (w 14),.binaryApply .wordEq (w 23)::unary,[w 14]⟩
  let negation : Core.State := ⟨.ret (.bool false),unary,[w 14]⟩
  check (decide (run 10 [w 23]=some (.bool,.outOfFuel between) ∧ run 26 [w 23]=some (.bool,.outOfFuel last) ∧ run 27 [w 23]=some (.bool,.outOfFuel negation) ∧ Core.runStateful 18 between=.done (.bool true) [w 14] ∧ Core.runStateful 2 last=.done (.bool true) [w 14] ∧ Core.runStateful 1 negation=.done (.bool true) [w 14])) "genuine binaryRight/binaryApply/unaryApply with original captures and intermediate store"
  let badState : Core.State := ⟨.ret (w 14),.binaryApply .wordEq (.bool true)::unary,[w 14]⟩
  let bad := Core.StatefulRunResult.fault (.invalidBinaryOperands .wordEq (.bool true) (w 14)) badState
  let badCp : Core.State := ⟨.ret (.cellRef .word 0),.loadCellApply::.binaryApply .wordEq (.bool true)::unary,[w 14]⟩
  let emptyCp : Core.State := ⟨.eval (.var 1) env,.applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word 0]::.binaryRight .wordEq right env::unary,[]⟩
  let empty := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),.loadCellApply::.binaryRight .wordEq right env::unary,[]⟩
  check (decide (run 25 [.bool true]=some (.bool,.outOfFuel badCp) ∧ run 26 [.bool true]=some (.bool,bad) ∧ Core.runStateful 1 badCp=bad ∧ run 5 []=some (.bool,.outOfFuel emptyCp) ∧ run 9 []=some (.bool,empty) ∧ Core.runStateful 4 emptyCp=empty)) "right write survives invalid left comparison; left child fault prevents right"
  let leftMissingEnv := [y.value,x.value,g.value,(reader 1).value]
  let leftMissingRun := runRecursiveComputationFunction? types owner source [reader 1,g,x,y]
  let leftMissingCp : Core.State := ⟨.eval (.var 1) [x.value,.cellRef .word 1],.loadCellApply::.binaryRight .wordEq right leftMissingEnv::unary,[w 23]⟩
  let leftMissing := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),.loadCellApply::.binaryRight .wordEq right leftMissingEnv::unary,[w 23]⟩
  check (decide (leftMissingRun 8 [w 23]=some (.bool,.outOfFuel leftMissingCp) ∧ leftMissingRun 9 [w 23]=some (.bool,leftMissing) ∧ Core.runStateful 1 leftMissingCp=leftMissing)) "missing left cell leaves writable right cell untouched"
  let rf := writer 0; let rg := reader 1
  let changed ← verify source rf rg x y .bool core [w 23,w 14] [w 11,w 14] (.bool true) 28
  let changedEnv := changed.inputs.environment.values
  let changedRun := runRecursiveComputationFunction? types owner source [rf,rg,x,y]
  let missingCp : Core.State := ⟨.eval (.var 1) [y.value,.cellRef .word 1],.loadCellApply::.binaryApply .wordEq (w 11)::unary,[w 11]⟩
  let missing := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),.loadCellApply::.binaryApply .wordEq (w 11)::unary,[w 11]⟩
  check (decide (changedRun 24 [w 23]=some (.bool,.outOfFuel missingCp) ∧ changedRun 25 [w 23]=some (.bool,missing) ∧ Core.runStateful 1 missingCp=missing)) "missing right preserves earlier left write and pending negation"
  let wrongRightCp : Core.State := ⟨.ret (.cellRef .word 1),.loadCellApply::.binaryApply .wordEq (w 11)::unary,[w 11,.bool false]⟩
  let wrongRight := Core.StatefulRunResult.fault (.invalidBinaryOperands .wordEq (w 11) (.bool false)) ⟨.ret (.bool false),.binaryApply .wordEq (w 11)::unary,[w 11,.bool false]⟩
  check (decide (changedRun 25 [w 23,.bool false]=some (.bool,.outOfFuel wrongRightCp) ∧ changedRun 26 [w 23,.bool false]=some (.bool,wrongRight) ∧ Core.runStateful 1 wrongRightCp=wrongRight)) "wrong actual right Word payload retains left write and unapplied negation"
  for (actualEnv,actualRun) in [(env,run),(changedEnv,changedRun)] do
    for store in [[w 23],[.bool true],[],[w 23,.bool false],[w 23,w 14]] do
      for fuel in List.range 30 do
        check (decide (actualRun fuel store=some (.bool,Core.runStateful fuel (.initial core actualEnv store)))) "same prepared actual values retain arbitrary stores and declared Bool tag"
        match exhausted : Core.runStateful fuel (.initial core actualEnv store) with
        | .outOfFuel residual =>
            have _ := Core.runStateful_resume exhausted 40
            check (decide (actualRun (fuel+40) store=some (.bool,Core.runStateful 40 residual))) "all genuine checkpoints resume complete success or fault"
        | _ => pure ()
  for body in ["return f(x) != missing;","return missing <= g(y);","return f(x) != (x==y);","return (x==y) <= g(y);"] do
    let rejected ← bodySource body
    check (decide (compileRecursiveComputationFunction? types owner rejected=none ∧ prepareRecursiveComputationFunction? types owner rejected [f,g,x,y]=none ∧ runRecursiveComputationFunction? types owner rejected [f,g,x,y] 50 [w 23]=none)) "whole Word gates and unknown names"
  let wrongReturn ← parsed "function comparison(f:F,g:G,x:X,y:Y) returns(Word){return f(x) != g(y);}"
  check (decide (elaborateRecursiveComputationReturnTree? types owner prepared.inputs.toTypeInputs wrongReturn.value.body=some (core,.bool) ∧ compileRecursiveComputationFunction? types owner wrongReturn=none ∧ prepareRecursiveComputationFunction? types owner wrongReturn [f,g,x,y]=none)) "original Bool comparison body versus declared Word"
  for body in ["f(x)<=g(y)<=x","f(x)!=g(y)!=x"] do
    let file : Syntax.SourceFile := ⟨⟨.main,"nonassociative-comparison-entry.sol"⟩,"function comparison(f:F,g:G,x:X,y:Y) returns(R){return "++body++";}"⟩
    let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "non-associative fixture lexer")
    check tokens.diagnostics.isEmpty "original chained comparison lexes"
    match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) with
    | .ok _ next => check (!next.diagnostics.isEmpty || !next.atEnd) "comparison grammar remains non-associative"
    | .reject _ _ => pure ()
    | .invariant _ => throw (IO.userError "non-associative parser invariant")
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveNegatedComparisonMigrations
/-! Two original rejection fixtures retain the exact Binary caller and source file.
Only the new recursive interpretation changes; old endpoints still reject them. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveNegatedComparisonMigrations

private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Binary",by decide⟩],by decide⟩⟩,56⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("f",foreign),("g",id 9),("y",id 14),("c",id 15),("f",id 88)]
private def context : Resolved.Context := [(id 7,.word),(foreign,.function .word .word),(id 9,.function .word .word),(id 14,.word),(id 15,.bool),(foreign,.bool)]

private structure Static (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates table ctx s core type
  typing : RecursiveLocalComputationHasType table ctx s type

private def statics (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) :
    IO (Static table ctx s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : table.lookup? name.value with
      | some localId =>
          match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some t,some n =>
              have r : ResolvesLocalExpression table s (.var localId) := by
                rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named)
              have ty : Resolved.HasType ctx (.var localId) t := .var (Resolved.LocalScope.lookup?_iff.mp typed)
              return ⟨.var n,t,.pure r (.var (Resolved.LocalScope.index?_iff.mp indexed)) ty,.pure (r.reflects_type ty)⟩
          | _,_ => throw (IO.userError "original ordered context")
      | _ => throw (IO.userError "original names")
  | ⟨_,.group inner⟩ =>
      let a ← statics table ctx inner
      return ⟨a.core,a.type,by rw [shape]; exact .group a.elaboration,by rw [shape]; exact .group a.typing⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← statics table ctx fn; let a ← statics table ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,
            by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨_,.binary left ⟨_,.notEqual⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.word ∧ b.type=.word then return ⟨.unary .boolNot (.binary .wordEq a.core b.core),.bool,
        by rw [shape]; exact .notEqual (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .notEqual (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Word comparison children")
  | ⟨_,.binary left ⟨_,.lessEqual⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.word ∧ b.type=.word then return ⟨.unary .boolNot (.binary .wordGt a.core b.core),.bool,
        by rw [shape]; exact .lessEqual (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .lessEqual (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Word comparison children")
  | _ => throw (IO.userError "migration original shape")
termination_by sizeOf s

end ParsedRecursiveNegatedComparisonMigrations
open ParsedRecursiveNegatedComparisonMigrations

def frontendParsedRecursiveNegatedComparisonMigrationTests : IO Unit := do
  for (text,op) in [("f(x) != g(y)",Core.BinaryOp.wordEq),("f(x) <= g(y)",.wordGt)] do
    let expected := Core.Expr.unary .boolNot (.binary op (.apply (.var 1) (.var 0)) (.apply (.var 2) (.var 3)))
    let file : Syntax.SourceFile := ⟨⟨.main,"recursive-binary.sol"⟩,text⟩
    let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "migration lexer")
    let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError "migration parser")
    check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "unchanged original parsed source"
    let a ← statics names context s
    have _ := elaborateRecursiveLocalComputation?_iff.mpr a.elaboration
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp a.typing
    have _ := a.elaboration.core_hasType
    check (decide (a.core=expected ∧ a.type=.bool ∧
      elaborateRecursiveLocalComputation? names context s=some (expected,.bool) ∧
      elaborateLocalExpression? names context s=none ∧
      elaborateLocalComputation? names context s=none)) "exact new comparison and unchanged old rejections"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveNegatedComparisons
/-! Original comparison syntax has independent static/raw evidence and separate
literal Core/manual paths; actual captures and pending frames are retained. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveNegatedComparisons
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"NegatedComparisons",by decide⟩],by decide⟩⟩,60⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("y",id 14),("c",id 15),("d",id 16),("f",foreign),("g",id 9),("p",id 20),("maker",id 25),("true",id 90),("false",id 91),("f",id 88)]
private def context (a : Core.Ty) : Resolved.Context := [(id 7,a),(id 14,a),(id 15,.bool),(id 16,.bool),(foreign,.function a a),(id 9,.function a a),(id 20,.function .bool .bool),(id 25,.function a (.function a a)),(id 90,.bool),(id 91,.bool),(foreign,.bool)]
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.bool false]
private def environment (a : Core.Ty) (x y : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(id 7,x),(id 14,y),(id 15,.bool c),(id 16,.bool d),(foreign,identity a),(id 9,identity a),(id 20,identity .bool),(id 25,.closure a (.function a a) (.var 1) [identity a]),(id 90,.bool false),(id 91,.bool true),(foreign,.bool false)]
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def wrap : Nat → String → String | 0,s => s | n+1,s => "("++wrap n s++")"
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-negated-comparisons.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError s!"parser: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "original bytes/span"
  return s
private structure Static (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates names ctx s core type
  typing : RecursiveLocalComputationHasType names ctx s type
private def statics (ctx : Resolved.Context) (s : Syntax.Expr) : IO (Static ctx s) := do
  match shape : s with
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span) "group span"; let a ← statics ctx inner
      return ⟨a.core,a.type,by rw [shape]; exact .group a.elaboration,by rw [shape]; exact .group a.typing⟩
  | ⟨span,.unary ⟨opSpan,op⟩ inner⟩ =>
      check (span.contains inner.span && span.contains opSpan && decide (span.startByte=opSpan.startByte ∧ opSpan.endByte=opSpan.startByte+1 ∧ opSpan.endByte≤inner.span.startByte)) "original prefix bytes/order"
      let a ← statics ctx inner
      match which : op with
      | .logicalNot => if same : a.type=.bool then return ⟨.unary .boolNot a.core,.bool,by rw [shape,which]; exact .logicalNot (same ▸ a.elaboration),by rw [shape,which]; exact .logicalNot (same ▸ a.typing)⟩ else throw (IO.userError "Bool operand")
      | .bitNot => if same : a.type=.word then return ⟨.unary .wordNot a.core,.word,by rw [shape,which]; exact .bitNot (same ▸ a.elaboration),by rw [shape,which]; exact .bitNot (same ▸ a.typing)⟩ else throw (IO.userError "Word operand")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call children"
      let f ← statics ctx fn; let a ← statics ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨span,.binary left ⟨opSpan,op⟩ right⟩ =>
      check (span.contains left.span && span.contains right.span && span.contains opSpan && decide (left.span.endByte≤opSpan.startByte ∧ opSpan.endByte=opSpan.startByte+2 ∧ opSpan.endByte≤right.span.startByte)) "original two-byte operator/children order"
      let a ← statics ctx left; let b ← statics ctx right
      match which : op with
      | .notEqual => if same : a.type=.word ∧ b.type=.word then return ⟨.unary .boolNot (.binary .wordEq a.core b.core),.bool,
          by rw [shape,which]; exact .notEqual (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .notEqual (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Word comparison operands")
      | .lessEqual => if same : a.type=.word ∧ b.type=.word then return ⟨.unary .boolNot (.binary .wordGt a.core b.core),.bool,
          by rw [shape,which]; exact .lessEqual (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .lessEqual (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Word comparison operands")
      | .logicalAnd => if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core b.core (.bool false),.bool,
          by rw [shape,which]; exact .logicalAnd (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .logicalAnd (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Bool logical operands")
      | .logicalOr => if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core (.bool true) b.core,.bool,
          by rw [shape,which]; exact .logicalOr (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .logicalOr (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Bool logical operands")
      | _ => throw (IO.userError "outside fixed comparison fixture")
  | ⟨span,.conditional guard question yes colon no⟩ =>
      check (span.contains guard.span && span.contains yes.span && span.contains no.span && span.contains question && span.contains colon &&
        decide (guard.span.endByte≤question.startByte ∧ question.endByte=question.startByte+1 ∧ question.endByte≤yes.span.startByte ∧
          yes.span.endByte≤colon.startByte ∧ colon.endByte=colon.startByte+1 ∧ colon.endByte≤no.span.startByte)) "original question/colon order"
      let g ← statics ctx guard; let a ← statics ctx yes; let b ← statics ctx no
      if valid : g.type=.bool ∧ b.type=a.type then return ⟨.ifE g.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ g.elaboration) a.elaboration (valid.2 ▸ b.elaboration),
        by rw [shape]; exact .conditional (valid.1 ▸ g.typing) a.typing (valid.2 ▸ b.typing)⟩
      else throw (IO.userError "whole conditional types")
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some t,some n =>
              have r : ResolvesLocalExpression names s (.var localId) := by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named)
              have ty : Resolved.HasType ctx (.var localId) t := .var (Resolved.LocalScope.lookup?_iff.mp typed)
              return ⟨.var n,t,(LocalComputationElaborates.pure r (.var (Resolved.LocalScope.index?_iff.mp indexed)) ty).toRecursiveLocalComputation,.pure (r.reflects_type ty)⟩
          | _,_ => throw (IO.userError "caller row")
      | _ => throw (IO.userError "caller name")
  | _ => throw (IO.userError "outside original source fixture")
termination_by sizeOf s
private structure RawLeaf (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, LocalExpressionEvaluatesWithCost names env store s value store 1
private def rawLeaf (env : Resolved.Environment) (s : Syntax.Expr) : IO (RawLeaf env s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : env.lookup? localId with
          | some v => return ⟨v,fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _ => throw (IO.userError "actual row")
      | _ => throw (IO.userError "actual name")
  | _ => throw (IO.userError "actual identifier")
private structure Actual (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost names env store s value store cost
private def actual (env : Resolved.Environment) (s : Syntax.Expr) : IO (Actual env s) := do
  match shape : s with
  | ⟨_,.group inner⟩ => let a ← actual env inner; return ⟨a.value,a.cost,fun store => by rw [shape]; exact .group (a.evidence store)⟩
  | ⟨_,.unary ⟨_,op⟩ inner⟩ =>
      let a ← actual env inner
      match which : op, v : a.value with
      | .logicalNot,.bool b => return ⟨.bool (!b),a.cost+2,fun store => by rw [shape,which]; exact .logicalNot (v ▸ a.evidence store)⟩
      | .bitNot,.word w => return ⟨.word w.bitNot,a.cost+2,fun store => by rw [shape,which]; exact .bitNot (v ▸ a.evidence store)⟩
      | _,_ => throw (IO.userError "actual unary payload")
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← actual env fn; let a ← actual env arg
      match closure : f.value with
      | .closure _ _ (.var n) captured =>
          match found : (a.value::captured)[n]? with
          | some v => return ⟨v,f.cost+a.cost+4,fun store => by rw [shape]; exact .application (closure ▸ f.evidence store) (a.evidence store) (.cons (.var found) .refl)⟩
          | _ => throw (IO.userError "actual captured index")
      | _ => throw (IO.userError "fixture body")
  | ⟨_,.binary left ⟨_,.logicalAnd⟩ right⟩ =>
      let a ← actual env left
      match value : a.value with
      | .bool false => return ⟨.bool false,a.cost+3,fun store => by rw [shape]; exact .andFalse (value ▸ a.evidence store)⟩
      | .bool true => let b ← actual env right; return ⟨b.value,a.cost+b.cost+2,fun store => by rw [shape]; exact .andTrue (value ▸ a.evidence store) (b.evidence store)⟩
      | _ => throw (IO.userError "actual conjunction left Bool")
  | ⟨_,.binary left ⟨_,.logicalOr⟩ right⟩ =>
      let a ← actual env left
      match value : a.value with
      | .bool true => return ⟨.bool true,a.cost+3,fun store => by rw [shape]; exact .orTrue (value ▸ a.evidence store)⟩
      | .bool false => let b ← actual env right; return ⟨b.value,a.cost+b.cost+2,fun store => by rw [shape]; exact .orFalse (value ▸ a.evidence store) (b.evidence store)⟩
      | _ => throw (IO.userError "actual disjunction left Bool")
  | ⟨_,.binary left ⟨_,op⟩ right⟩ =>
      let a ← actual env left; let b ← actual env right
      match lv : a.value, rv : b.value with
      | .word l,.word r =>
          match which : op with
          | .notEqual => return ⟨.bool (!(l==r)),a.cost+b.cost+5,fun store => by rw [shape,which]; exact .notEqual (lv ▸ a.evidence store) (rv ▸ b.evidence store)⟩
          | .lessEqual => return ⟨.bool (!(decide (l>r))),a.cost+b.cost+5,fun store => by rw [shape,which]; exact .lessEqual (lv ▸ a.evidence store) (rv ▸ b.evidence store)⟩
          | _ => throw (IO.userError "actual fixed operator")
      | _,_ => throw (IO.userError "actual Word comparison operands")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← actual env guard
      match gv : g.value with
      | .bool true => let a ← actual env yes; return ⟨a.value,g.cost+a.cost+2,fun store => by rw [shape]; exact .ifTrue (gv ▸ g.evidence store) (a.evidence store)⟩
      | .bool false => let b ← actual env no; return ⟨b.value,g.cost+b.cost+2,fun store => by rw [shape]; exact .ifFalse (gv ▸ g.evidence store) (b.evidence store)⟩
      | _ => throw (IO.userError "actual Bool")
  | _ => let a ← rawLeaf env s; return ⟨a.value,1,fun store => .pure (a.evidence store)⟩
termination_by sizeOf s
private structure Path (env : Core.Environment) (core : Core.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store k, Core.Steps cost ⟨.eval core env,k,store⟩ ⟨.ret value,k,store⟩
private def manual : (fuel : Nat) → (env : Core.Environment) → (core : Core.Expr) → IO (Path env core)
  | 0,_,_ => throw (IO.userError "manual certificate depth")
  | fuel+1,env,core => do
    match shape : core with
    | .bool b => return ⟨.bool b,1,fun _ _ => by rw [shape]; exact .cons .bool .refl⟩
    | .var n => match found : env[n]? with
      | some v => return ⟨v,1,fun _ _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | _ => throw (IO.userError "manual variable")
    | .unary op inner =>
      let a ← manual fuel env inner
      match applied : op.apply a.value with
      | some v => return ⟨v,a.cost+2,fun store k => by rw [shape]; exact CostStepComposition.unary (a.evidence store _) applied⟩
      | _ => throw (IO.userError "manual unary")
    | .binary op left right =>
      let a ← manual fuel env left; let b ← manual fuel env right
      match applied : op.apply a.value b.value with
      | some v => return ⟨v,a.cost+b.cost+3,fun store k => by rw [shape]; exact CostStepComposition.binary (a.evidence store _) (b.evidence store _) applied⟩
      | _ => throw (IO.userError "manual binary")
    | .apply fn arg =>
      let f ← manual fuel env fn; let a ← manual fuel env arg
      match closure : f.value with
      | .closure _ _ (.var n) captured => match found : (a.value::captured)[n]? with
        | some v => return ⟨v,f.cost+a.cost+4,fun store _ => by rw [shape]; exact CostStepComposition.apply (closure ▸ f.evidence store _) (a.evidence store _) (.cons (.var found) .refl)⟩
        | _ => throw (IO.userError "manual body index")
      | _ => throw (IO.userError "manual closure")
    | .ifE guard yes no =>
      let g ← manual fuel env guard
      match gv : g.value with
      | .bool true => let a ← manual fuel env yes; return ⟨a.value,g.cost+a.cost+2,fun store k => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence store _) (a.evidence store k)⟩
      | .bool false => let b ← manual fuel env no; return ⟨b.value,g.cost+b.cost+2,fun store k => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence store _) (b.evidence store k)⟩
      | _ => throw (IO.userError "manual guard")
    | _ => throw (IO.userError "manual Core grammar")
private def exercise (text : String) (a : Core.Ty) (x y : Core.Value) (c d : Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) (pureSource : Bool := false) : IO Unit := do
  let s ← parsed text; let env := environment a x y c d; let p ← statics (context a) s; let r ← actual env s; let m ← manual 30 env.values core
  if fixed : p.core=core ∧ p.type=type ∧ r.value=value ∧ r.cost=cost ∧ m.value=value ∧ m.cost=cost then
    have e : RecursiveLocalComputationElaborates names (context a) s core type := by simpa only [fixed.1,fixed.2.1] using p.elaboration
    have _ := elaborateRecursiveLocalComputation?_iff.mp (elaborateRecursiveLocalComputation?_iff.mpr e)
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp p.typing
    have _ := e.core_hasType
    check (decide (elaborateRecursiveLocalComputation? names (context a) s=some (core,type) ∧ elaborateLocalExpression? names (context a) s=(if pureSource then some (core,type) else none) ∧ elaborateLocalComputation? names (context a) s=(if pureSource then some (core,type) else none))) "new exact and original pure/old endpoint boundary"
    for store in [[],[Core.Value.bool true,.cellRef .word 91]] do
      have counted : RecursiveLocalComputationEvaluatesWithCost names env store s value store cost := by simpa only [fixed.2.2.1,fixed.2.2.2.1] using r.evidence store
      have path : ∀ k, Core.Steps cost ⟨.eval core env.values,k,store⟩ ⟨.ret value,k,store⟩ := by simpa only [fixed.2.2.2.2.1,fixed.2.2.2.2.2] using m.evidence store
      have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨cost,counted⟩
      have coreRaw := (e.evaluates_iff rfl).mp raw
      have _ := counted.deterministic ((e.evaluatesWithCost_iff_steps rfl).mpr (path []))
      let pending : List Core.Frame := [.letBody .unit []]
      have _ := counted.toStepsWithContinuation e rfl pending
      for fuel in List.range (cost+2) do
        have _ := (path []).runStateful_done_iff (fuel := fuel)
        match outcome : Core.runStateful fuel (.initial core env.values store) with
        | .done v st => check (decide (cost≤fuel ∧ v=value ∧ st=store)) "literal value/store/threshold"
        | .outOfFuel cp =>
            have _ := (path []).residual_of_outOfFuel outcome
            check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value store ∧ Core.runStateful 1 cp=Core.runStateful (fuel+1) (.initial core env.values store))) "genuine residual/full replay"
        | .fault _ _ => throw (IO.userError "fixed path fault")
      have fragment := e.core_fragment
      have _ := fragment.weakenAt 3
      for cutoff in [0,3] do
        let leading := env.values.take cutoff; let suffix := env.values.drop cutoff
        have same : leading++suffix=env.values := List.take_append_drop cutoff env.values
        let inserted : Core.Value := .closure .bool .unit (.var 99) [.cellRef .word 77]
        have original : Core.Evaluates (leading++suffix) store core value store := by rw [same]; exact coreRaw
        have changed := (fragment.evaluates_insert_iff leading suffix inserted).mpr original
        have paired : ∀ k, Core.Steps cost ⟨.eval core (leading++suffix),k,store⟩ ⟨.ret value,k,store⟩ ∧
            Core.Steps cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),k,store⟩ ⟨.ret value,k,store⟩ := by
          obtain ⟨n,paths⟩ := fragment.insertion_paths leading suffix inserted original
          have eqCost : n=cost := ((paths []).1.final_unique (by simpa only [same,Core.State.final] using path [])).1
          exact eqCost ▸ paths
        check (decide (Core.runStateful cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),pending,store⟩=.outOfFuel ⟨.ret value,pending,store⟩)) "inserted pending endpoint"
  else throw (IO.userError s!"independent certificate mismatch: {text}")
private def skippedOverlap (isLe : Bool) : IO Unit := do
  let s ← parsed (if isLe then "(c ? x : Missing) <= y" else "(c ? x : Missing) != y")
  let w := Core.Word.ofNatModulo; let env := environment .word (.word (w 17)) (.word (w 5)) true false; let fresh ← actual env s
  match shape : s with
  | ⟨_,.binary ⟨_,.group ⟨_,.conditional guard _ yes _ _⟩⟩ ⟨_,op⟩ right⟩ =>
      let g ← rawLeaf env guard; let l ← rawLeaf env yes; let r ← rawLeaf env right
      if same : g.value=.bool true ∧ l.value=.word (w 17) ∧ r.value=.word (w 5) then
        match which : op with
        | .notEqual =>
            have old : LocalComputationEvaluatesWithCost names env [] s (.bool true) [] 10 := .pure (by rw [shape,which]; exact .notEqual (.group (.ifTrue (same.1 ▸ g.evidence []) (same.2.1 ▸ l.evidence []))) (same.2.2 ▸ r.evidence []))
            have _ := (fresh.evidence []).deterministic old.toRecursiveLocalComputation
        | .lessEqual =>
            have old : LocalComputationEvaluatesWithCost names env [] s (.bool false) [] 10 := .pure (by rw [shape,which]; exact .lessEqual (.group (.ifTrue (same.1 ▸ g.evidence []) (same.2.1 ▸ l.evidence []))) (same.2.2 ▸ r.evidence []))
            have _ := (fresh.evidence []).deterministic old.toRecursiveLocalComputation
        | _ => throw (IO.userError "original comparison")
      else throw (IO.userError "old actual leaves")
  | _ => throw (IO.userError "original skipped conditional")
  check (decide (fresh.value=.bool (!isLe) ∧ fresh.cost=10 ∧ elaborateRecursiveLocalComputation? names (context .word) s=none)) "pure/new comparison overlap skips unknown syntax"
private def sourceCalls (fn arg : String) : Nat → String | 0 => arg | n+1 => fn++"("++sourceCalls fn arg n++")"
private def coreCalls (fn arg : Nat) : Nat → Core.Expr | 0 => .var arg | n+1 => .apply (.var fn) (coreCalls fn arg n)
end ParsedRecursiveNegatedComparisons
open ParsedRecursiveNegatedComparisons
def frontendParsedRecursiveNegatedComparisonTests : IO Unit := do
  let w := Core.Word.ofNatModulo; let hi := 2^255; let max := Core.wordModulus-1
  for (l,r,ne,le) in [(0,0,false,true),(0,max,true,true),(max,0,true,false),(hi,hi,false,true),
      (hi,hi-1,true,false),(hi-1,hi,true,true),(17,5,true,false),(5,17,true,true)] do
    for isLe in [false,true] do
      let op := if isLe then Core.BinaryOp.wordGt else .wordEq; let token := if isLe then " <= " else " != "
      let value := if isLe then le else ne; let join (a b : Core.Expr) := Core.Expr.unary .boolNot (.binary op a b)
      exercise ("x"++token++"y") .word (.word (w l)) (.word (w r)) false false (join (.var 0) (.var 1)) .bool (.bool value) 7 true
      for depth in [1,3,8] do
        let left := coreCalls 4 0 depth; let right := coreCalls 5 1 (depth+1); let lc := 5*depth+1; let rc := 5*(depth+1)+1
        for groups in [0,2] do
          exercise (wrap groups (sourceCalls "f" "x" depth++token++sourceCalls "g" "y" (depth+1))) .word (.word (w l)) (.word (w r)) false false (join left right) .bool (.bool value) (lc+rc+5)
        let env := (environment .word (.word (w l)) (.word (w r)) false false).values
        let leftCp : Core.State := ⟨.ret (.word (w l)),[.binaryRight op right env,.unaryApply .boolNot],[]⟩
        let rightCp : Core.State := ⟨.ret (.word (w r)),[.binaryApply op (.word (w l)),.unaryApply .boolNot],[]⟩
        let notCp : Core.State := ⟨.ret (.bool (!value)),[.unaryApply .boolNot],[]⟩
        check (decide (Core.runStateful (lc+2) (.initial (join left right) env [])=.outOfFuel leftCp ∧ Core.runStateful (rc+1) leftCp=.outOfFuel rightCp ∧
          Core.runStateful 1 rightCp=.outOfFuel notCp ∧ Core.runStateful 1 notCp=.done (.bool value) [] ∧ Core.runStateful (rc+3) leftCp=.done (.bool value) [])) "genuine binaryRight/binaryApply/unaryApply and residual completion"
  for isLe in [false,true] do
    skippedOverlap isLe
    let op := if isLe then Core.BinaryOp.wordGt else .wordEq; let token := if isLe then " <= " else " != "
    let join (a b : Core.Expr) := Core.Expr.unary .boolNot (.binary op a b); let base := join (call 4 0) (call 5 1)
    for c in [false,true] do
      for (text,core,type,value,cost) in [
          ("!(f(x)"++token++"g(y))",Core.Expr.unary .boolNot base,Core.Ty.bool,Core.Value.bool isLe,19),
          ("f(x)"++token++"g(y) && p(c)",.ifE base (call 6 2) (.bool false),.bool,.bool (!isLe && c),if isLe then 20 else 25),
          ("f(x)"++token++"g(y) || p(c)",.ifE base (.bool true) (call 6 2),.bool,.bool (!isLe || c),if isLe then 25 else 20),
          ("f(x)"++token++"g(y) ? x : y",.ifE base (.var 0) (.var 1),.word,.word (w (if isLe then 5 else 17)),20),
          ("(p(c) ? maker(x) : f)(y)"++token++"g(x)",join (.apply (.ifE (call 6 2) (call 7 0) (.var 4)) (.var 1)) (call 5 0),.bool,.bool true,if c then 30 else 25)] do
        exercise text .word (.word (w 17)) (.word (w 5)) c false core type value cost
    exercise ("~f(x)"++token++"g(y)") .word (.word (w max)) (.word (w 0)) false false (join (.unary .wordNot (call 4 0)) (call 5 1)) .bool (.bool isLe) 19
    let s ← parsed ("(c ? f(x) : Missing)"++token++"g(y)"); let raw ← actual (environment .word (.word (w 17)) (.word (w 5)) true false) s
    have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨raw.cost,raw.evidence []⟩
    check (decide (raw.value=.bool (!isLe) ∧ raw.cost=20 ∧ elaborateRecursiveLocalComputation? names (context .word) s=none)) "raw chosen call succeeds despite unselected unknown"
  for a in [Core.Ty.bool,.unit,.namedData ⟨77⟩,.cell .word,.function .word .word] do
    for text in ["f(x) != g(y)","f(x) <= g(y)"] do check ((elaborateRecursiveLocalComputation? names (context a) (← parsed text)).isNone) "value-free non-Word comparison"
  for text in ["f(x) != p(c)","p(c) <= f(x)","f(Missing) != y","x <= Missing"] do
    check ((elaborateRecursiveLocalComputation? names (context .word) (← parsed text)).isNone) "unchanged wrong-type/name/unextended boundaries"
  let precedence ← parsed "f(x) <= g(y) != f(y) <= g(x)"
  check (match precedence.value with | .binary ⟨_,.binary _ ⟨_,.lessEqual⟩ _⟩ ⟨_,.notEqual⟩ ⟨_,.binary _ ⟨_,.lessEqual⟩ _⟩ => true | _ => false) "original relational precedence above nonassociative inequality"
  for text in ["f(x) != g(y) != x","f(x) <= g(y) <= x","f(x) <= g(y) > x"] do
    let file : Syntax.SourceFile := ⟨⟨.main,"recursive-negated-comparisons.sol"⟩,text⟩
    let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "nonassociative lexer")
    check (match Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) with | .ok _ next => !(tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) | .reject _ _ => true | .invariant _ => false) "nonassociative comparison rejection"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveOrderedComparisonEntries
/-! Independent original declaration certificates and manual paths retain actual captures, stores and whole results. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveOrderedComparisonEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveNegatedComparisonEntries",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-negated-comparison-entries.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) ("complete original bytes: "++text)
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span && decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original header and parameter ranges"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside named fixture")
private structure Parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span && decide (name.span.endByte≤annotation.span.startByte)) "original parameter fields/order"
      let m ← meaning types annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters types (s.bindFresh owner name.value arg.type)
            (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,
            by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate original parameter")
      else throw (IO.userError "original argument type mismatch")
  | _,_ => throw (IO.userError "original parameter arity")
private structure Path (core : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [original]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual var missing")
    | .letE head tail =>
        let a ← path n head env s; let b ← path n tail (a.value::env) a.final
        return ⟨b.value,b.final,a.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.letE (a.evidence _) (b.evidence _)⟩
    | .apply fn arg =>
        let f ← path n fn env s; let a ← path n arg env f.final
        match fv : f.value with
        | .closure _ _ body captured =>
            let b ← path n body (a.value::captured) a.final
            return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.apply (fv ▸ f.evidence _) (a.evidence _) (b.evidence [])⟩
        | _ => throw (IO.userError "manual callee shape")
    | .unary op operand =>
        let a ← path n operand env s
        match applied : op.apply a.value with
        | some v => return ⟨v,a.final,a.cost+2,fun _ => by rw [original]; exact CostStepComposition.unary (a.evidence _) applied⟩
        | none => throw (IO.userError "manual unary shape")
    | .binary op left right =>
        let a ← path n left env s; let b ← path n right env a.final
        match applied : op.apply a.value b.value with
        | some v => return ⟨v,b.final,a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.binary (a.evidence _) (b.evidence _) applied⟩
        | none => throw (IO.userError "manual binary shape")
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [original]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual load missing")
        | _ => throw (IO.userError "manual reference shape")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Certificate (Elaborates : Core.Expr → Core.Ty → Prop) (Evaluates : Core.Value → Core.Store → Nat → Prop) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : Elaborates core type
  raw : Evaluates value final cost
private abbrev Child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) :=
  Certificate (RecursiveLocalComputationElaborates s.names s.context source) (RecursiveLocalComputationEvaluatesWithCost s.names env store source)
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (source.span.contains fn.span && source.span.contains argsSpan && argsSpan.contains arg.span &&
        decide (fn.span.endByte ≤ argsSpan.startByte)) "original recursive child order"
      let f ← child s env store fn; let a ← child s env f.final arg
      match ft : f.type, fv : f.value with
      | .function input output,.closure _ _ body captured =>
          if same : a.type=input then
            let b ← path 100 body (a.value::captured) a.final
            return ⟨.apply f.core a.core,output,b.value,b.final,f.cost+a.cost+b.cost+3,
              by rw [original]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
              by rw [original]; exact .application (fv ▸ f.raw) a.raw (b.evidence [])⟩
          else throw (IO.userError "static argument differs")
      | _,_ => throw (IO.userError "static or actual Function differs")
  | ⟨_,.binary left ⟨opSpan,op⟩ right⟩ =>
      check (source.span.contains left.span && source.span.contains right.span && source.span.contains opSpan &&
        decide (left.span.endByte≤opSpan.startByte ∧ opSpan.endByte≤right.span.startByte)) "original ordered comparison child/operator order"
      let l ← child s env store left; let r ← child s env l.final right
      if typed : l.type=.word ∧ r.type=.word then
        match lv : l.value, rv : r.value with
        | .word a,.word b =>
            match which : op with
            | .less => return ⟨l.core.wordLt r.core,.bool,.bool (decide (a<b)),r.final,l.cost+r.cost+9,
                by rw [original,which]; exact .less (typed.1 ▸ l.elaboration) (typed.2 ▸ r.elaboration),
                by rw [original,which]; exact .less (lv ▸ l.raw) (rv ▸ r.raw)⟩
            | .greaterEqual => return ⟨.unary .boolNot (l.core.wordLt r.core),.bool,.bool (!(decide (a<b))),r.final,l.cost+r.cost+11,
                by rw [original,which]; exact .greaterEqual (typed.1 ▸ l.elaboration) (typed.2 ▸ r.elaboration),
                by rw [original,which]; exact .greaterEqual (lv ▸ l.raw) (rv ▸ r.raw)⟩
            | _ => throw (IO.userError "outside two ordered comparisons")
        | _,_ => throw (IO.userError "actual comparison operands are not Word")
      else throw (IO.userError "original comparison operands are not Word")
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨.var i,t,v,store,1,
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original row missing")
      | none => throw (IO.userError "original actual name missing")
  | _ => throw (IO.userError "outside fixture expression")
termination_by sizeOf source
private abbrev Tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) :=
  Certificate (RecursiveComputationReturnTreeElaborates types owner s source) (RecursiveComputationReturnTreeEvaluatesWithCost owner s.names env store source)
private def tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) : IO (Tree types s env store source) := do
  check (source.value.all fun statement => source.span.contains statement.span) "original statement spans"
  match original : source with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
      let a ← child s env store e
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .expression a.elaboration,by rw [original]; exact .expression a.raw⟩
  | _ => throw (IO.userError "outside original singleton return body")
private def header (types : TypeNameTable) (source : Syntax.FunctionDecl) (output : Core.Ty) : IO (PLift (RuntimeFunctionHeader types source.value.signature output)) := do
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.1=output then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧
            source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          return ⟨⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.2.down)⟩⟩
        else throw (IO.userError "original header policy")
      else throw (IO.userError "original return meaning")
  | _ => throw (IO.userError "original singleton return clause")
private def bodySource (body : String) : IO Syntax.FunctionDecl := parsed ("function comparison(f:F,g:G,x:X,y:Y) returns(R){"++body++"}")
private def verify (source : Syntax.FunctionDecl) (f g x y : TypedRuntimeArgument) (output : Core.Ty) (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO PreparedRuntimeFunction := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["Y"],y.type),(["R"],output),(["Word"],.word)]
  let args := [f,g,x,y]; let ps ← parameters types .empty .empty source.value.signature.parameters.elements args
  let inputs := ps.actual; let env := inputs.environment.values
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body; let manual ← path 100 core env s
  have erased : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  check (decide (env=[y.value,x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("y",⟨owner,3⟩,y.type,y.value),("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
  check (decide (b.value=value ∧ b.final=final ∧ b.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent raw/Core value/store/cost"
  if fixed : b.core=core ∧ b.type=output then
    let compiled : CompiledRuntimeFunction := ⟨ps.statics,core,output⟩; let prepared : PreparedRuntimeFunction := ⟨inputs,core,output⟩
    have preparation : RecursiveComputationFunctionPrepares types owner source args prepared := ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have compilation : RecursiveComputationFunctionCompiles types owner source compiled := ⟨h.down,ps.declared,by simpa only [compiled,prepared,erased] using preparation.body⟩
    have compiledSome := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
    have preparedSome := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr preparation
    have matching : args.map (·.type)=ps.statics.context.values.reverse := by
      have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
      simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
    have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some compiled := by
      rw [prepareComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte]
    have whole (fuel) (store) : runRecursiveComputationFunction? types owner source args fuel store = some (output,Core.runStateful fuel (.initial core [y.value,x.value,g.value,f.value] store)) := by
      rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte,args,List.reverse_cons,List.reverse_nil]; rfl
    have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
    have _ := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation b.raw b.elaboration ids []
    check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old entry remains None"
    for fuel in List.range (cost+2) do
      have _ := whole fuel s
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial core env s)) ∧ runRuntimeComputationFunction? types owner source args fuel s=none)) "whole full result/tag"
      match exhausted : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact completion"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel exhausted; have _ := Core.runStateful_resume exhausted 2
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧ runRecursiveComputationFunction? types owner source args (fuel+2) s=some (output,Core.runStateful 2 cp))) "genuine saved state/residual/full resume"
      | .fault _ _ => throw (IO.userError "independent successful path faulted")
    return prepared
  else throw (IO.userError "independent exact Core/type")
private def reader (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word location],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word location],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def arg (value : Nat) : TypedRuntimeArgument := ⟨.word,w value,.word⟩
end RecursiveOrderedComparisonEntries
open RecursiveOrderedComparisonEntries
def frontendParsedRecursiveOrderedComparisonEntryTests : IO Unit := do
  let left := Core.Expr.apply (.var 3) (.var 1); let shiftedRight := Core.Expr.apply (.var 3) (.var 1)
  let comparison := Core.Expr.binary .wordGt (.var 0) (.var 1)
  let inner := Core.Expr.letE shiftedRight comparison; let ordered := Core.Expr.letE left inner
  let f := reader 0; let g := writer 0; let x := arg 11; let y := arg 14
  for ge in [false,true] do
    let source ← bodySource (if ge then "return f(x) >= g(y);" else "return f(x) < g(y);")
    let core := if ge then Core.Expr.unary .boolNot ordered else ordered
    let offset := if ge then 1 else 0; let cost := if ge then 34 else 32
    for (old,rhs) in [(23,14),(14,23),(14,14),(0,2^256-1),(2^256-1,0),(2^255,2^255),(2^256-1,2^255)] do
      discard <| verify source f g x (arg rhs) .bool core [w old] [w rhs] (.bool (if ge then old≥rhs else old<rhs)) cost
    discard <| verify source g f x y .bool core [w 23] [w 11] (.bool ge) cost
    discard <| verify source (reader 1) g x y .bool core [w 23,w 7] [w 14,w 7] (.bool (!ge)) cost
    discard <| verify source g (reader 1) y x .bool core [w 23,w 7] [w 14,w 7] (.bool ge) cost
    discard <| verify source f g y x .bool core [w 23] [w 11] (.bool ge) cost
    let prepared ← verify source f g x y .bool core [w 23] [w 14] (.bool ge) cost
    let env := prepared.inputs.environment.values
    let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],.word),(["Y"],.word),(["R"],.bool),(["Word"],.word)]
    let run := runRecursiveComputationFunction? types owner source [f,g,x,y]
    let outer : List Core.Frame := if ge then [.unaryApply .boolNot] else []
    let first : Core.State := ⟨.ret (w 23),.letBody inner env::outer,[w 23]⟩
    let shifted : Core.State := ⟨.eval shiftedRight (w 23::env),.letBody comparison (w 23::env)::outer,[w 23]⟩
    let second : Core.State := ⟨.ret (w 14),.letBody comparison (w 23::env)::outer,[w 14]⟩
    let last : Core.State := ⟨.ret (w 23),.binaryApply .wordGt (w 14)::outer,[w 14]⟩
    check (decide (run (9+offset) [w 23]=some (.bool,.outOfFuel first) ∧ run (11+offset) [w 23]=some (.bool,.outOfFuel shifted) ∧ run (26+offset) [w 23]=some (.bool,.outOfFuel second) ∧ run (31+offset) [w 23]=some (.bool,.outOfFuel last))) "genuine two lets, shifted original right under saved left, and retained right/left positional operands"
    for (spent,cp) in [(9+offset,first),(11+offset,shifted),(26+offset,second),(31+offset,last)] do
      check (decide (Core.runStateful (cost-spent) cp=.done (.bool ge) [w 14])) "each independently fixed checkpoint resumes exact residual cost"
    if ge then
      let negation : Core.State := ⟨.ret (.bool false),[.unaryApply .boolNot],[w 14]⟩
      check (decide (run 33 [w 23]=some (.bool,.outOfFuel negation) ∧ Core.runStateful 1 negation=.done (.bool true) [w 14])) "greater-equal keeps genuine final negation"
    let badEnv := w 14::.bool true::env
    let badCp : Core.State := ⟨.eval (.var 1) badEnv,.binaryApply .wordGt (w 14)::outer,[w 14]⟩
    let bad := Core.StatefulRunResult.fault (.invalidBinaryOperands .wordGt (w 14) (.bool true)) ⟨.ret (.bool true),.binaryApply .wordGt (w 14)::outer,[w 14]⟩
    check (decide (run (30+offset) [.bool true]=some (.bool,.outOfFuel badCp) ∧ run (31+offset) [.bool true]=some (.bool,bad) ∧ Core.runStateful 1 badCp=bad)) "wrong left still allows right write before reversed actual primitive operands fault"
    let leftMissingEnv := [y.value,x.value,g.value,(reader 1).value]
    let leftMissingRun := runRecursiveComputationFunction? types owner source [reader 1,g,x,y]
    let leftCp : Core.State := ⟨.eval (.var 1) [x.value,.cellRef .word 1],.loadCellApply::.letBody inner leftMissingEnv::outer,[w 23]⟩
    let leftFault := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),.loadCellApply::.letBody inner leftMissingEnv::outer,[w 23]⟩
    check (decide (leftMissingRun (7+offset) [w 23]=some (.bool,.outOfFuel leftCp) ∧ leftMissingRun (8+offset) [w 23]=some (.bool,leftFault) ∧ Core.runStateful 1 leftCp=leftFault)) "left missing cell prevents a possible write to right cell zero"
    let rf := writer 0; let rg := reader 1
    let changed ← verify source rf rg x y .bool core [w 23,w 14] [w 11,w 14] (.bool (!ge)) cost
    let changedEnv := changed.inputs.environment.values; let changedRun := runRecursiveComputationFunction? types owner source [rf,rg,x,y]
    let missingFrames := Core.Frame.loadCellApply::.letBody comparison (w 11::changedEnv)::outer
    let missingCp : Core.State := ⟨.eval (.var 1) [y.value,.cellRef .word 1],missingFrames,[w 11]⟩
    let missing := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),missingFrames,[w 11]⟩
    check (decide (changedRun (24+offset) [w 23]=some (.bool,.outOfFuel missingCp) ∧ changedRun (25+offset) [w 23]=some (.bool,missing) ∧ Core.runStateful 1 missingCp=missing)) "missing right retains left write and actual left binding"
    let wrongRightCp : Core.State := ⟨.eval (.var 1) (.bool false::w 11::changedEnv),.binaryApply .wordGt (.bool false)::outer,[w 11,.bool false]⟩
    let wrongRight := Core.StatefulRunResult.fault (.invalidBinaryOperands .wordGt (.bool false) (w 11)) ⟨.ret (w 11),.binaryApply .wordGt (.bool false)::outer,[w 11,.bool false]⟩
    check (decide (changedRun (30+offset) [w 23,.bool false]=some (.bool,.outOfFuel wrongRightCp) ∧ changedRun (31+offset) [w 23,.bool false]=some (.bool,wrongRight) ∧ Core.runStateful 1 wrongRightCp=wrongRight)) "wrong right is first generated gt operand and retains left update"
    for (actualEnv,actualRun) in [(env,run),(changedEnv,changedRun)] do
      for store in [[w 23],[.bool true],[],[w 23,.bool false],[w 23,w 14]] do
        for fuel in List.range 36 do
          check (decide (actualRun fuel store=some (.bool,Core.runStateful fuel (.initial core actualEnv store)))) "same prepared arbitrary stores retain full outcomes and declared Bool tag"
          match exhausted : Core.runStateful fuel (.initial core actualEnv store) with
          | .outOfFuel residual =>
              have _ := Core.runStateful_resume exhausted 40
              check (decide (actualRun (fuel+40) store=some (.bool,Core.runStateful 40 residual))) "all genuine checkpoints resume success and faults"
          | _ => pure ()
    for body in ["return f(x) < missing;","return missing >= g(y);","return f(x) < (x==y);","return (x==y) >= g(y);"] do
      let rejected ← bodySource body
      check (decide (compileRecursiveComputationFunction? types owner rejected=none ∧ prepareRecursiveComputationFunction? types owner rejected [f,g,x,y]=none ∧ runRecursiveComputationFunction? types owner rejected [f,g,x,y] 50 [w 23]=none)) "whole Word and unknown-name gates unchanged"
    let wrongReturn ← parsed ("function comparison(f:F,g:G,x:X,y:Y) returns(Word){"++(if ge then "return f(x) >= g(y);" else "return f(x) < g(y);")++"}")
    check (decide (elaborateRecursiveComputationReturnTree? types owner prepared.inputs.toTypeInputs wrongReturn.value.body=some (core,.bool) ∧ compileRecursiveComputationFunction? types owner wrongReturn=none ∧ prepareRecursiveComputationFunction? types owner wrongReturn [f,g,x,y]=none)) "original ordered Bool body versus declared Word"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveOrderedComparisonMigrations
/-! Original ordered-comparison rejections retain both earlier caller layouts,
source files and operator spans. Older endpoints still reject these sources. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveOrderedComparisonMigrations

private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Binary",by decide⟩],by decide⟩⟩,56⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("f",foreign),("g",id 9),("y",id 14),("c",id 15),("f",id 88)]
private def context : Resolved.Context := [(id 7,.word),(foreign,.function .word .word),(id 9,.function .word .word),(id 14,.word),(id 15,.bool),(foreign,.bool)]

private def negatedOwner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"NegatedComparisons",by decide⟩],by decide⟩⟩,60⟩
private def nid (n : Nat) : Resolved.LocalId := ⟨negatedOwner,n⟩
private def nforeign : Resolved.LocalId := ⟨{negatedOwner with declarationIndex := 91},302⟩
private def negatedNames : LocalNameTable := [("x",nid 7),("y",nid 14),("c",nid 15),("d",nid 16),("f",nforeign),("g",nid 9),("p",nid 20),("maker",nid 25),("true",nid 90),("false",nid 91),("f",nid 88)]
private def negatedContext : Resolved.Context := [(nid 7,.word),(nid 14,.word),(nid 15,.bool),(nid 16,.bool),(nforeign,.function .word .word),(nid 9,.function .word .word),(nid 20,.function .bool .bool),(nid 25,.function .word (.function .word .word)),(nid 90,.bool),(nid 91,.bool),(nforeign,.bool)]

private structure Static (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates table ctx s core type
  typing : RecursiveLocalComputationHasType table ctx s type

private def statics (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) :
    IO (Static table ctx s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : table.lookup? name.value with
      | some localId =>
          match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some t,some n =>
              have r : ResolvesLocalExpression table s (.var localId) := by
                rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named)
              have ty : Resolved.HasType ctx (.var localId) t := .var (Resolved.LocalScope.lookup?_iff.mp typed)
              return ⟨.var n,t,.pure r (.var (Resolved.LocalScope.index?_iff.mp indexed)) ty,.pure (r.reflects_type ty)⟩
          | _,_ => throw (IO.userError "original ordered context")
      | _ => throw (IO.userError "original names")
  | ⟨_,.group inner⟩ =>
      let a ← statics table ctx inner
      return ⟨a.core,a.type,by rw [shape]; exact .group a.elaboration,by rw [shape]; exact .group a.typing⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← statics table ctx fn; let a ← statics table ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,
            by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨_,.binary left ⟨_,.less⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.word ∧ b.type=.word then return ⟨a.core.wordLt b.core,.bool,
        by rw [shape]; exact .less (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .less (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Word comparison children")
  | ⟨_,.binary left ⟨_,.greaterEqual⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.word ∧ b.type=.word then return ⟨.unary .boolNot (a.core.wordLt b.core),.bool,
        by rw [shape]; exact .greaterEqual (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .greaterEqual (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Word comparison children")
  | _ => throw (IO.userError "migration original shape")
termination_by sizeOf s

end ParsedRecursiveOrderedComparisonMigrations
open ParsedRecursiveOrderedComparisonMigrations

def frontendParsedRecursiveOrderedComparisonMigrationTests : IO Unit := do
  let apply (fn arg : Nat) := Core.Expr.apply (.var fn) (.var arg)
  for (table,ctx,path,left,right) in
      [(names,context,"recursive-binary.sol",apply 1 0,apply 2 3),
       (negatedNames,negatedContext,"recursive-negated-comparisons.sol",apply 4 0,apply 5 1)] do
    for (text,ge) in [("f(x) < g(y)",false),("f(x) >= g(y)",true)] do
      let comparison := Core.Expr.letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1)))
      let expected := if ge then .unary .boolNot comparison else comparison
      let file : Syntax.SourceFile := ⟨⟨.main,path⟩,text⟩
      let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "migration lexer")
      let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError "migration parser")
      check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
        decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "unchanged original parsed source"
      match s.value with
      | .binary lhs ⟨opSpan,op⟩ rhs =>
          check (decide (op=(if ge then .greaterEqual else .less) ∧ opSpan.source=file.id ∧
            opSpan.startByte=5 ∧ opSpan.endByte=(if ge then 7 else 6) ∧
            lhs.span.endByte≤opSpan.startByte ∧ opSpan.endByte≤rhs.span.startByte)) "original operator bytes/order"
      | _ => throw (IO.userError "original binary root")
      let a ← statics table ctx s
      have _ := elaborateRecursiveLocalComputation?_iff.mpr a.elaboration
      have _ := recursiveLocalComputationHasType_iff_elaborates.mp a.typing
      have _ := a.elaboration.core_hasType
      check (decide (a.core=expected ∧ a.type=.bool ∧
        elaborateRecursiveLocalComputation? table ctx s=some (expected,.bool) ∧
        elaborateLocalExpression? table ctx s=none ∧
        elaborateLocalComputation? table ctx s=none)) "original new ordered Core and unchanged old rejections"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveOrderedComparisons
/-! Original comparison syntax has independent static/raw evidence and separate
literal Core/manual paths; actual captures and pending frames are retained. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveOrderedComparisons
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"OrderedComparisons",by decide⟩],by decide⟩⟩,62⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("y",id 14),("c",id 15),("d",id 16),("f",foreign),("g",id 9),("p",id 20),("maker",id 25),("true",id 90),("false",id 91),("f",id 88)]
private def context (a : Core.Ty) : Resolved.Context := [(id 7,a),(id 14,a),(id 15,.bool),(id 16,.bool),(foreign,.function a a),(id 9,.function a a),(id 20,.function .bool .bool),(id 25,.function a (.function a a)),(id 90,.bool),(id 91,.bool),(foreign,.bool)]
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.bool false]
private def environment (a : Core.Ty) (x y : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(id 7,x),(id 14,y),(id 15,.bool c),(id 16,.bool d),(foreign,identity a),(id 9,identity a),(id 20,identity .bool),(id 25,.closure a (.function a a) (.var 1) [identity a]),(id 90,.bool false),(id 91,.bool true),(foreign,.bool false)]
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def join (ge : Bool) (left right : Core.Expr) : Core.Expr :=
  let ordered := Core.Expr.letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1)))
  if ge then .unary .boolNot ordered else ordered
private def wrap : Nat → String → String | 0,s => s | n+1,s => "("++wrap n s++")"
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-ordered-comparisons.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError s!"parser: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "original bytes/span"
  return s
private structure Static (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates names ctx s core type
  typing : RecursiveLocalComputationHasType names ctx s type
private def statics (ctx : Resolved.Context) (s : Syntax.Expr) : IO (Static ctx s) := do
  match shape : s with
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span) "group span"; let a ← statics ctx inner
      return ⟨a.core,a.type,by rw [shape]; exact .group a.elaboration,by rw [shape]; exact .group a.typing⟩
  | ⟨span,.unary ⟨opSpan,op⟩ inner⟩ =>
      check (span.contains inner.span && span.contains opSpan && decide (span.startByte=opSpan.startByte ∧ opSpan.endByte=opSpan.startByte+1 ∧ opSpan.endByte≤inner.span.startByte)) "original prefix bytes/order"
      let a ← statics ctx inner
      match which : op with
      | .logicalNot => if same : a.type=.bool then return ⟨.unary .boolNot a.core,.bool,by rw [shape,which]; exact .logicalNot (same ▸ a.elaboration),by rw [shape,which]; exact .logicalNot (same ▸ a.typing)⟩ else throw (IO.userError "Bool operand")
      | .bitNot => if same : a.type=.word then return ⟨.unary .wordNot a.core,.word,by rw [shape,which]; exact .bitNot (same ▸ a.elaboration),by rw [shape,which]; exact .bitNot (same ▸ a.typing)⟩ else throw (IO.userError "Word operand")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call children"
      let f ← statics ctx fn; let a ← statics ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨span,.binary left ⟨opSpan,op⟩ right⟩ =>
      check (span.contains left.span && span.contains right.span && span.contains opSpan && decide (left.span.endByte≤opSpan.startByte ∧ opSpan.endByte=opSpan.startByte+(if op = .less then 1 else 2) ∧ opSpan.endByte≤right.span.startByte)) "original operator width/children order"
      let a ← statics ctx left; let b ← statics ctx right
      match which : op with
      | .less => if same : a.type=.word ∧ b.type=.word then return ⟨a.core.wordLt b.core,.bool,
          by rw [shape,which]; exact .less (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .less (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Word comparison operands")
      | .greaterEqual => if same : a.type=.word ∧ b.type=.word then return ⟨.unary .boolNot (a.core.wordLt b.core),.bool,
          by rw [shape,which]; exact .greaterEqual (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .greaterEqual (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Word comparison operands")
      | .logicalAnd => if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core b.core (.bool false),.bool,
          by rw [shape,which]; exact .logicalAnd (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .logicalAnd (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Bool logical operands")
      | .logicalOr => if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core (.bool true) b.core,.bool,
          by rw [shape,which]; exact .logicalOr (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .logicalOr (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Bool logical operands")
      | _ => throw (IO.userError "outside fixed comparison fixture")
  | ⟨span,.conditional guard question yes colon no⟩ =>
      check (span.contains guard.span && span.contains yes.span && span.contains no.span && span.contains question && span.contains colon &&
        decide (guard.span.endByte≤question.startByte ∧ question.endByte=question.startByte+1 ∧ question.endByte≤yes.span.startByte ∧
          yes.span.endByte≤colon.startByte ∧ colon.endByte=colon.startByte+1 ∧ colon.endByte≤no.span.startByte)) "original question/colon order"
      let g ← statics ctx guard; let a ← statics ctx yes; let b ← statics ctx no
      if valid : g.type=.bool ∧ b.type=a.type then return ⟨.ifE g.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ g.elaboration) a.elaboration (valid.2 ▸ b.elaboration),
        by rw [shape]; exact .conditional (valid.1 ▸ g.typing) a.typing (valid.2 ▸ b.typing)⟩
      else throw (IO.userError "whole conditional types")
  | ⟨_,.identifier name⟩ => match named : names.lookup? name.value with
    | some localId => match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
      | some t,some n =>
          have r : ResolvesLocalExpression names s (.var localId) := by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named)
          have ty : Resolved.HasType ctx (.var localId) t := .var (Resolved.LocalScope.lookup?_iff.mp typed)
          return ⟨.var n,t,(LocalComputationElaborates.pure r (.var (Resolved.LocalScope.index?_iff.mp indexed)) ty).toRecursiveLocalComputation,.pure (r.reflects_type ty)⟩
      | _,_ => throw (IO.userError "caller row")
    | _ => throw (IO.userError "caller name")
  | _ => throw (IO.userError "outside original source fixture")
termination_by sizeOf s
private structure RawLeaf (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, LocalExpressionEvaluatesWithCost names env store s value store 1
private def rawLeaf (env : Resolved.Environment) (s : Syntax.Expr) : IO (RawLeaf env s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match named : names.lookup? name.value with
    | some localId => match found : env.lookup? localId with
      | some v => return ⟨v,fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
      | _ => throw (IO.userError "actual row")
    | _ => throw (IO.userError "actual name")
  | _ => throw (IO.userError "actual identifier")
private structure Actual (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost names env store s value store cost
private def actual (env : Resolved.Environment) (s : Syntax.Expr) : IO (Actual env s) := do
  match shape : s with
  | ⟨_,.group inner⟩ => let a ← actual env inner; return ⟨a.value,a.cost,fun store => by rw [shape]; exact .group (a.evidence store)⟩
  | ⟨_,.unary ⟨_,op⟩ inner⟩ =>
      let a ← actual env inner
      match which : op, v : a.value with
      | .logicalNot,.bool b => return ⟨.bool (!b),a.cost+2,fun store => by rw [shape,which]; exact .logicalNot (v ▸ a.evidence store)⟩
      | .bitNot,.word w => return ⟨.word w.bitNot,a.cost+2,fun store => by rw [shape,which]; exact .bitNot (v ▸ a.evidence store)⟩
      | _,_ => throw (IO.userError "actual unary payload")
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← actual env fn; let a ← actual env arg
      match closure : f.value with
      | .closure _ _ (.var n) captured => match found : (a.value::captured)[n]? with
        | some v => return ⟨v,f.cost+a.cost+4,fun store => by rw [shape]; exact .application (closure ▸ f.evidence store) (a.evidence store) (.cons (.var found) .refl)⟩
        | _ => throw (IO.userError "actual captured index")
      | _ => throw (IO.userError "fixture body")
  | ⟨_,.binary left ⟨_,.logicalAnd⟩ right⟩ =>
      let a ← actual env left
      match value : a.value with
      | .bool false => return ⟨.bool false,a.cost+3,fun store => by rw [shape]; exact .andFalse (value ▸ a.evidence store)⟩
      | .bool true => let b ← actual env right; return ⟨b.value,a.cost+b.cost+2,fun store => by rw [shape]; exact .andTrue (value ▸ a.evidence store) (b.evidence store)⟩
      | _ => throw (IO.userError "actual conjunction left Bool")
  | ⟨_,.binary left ⟨_,.logicalOr⟩ right⟩ =>
      let a ← actual env left
      match value : a.value with
      | .bool true => return ⟨.bool true,a.cost+3,fun store => by rw [shape]; exact .orTrue (value ▸ a.evidence store)⟩
      | .bool false => let b ← actual env right; return ⟨b.value,a.cost+b.cost+2,fun store => by rw [shape]; exact .orFalse (value ▸ a.evidence store) (b.evidence store)⟩
      | _ => throw (IO.userError "actual disjunction left Bool")
  | ⟨_,.binary left ⟨_,op⟩ right⟩ =>
      let a ← actual env left; let b ← actual env right
      match lv : a.value, rv : b.value with
      | .word l,.word r =>
          match which : op with
          | .less => return ⟨.bool (decide (l<r)),a.cost+b.cost+9,fun store => by rw [shape,which]; exact .less (lv ▸ a.evidence store) (rv ▸ b.evidence store)⟩
          | .greaterEqual => return ⟨.bool (!(decide (l<r))),a.cost+b.cost+11,fun store => by rw [shape,which]; exact .greaterEqual (lv ▸ a.evidence store) (rv ▸ b.evidence store)⟩
          | _ => throw (IO.userError "actual fixed operator")
      | _,_ => throw (IO.userError "actual Word comparison operands")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← actual env guard
      match gv : g.value with
      | .bool true => let a ← actual env yes; return ⟨a.value,g.cost+a.cost+2,fun store => by rw [shape]; exact .ifTrue (gv ▸ g.evidence store) (a.evidence store)⟩
      | .bool false => let b ← actual env no; return ⟨b.value,g.cost+b.cost+2,fun store => by rw [shape]; exact .ifFalse (gv ▸ g.evidence store) (b.evidence store)⟩
      | _ => throw (IO.userError "actual Bool")
  | _ => let a ← rawLeaf env s; return ⟨a.value,1,fun store => .pure (a.evidence store)⟩
termination_by sizeOf s
private structure Path (env : Core.Environment) (core : Core.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store k, Core.Steps cost ⟨.eval core env,k,store⟩ ⟨.ret value,k,store⟩
private def manual : (fuel : Nat) → (env : Core.Environment) → (core : Core.Expr) → IO (Path env core)
  | 0,_,_ => throw (IO.userError "manual certificate depth")
  | fuel+1,env,core => do
    match shape : core with
    | .bool b => return ⟨.bool b,1,fun _ _ => by rw [shape]; exact .cons .bool .refl⟩
    | .var n => match found : env[n]? with
      | some v => return ⟨v,1,fun _ _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | _ => throw (IO.userError "manual variable")
    | .unary op inner =>
      let a ← manual fuel env inner
      match applied : op.apply a.value with
      | some v => return ⟨v,a.cost+2,fun store k => by rw [shape]; exact CostStepComposition.unary (a.evidence store _) applied⟩
      | _ => throw (IO.userError "manual unary")
    | .binary op left right =>
      let a ← manual fuel env left; let b ← manual fuel env right
      match applied : op.apply a.value b.value with
      | some v => return ⟨v,a.cost+b.cost+3,fun store k => by rw [shape]; exact CostStepComposition.binary (a.evidence store _) (b.evidence store _) applied⟩
      | _ => throw (IO.userError "manual binary")
    | .letE bound body =>
      let a ← manual fuel env bound; let b ← manual fuel (a.value::env) body
      return ⟨b.value,a.cost+b.cost+2,fun store k => by rw [shape]; exact CostStepComposition.letE (a.evidence store _) (b.evidence store k)⟩
    | .apply fn arg =>
      let f ← manual fuel env fn; let a ← manual fuel env arg
      match closure : f.value with
      | .closure _ _ (.var n) captured => match found : (a.value::captured)[n]? with
        | some v => return ⟨v,f.cost+a.cost+4,fun store _ => by rw [shape]; exact CostStepComposition.apply (closure ▸ f.evidence store _) (a.evidence store _) (.cons (.var found) .refl)⟩
        | _ => throw (IO.userError "manual body index")
      | _ => throw (IO.userError "manual closure")
    | .ifE guard yes no =>
      let g ← manual fuel env guard
      match gv : g.value with
      | .bool true => let a ← manual fuel env yes; return ⟨a.value,g.cost+a.cost+2,fun store k => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence store _) (a.evidence store k)⟩
      | .bool false => let b ← manual fuel env no; return ⟨b.value,g.cost+b.cost+2,fun store k => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence store _) (b.evidence store k)⟩
      | _ => throw (IO.userError "manual guard")
    | _ => throw (IO.userError "manual Core grammar")
private def exercise (text : String) (a : Core.Ty) (x y : Core.Value) (c d : Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) (pureSource : Bool := false) : IO Unit := do
  let s ← parsed text; let env := environment a x y c d; let p ← statics (context a) s; let r ← actual env s; let m ← manual 30 env.values core
  if fixed : p.core=core ∧ p.type=type ∧ r.value=value ∧ r.cost=cost ∧ m.value=value ∧ m.cost=cost then
    have e : RecursiveLocalComputationElaborates names (context a) s core type := by simpa only [fixed.1,fixed.2.1] using p.elaboration
    have _ := elaborateRecursiveLocalComputation?_iff.mp (elaborateRecursiveLocalComputation?_iff.mpr e)
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp p.typing
    have _ := e.core_hasType
    check (decide (elaborateRecursiveLocalComputation? names (context a) s=some (core,type) ∧ elaborateLocalExpression? names (context a) s=(if pureSource then some (core,type) else none) ∧ elaborateLocalComputation? names (context a) s=(if pureSource then some (core,type) else none))) "new exact and original pure/old endpoint boundary"
    for store in [[],[Core.Value.bool true,.cellRef .word 91]] do
      have counted : RecursiveLocalComputationEvaluatesWithCost names env store s value store cost := by simpa only [fixed.2.2.1,fixed.2.2.2.1] using r.evidence store
      have path : ∀ k, Core.Steps cost ⟨.eval core env.values,k,store⟩ ⟨.ret value,k,store⟩ := by simpa only [fixed.2.2.2.2.1,fixed.2.2.2.2.2] using m.evidence store
      have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨cost,counted⟩
      have coreRaw := (e.evaluates_iff rfl).mp raw
      have _ := counted.deterministic ((e.evaluatesWithCost_iff_steps rfl).mpr (path []))
      let pending : List Core.Frame := [.letBody .unit []]
      have _ := counted.toStepsWithContinuation e rfl pending
      for fuel in List.range (cost+2) do
        have _ := (path []).runStateful_done_iff (fuel := fuel)
        match outcome : Core.runStateful fuel (.initial core env.values store) with
        | .done v st => check (decide (cost≤fuel ∧ v=value ∧ st=store)) "literal value/store/threshold"
        | .outOfFuel cp =>
            have _ := (path []).residual_of_outOfFuel outcome
            check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value store ∧ Core.runStateful 1 cp=Core.runStateful (fuel+1) (.initial core env.values store))) "genuine residual/full replay"
        | .fault _ _ => throw (IO.userError "fixed path fault")
      have fragment := e.core_fragment
      have _ := fragment.weakenAt 3
      for cutoff in [0,3] do
        let leading := env.values.take cutoff; let suffix := env.values.drop cutoff
        have same : leading++suffix=env.values := List.take_append_drop cutoff env.values
        let inserted : Core.Value := .closure .bool .unit (.var 99) [.cellRef .word 77]
        have original : Core.Evaluates (leading++suffix) store core value store := by rw [same]; exact coreRaw
        have changed := (fragment.evaluates_insert_iff leading suffix inserted).mpr original
        have paired : ∀ k, Core.Steps cost ⟨.eval core (leading++suffix),k,store⟩ ⟨.ret value,k,store⟩ ∧
            Core.Steps cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),k,store⟩ ⟨.ret value,k,store⟩ := by
          obtain ⟨n,paths⟩ := fragment.insertion_paths leading suffix inserted original
          have eqCost : n=cost := ((paths []).1.final_unique (by simpa only [same,Core.State.final] using path [])).1
          exact eqCost ▸ paths
        check (decide (Core.runStateful cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),pending,store⟩=.outOfFuel ⟨.ret value,pending,store⟩)) "inserted pending endpoint"
  else throw (IO.userError s!"independent certificate mismatch: {text}")
private def skippedOverlap (ge : Bool) : IO Unit := do
  let s ← parsed (if ge then "(c ? x : Missing) >= y" else "(c ? x : Missing) < y")
  let w := Core.Word.ofNatModulo; let env := environment .word (.word (w 17)) (.word (w 5)) true false; let fresh ← actual env s
  match shape : s with
  | ⟨_,.binary ⟨_,.group ⟨_,.conditional guard _ yes _ _⟩⟩ ⟨_,op⟩ right⟩ =>
      let g ← rawLeaf env guard; let l ← rawLeaf env yes; let r ← rawLeaf env right
      if same : g.value=.bool true ∧ l.value=.word (w 17) ∧ r.value=.word (w 5) then
        match which : op with
        | .less =>
            have old : LocalComputationEvaluatesWithCost names env [] s (.bool false) [] 14 := .pure (by rw [shape,which]; exact .less (.group (.ifTrue (same.1 ▸ g.evidence []) (same.2.1 ▸ l.evidence []))) (same.2.2 ▸ r.evidence []))
            have _ := (fresh.evidence []).deterministic old.toRecursiveLocalComputation
        | .greaterEqual =>
            have old : LocalComputationEvaluatesWithCost names env [] s (.bool true) [] 16 := .pure (by rw [shape,which]; exact .greaterEqual (.group (.ifTrue (same.1 ▸ g.evidence []) (same.2.1 ▸ l.evidence []))) (same.2.2 ▸ r.evidence []))
            have _ := (fresh.evidence []).deterministic old.toRecursiveLocalComputation
        | _ => throw (IO.userError "original comparison")
      else throw (IO.userError "old actual leaves")
  | _ => throw (IO.userError "original skipped conditional")
  check (decide (fresh.value=.bool ge ∧ fresh.cost=(if ge then 16 else 14) ∧ elaborateRecursiveLocalComputation? names (context .word) s=none)) "pure/new ordered overlap skips unknown syntax"
private def sourceCalls (fn arg : String) : Nat → String | 0 => arg | n+1 => fn++"("++sourceCalls fn arg n++")"
private def coreCalls (fn arg : Nat) : Nat → Core.Expr | 0 => .var arg | n+1 => .apply (.var fn) (coreCalls fn arg n)
end ParsedRecursiveOrderedComparisons
open ParsedRecursiveOrderedComparisons
def frontendParsedRecursiveOrderedComparisonTests : IO Unit := do
  let w := Core.Word.ofNatModulo; let hi := 2^255; let max := Core.wordModulus-1
  for (l,r,lt,ge) in [(0,0,false,true),(0,max,true,false),(max,0,false,true),(hi,hi,false,true),
      (hi,hi-1,false,true),(hi-1,hi,true,false),(17,5,false,true),(5,17,true,false)] do
    for isGe in [false,true] do
      let token := if isGe then " >= " else " < "; let overhead := if isGe then 11 else 9; let value := if isGe then ge else lt
      exercise ("x"++token++"y") .word (.word (w l)) (.word (w r)) false false (join isGe (.var 0) (.var 1)) .bool (.bool value) (2+overhead) true
      for depth in [1,3,8] do
        let left := coreCalls 4 0 depth; let right := coreCalls 5 1 (depth+1); let lc := 5*depth+1; let rc := 5*(depth+1)+1
        for groups in [0,2] do
          exercise (wrap groups (sourceCalls "f" "x" depth++token++sourceCalls "g" "y" (depth+1))) .word (.word (w l)) (.word (w r)) false false (join isGe left right) .bool (.bool value) (lc+rc+overhead)
        let env := (environment .word (.word (w l)) (.word (w r)) false false).values
        let k := if isGe then [Core.Frame.unaryApply .boolNot] else []; let gt := Core.Expr.binary .wordGt (.var 0) (.var 1)
        let first : Core.State := ⟨.ret (.word (w l)),.letBody (.letE (right.weakenAt 0) gt) env::k,[]⟩
        let second : Core.State := ⟨.ret (.word (w r)),.letBody gt (.word (w l)::env)::k,[]⟩
        let applied : Core.State := ⟨.ret (.word (w l)),.binaryApply .wordGt (.word (w r))::k,[]⟩
        check (decide (Core.runStateful (lc+1+(if isGe then 1 else 0)) (.initial (join isGe left right) env [])=.outOfFuel first ∧
          Core.runStateful (rc+2) first=.outOfFuel second ∧ Core.runStateful 5 second=.outOfFuel applied ∧
          Core.runStateful 1 applied=(if isGe then .outOfFuel ⟨.ret (.bool lt),k,[]⟩ else .done (.bool lt) []) ∧
          Core.runStateful (if isGe then 2 else 1) applied=.done (.bool value) [])) "genuine first/second let, swapped gt and optional boolNot checkpoints"
  for isGe in [false,true] do
    skippedOverlap isGe
    let token := if isGe then " >= " else " < "; let overhead := if isGe then 11 else 9; let base := join isGe (call 4 0) (call 5 1)
    for c in [false,true] do
      for (text,core,type,value,cost) in [
          ("!(f(x)"++token++"g(y))",Core.Expr.unary .boolNot base,Core.Ty.bool,Core.Value.bool (!isGe),14+overhead),
          ("f(x)"++token++"g(y) && p(c)",.ifE base (call 6 2) (.bool false),.bool,.bool (isGe && c),if isGe then 31 else 24),
          ("f(x)"++token++"g(y) || p(c)",.ifE base (.bool true) (call 6 2),.bool,.bool (isGe || c),if isGe then 26 else 29),
          ("f(x)"++token++"g(y) ? x : y",.ifE base (.var 0) (.var 1),.word,.word (w (if isGe then 17 else 5)),15+overhead),
          ("(p(c) ? maker(x) : f)(y)"++token++"g(x)",join isGe (.apply (.ifE (call 6 2) (call 7 0) (.var 4)) (.var 1)) (call 5 0),.bool,.bool (!isGe),(if c then 25 else 20)+overhead)] do
        exercise text .word (.word (w 17)) (.word (w 5)) c false core type value cost
    exercise ("~f(x)"++token++"g(y)") .word (.word (w max)) (.word (w 0)) false false (join isGe (.unary .wordNot (call 4 0)) (call 5 1)) .bool (.bool isGe) (14+overhead)
    let s ← parsed ("(c ? f(x) : Missing)"++token++"g(y)"); let raw ← actual (environment .word (.word (w 17)) (.word (w 5)) true false) s
    have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨raw.cost,raw.evidence []⟩
    check (decide (raw.value=.bool isGe ∧ raw.cost=15+overhead ∧ elaborateRecursiveLocalComputation? names (context .word) s=none)) "raw chosen call succeeds despite unselected unknown"
  for a in [Core.Ty.bool,.unit,.namedData ⟨77⟩,.cell .word,.function .word .word] do
    for text in ["f(x) < g(y)","f(x) >= g(y)"] do check ((elaborateRecursiveLocalComputation? names (context a) (← parsed text)).isNone) "value-free non-Word comparison"
  for text in ["f(x) < p(c)","p(c) >= f(x)","f(Missing) < y","x >= Missing"] do
    check ((elaborateRecursiveLocalComputation? names (context .word) (← parsed text)).isNone) "unchanged wrong-type/name/unextended boundaries"
  let precedence ← parsed "f(x) < g(y) != f(y) >= g(x)"
  check (match precedence.value with | .binary ⟨_,.binary _ ⟨_,.less⟩ _⟩ ⟨_,.notEqual⟩ ⟨_,.binary _ ⟨_,.greaterEqual⟩ _⟩ => true | _ => false) "ordered precedence above nonassociative inequality"
  for text in ["f(x) < g(y) < x","f(x) >= g(y) >= x","f(x) < g(y) >= x"] do
    let file : Syntax.SourceFile := ⟨⟨.main,"recursive-ordered-comparisons.sol"⟩,text⟩
    let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "nonassociative lexer")
    check (match Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) with | .ok _ next => !(tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) | .reject _ _ => true | .invariant _ => false) "nonassociative ordered rejection"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveTupleEntries
/-! Independent original declaration certificates and manual paths retain actual captures, stores and whole results. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveTupleEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveTupleEntries",by decide⟩],by decide⟩⟩,67⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-tuple-entries.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) ("complete original bytes: "++text)
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span && decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original header and parameter ranges"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | ⟨_,.tuple []⟩ => return ⟨.unit,⟨by rw [atSource]; exact .unit⟩⟩
  | ⟨_,.tuple [inner]⟩ => let a ← meaning types inner; return ⟨a.1,⟨by rw [atSource]; exact .single a.2.down⟩⟩
  | ⟨_,.tuple [left,right]⟩ =>
      let a ← meaning types left; let b ← meaning types right
      return ⟨.product a.1 b.1,⟨by rw [atSource]; exact .pair a.2.down b.2.down⟩⟩
  | ⟨span,.tuple (first::second::third::rest)⟩ =>
      let a ← meaning types first; let b ← meaning types ⟨span,.tuple (second::third::rest)⟩
      return ⟨.product a.1 b.1,⟨by rw [atSource]; exact .many a.2.down b.2.down⟩⟩
  | _ => throw (IO.userError "outside structural annotation fixture")
termination_by sizeOf source
private structure Parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span && decide (name.span.endByte≤annotation.span.startByte)) "original parameter fields/order"
      let m ← meaning types annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters types (s.bindFresh owner name.value arg.type)
            (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,
            by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate original parameter")
      else throw (IO.userError "original argument type mismatch")
  | _,_ => throw (IO.userError "original parameter arity")
private structure Path (core : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
    | .unit => return ⟨.unit,s,1,fun _ => by rw [original]; exact .cons .unit .refl⟩
    | .pair left right =>
        let a ← path n left env s; let b ← path n right env a.final
        return ⟨.pair a.value b.value,b.final,a.cost+b.cost+3,fun k => by
          rw [original]
          have p := Core.Steps.cons .enterPair ((a.evidence (.pairRight right env::k)).trans
            (.cons .enterPairRight ((b.evidence (.pairApply a.value::k)).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using p⟩
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [original]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual var missing")
    | .letE head tail =>
        let a ← path n head env s; let b ← path n tail (a.value::env) a.final
        return ⟨b.value,b.final,a.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.letE (a.evidence _) (b.evidence _)⟩
    | .apply fn arg =>
        let f ← path n fn env s; let a ← path n arg env f.final
        match fv : f.value with
        | .closure _ _ body captured =>
            let b ← path n body (a.value::captured) a.final
            return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.apply (fv ▸ f.evidence _) (a.evidence _) (b.evidence [])⟩
        | _ => throw (IO.userError "manual callee shape")
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [original]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual load missing")
        | _ => throw (IO.userError "manual reference shape")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Certificate (Elaborates : Core.Expr → Core.Ty → Prop) (Evaluates : Core.Value → Core.Store → Nat → Prop) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : Elaborates core type
  raw : Evaluates value final cost
private abbrev Child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) :=
  Certificate (RecursiveLocalComputationElaborates s.names s.context source) (RecursiveLocalComputationEvaluatesWithCost s.names env store source)
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (source.span.contains fn.span && source.span.contains argsSpan && argsSpan.contains arg.span &&
        decide (fn.span.endByte ≤ argsSpan.startByte)) "original recursive child order"
      let f ← child s env store fn; let a ← child s env f.final arg
      match ft : f.type, fv : f.value with
      | .function input output,.closure _ _ body captured =>
          if same : a.type=input then
            let b ← path 100 body (a.value::captured) a.final
            return ⟨.apply f.core a.core,output,b.value,b.final,f.cost+a.cost+b.cost+3,
              by rw [original]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
              by rw [original]; exact .application (fv ▸ f.raw) a.raw (b.evidence [])⟩
          else throw (IO.userError "static argument differs")
      | _,_ => throw (IO.userError "static or actual Function differs")
  | ⟨_,.group inner⟩ =>
      let a ← child s env store inner
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .group a.elaboration,by rw [original]; exact .group a.raw⟩
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,.unit,.unit,store,1,by rw [original]; exact .pure .unit .unit .unit,by rw [original]; exact .pure .unit⟩
  | ⟨span,.tuple ⟨tupleSpan,[left,right]⟩⟩ =>
      check (decide (span=tupleSpan ∧ left.span.endByte<right.span.startByte) && tupleSpan.contains left.span && tupleSpan.contains right.span) "original binary tuple spans/order"
      let a ← child s env store left; let b ← child s env a.final right
      return ⟨.pair a.core b.core,.product a.type b.type,.pair a.value b.value,b.final,a.cost+b.cost+3,
        by rw [original]; exact .pair a.elaboration b.elaboration,by rw [original]; exact .pair a.raw b.raw⟩
  | ⟨span,.tuple ⟨tupleSpan,first::second::third::rest⟩⟩ =>
      check (decide (span=tupleSpan ∧ first.span.endByte<second.span.startByte) && tupleSpan.contains first.span) "original flat tuple head/range"
      let a ← child s env store first; let b ← child s env a.final ⟨span,.tuple ⟨tupleSpan,second::third::rest⟩⟩
      return ⟨.pair a.core b.core,.product a.type b.type,.pair a.value b.value,b.final,a.cost+b.cost+3,
        by rw [original]; exact .many a.elaboration b.elaboration,by rw [original]; exact .many a.raw b.raw⟩
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨.var i,t,v,store,1,
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original row missing")
      | none => throw (IO.userError "original actual name missing")
  | _ => throw (IO.userError "outside fixture expression")
termination_by sizeOf source
private abbrev Tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) :=
  Certificate (RecursiveComputationReturnTreeElaborates types owner s source) (RecursiveComputationReturnTreeEvaluatesWithCost owner s.names env store source)
private def tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) : IO (Tree types s env store source) := do
  check (source.value.all fun statement => source.span.contains statement.span) "original statement spans"
  match original : source with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
      let a ← child s env store e
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .expression a.elaboration,by rw [original]; exact .expression a.raw⟩
  | _ => throw (IO.userError "outside original singleton return body")
private def header (types : TypeNameTable) (source : Syntax.FunctionDecl) (output : Core.Ty) : IO (PLift (RuntimeFunctionHeader types source.value.signature output)) := do
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.1=output then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧
            source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          return ⟨⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.2.down)⟩⟩
        else throw (IO.userError "original header policy")
      else throw (IO.userError "original return meaning")
  | _ => throw (IO.userError "original singleton return clause")
private def bodySource (body returns : String) : IO Syntax.FunctionDecl := parsed ("function tuple(f:F,g:G,x:X,y:Y) returns("++returns++"){return "++body++";}")
private def verify (source : Syntax.FunctionDecl) (f g x y : TypedRuntimeArgument) (output : Core.Ty) (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO PreparedRuntimeFunction := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["Y"],y.type),(["R"],output),(["Word"],.word),(["Cell"],.cell .word),(["Fn"],.function .word .word)]
  let args := [f,g,x,y]; let ps ← parameters types .empty .empty source.value.signature.parameters.elements args
  let inputs := ps.actual; let env := inputs.environment.values
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body; let manual ← path 100 core env s
  have erased : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  check (decide (env=[y.value,x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("y",⟨owner,3⟩,y.type,y.value),("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
  check (decide (b.value=value ∧ b.final=final ∧ b.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent raw/Core value/store/cost"
  if fixed : b.core=core ∧ b.type=output then
    let compiled : CompiledRuntimeFunction := ⟨ps.statics,core,output⟩; let prepared : PreparedRuntimeFunction := ⟨inputs,core,output⟩
    have preparation : RecursiveComputationFunctionPrepares types owner source args prepared := ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have compilation : RecursiveComputationFunctionCompiles types owner source compiled := ⟨h.down,ps.declared,by simpa only [compiled,prepared,erased] using preparation.body⟩
    have compiledSome := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
    have preparedSome := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr preparation
    have matching : args.map (·.type)=ps.statics.context.values.reverse := by
      have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
      simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
    have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some compiled := by
      rw [prepareComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte]
    have whole (fuel) (store) : runRecursiveComputationFunction? types owner source args fuel store = some (output,Core.runStateful fuel (.initial core [y.value,x.value,g.value,f.value] store)) := by
      rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte,args,List.reverse_cons,List.reverse_nil]; rfl
    have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
    have _ := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation b.raw b.elaboration ids []
    check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old entry remains None"
    for fuel in List.range (cost+2) do
      have _ := whole fuel s
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial core env s)) ∧ runRuntimeComputationFunction? types owner source args fuel s=none)) "whole full result/tag"
      match exhausted : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact completion"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel exhausted; have _ := Core.runStateful_resume exhausted 2
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧ runRecursiveComputationFunction? types owner source args (fuel+2) s=some (output,Core.runStateful 2 cp))) "genuine saved state/residual/full resume"
      | .fault _ _ => throw (IO.userError "independent successful path faulted")
    return prepared
  else throw (IO.userError "independent exact Core/type")
private def reader (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word location],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word location],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def arg (value : Nat) : TypedRuntimeArgument := ⟨.word,w value,.word⟩
private def captured (a : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.function .word a.type,.closure .word a.type (.var 1) [a.value],.closure (.cons a.valueTyped .nil) (.var rfl)⟩
end RecursiveTupleEntries
open RecursiveTupleEntries
def frontendParsedRecursiveTupleEntryTests : IO Unit := do
  let left := Core.Expr.apply (.var 3) (.var 1); let right := Core.Expr.apply (.var 2) (.var 0)
  let third := Core.Expr.apply (.var 3) (.var 0); let fourth := Core.Expr.apply (.var 2) (.var 1)
  let f := reader 0; let g := writer 0; let x := arg 11; let y := arg 14
  let pairType := Core.Ty.product .word .word; let pairCore := Core.Expr.pair left right
  let payloadClosure := Core.Value.closure .bool .unit (.var 99) [.cellRef .word 77]
  for (body,annotation,arity,core,type,value,cost) in [
      ("(f(x),g(y))","(Word,Word)",2,pairCore,pairType,Core.Value.pair (w 23) (w 14),26),
      ("(f(x),g(y),f(y))","(Word,Word,Word)",3,.pair left (.pair right third),.product .word pairType,.pair (w 23) (.pair (w 14) (w 14)),37),
      ("((f(x),),g(y),f(y),)","(Word,Word,Word)",3,.pair left (.pair right third),.product .word pairType,.pair (w 23) (.pair (w 14) (w 14)),37),
      ("(f(x),g(y),g(x),f(y))","(Word,Word,Word,Word)",4,.pair left (.pair right (.pair fourth third)),.product .word (.product .word pairType),.pair (w 23) (.pair (w 14) (.pair (w 11) (w 11))),55),
      ("(f(x),(g(y),f(y)))","(Word,(Word,Word))",2,.pair left (.pair right third),.product .word pairType,.pair (w 23) (.pair (w 14) (w 14)),37),
      ("(f(x),g(y),f(y),())","(Word,Word,Word,())",4,.pair left (.pair right (.pair third .unit)),.product .word (.product .word (.product .word .unit)),.pair (w 23) (.pair (w 14) (.pair (w 14) .unit)),41)] do
    let source ← bodySource body annotation; let final := if cost=55 then [w 11] else [w 14]
    check (match source.value.body.value with | [⟨_,.returnStmt (some ⟨_,.tuple ⟨_,elements⟩⟩)⟩] => decide (elements.length=arity) | _ => false) "original flat list versus explicit nested child count"
    let prepared ← verify source f g x y type core [w 23] final value cost
    let env := prepared.inputs.environment.values
    let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],.word),(["Y"],.word),(["Word"],.word)]
    let run := runRecursiveComputationFunction? types owner source [f,g,x,y]
    match core,value with
    | .pair _ tail,.pair _ tailValue =>
        let first : Core.State := ⟨.ret (w 23),[.pairRight tail env],[w 23]⟩
        let startTail : Core.State := ⟨.eval tail env,[.pairApply (w 23)],[w 23]⟩
        let apply : Core.State := ⟨.ret tailValue,[.pairApply (w 23)],final⟩
        check (decide (run 9 [w 23]=some (type,.outOfFuel first) ∧ run 10 [w 23]=some (type,.outOfFuel startTail) ∧ run (cost-1) [w 23]=some (type,.outOfFuel apply) ∧ Core.runStateful 1 apply=.done value final)) "saved original left survives every right update"
        for (spent,cp) in [(9,first),(10,startTail),(cost-1,apply)] do check (decide (Core.runStateful (cost-spent) cp=.done value final)) "fixed pair checkpoints resume exactly"
        match tail with
        | .pair _ rest =>
            let inner : Core.State := ⟨.ret (w 14),[.pairRight rest env,.pairApply (w 23)],[w 14]⟩
            check (decide (run 26 [w 23]=some (type,.outOfFuel inner) ∧ Core.runStateful (cost-26) inner=.done value final)) "flat tail keeps original env and latest store before its remaining calls"
        | _ => pure ()
    | _,_ => throw (IO.userError "literal pair expectation")
    for store in [[],[w 23],[.bool true],[.pair payloadClosure .unit],[payloadClosure],[w 23,.bool false]] do
      for fuel in List.range (cost+2) do
        check (decide (run fuel store=some (type,Core.runStateful fuel (.initial core env store)))) "same prepared arbitrary stores retain product tag and whole result"
        match exhausted : Core.runStateful fuel (.initial core env store) with
        | .outOfFuel cp =>
            have _ := Core.runStateful_resume exhausted 60
            check (decide (run (fuel+60) store=some (type,Core.runStateful 60 cp))) "all genuine checkpoints resume success or child fault"
        | _ => pure ()
  let source ← bodySource "(f(x),g(y))" "(Word,Word)"
  for old in [w 23,.bool true,.pair payloadClosure .unit,payloadClosure,.cellRef .word 71] do
    discard <| verify source f g x y pairType pairCore [old] [w 14] (.pair old (w 14)) 26
    discard <| verify source g (reader 1) x y pairType pairCore [w 23,old] [w 11,old] (.pair (w 11) old) 26
  discard <| verify source g f x y pairType pairCore [w 23] [w 11] (.pair (w 11) (w 11)) 26
  discard <| verify source f g y x pairType pairCore [w 23] [w 11] (.pair (w 23) (w 11)) 26
  discard <| verify source (reader 1) g x y pairType pairCore [w 23,w 7] [w 14,w 7] (.pair (w 7) (w 14)) 26
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 77,.cellRef⟩
  let captures ← bodySource "(f(x),g(y))" "(Cell,Fn)"
  discard <| verify captures (captured cell) (captured f) x y (.product cell.type f.type) pairCore [] [] (.pair cell.value f.value) 15
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],.word),(["Y"],.word),(["Word"],.word)]
  for (a,b,store,firstFault) in [(reader 1,g,[w 23],8),(g,reader 1,[w 23],24)] do
    let env := [y.value,x.value,b.value,a.value]; let run := runRecursiveComputationFunction? types owner source [a,b,x,y]
    let (frames,actual,kept) := if firstFault=8 then ([Core.Frame.loadCellApply,.pairRight right env],x.value,[w 23])
      else ([Core.Frame.loadCellApply,.pairApply (w 11)],y.value,[w 11])
    let cp : Core.State := ⟨.eval (.var 1) [actual,.cellRef .word 1],frames,kept⟩
    let fault := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),frames,kept⟩
    check (decide (run (firstFault-1) store=some (pairType,.outOfFuel cp) ∧ run firstFault store=some (pairType,fault) ∧ Core.runStateful 1 cp=fault)) "left child fault skips writable right; right fault keeps actual left update"
    for fuel in List.range 30 do
      check (decide (run fuel store=some (pairType,Core.runStateful fuel (.initial pairCore env store)))) "fault threshold and full saved state"
      match exhausted : Core.runStateful fuel (.initial pairCore env store) with
      | .outOfFuel residual =>
          have _ := Core.runStateful_resume exhausted 30
          check (decide (fuel<firstFault ∧ run (fuel+30) store=some (pairType,Core.runStateful 30 residual))) "every pre-fault checkpoint resumes"
      | outcome => check (decide (firstFault≤fuel ∧ outcome=fault)) "first child fault threshold remains exact at every later fuel"
  for declaration in ["function tuple(f:F,g:G,x:X,y:Y) returns(Word,Word){return (f(x),g(y));}",
      "function tuple(f:F,g:G,x:X,y:Y) returns(((Word,Word),Word)){return (f(x),g(y),f(y));}",
      "function tuple(f:F,g:G,x:X,y:Y) returns((Word,Word)){return (f(x),missing);}"] do
    let bad ← parsed declaration
    check (decide (compileRecursiveComputationFunction? types owner bad=none ∧ prepareRecursiveComputationFunction? types owner bad [f,g,x,y]=none ∧ runRecursiveComputationFunction? types owner bad [f,g,x,y] 60 [w 23]=none)) "multiple returns, association and unknown names remain rejected"
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-tuple-entries.sol"⟩,"function tuple(f:F,g:G,x,y:Y) returns((Word,Word)){return (f(x),g(y));}"⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "untyped parameter lexer")
  check (match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) with | .ok _ next => !(tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) | .reject _ _ => true | .invariant _ => false) "missing parameter annotation remains a parser rejection"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveTupleMigrations
/-! Six original tuple rejection fixtures retain their exact source, owner,
file and ordered caller rows. Independent typing/elaboration meets literal Core. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveTupleMigrations

private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def rows (owner : Resolved.DeclarationId) (variant : Nat) : LocalNameTable × Resolved.Context :=
  let id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
  let foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
  let wordFn := Core.Ty.function .word .word
  match variant with
  | 0 => ([("x",id 7),("f",foreign),("g",id 9),("maker",id 12),("y",id 14),("c",id 15),("p",id 20),("f",id 88)],
      [(id 7,.word),(foreign,wordFn),(id 9,wordFn),(id 12,.function .word wordFn),(id 14,.word),(id 15,.bool),
       (id 20,.function (.product .word .unit) .word),(foreign,.bool)])
  | 1 => ([("x",id 7),("f",foreign),("g",id 9),("y",id 14),("c",id 15),("f",id 88)],
      [(id 7,.word),(foreign,wordFn),(id 9,wordFn),(id 14,.word),(id 15,.bool),(foreign,.bool)])
  | _ =>
      let boolNames := if variant=3 then [("true",id 90),("false",id 91)] else []
      let boolTypes := if variant=3 then [(id 90,Core.Ty.bool),(id 91,.bool)] else []
      ([("x",id 7),("y",id 14),("c",id 15),("d",id 16),("f",foreign),("g",id 9),("p",id 20),("maker",id 25)]++boolNames++[("f",id 88)],
       [(id 7,.word),(id 14,.word),(id 15,.bool),(id 16,.bool),(foreign,wordFn),(id 9,wordFn),
        (id 20,.function .bool .bool),(id 25,.function .word wordFn)]++boolTypes++[(foreign,.bool)])

private structure Static (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates table ctx s core type
  typing : RecursiveLocalComputationHasType table ctx s type

private def statics (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) : IO (Static table ctx s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : table.lookup? name.value with
      | some localId =>
          match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some t,some n =>
              have r : ResolvesLocalExpression table s (.var localId) := by
                rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named)
              have ty : Resolved.HasType ctx (.var localId) t := .var (Resolved.LocalScope.lookup?_iff.mp typed)
              return ⟨.var n,t,.pure r (.var (Resolved.LocalScope.index?_iff.mp indexed)) ty,.pure (r.reflects_type ty)⟩
          | _,_ => throw (IO.userError "original typed/indexed row")
      | _ => throw (IO.userError "original first name")
  | ⟨_,.group inner⟩ =>
      let a ← statics table ctx inner
      return ⟨a.core,a.type,by rw [shape]; exact .group a.elaboration,by rw [shape]; exact .group a.typing⟩
  | ⟨span,.tuple ⟨tupleSpan,[left,right]⟩⟩ =>
      check (decide (span=tupleSpan ∧ left.span.startByte=span.startByte+1 ∧ right.span.endByte+1=span.endByte ∧
        left.span.endByte<right.span.startByte) && span.contains left.span && span.contains right.span) "original ordered tuple ranges"
      let a ← statics table ctx left; let b ← statics table ctx right
      return ⟨.pair a.core b.core,.product a.type b.type,by rw [shape]; exact .pair a.elaboration b.elaboration,
        by rw [shape]; exact .pair a.typing b.typing⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← statics table ctx fn; let a ← statics table ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,
            by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨_,.unary ⟨_,.bitNot⟩ inner⟩ =>
      let a ← statics table ctx inner
      if word : a.type=.word then return ⟨.unary .wordNot a.core,.word,
        by rw [shape]; exact .bitNot (word ▸ a.elaboration),by rw [shape]; exact .bitNot (word ▸ a.typing)⟩
      else throw (IO.userError "Word complement")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← statics table ctx guard; let a ← statics table ctx yes; let b ← statics table ctx no
      if valid : g.type=.bool ∧ b.type=a.type then return ⟨.ifE g.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ g.elaboration) a.elaboration (valid.2 ▸ b.elaboration),
        by rw [shape]; exact .conditional (valid.1 ▸ g.typing) a.typing (valid.2 ▸ b.typing)⟩
      else throw (IO.userError "whole guard/branch typing")
  | _ => throw (IO.userError "original migration shape")
termination_by sizeOf s

end ParsedRecursiveTupleMigrations
open ParsedRecursiveTupleMigrations

def frontendParsedRecursiveTupleMigrationTests : IO Unit := do
  let call (f x : Nat) := Core.Expr.apply (.var f) (.var x)
  let fixtures : List (Resolved.DeclarationId × String × String × Nat × Core.Expr × Core.Expr) := [
    (⟨⟨.main,⟨[⟨"Recursive",by decide⟩],by decide⟩⟩,53⟩,"recursive-computation.sol","(g(x),x)",0,call 2 0,.var 0),
    (⟨⟨.main,⟨[⟨"Binary",by decide⟩],by decide⟩⟩,56⟩,"recursive-binary.sol","(f(x),y)",1,call 1 0,.var 3),
    (⟨⟨.main,⟨[⟨"Conditional",by decide⟩],by decide⟩⟩,57⟩,"recursive-conditional.sol","(c ? f(x) : y,y)",2,.ifE (.var 2) (call 4 0) (.var 1),.var 1),
    (⟨⟨.main,⟨[⟨"Unary",by decide⟩],by decide⟩⟩,58⟩,"recursive-unary.sol","(~f(x),y)",2,.unary .wordNot (call 4 0),.var 1),
    (⟨⟨.main,⟨[⟨"NegatedComparisons",by decide⟩],by decide⟩⟩,60⟩,"recursive-negated-comparisons.sol","(f(x),y)",3,call 4 0,.var 1),
    (⟨⟨.main,⟨[⟨"OrderedComparisons",by decide⟩],by decide⟩⟩,62⟩,"recursive-ordered-comparisons.sol","(f(x),y)",3,call 4 0,.var 1)]
  for (owner,path,text,variant,left,right) in fixtures do
    let (table,ctx) := rows owner variant
    let expected := Core.Expr.pair left right; let expectedType := Core.Ty.product .word .word
    let file : Syntax.SourceFile := ⟨⟨.main,path⟩,text⟩
    let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "migration lexer")
    let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError "migration parser")
    check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "unchanged original source"
    let a ← statics table ctx s
    have _ := elaborateRecursiveLocalComputation?_iff.mpr a.elaboration
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp a.typing
    have _ := a.elaboration.core_hasType
    check (decide (a.core=expected ∧ a.type=expectedType ∧
      elaborateRecursiveLocalComputation? table ctx s=some (expected,expectedType) ∧
      elaborateLocalExpression? table ctx s=none ∧ elaborateLocalComputation? table ctx s=none)) "original tuple exact success and old rejection"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveTuples
/-! Original tuple syntax has independent static/raw evidence and separate literal
Core/manual paths. No environment typing is assumed; opaque values/captures stay literal. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveTuples
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Tuples",by decide⟩],by decide⟩⟩,64⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("y",id 14),("c",id 15),("d",id 16),("f",foreign),("g",id 9),("p",id 20),("maker",id 25),("true",id 90),("false",id 91),("f",id 88)]
private def context (a : Core.Ty) : Resolved.Context := [(id 7,a),(id 14,a),(id 15,.bool),(id 16,.bool),(foreign,.function a a),(id 9,.function a a),(id 20,.function .bool .bool),(id 25,.function a (.function a a)),(id 90,.bool),(id 91,.bool),(foreign,.bool)]
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.bool false]
private def environment (a : Core.Ty) (x y : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(id 7,x),(id 14,y),(id 15,.bool c),(id 16,.bool d),(foreign,identity a),(id 9,identity a),(id 20,identity .bool),(id 25,.closure a (.function a a) (.var 1) [identity a]),(id 90,.bool false),(id 91,.bool true),(foreign,.bool false)]
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def wrap : Nat → String → String | 0,s => s | n+1,s => "("++wrap n s++")"
private def flatArity : Syntax.Expr → Nat
  | ⟨_,.group inner⟩ => flatArity inner | ⟨_,.tuple elements⟩ => elements.elements.length | _ => 0
private def tupleRanges (span tupleSpan : Syntax.SourceSpan) (elements : List Syntax.Expr) : Bool :=
  span.contains tupleSpan && elements.all (tupleSpan.contains ·.span) &&
    (elements.zip elements.tail).all (fun (a,b) => decide (a.span.endByte<b.span.startByte))
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-tuples.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError s!"parser: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "original bytes/span"
  return s
private structure Static (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates names ctx s core type
  typing : RecursiveLocalComputationHasType names ctx s type
private def statics (ctx : Resolved.Context) (s : Syntax.Expr) : IO (Static ctx s) := do
  match shape : s with
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span) "group span"; let a ← statics ctx inner
      return ⟨a.core,a.type,by rw [shape]; exact .group a.elaboration,by rw [shape]; exact .group a.typing⟩
  | ⟨span,.tuple ⟨tupleSpan,[]⟩⟩ =>
      check (tupleRanges span tupleSpan []) "empty tuple spans"
      return ⟨.unit,.unit,by rw [shape]; exact .pure .unit .unit .unit,by rw [shape]; exact .pure .unit⟩
  | ⟨span,.tuple ⟨tupleSpan,[left,right]⟩⟩ =>
      check (tupleRanges span tupleSpan [left,right]) "original binary tuple elements"
      let a ← statics ctx left; let b ← statics ctx right
      return ⟨.pair a.core b.core,.product a.type b.type,by rw [shape]; exact .pair a.elaboration b.elaboration,by rw [shape]; exact .pair a.typing b.typing⟩
  | ⟨span,.tuple ⟨tupleSpan,first::second::third::rest⟩⟩ =>
      check (tupleRanges span tupleSpan (first::second::third::rest)) "original flat tuple elements/order"
      let a ← statics ctx first; let b ← statics ctx ⟨span,.tuple ⟨tupleSpan,second::third::rest⟩⟩
      return ⟨.pair a.core b.core,.product a.type b.type,by rw [shape]; exact .many a.elaboration b.elaboration,by rw [shape]; exact .many a.typing b.typing⟩
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call children"
      let f ← statics ctx fn; let a ← statics ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨span,.conditional guard question yes colon no⟩ =>
      check (span.contains guard.span && span.contains yes.span && span.contains no.span && span.contains question && span.contains colon &&
        decide (guard.span.endByte≤question.startByte ∧ question.endByte=question.startByte+1 ∧ question.endByte≤yes.span.startByte ∧
          yes.span.endByte≤colon.startByte ∧ colon.endByte=colon.startByte+1 ∧ colon.endByte≤no.span.startByte)) "original question/colon order"
      let g ← statics ctx guard; let a ← statics ctx yes; let b ← statics ctx no
      if valid : g.type=.bool ∧ b.type=a.type then return ⟨.ifE g.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ g.elaboration) a.elaboration (valid.2 ▸ b.elaboration),
        by rw [shape]; exact .conditional (valid.1 ▸ g.typing) a.typing (valid.2 ▸ b.typing)⟩
      else throw (IO.userError "whole conditional types")
  | ⟨_,.identifier name⟩ => match named : names.lookup? name.value with
    | some localId => match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
      | some t,some n =>
          have r : ResolvesLocalExpression names s (.var localId) := by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named)
          have ty : Resolved.HasType ctx (.var localId) t := .var (Resolved.LocalScope.lookup?_iff.mp typed)
          return ⟨.var n,t,(LocalComputationElaborates.pure r (.var (Resolved.LocalScope.index?_iff.mp indexed)) ty).toRecursiveLocalComputation,.pure (r.reflects_type ty)⟩
      | _,_ => throw (IO.userError "caller row")
    | _ => throw (IO.userError "caller name")
  | _ => throw (IO.userError "outside original source fixture")
termination_by sizeOf s
private structure RawLeaf (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, LocalExpressionEvaluatesWithCost names env store s value store 1
private def rawLeaf (env : Resolved.Environment) (s : Syntax.Expr) : IO (RawLeaf env s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match named : names.lookup? name.value with
    | some localId => match found : env.lookup? localId with
      | some v => return ⟨v,fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
      | _ => throw (IO.userError "actual row")
    | _ => throw (IO.userError "actual name")
  | _ => throw (IO.userError "actual identifier")
private structure Actual (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost names env store s value store cost
private def actual (env : Resolved.Environment) (s : Syntax.Expr) : IO (Actual env s) := do
  match shape : s with
  | ⟨_,.group inner⟩ => let a ← actual env inner; return ⟨a.value,a.cost,fun store => by rw [shape]; exact .group (a.evidence store)⟩
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,1,fun _ => by rw [shape]; exact .pure .unit⟩
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
      let a ← actual env left; let b ← actual env right
      return ⟨.pair a.value b.value,a.cost+b.cost+3,fun store => by rw [shape]; exact .pair (a.evidence store) (b.evidence store)⟩
  | ⟨span,.tuple ⟨tupleSpan,first::second::third::rest⟩⟩ =>
      let a ← actual env first; let b ← actual env ⟨span,.tuple ⟨tupleSpan,second::third::rest⟩⟩
      return ⟨.pair a.value b.value,a.cost+b.cost+3,fun store => by rw [shape]; exact .many (a.evidence store) (b.evidence store)⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← actual env fn; let a ← actual env arg
      match closure : f.value with
      | .closure _ _ (.var n) captured => match found : (a.value::captured)[n]? with
        | some v => return ⟨v,f.cost+a.cost+4,fun store => by rw [shape]; exact .application (closure ▸ f.evidence store) (a.evidence store) (.cons (.var found) .refl)⟩
        | _ => throw (IO.userError "actual captured index")
      | _ => throw (IO.userError "fixture body")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← actual env guard
      match gv : g.value with
      | .bool true => let a ← actual env yes; return ⟨a.value,g.cost+a.cost+2,fun store => by rw [shape]; exact .ifTrue (gv ▸ g.evidence store) (a.evidence store)⟩
      | .bool false => let b ← actual env no; return ⟨b.value,g.cost+b.cost+2,fun store => by rw [shape]; exact .ifFalse (gv ▸ g.evidence store) (b.evidence store)⟩
      | _ => throw (IO.userError "actual Bool")
  | _ => let a ← rawLeaf env s; return ⟨a.value,1,fun store => .pure (a.evidence store)⟩
termination_by sizeOf s
private structure Path (env : Core.Environment) (core : Core.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store k, Core.Steps cost ⟨.eval core env,k,store⟩ ⟨.ret value,k,store⟩
private def manual : (fuel : Nat) → (env : Core.Environment) → (core : Core.Expr) → IO (Path env core)
  | 0,_,_ => throw (IO.userError "manual certificate depth")
  | fuel+1,env,core => do
    match shape : core with
    | .unit => return ⟨.unit,1,fun _ _ => by rw [shape]; exact .cons .unit .refl⟩
    | .pair left right =>
      let a ← manual fuel env left; let b ← manual fuel env right
      return ⟨.pair a.value b.value,a.cost+b.cost+3,fun store _ => by rw [shape]; simpa only [Nat.add_assoc] using Core.Steps.cons .enterPair ((a.evidence store _).trans (.cons .enterPairRight ((b.evidence store _).trans (.cons .applyPair .refl))))⟩
    | .bool b => return ⟨.bool b,1,fun _ _ => by rw [shape]; exact .cons .bool .refl⟩
    | .var n => match found : env[n]? with
      | some v => return ⟨v,1,fun _ _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | _ => throw (IO.userError "manual variable")
    | .apply fn arg =>
      let f ← manual fuel env fn; let a ← manual fuel env arg
      match closure : f.value with
      | .closure _ _ (.var n) captured => match found : (a.value::captured)[n]? with
        | some v => return ⟨v,f.cost+a.cost+4,fun store _ => by rw [shape]; exact CostStepComposition.apply (closure ▸ f.evidence store _) (a.evidence store _) (.cons (.var found) .refl)⟩
        | _ => throw (IO.userError "manual body index")
      | _ => throw (IO.userError "manual closure")
    | .ifE guard yes no =>
      let g ← manual fuel env guard
      match gv : g.value with
      | .bool true => let a ← manual fuel env yes; return ⟨a.value,g.cost+a.cost+2,fun store k => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence store _) (a.evidence store k)⟩
      | .bool false => let b ← manual fuel env no; return ⟨b.value,g.cost+b.cost+2,fun store k => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence store _) (b.evidence store k)⟩
      | _ => throw (IO.userError "manual guard")
    | _ => throw (IO.userError "manual Core grammar")
private def exercise (text : String) (a : Core.Ty) (x y : Core.Value) (c d : Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) (pureSource : Bool := false) : IO Unit := do
  let s ← parsed text; let env := environment a x y c d; let p ← statics (context a) s; let r ← actual env s; let m ← manual 30 env.values core
  if fixed : p.core=core ∧ p.type=type ∧ r.value=value ∧ r.cost=cost ∧ m.value=value ∧ m.cost=cost then
    have e : RecursiveLocalComputationElaborates names (context a) s core type := by simpa only [fixed.1,fixed.2.1] using p.elaboration
    have _ := elaborateRecursiveLocalComputation?_iff.mp (elaborateRecursiveLocalComputation?_iff.mpr e)
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp p.typing
    have _ := e.core_hasType
    check (decide (elaborateRecursiveLocalComputation? names (context a) s=some (core,type) ∧ elaborateLocalExpression? names (context a) s=(if pureSource then some (core,type) else none) ∧ elaborateLocalComputation? names (context a) s=(if pureSource then some (core,type) else none))) "new exact and original pure/old endpoint boundary"
    for store in [[],[Core.Value.bool true,.cellRef .word 91]] do
      have counted : RecursiveLocalComputationEvaluatesWithCost names env store s value store cost := by simpa only [fixed.2.2.1,fixed.2.2.2.1] using r.evidence store
      have path : ∀ k, Core.Steps cost ⟨.eval core env.values,k,store⟩ ⟨.ret value,k,store⟩ := by simpa only [fixed.2.2.2.2.1,fixed.2.2.2.2.2] using m.evidence store
      have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨cost,counted⟩
      have coreRaw := (e.evaluates_iff rfl).mp raw
      have _ := counted.deterministic ((e.evaluatesWithCost_iff_steps rfl).mpr (path []))
      let pending : List Core.Frame := [.letBody .unit []]
      have _ := counted.toStepsWithContinuation e rfl pending
      for fuel in List.range (cost+2) do
        have _ := (path []).runStateful_done_iff (fuel := fuel)
        match outcome : Core.runStateful fuel (.initial core env.values store) with
        | .done v st => check (decide (cost≤fuel ∧ v=value ∧ st=store)) "literal value/store/threshold"
        | .outOfFuel cp =>
            have _ := (path []).residual_of_outOfFuel outcome
            check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value store ∧ Core.runStateful 1 cp=Core.runStateful (fuel+1) (.initial core env.values store))) "genuine residual/full replay"
        | .fault _ _ => throw (IO.userError "fixed path fault")
      have fragment := e.core_fragment
      have _ := fragment.weakenAt 3
      for cutoff in [0,3] do
        let leading := env.values.take cutoff; let suffix := env.values.drop cutoff
        have same : leading++suffix=env.values := List.take_append_drop cutoff env.values
        let inserted : Core.Value := .closure .bool .unit (.var 99) [.cellRef .word 77]
        have original : Core.Evaluates (leading++suffix) store core value store := by rw [same]; exact coreRaw
        have changed := (fragment.evaluates_insert_iff leading suffix inserted).mpr original
        have paired : ∀ k, Core.Steps cost ⟨.eval core (leading++suffix),k,store⟩ ⟨.ret value,k,store⟩ ∧
            Core.Steps cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),k,store⟩ ⟨.ret value,k,store⟩ := by
          obtain ⟨n,paths⟩ := fragment.insertion_paths leading suffix inserted original
          have eqCost : n=cost := ((paths []).1.final_unique (by simpa only [same,Core.State.final] using path [])).1
          exact eqCost ▸ paths
        check (decide (Core.runStateful cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),pending,store⟩=.outOfFuel ⟨.ret value,pending,store⟩)) "inserted pending endpoint"
  else throw (IO.userError s!"independent certificate mismatch: {text}")
private def overlap : IO Unit := do
  let s ← parsed "(c ? x : Missing,y)"; let w := Core.Word.ofNatModulo
  let env := environment .word (.word (w 17)) (.word (w 5)) true false; let fresh ← actual env s
  match shape : s with
  | ⟨_,.tuple ⟨_,[⟨_,.conditional guard _ yes _ _⟩,right]⟩⟩ =>
      let g ← rawLeaf env guard; let l ← rawLeaf env yes; let r ← rawLeaf env right
      if same : g.value=.bool true ∧ l.value=.word (w 17) ∧ r.value=.word (w 5) then
        have old : LocalComputationEvaluatesWithCost names env [] s (.pair (.word (w 17)) (.word (w 5))) [] 8 :=
          .pure (by rw [shape]; exact .pair (.ifTrue (same.1 ▸ g.evidence []) (same.2.1 ▸ l.evidence [])) (same.2.2 ▸ r.evidence []))
        have _ := (fresh.evidence []).deterministic old.toRecursiveLocalComputation
      else throw (IO.userError "old leaves")
  | _ => throw (IO.userError "original pure-overlap tuple")
  check (decide (fresh.value=.pair (.word (w 17)) (.word (w 5)) ∧ fresh.cost=8 ∧ elaborateRecursiveLocalComputation? names (context .word) s=none)) "old pure/new pair overlap despite unselected unknown"
private def foldTuple {α : Type} (empty : α) (pair : α → α → α) : List α → α
  | [] => empty | [last] => last | first::second::rest => pair first (foldTuple empty pair (second::rest))
private def sourceCalls (fn arg : String) : Nat → String | 0 => arg | n+1 => fn++"("++sourceCalls fn arg n++")"
private def coreCalls (fn arg : Nat) : Nat → Core.Expr | 0 => .var arg | n+1 => .apply (.var fn) (coreCalls fn arg n)
private structure Item where
  text : String
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
private def checkpoints (a : Core.Ty) (x y : Core.Value) (left right : Core.Expr)
    (leftValue rightValue : Core.Value) (lc rc : Nat) : IO Unit := do
  let env := (environment a x y true false).values; let store := [Core.Value.cellRef .word 37]
  let first : Core.State := ⟨.ret leftValue,[.pairRight right env],store⟩
  let second : Core.State := ⟨.ret rightValue,[.pairApply leftValue],store⟩
  check (decide (Core.runStateful (lc+1) (.initial (.pair left right) env store)=.outOfFuel first ∧
    Core.runStateful (rc+1) first=.outOfFuel second ∧ Core.runStateful 1 second=.done (.pair leftValue rightValue) store ∧
    Core.runStateful (rc+2) first=.done (.pair leftValue rightValue) store)) "genuine pairRight saved caller/opaque left and pairApply residual"
end ParsedRecursiveTuples
open ParsedRecursiveTuples
def frontendParsedRecursiveTupleTests : IO Unit := do
  let w := fun n => Core.Value.word (Core.Word.ofNatModulo n)
  let storedClosure := Core.Value.closure .word .word (.loadCell (.var 1)) [.cellRef .word 91]
  for (a,x,y) in [(Core.Ty.word,w 17,w 5),(.bool,.bool false,.bool true),(.unit,.unit,.unit),
      (.namedData ⟨77⟩,.constructed ⟨⟨77⟩,3⟩ (.cellRef .word 89),.constructed ⟨⟨77⟩,4⟩ storedClosure),
      (.cell .word,.cellRef .word 5,.cellRef .word 8),(.function .word .word,storedClosure,.closure .word .word (.var 0) [.bool false])] do
    exercise "()" a x y true false .unit .unit .unit 1 true
    for text in ["(x)","(x,)"] do
      check (match (← parsed text).value with | .group _ => true | _ => false) "singleton source is a group"
      exercise text a x y true false (.var 0) a x 1 true
    exercise "(f(f(x)),)" a x y true false (.apply (.var 4) (call 4 0)) a x 11
    exercise "(x,y,c,())" a x y true false (.pair (.var 0) (.pair (.var 1) (.pair (.var 2) .unit))) (.product a (.product a (.product .bool .unit))) (.pair x (.pair y (.pair (.bool true) .unit))) 13 true
    exercise "(f(x),g(y))" a x y true false (.pair (call 4 0) (call 5 1)) (.product a a) (.pair x y) 15
    exercise "((f(x),g(y)),c)" a x y true false (.pair (.pair (call 4 0) (call 5 1)) (.var 2)) (.product (.product a a) .bool) (.pair (.pair x y) (.bool true)) 19
    exercise "(f(x),(g(y),c))" a x y true false (.pair (call 4 0) (.pair (call 5 1) (.var 2))) (.product a (.product a .bool)) (.pair x (.pair y (.bool true))) 19
    checkpoints a x y (call 4 0) (call 5 1) x y 6 6
    for c in [false,true] do
      exercise "((p(c)?maker(x):f)(y),f(x))" a x y c false (.pair (.apply (.ifE (call 6 2) (call 7 0) (.var 4)) (.var 1)) (call 4 0)) (.product a a) (.pair y x) (if c then 28 else 23)
      exercise "(c?f(x):g(y),c)" a x y c false (.pair (.ifE (.var 2) (call 4 0) (call 5 1)) (.var 2)) (.product a .bool) (.pair (if c then x else y) (.bool c)) 13
  for length in [2,3,4,9] do
    for depth in [1,3,7] do
      let items : List Item := (List.range length).map fun i =>
        if i%4=0 then ⟨sourceCalls "f" "x" depth,coreCalls 4 0 depth,.word,w 17,5*depth+1⟩
        else if i%4=1 then ⟨sourceCalls "g" "y" (depth+1),coreCalls 5 1 (depth+1),.word,w 5,5*(depth+1)+1⟩
        else if i%4=2 then ⟨"p(c)",call 6 2,.bool,.bool true,6⟩ else ⟨"()",.unit,.unit,.unit,1⟩
      let core := foldTuple .unit Core.Expr.pair (items.map (·.core))
      let type := foldTuple .unit Core.Ty.product (items.map (·.type))
      let value := foldTuple .unit Core.Value.pair (items.map (·.value))
      let cost := (items.map (·.cost)).sum+3*(length-1)
      for trailing in [false,true] do
        for groups in [0,2] do
          let text := wrap groups ("("++String.intercalate ", " (items.map (·.text))++(if trailing then "," else "")++")")
          check (decide (flatArity (← parsed text)=length)) "original flat element count, trailing comma and outer groups"
          exercise text .word (w 17) (w 5) true false core type value cost
      match items with
      | first::rest =>
          checkpoints .word (w 17) (w 5) first.core (foldTuple .unit Core.Expr.pair (rest.map (·.core))) first.value
            (foldTuple .unit Core.Value.pair (rest.map (·.value))) first.cost ((rest.map (·.cost)).sum+3*(rest.length-1))
      | _ => throw (IO.userError "generated nonempty tuple")
  overlap
  exercise "(true,false)" .word (w 17) (w 5) true false (.pair (.var 8) (.var 9)) (.product .bool .bool) (.pair (.bool false) (.bool true)) 5 true
  let rawSource ← parsed "(f(x),c?g(y):Missing,p(c))"; let raw ← actual (environment .word (w 17) (w 5) true false) rawSource
  have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨raw.cost,raw.evidence []⟩
  check (decide (raw.value=.pair (w 17) (.pair (w 5) (.bool true)) ∧ raw.cost=27 ∧ elaborateRecursiveLocalComputation? names (context .word) rawSource=none)) "recursive chosen component versus whole missing tail"
  let base ← parsed "x"; let singleton : Syntax.Expr := ⟨base.span,.tuple ⟨base.span,[base]⟩⟩
  have noRaw {env : Resolved.Environment} {st final : Core.Store} {v : Core.Value}
      (h : RecursiveLocalComputationEvaluates names env st singleton v final) : False := by
    dsimp only [singleton] at h; cases h with | pure child => cases child
  check ((elaborateRecursiveLocalComputation? names (context .word) singleton).isNone && (resolveLocalExpression? names singleton).isNone) "manual singleton AST stays unsupported"
  for text in ["(Missing,f(x))","(f(x),Missing)","(f(x),y,Missing)","(f(c),x)","(x,x(c))",
      "(c?(x,y):x,f(x))","[f(x),y]","(f(x),y).x","(f(x),y)[x]"] do
    check ((elaborateRecursiveLocalComputation? names (context .word) (← parsed text)).isNone) "whole strict children/name/type/unextended boundaries"
  for text in ["(Missing,f(x))","(f(x),Missing)","(f(x),y,Missing)"] do
    let s ← parsed text
    let success ← try let _ ← actual (environment .word (w 17) (w 5) true false) s; pure true catch _ => pure false
    check (!success) "every tuple child is actually strict"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveIdentityRenamingBoundaryProperties
/-! Injectivity is distinct from positional typing, and whole checking is
distinct from selected raw success. The original source and actual captured
payload are not rewritten when names/context/environment IDs are relabeled. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveIdentityRenamingBoundary
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveIdentityBoundary",by decide⟩],by decide⟩⟩,127⟩
private def ident (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"recursive-identity-boundary.sol"⟩,37,200⟩
private def ref (n : String) : Syntax.Expr := ⟨span,.identifier ⟨span,n⟩⟩
private def names : LocalNameTable := [("c",ident 7),("f",ident 13),("x",ident 21)]
private def context : Resolved.Context := [(ident 7,.bool),(ident 13,.function .bool .bool),(ident 21,.bool)]
private def call : Syntax.Expr := ⟨span,.call (ref "f") ⟨span,[ref "x"]⟩⟩
private def lazySource (right : Syntax.Expr) : Syntax.Expr := ⟨span,.binary (ref "c") ⟨span,.logicalAnd⟩ right⟩
private def core : Core.Expr := .ifE (.var 0) (.apply (.var 1) (.var 2)) (.bool false)
private def closure (payload : Core.Value) (captured : Core.Environment) : Core.Value :=
  .closure .bool .bool (.var 1) (payload::captured)
private def env (choice : Bool) (payload argument : Core.Value) (captured : Core.Environment) : Resolved.Environment :=
  [(ident 7,.bool choice),(ident 13,closure payload captured),(ident 21,argument)]
private theorem original : RecursiveLocalComputationElaborates names context (lazySource call) core .bool :=
  .logicalAnd (.pure (.identifier .head) (.var .head) (.var .head))
    (.application
      (.pure (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head)))
      (.pure (.identifier (.tail (by decide) (.tail (by decide) .head)))
        (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) (.tail (by decide) .head)))))
private theorem callCost (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env true payload argument captured) s call payload s 6 := by
  refine .application (parameterType := .bool) (resultType := .bool) (body := .var 1) (captured := payload::captured)
    (argumentValue := argument) (argumentStore := s) (bodyStore := s) (functionCost := 1) (argumentCost := 1) (bodyCost := 1) ?_ ?_ (.cons (.var rfl) .refl)
  · exact .pure (.identifier (.tail (by decide) .head) (.tail (by decide) .head))
  · exact .pure (.identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head)))
private theorem raw (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env true payload argument captured) s (lazySource call) payload s 9 := by
  refine .andTrue (middleStore := s) (leftCost := 1) (rightCost := 6) ?_ (callCost payload argument captured s)
  exact .pure (.identifier .head .head)
private theorem manual (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 9 ⟨.eval core (env true payload argument captured).values,k,s⟩ ⟨.ret payload,k,s⟩ :=
  CostStepComposition.ifTrue (.cons (.var rfl) .refl)
    (CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))

theorem selected_rhs_keeps_arbitrary_actual_payload_despite_static_bool_tag
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping context)
      (lazySource call)=some (core,.bool) ∧
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping names)
      (Resolved.LocalScope.mapIds mapping (env true payload argument captured)) s (lazySource call) payload s 9 ∧
    Core.Steps 9 ⟨.eval core (Resolved.LocalScope.mapIds mapping (env true payload argument captured)).values,k,s⟩ ⟨.ret payload,k,s⟩ :=
  ⟨(elaborateRecursiveLocalComputation?_mapIds mapping injective names context _).trans (elaborateRecursiveLocalComputation?_iff.mpr original),
    (recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mpr (raw payload argument captured s),
    by simpa only [Resolved.LocalScope.values_mapIds] using manual payload argument captured s k⟩
theorem selected_call_exact_fuel_and_full_resumption
    (mapping : Resolved.LocalId → Resolved.LocalId) (payload argument : Core.Value) (captured : Core.Environment)
    (s : Core.Store) (fuel extra : Nat) :
    let start := Core.State.initial core (Resolved.LocalScope.mapIds mapping (env true payload argument captured)).values s
    (Core.runStateful fuel start=.done payload s ↔ 9≤fuel) ∧
    ∀ cp, Core.runStateful fuel start=.outOfFuel cp → Core.runStateful extra cp=Core.runStateful (fuel+extra) start := by
  simp only [Resolved.LocalScope.values_mapIds]
  exact ⟨(manual payload argument captured s []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
private def unsupported : Syntax.Expr := ⟨span,.literal ⟨span,.string "unsupported"⟩⟩
private def badRights : List Syntax.Expr := [ref "missing",unsupported]
private theorem badCheck (right : Syntax.Expr) (member : right∈badRights) :
    elaborateRecursiveLocalComputation? names context (lazySource right)=none := by
  simp only [badRights,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals simp [lazySource,ref,unsupported,names,elaborateRecursiveLocalComputation?,elaborateLocalExpression?,
    resolveLocalExpression?,LocalNameTable.lookup?,interpretWordLiteral?,numericLiteralValue?]
theorem unchecked_skipped_syntax_retains_raw_success_and_whole_rejection
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (right : Syntax.Expr) (member : right∈badRights) (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping names)
      (Resolved.LocalScope.mapIds mapping (env false payload argument captured)) s (lazySource right) (.bool false) s 4 ∧
    elaborateRecursiveLocalComputation? names context (lazySource right)=none ∧
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping context) (lazySource right)=none :=
  ⟨(recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mpr (.andFalse (.pure (.identifier .head .head))),
    badCheck right member,(elaborateRecursiveLocalComputation?_mapIds mapping injective names context _).trans (badCheck right member)⟩
private theorem unknownAbsent (e : Resolved.Environment) (s t : Core.Store) (v : Core.Value) :
    ¬ RecursiveLocalComputationEvaluates names e s (ref "missing") v t := by
  intro evaluated
  cases evaluated with
  | pure child => cases child with
    | identifier named _ => have found := LocalNameTable.lookup?_iff.mpr named; change none=some _ at found; cases found
theorem raw_success_absence_is_reflected_without_a_typing_premise
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (e : Resolved.Environment) (s t : Core.Store) (v : Core.Value) :
    ¬ RecursiveLocalComputationEvaluates (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping e) s (ref "missing") v t :=
  fun evaluated => unknownAbsent e s t v ((recursiveLocalComputationEvaluates_mapIds_iff mapping injective).mp evaluated)

private def shifted (id : Resolved.LocalId) : Resolved.LocalId :=
  { owner := { id.owner with declarationIndex := id.owner.declarationIndex+6 },binderIndex := id.binderIndex+10 }
private theorem shiftInjective : Function.Injective shifted := by
  intro left right equal
  have modules := congrArg (fun id : Resolved.LocalId => id.owner.moduleId) equal
  have owners := Nat.add_right_cancel (congrArg (fun id : Resolved.LocalId => id.owner.declarationIndex) equal)
  have binders := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex equal)
  cases left with | mk l i => cases l with | mk lm ld =>
    cases right with | mk r j => cases r with | mk rm rd => cases modules; cases owners; cases binders; rfl
theorem a_nonsurjective_map_changes_owners_and_indices_but_not_the_child
    (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) :
    Function.Injective shifted ∧ (¬ ∃ id,shifted id=ident 0) ∧
    (LocalNameTable.mapIds shifted names).lookup? "f"=some ⟨{ owner with declarationIndex := 133 },23⟩ ∧
    RecursiveLocalComputationElaborates (LocalNameTable.mapIds shifted names) (Resolved.LocalScope.mapIds shifted context)
      (lazySource call) core .bool ∧
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds shifted names)
      (Resolved.LocalScope.mapIds shifted (env true payload argument captured)) s (lazySource call) payload s 9 := by
  refine ⟨shiftInjective,?_,rfl,(recursiveLocalComputationElaborates_mapIds_iff shifted shiftInjective).mpr original,
    (recursiveLocalComputationEvaluatesWithCost_mapIds_iff shifted shiftInjective).mpr (raw payload argument captured s)⟩
  rintro ⟨id,equal⟩; have impossible := congrArg Resolved.LocalId.binderIndex equal; change id.binderIndex+10=0 at impossible; omega
private def merge (_ : Resolved.LocalId) := ident 0
private def distinctNames : LocalNameTable := [("a",ident 0),("b",ident 1)]
private def distinctContext : Resolved.Context := [(ident 0,.bool),(ident 1,.word)]
private def word : Core.Value := .word (Core.Word.ofNatModulo 17)
private def distinctValues : Resolved.Environment := [(ident 0,.bool true),(ident 1,word)]
private theorem originalB : RecursiveLocalComputationElaborates distinctNames distinctContext (ref "b") (.var 1) .word :=
  .pure (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head))
private theorem mergedB : RecursiveLocalComputationElaborates (LocalNameTable.mapIds merge distinctNames)
    (Resolved.LocalScope.mapIds merge distinctContext) (ref "b") (.var 0) .bool :=
  .pure (.identifier (.tail (by decide) .head)) (.var .head) (.var .head)
theorem noninjective_first_identity_capture_changes_core_type_and_actual_value (s : Core.Store) :
    (¬ Function.Injective merge) ∧
    elaborateRecursiveLocalComputation? distinctNames distinctContext (ref "b")=some (.var 1,.word) ∧
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds merge distinctNames)
      (Resolved.LocalScope.mapIds merge distinctContext) (ref "b")=some (.var 0,.bool) ∧
    RecursiveLocalComputationEvaluatesWithCost distinctNames distinctValues s (ref "b") word s 1 ∧
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds merge distinctNames)
      (Resolved.LocalScope.mapIds merge distinctValues) s (ref "b") (.bool true) s 1 ∧
    Core.runStateful 1 (.initial (.var 1) distinctValues.values s)=.done word s ∧
    Core.runStateful 1 (.initial (.var 0) (Resolved.LocalScope.mapIds merge distinctValues).values s)=.done (.bool true) s := by
  refine ⟨?_,elaborateRecursiveLocalComputation?_iff.mpr originalB,elaborateRecursiveLocalComputation?_iff.mpr mergedB,
    .pure (.identifier (.tail (by decide) .head) (.tail (by decide) .head)),
    .pure (.identifier (.tail (by decide) .head) .head),rfl,rfl⟩
  intro injective; have impossible := injective (show merge (ident 0)=merge (ident 1) from rfl); exact (by decide : ident 0≠ident 1) impossible
theorem positional_typing_alone_does_not_exclude_noninjective_capture :
    Core.EnvironmentHasTypes (Resolved.LocalScope.mapIds merge distinctValues).values
      (Resolved.LocalScope.mapIds merge distinctContext).values ∧
    ¬ RecursiveLocalComputationHasType (LocalNameTable.mapIds merge distinctNames)
      (Resolved.LocalScope.mapIds merge distinctContext) (ref "b") .word := by
  refine ⟨.cons .bool (.cons .word .nil),?_⟩
  intro typed
  obtain ⟨expression,elaborated⟩ := recursiveLocalComputationHasType_iff_elaborates.mp typed
  have conflict := (elaborateRecursiveLocalComputation?_iff.mpr elaborated).symm.trans (elaborateRecursiveLocalComputation?_iff.mpr mergedB)
  cases conflict
end Tests.FrontendRecursiveIdentityRenamingBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveIdentityRenamingProperties
/-! Independent original syntax, arbitrary static types and unchecked actual
captures precede relabeling. Only the explicit delay fixture preserves stores;
the original mixed tuple has no named binder or fresh-identity allocation. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveIdentityRenaming
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveIdentitySymbols",by decide⟩],by decide⟩⟩,126⟩
private def foreign : Resolved.DeclarationId := { owner with declarationIndex := 903 }
private def span : Syntax.SourceSpan := ⟨⟨.main,"recursive-identity-symbols.sol"⟩,17,300⟩
private inductive Key | f | x | c | w
private def index : Key → Nat | .f => 0 | .x => 1 | .c => 2 | .w => 3
private def ident : Key → Resolved.LocalId
  | .f => ⟨owner,91⟩ | .x => ⟨foreign,700⟩ | .c => ⟨foreign,4⟩ | .w => ⟨owner,33⟩
private def name : Key → String | .f => "f" | .x => "x" | .c => "c" | .w => "w"
private def typeOf (a : Core.Ty) : Key → Core.Ty | .f => .function a a | .x => a | .c => .bool | .w => .word
private def names : LocalNameTable := [("f",ident .f),("x",ident .x),("c",ident .c),("w",ident .w),("f",ident .x)]
private def context (a : Core.Ty) : Resolved.Context :=
  [(ident .f,.function a a),(ident .x,a),(ident .c,.bool),(ident .w,.word),(ident .f,.bool)]
private def ref (key : Key) : Syntax.Expr := ⟨span,.identifier ⟨span,name key⟩⟩
private def calls : Nat → Syntax.Expr
  | 0 => ref .x | n+1 => ⟨span,.call (ref .f) ⟨span,[calls n]⟩⟩
private def callCore : Nat → Core.Expr | 0 => .var 1 | n+1 => .apply (.var 0) (callCore n)
private def complemented : Syntax.Expr := ⟨span,.unary ⟨span,.bitNot⟩ (ref .w)⟩
private def conditional : Syntax.Expr := ⟨span,.conditional (ref .c) span complemented span complemented⟩
private def source (n : Nat) : Syntax.Expr := ⟨span,.tuple ⟨span,[⟨span,.group (calls n)⟩,conditional,ref .c]⟩⟩
private def choiceCore : Core.Expr := .ifE (.var 2) (.unary .wordNot (.var 3)) (.unary .wordNot (.var 3))
private def tailCore : Core.Expr := .pair choiceCore (.var 2)
private def core (n : Nat) : Core.Expr := .pair (callCore n) tailCore
private theorem leaf (a : Core.Ty) (key : Key) :
    RecursiveLocalComputationElaborates names (context a) (ref key) (.var (index key)) (typeOf a key) :=
  .pure (.identifier (id := ident key) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem callElab (a : Core.Ty) (n : Nat) :
    RecursiveLocalComputationElaborates names (context a) (calls n) (callCore n) a := by
  induction n with | zero => exact leaf a .x | succ n ih => exact .application (leaf a .f) ih
private theorem original (a : Core.Ty) (n : Nat) :
    RecursiveLocalComputationElaborates names (context a) (source n) (core n) (.product a (.product .word .bool)) :=
  .many (.group (callElab a n)) (.pair (.conditional (leaf a .c) (.bitNot (leaf a .w)) (.bitNot (leaf a .w))) (leaf a .c))
private def delay : Nat → Nat → Core.Expr | 0,i => .var i | m+1,i => .letE (.var 0) (delay m (i+1))
private structure Actual where
  payload : Core.Value
  word : Core.Word
  choice : Bool
  depth : Nat
  captures : Core.Environment
  hidden : Core.Value
private def actual (a : Core.Ty) (v : Actual) : Key → Core.Value
  | .f => .closure a a (delay v.depth 0) v.captures | .x => v.payload | .c => .bool v.choice | .w => .word v.word
private def env (a : Core.Ty) (v : Actual) : Resolved.Environment :=
  [(ident .f,actual a v .f),(ident .x,v.payload),(ident .c,.bool v.choice),(ident .w,.word v.word),(ident .f,v.hidden)]
private def charge (n m : Nat) := n*(3*m+5)+1
private def result (v : Actual) : Core.Value := .pair v.payload (.pair (.word v.word.bitNot) (.bool v.choice))
private theorem atomCost (a : Core.Ty) (v : Actual) (key : Key) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env a v) s (ref key) (actual a v key) s 1 :=
  .pure (.identifier (id := ident key) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem delayed (m i : Nat) (e : Core.Environment) (v : Core.Value) (s : Core.Store) (k : List Core.Frame)
    (found : e[i]?=some v) : Core.Steps (3*m+1) ⟨.eval (delay m i) e,k,s⟩ ⟨.ret v,k,s⟩ := by
  induction m generalizing i e k with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      cases e with
      | nil => simp at found
      | cons head rest =>
          simpa [delay,Nat.mul_add,Nat.add_assoc] using Core.Steps.cons .enterLet
            (.cons (.var rfl) (.cons .bindLet (ih (i+1) (head::head::rest) k (by simpa using found))))
private theorem callCost (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env a v) s (calls n) v.payload s (charge n v.depth) := by
  induction n with
  | zero => simpa only [calls,actual,charge,Nat.zero_mul,Nat.zero_add] using atomCost a v .x s
  | succ n ih =>
      have count : charge (n+1) v.depth=1+charge n v.depth+(3*v.depth+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact .application (atomCost a v .f s) ih (delayed v.depth 0 (v.payload::v.captures) v.payload s [] rfl)
private theorem callPath (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n v.depth) ⟨.eval (callCore n) (env a v).values,k,s⟩ ⟨.ret v.payload,k,s⟩ := by
  induction n generalizing k with
  | zero => simp only [charge,Nat.zero_mul,Nat.zero_add]; exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge (n+1) v.depth=1+charge n v.depth+(3*v.depth+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _)
        (delayed v.depth 0 (v.payload::v.captures) v.payload s [] rfl)
private theorem branchCost (a : Core.Ty) (v : Actual) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env a v) s conditional (.word v.word.bitNot) s 6 := by
  cases chosen : v.choice
  · exact .ifFalse (by simpa [actual,chosen] using atomCost a v .c s) (.bitNot (atomCost a v .w s))
  · exact .ifTrue (by simpa [actual,chosen] using atomCost a v .c s) (.bitNot (atomCost a v .w s))
private theorem raw (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env a v) s (source n) (result v) s (charge n v.depth+13) := by
  exact .many (.group (callCost a v n s)) (.pair (branchCost a v s) (atomCost a v .c s))
private theorem pairPath {e : Core.Environment} {s t u : Core.Store} {left right : Core.Expr}
    {v w : Core.Value} {lc rc : Nat} (k : List Core.Frame)
    (l : Core.Steps lc ⟨.eval left e,.pairRight right e::k,s⟩ ⟨.ret v,.pairRight right e::k,t⟩)
    (r : Core.Steps rc ⟨.eval right e,.pairApply v::k,t⟩ ⟨.ret w,.pairApply v::k,u⟩) :
    Core.Steps (lc+rc+3) ⟨.eval (.pair left right) e,k,s⟩ ⟨.ret (.pair v w),k,u⟩ := by
  simpa only [Nat.add_assoc] using Core.Steps.cons .enterPair
    (l.trans (.cons .enterPairRight (r.trans (.cons .applyPair .refl))))
private theorem branchPath (a : Core.Ty) (v : Actual) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 6 ⟨.eval choiceCore (env a v).values,k,s⟩ ⟨.ret (.word v.word.bitNot),k,s⟩ := by
  cases chosen : v.choice
  · exact CostStepComposition.ifFalse (.cons (.var (by simp [env,Resolved.LocalScope.values,chosen])) .refl)
      (CostStepComposition.unary (.cons (.var rfl) .refl) rfl)
  · exact CostStepComposition.ifTrue (.cons (.var (by simp [env,Resolved.LocalScope.values,chosen])) .refl)
      (CostStepComposition.unary (.cons (.var rfl) .refl) rfl)
private theorem manual (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n v.depth+13) ⟨.eval (core n) (env a v).values,k,s⟩ ⟨.ret (result v),k,s⟩ :=
  pairPath k (callPath a v n s _) (pairPath _ (branchPath a v s _) (.cons (.var rfl) .refl))

theorem arbitrary_types_and_depth_have_independent_original_meaning (a : Core.Ty) (n : Nat) :
    RecursiveLocalComputationElaborates names (context a) (source n) (core n) (.product a (.product .word .bool)) ∧
    RecursiveLocalComputationHasType names (context a) (source n) (.product a (.product .word .bool)) :=
  ⟨original a n,recursiveLocalComputationHasType_iff_elaborates.mpr ⟨_,original a n⟩⟩
theorem injective_relabeling_keeps_original_code_type_and_whole_check
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) (a : Core.Ty) (n : Nat) :
    RecursiveLocalComputationElaborates (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context a))
      (source n) (core n) (.product a (.product .word .bool)) ∧
    RecursiveLocalComputationHasType (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context a))
      (source n) (.product a (.product .word .bool)) ∧
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context a))
      (source n)=some (core n,.product a (.product .word .bool)) :=
  ⟨(recursiveLocalComputationElaborates_mapIds_iff mapping injective).mpr (original a n),
    (recursiveLocalComputationHasType_mapIds_iff mapping injective).mpr (arbitrary_types_and_depth_have_independent_original_meaning a n).2,
    (elaborateRecursiveLocalComputation?_mapIds mapping injective names (context a) (source n)).trans
      (elaborateRecursiveLocalComputation?_iff.mpr (original a n))⟩
theorem unchecked_actual_captures_keep_value_store_cost_and_literal_path
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) (k : List Core.Frame) :
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (env a v))
      s (source n) (result v) s (charge n v.depth+13) ∧
    RecursiveLocalComputationEvaluates (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (env a v)) s (source n) (result v) s ∧
    Core.Steps (charge n v.depth+13) ⟨.eval (core n) (Resolved.LocalScope.mapIds mapping (env a v)).values,k,s⟩ ⟨.ret (result v),k,s⟩ := by
  exact ⟨(recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mpr (raw a v n s),
    (recursiveLocalComputationEvaluates_mapIds_iff mapping injective).mpr (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,raw a v n s⟩),
    by simpa only [Resolved.LocalScope.values_mapIds] using manual a v n s k⟩
theorem same_actual_value_store_and_cost_are_jointly_unique
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (a : Core.Ty) (v : Actual) (n : Nat) (s t : Core.Store) (value : Core.Value) (cost : Nat)
    (other : RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping names)
      (Resolved.LocalScope.mapIds mapping (env a v)) s (source n) value t cost) :
    value=result v ∧ t=s ∧ cost=charge n v.depth+13 :=
  ((recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mp other).deterministic (raw a v n s)
/-- With literal Core fixed, erasing renamed environment IDs needs no injectivity.
Transport of source compilation above does require it. -/
theorem same_fuel_and_every_genuine_checkpoint_keep_full_resumption
    (mapping : Resolved.LocalId → Resolved.LocalId) (a : Core.Ty) (v : Actual) (n fuel extra : Nat) (s : Core.Store) :
    let start := Core.State.initial (core n) (Resolved.LocalScope.mapIds mapping (env a v)).values s
    (Core.runStateful fuel start=.done (result v) s ↔ charge n v.depth+13≤fuel) ∧
    ∀ cp, Core.runStateful fuel start=.outOfFuel cp →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (core n) (env a v).values s) := by
  simp only [Resolved.LocalScope.values_mapIds]
  exact ⟨(manual a v n s []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
theorem actual_left_child_is_saved_before_the_unchanged_pending_tuple
    (mapping : Resolved.LocalId → Resolved.LocalId) (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) (k : List Core.Frame) :
    let e := (Resolved.LocalScope.mapIds mapping (env a v)).values
    let start : Core.State := ⟨.eval (core n) e,k,s⟩
    let cp : Core.State := ⟨.ret v.payload,.pairRight tailCore e::k,s⟩
    Core.runStateful (charge n v.depth+1) start=.outOfFuel cp ∧
    ∀ extra, Core.runStateful extra cp=Core.runStateful (charge n v.depth+1+extra) start := by
  simp only [Resolved.LocalScope.values_mapIds]
  have path := Core.Steps.cons .enterPair (callPath a v n s (.pairRight tailCore (env a v).values::k))
  have stopped := Core.runStateful_outOfFuel_complete path (show Core.advance _=.next _ from rfl)
  exact ⟨stopped,Core.runStateful_resume stopped⟩
theorem fixed_original_source_does_not_bound_actual_cost
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (a : Core.Ty) (v : Actual) (s : Core.Store) (bound : Nat) :
    ∃ m cost, bound<cost ∧ RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping names)
      (Resolved.LocalScope.mapIds mapping (env a { v with depth := m })) s (source 1) (result v) s cost := by
  refine ⟨bound,charge 1 bound+13,by simp [charge]; omega,?_⟩
  exact (recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mpr (raw a { v with depth := bound } 1 s)
end Tests.FrontendRecursiveIdentityRenaming
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveNegatedComparisonProperties
/-! Original ordered comparisons have separate static, actual and manual paths.
Unchanged stores below belong only to the explicit store-free delayed bodies. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveNegatedComparison
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Comparison",by decide⟩],by decide⟩⟩,60⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"comparison.sol"⟩,0,1024⟩
private inductive Key | f | x | g | y | c
private def index : Key → Nat | .f => 0 | .x => 1 | .g => 2 | .y => 3 | .c => 4
private def name : Key → String | .f => "f" | .x => "x" | .g => "g" | .y => "y" | .c => "c"
private def typeOf : Key → Core.Ty | .f | .g => .function .word .word | .c => .bool | _ => .word
private def inputs : LocalTypeInputs := ⟨[⟨"f",id 0,.function .word .word⟩,⟨"x",id 1,.word⟩,
  ⟨"g",id 2,.function .word .word⟩,⟨"y",id 3,.word⟩,⟨"c",id 4,.bool⟩],by change [id 0,id 1,id 2,id 3,id 4].Nodup; decide⟩
private def ref (key : Key) : Syntax.Expr := ⟨span,.identifier ⟨span,name key⟩⟩
private def calls (side : Bool) : Nat → Syntax.Expr
  | 0 => ref (if side then .y else .x)
  | n+1 => ⟨span,.call (ref (if side then .g else .f)) ⟨span,[calls side n]⟩⟩
private def callCore (side : Bool) : Nat → Core.Expr
  | 0 => .var (if side then 3 else 1)
  | n+1 => .apply (.var (if side then 2 else 0)) (callCore side n)
private def comparison (isLe : Bool) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.binary left ⟨⟨span.source,500,502⟩,if isLe then .lessEqual else .notEqual⟩ right⟩
private def op (isLe : Bool) : Core.BinaryOp := if isLe then .wordGt else .wordEq
private def source (isLe : Bool) (n k : Nat) := comparison isLe (calls false n) (calls true k)
private def core (isLe : Bool) (n k : Nat) : Core.Expr := .unary .boolNot (.binary (op isLe) (callCore false n) (callCore true k))
private theorem oldLeaf (key : Key) :
    LocalComputationElaborates inputs.names inputs.context (ref key) (.var (index key)) (typeOf key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem leafTyped (key : Key) :
    RecursiveLocalComputationHasType inputs.names inputs.context (ref key) (typeOf key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem callsElab (side : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (calls side n) (callCore side n) .word := by
  induction n with
  | zero => cases side <;> exact (oldLeaf _).toRecursiveLocalComputation
  | succ n ih => exact .application (by cases side <;> exact (oldLeaf _).toRecursiveLocalComputation) ih
private theorem callsTyped (side : Bool) (n : Nat) :
    RecursiveLocalComputationHasType inputs.names inputs.context (calls side n) .word := by
  induction n with
  | zero => cases side <;> exact leafTyped _
  | succ n ih => exact .application (by cases side <;> exact leafTyped _) ih
private theorem elaboration (isLe : Bool) (n k : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (source isLe n k) (core isLe n k) .bool := by
  cases isLe; exact .notEqual (callsElab false n) (callsElab true k); exact .lessEqual (callsElab false n) (callsElab true k)
private def delay : Nat → Nat → Core.Expr | 0,i => .var i | m+1,i => .letE (.var 0) (delay m (i+1))
private structure Actual where
  x : Core.Word
  y : Core.Word
  m : Nat
  t : Nat
  leftCapture : Core.Environment
  rightCapture : Core.Environment
private def childWord (a : Actual) (side : Bool) := if side then a.y else a.x
private def depth (a : Actual) (side : Bool) := if side then a.t else a.m
private def capture (a : Actual) (side : Bool) := if side then a.rightCapture else a.leftCapture
private def actual (a : Actual) : Key → Core.Value
  | .f => .closure .word .word (delay a.m 0) a.leftCapture | .x => .word a.x
  | .g => .closure .word .word (delay a.t 0) a.rightCapture | .y => .word a.y | .c => .bool true
private def env (a : Actual) : Resolved.Environment :=
  [(id 0,actual a .f),(id 1,.word a.x),(id 2,actual a .g),(id 3,.word a.y),(id 4,.bool true)]
private def charge (n m : Nat) := n*(3*m+5)+1
private def cost (a : Actual) (n k : Nat) := charge n a.m+charge k a.t+5
private def compared (isLe : Bool) (a : Actual) := if isLe then decide (a.x > a.y) else a.x == a.y
private def result (isLe : Bool) (a : Actual) := Core.Value.bool (!(compared isLe a))
private theorem atomCost (a : Actual) (key : Key) (s : Core.Store) :
    LocalExpressionEvaluatesWithCost inputs.names (env a) s (ref key) (actual a key) s 1 :=
  .identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl))
private theorem delayed (m i : Nat) (value : Core.Value) (rest : Core.Environment) (s : Core.Store) (frames : List Core.Frame)
    (found : (value::rest)[i]? = some value) :
    Core.Steps (3*m+1) ⟨.eval (delay m i) (value::rest),frames,s⟩ ⟨.ret value,frames,s⟩ := by
  induction m generalizing i rest frames with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay,Nat.mul_add,Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (i+1) (value::rest) frames (by simpa using found))))
private theorem callsCost (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (calls side n) (.word (childWord a side)) s (charge n (depth a side)) := by
  induction n with
  | zero =>
      cases side
      · simpa [calls,charge,actual,childWord] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost a .x s)
      · simpa [calls,charge,actual,childWord] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost a .y s)
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact .application (.pure (by cases side <;> exact atomCost a _ s)) ih
        (delayed (depth a side) 0 (.word (childWord a side)) (capture a side) s [] rfl)
private theorem callsPath (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n (depth a side)) ⟨.eval (callCore side n) (env a).values,frames,s⟩ ⟨.ret (.word (childWord a side)),frames,s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge,Nat.zero_mul,Nat.zero_add]; exact .cons (.var (by cases side <;> rfl)) .refl
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var (by cases side <;> rfl)) .refl) (ih _)
        (delayed (depth a side) 0 (.word (childWord a side)) (capture a side) s [] rfl)
private theorem counted (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isLe n k) (result isLe a) s (cost a n k) := by
  cases isLe; exact .notEqual (callsCost a false n s) (callsCost a true k s); exact .lessEqual (callsCost a false n s) (callsCost a true k s)
private theorem manual (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost a n k) ⟨.eval (core isLe n k) (env a).values,frames,s⟩ ⟨.ret (result isLe a),frames,s⟩ := by
  simpa [cost,depth,core,result,Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
    (CostStepComposition.binary (op := op isLe) (result := .bool (compared isLe a))
      (callsPath a false n s _) (callsPath a true k s _) (by cases isLe <;> rfl)) rfl

theorem original_ordered_word_static (isLe : Bool) (n k : Nat) :
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source isLe n k) = some (core isLe n k,.bool) ∧
    RecursiveLocalComputationHasType inputs.names inputs.context (source isLe n k) .bool ∧ Core.HasType inputs.context.values (core isLe n k) .bool := by
  have typed : RecursiveLocalComputationHasType inputs.names inputs.context (source isLe n k) .bool := by
    cases isLe; exact .notEqual (callsTyped false n) (callsTyped true k); exact .lessEqual (callsTyped false n) (callsTyped true k)
  exact ⟨elaborateRecursiveLocalComputation?_iff.mpr (elaboration isLe n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed),(elaboration isLe n k).core_hasType⟩

theorem actual_words_and_exact_paths (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates inputs.names (env a) s (source isLe n k) (result isLe a) s ∧
    Core.Evaluates (env a).values s (core isLe n k) (result isLe a) s ∧
    Core.Steps (cost a n k) ⟨.eval (core isLe n k) (env a).values,frames,s⟩ ⟨.ret (result isLe a),frames,s⟩ := by
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,counted isLe a n k s⟩
  have fromManual := ((elaboration isLe n k).evaluatesWithCost_iff_steps (environment := env a) rfl).mpr (manual isLe a n k s [])
  exact ⟨raw,((elaboration isLe n k).evaluates_iff rfl).mp raw,fromManual.toStepsWithContinuation (elaboration isLe n k) rfl frames⟩

theorem actual_value_store_cost_jointly_unique (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    {value : Core.Value} {finalStore : Core.Store} {steps : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isLe n k) value finalStore steps) :
    value = result isLe a ∧ finalStore = s ∧ steps = charge n a.m+charge k a.t+5 :=
  other.deterministic (counted isLe a n k s)

theorem arbitrary_caller_insertion (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading++suffix = (env a).values) :
    RecursiveLocalComputationFragment ((core isLe n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost a n k) ⟨.eval ((core isLe n k).weakenAt leading.length) (leading++inserted::suffix),frames,s⟩ ⟨.ret (result isLe a),frames,s⟩ := by
  have fragment := (elaboration isLe n k).core_fragment
  have original := Core.steps_from_initial_sound (manual isLe a n k s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost,paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (cost a n k) (.initial (core isLe n k) (leading++suffix) s) (.final (result isLe a) s) := by rw [split]; exact manual isLe a n k s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length,fun frames => same ▸ (paths frames).2⟩

private def between (isLe : Bool) (a : Actual) (k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret (.word a.x),[.binaryRight (op isLe) (callCore true k) (env a).values,.unaryApply .boolNot],s⟩
private def pending (isLe : Bool) (a : Actual) (s : Core.Store) : Core.State :=
  ⟨.ret (.word a.y),[.binaryApply (op isLe) (.word a.x),.unaryApply .boolNot],s⟩
private def negation (isLe : Bool) (a : Actual) (s : Core.Store) : Core.State :=
  ⟨.ret (.bool (compared isLe a)),[.unaryApply .boolNot],s⟩
theorem three_genuine_operand_and_negation_checkpoints (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    Core.runStateful (charge n a.m+2) (.initial (core isLe n k) (env a).values s) = .outOfFuel (between isLe a k s) ∧
    Core.runStateful (charge n a.m+charge k a.t+3) (.initial (core isLe n k) (env a).values s) = .outOfFuel (pending isLe a s) ∧
    Core.runStateful (charge n a.m+charge k a.t+4) (.initial (core isLe n k) (env a).values s) = .outOfFuel (negation isLe a s) := by
  constructor
  · apply Core.runStateful_outOfFuel_complete
    · simpa [Core.State.initial,core,between,depth,childWord,Nat.add_assoc,Nat.add_left_comm] using Core.Steps.cons .enterUnary
        (.cons .enterBinary (callsPath a false n s [.binaryRight (op isLe) (callCore true k) (env a).values,.unaryApply .boolNot]))
    · exact Core.advance_next_iff.mpr .enterBinaryRight
  constructor
  · apply Core.runStateful_outOfFuel_complete
    · simpa [Core.State.initial,core,pending,depth,childWord,Nat.add_assoc,Nat.add_left_comm] using Core.Steps.cons .enterUnary (.cons .enterBinary
        ((callsPath a false n s [.binaryRight (op isLe) (callCore true k) (env a).values,.unaryApply .boolNot]).trans
          (.cons .enterBinaryRight (callsPath a true k s [.binaryApply (op isLe) (.word a.x),.unaryApply .boolNot]))))
    · exact Core.advance_next_iff.mpr (.applyBinary (result := .bool (compared isLe a)) (by cases isLe <;> rfl))
  · apply Core.runStateful_outOfFuel_complete
    · simpa [Core.State.initial,core,negation,depth,Nat.add_assoc,Nat.add_left_comm] using Core.Steps.cons .enterUnary
        (CostStepComposition.binary (op := op isLe) (result := .bool (compared isLe a))
          (callsPath a false n s _) (callsPath a true k s _) (by cases isLe <;> rfl))
    · exact Core.advance_next_iff.mpr (.applyUnary (result := result isLe a) rfl)

theorem all_fuels_residual_and_full_resume (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core isLe n k) (env a).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core isLe n k) (env a).values s) = .done (result isLe a) s ↔ cost a n k ≤ fuel) ∧
    spent < cost a n k ∧ Core.Steps (cost a n k-spent) cp (.final (result isLe a) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent+additional) (.initial (core isLe n k) (env a).values s) := by
  have path := manual isLe a n k s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff,residual.1,residual.2,Core.runStateful_resume exhausted additional⟩

theorem fixed_source_actual_body_cost_is_unbounded (isLe : Bool) (limit : Nat) (x y : Core.Word) (leftCapture rightCapture : Core.Environment) (s : Core.Store) :
    ∃ a : Actual, RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isLe 1 1) (result isLe a) s (cost a 1 1) ∧ limit < cost a 1 1 := by
  let a : Actual := ⟨x,y,limit,0,leftCapture,rightCapture⟩
  exact ⟨a,counted isLe a 1 1 s,by simp [cost,charge,a]; omega⟩

private def guarded (skipped : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.conditional (ref .c) ⟨span.source,100,101⟩ (ref .x) ⟨span.source,400,401⟩ skipped⟩
theorem pure_overlap_with_skipped_original_operand (isLe : Bool) (a : Actual) (s : Core.Store) (skipped : Syntax.Expr) :
    LocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isLe (guarded skipped) (ref .y)) (result isLe a) s 10 ∧
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isLe (guarded skipped) (ref .y)) (result isLe a) s 10 := by
  have old : LocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isLe (guarded skipped) (ref .y)) (result isLe a) s 10 := by
    cases isLe
    · exact .pure (.notEqual (.ifTrue (atomCost a .c s) (atomCost a .x s)) (atomCost a .y s))
    · exact .pure (.lessEqual (.ifTrue (atomCost a .c s) (atomCost a .x s)) (atomCost a .y s))
  have new : RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isLe (guarded skipped) (ref .y)) (result isLe a) s 10 := by
    cases isLe
    · exact .notEqual (.ifTrue (.pure (atomCost a .c s)) (.pure (atomCost a .x s))) (.pure (atomCost a .y s))
    · exact .lessEqual (.ifTrue (.pure (atomCost a .c s)) (.pure (atomCost a .x s))) (.pure (atomCost a .y s))
  have same := new.deterministic old.toRecursiveLocalComputation
  exact ⟨old,same.2.2 ▸ new⟩

private def body (isLe : Bool) (n k : Nat) : Syntax.Block := ⟨span,
  [⟨span,.letDecl ⟨span,"r"⟩ none (some (source isLe n k))⟩,⟨span,.returnStmt (some ⟨span,.identifier ⟨span,"r"⟩⟩)⟩]⟩
private theorem bodyElab (isLe : Bool) (n k : Nat) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isLe n k) (.letE (core isLe n k) (.var 0)) .bool :=
  .inferred (elaboration isLe n k)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCost (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isLe n k) (result isLe a) s (cost a n k+3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost,body,Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted isLe a n k s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost a n k+3) ⟨.eval (.letE (core isLe n k) (.var 0)) (env a).values,frames,s⟩ ⟨.ret (result isLe a),frames,s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual isLe a n k s (.letBody (.var 0) (env a).values::frames)) (.cons (.var rfl) .refl)
private theorem oldElab (isLe : Bool) :
    LocalComputationElaborates inputs.names inputs.context (source isLe 0 0) (core isLe 0 0) .bool := by
  cases oldLeaf .x with
  | pure lr ll lt =>
      cases oldLeaf .y with
      | pure rr rl rt =>
          cases isLe
          · exact .pure (.notEqual lr rr) (.unary (.binary ll rl)) (.unary (.binary lt rt))
          · exact .pure (.lessEqual lr rr) (.unary (.binary ll rl)) (.unary (.binary lt rt))
      | application child => cases child
  | application child => cases child
theorem old_original_body_embeddings (isLe : Bool) (a : Actual) (s : Core.Store) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isLe 0 0) (.letE (core isLe 0 0) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isLe 0 0) (result isLe a) s 10 := by
  have oldStatic : LocalComputationReturnTreeElaborates [] owner inputs (body isLe 0 0) (.letE (core isLe 0 0) (.var 0)) .bool :=
    .inferred (by change ¬"r" ∈ ["f","x","g","y","c"]; decide) (oldElab isLe)
      (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
  have child : LocalComputationEvaluatesWithCost inputs.names (env a) s (source isLe 0 0) (result isLe a) s 7 := by
    cases isLe; exact .pure (.notEqual (atomCost a .x s) (atomCost a .y s)); exact .pure (.lessEqual (atomCost a .x s) (atomCost a .y s))
  have oldCost : LocalComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isLe 0 0) (result isLe a) s 10 :=
    .inferred child (.expression (.pure (.identifier .head .head)))
  exact ⟨oldStatic.toRecursiveComputationReturnTree,oldCost.toRecursiveComputationReturnTree⟩

theorem shared_body_original_source_and_actual_cost (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner inputs (body isLe n k) = some (.letE (core isLe n k) (.var 0),.bool) ∧
    Core.HasType inputs.context.values (.letE (core isLe n k) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isLe n k) (result isLe a) s (cost a n k+3) ∧
    Core.Steps (cost a n k+3) ⟨.eval (.letE (core isLe n k) (.var 0)) (env a).values,frames,s⟩ ⟨.ret (result isLe a),frames,s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab isLe n k) (environment := env a) rfl).mpr (bodyManual isLe a n k s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab isLe n k),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab isLe n k),costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCost isLe a n k s) (bodyElab isLe n k) rfl frames⟩

end Tests.FrontendRecursiveNegatedComparison
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveOrderedComparisonProperties
/-! Original two-binding comparisons have separate static, actual and manual paths.
Unchanged stores below belong only to the explicit store-free delayed bodies. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveOrderedComparison
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Comparison",by decide⟩],by decide⟩⟩,60⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"ordering.sol"⟩,0,1024⟩
private inductive Key | f | x | g | y | c
private def index : Key → Nat | .f => 0 | .x => 1 | .g => 2 | .y => 3 | .c => 4
private def name : Key → String | .f => "f" | .x => "x" | .g => "g" | .y => "y" | .c => "c"
private def typeOf : Key → Core.Ty | .f | .g => .function .word .word | .c => .bool | _ => .word
private def inputs : LocalTypeInputs := ⟨[⟨"f",id 0,.function .word .word⟩,⟨"x",id 1,.word⟩,
  ⟨"g",id 2,.function .word .word⟩,⟨"y",id 3,.word⟩,⟨"c",id 4,.bool⟩],by change [id 0,id 1,id 2,id 3,id 4].Nodup; decide⟩
private def ref (key : Key) : Syntax.Expr := ⟨span,.identifier ⟨span,name key⟩⟩
private def calls (side : Bool) : Nat → Syntax.Expr
  | 0 => ref (if side then .y else .x)
  | n+1 => ⟨span,.call (ref (if side then .g else .f)) ⟨span,[calls side n]⟩⟩
private def callCore (side : Bool) : Nat → Core.Expr
  | 0 => .var (if side then 3 else 1)
  | n+1 => .apply (.var (if side then 2 else 0)) (callCore side n)
private def comparison (isGe : Bool) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.binary left ⟨⟨span.source,500,502⟩,if isGe then .greaterEqual else .less⟩ right⟩
private def source (isGe : Bool) (n k : Nat) := comparison isGe (calls false n) (calls true k)
private def comparisonCore : Core.Expr := .binary .wordGt (.var 0) (.var 1)
private def tailCore (k : Nat) : Core.Expr := .letE ((callCore true k).weakenAt 0) comparisonCore
private def ordered (n k : Nat) : Core.Expr := .letE (callCore false n) (tailCore k)
private def core (isGe : Bool) (n k : Nat) : Core.Expr := if isGe then .unary .boolNot (ordered n k) else ordered n k
private theorem oldLeaf (key : Key) :
    LocalComputationElaborates inputs.names inputs.context (ref key) (.var (index key)) (typeOf key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem leafTyped (key : Key) :
    RecursiveLocalComputationHasType inputs.names inputs.context (ref key) (typeOf key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem callsElab (side : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (calls side n) (callCore side n) .word := by
  induction n with
  | zero => cases side <;> exact (oldLeaf _).toRecursiveLocalComputation
  | succ n ih => exact .application (by cases side <;> exact (oldLeaf _).toRecursiveLocalComputation) ih
private theorem callsTyped (side : Bool) (n : Nat) :
    RecursiveLocalComputationHasType inputs.names inputs.context (calls side n) .word := by
  induction n with
  | zero => cases side <;> exact leafTyped _
  | succ n ih => exact .application (by cases side <;> exact leafTyped _) ih
private theorem elaboration (isGe : Bool) (n k : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (source isGe n k) (core isGe n k) .bool := by
  cases isGe; exact .less (callsElab false n) (callsElab true k); exact .greaterEqual (callsElab false n) (callsElab true k)
private def delay : Nat → Nat → Core.Expr | 0,i => .var i | m+1,i => .letE (.var 0) (delay m (i+1))
private structure Actual where
  x : Core.Word
  y : Core.Word
  m : Nat
  t : Nat
  leftCapture : Core.Environment
  rightCapture : Core.Environment
private def childWord (a : Actual) (side : Bool) := if side then a.y else a.x
private def depth (a : Actual) (side : Bool) := if side then a.t else a.m
private def capture (a : Actual) (side : Bool) := if side then a.rightCapture else a.leftCapture
private def actual (a : Actual) : Key → Core.Value
  | .f => .closure .word .word (delay a.m 0) a.leftCapture | .x => .word a.x
  | .g => .closure .word .word (delay a.t 0) a.rightCapture | .y => .word a.y | .c => .bool true
private def env (a : Actual) : Resolved.Environment :=
  [(id 0,actual a .f),(id 1,.word a.x),(id 2,actual a .g),(id 3,.word a.y),(id 4,.bool true)]
private def charge (n m : Nat) := n*(3*m+5)+1
private def cost (isGe : Bool) (a : Actual) (n k : Nat) := charge n a.m+charge k a.t+(if isGe then 11 else 9)
private def compared (a : Actual) := decide (a.x < a.y)
private def result (isGe : Bool) (a : Actual) := Core.Value.bool (if isGe then !(compared a) else compared a)
private theorem atomCost (a : Actual) (key : Key) (s : Core.Store) :
    LocalExpressionEvaluatesWithCost inputs.names (env a) s (ref key) (actual a key) s 1 :=
  .identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl))
private theorem delayed (m i : Nat) (value : Core.Value) (rest : Core.Environment) (s : Core.Store) (frames : List Core.Frame)
    (found : (value::rest)[i]? = some value) :
    Core.Steps (3*m+1) ⟨.eval (delay m i) (value::rest),frames,s⟩ ⟨.ret value,frames,s⟩ := by
  induction m generalizing i rest frames with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay,Nat.mul_add,Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (i+1) (value::rest) frames (by simpa using found))))
private theorem callsCost (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (calls side n) (.word (childWord a side)) s (charge n (depth a side)) := by
  induction n with
  | zero =>
      cases side
      · simpa [calls,charge,actual,childWord] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost a .x s)
      · simpa [calls,charge,actual,childWord] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost a .y s)
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact .application (.pure (by cases side <;> exact atomCost a _ s)) ih
        (delayed (depth a side) 0 (.word (childWord a side)) (capture a side) s [] rfl)
private theorem callsPath (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n (depth a side)) ⟨.eval (callCore side n) (env a).values,frames,s⟩ ⟨.ret (.word (childWord a side)),frames,s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge,Nat.zero_mul,Nat.zero_add]; exact .cons (.var (by cases side <;> rfl)) .refl
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var (by cases side <;> rfl)) .refl) (ih _)
        (delayed (depth a side) 0 (.word (childWord a side)) (capture a side) s [] rfl)
private theorem shiftedPath (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) (bound : Core.Value) (frames : List Core.Frame) :
    Core.Steps (charge n (depth a side)) ⟨.eval ((callCore side n).weakenAt 0) (bound::(env a).values),frames,s⟩ ⟨.ret (.word (childWord a side)),frames,s⟩ := by
  induction n generalizing frames with
  | zero => cases side <;> simp only [charge,Nat.zero_mul,Nat.zero_add,callCore,Core.Expr.weakenAt] <;> exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]
      have body := delayed (depth a side) 0 (.word (childWord a side)) (capture a side) s [] rfl
      cases side <;> simp only [callCore,Core.Expr.weakenAt] <;>
        exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _) body
private theorem counted (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isGe n k) (result isGe a) s (cost isGe a n k) := by
  cases isGe; exact .less (callsCost a false n s) (callsCost a true k s); exact .greaterEqual (callsCost a false n s) (callsCost a true k s)
private theorem orderedManual (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n a.m+charge k a.t+9) ⟨.eval (ordered n k) (env a).values,frames,s⟩ ⟨.ret (.bool (compared a)),frames,s⟩ := by
  simpa [ordered,tailCore,comparisonCore,depth,childWord,Nat.add_assoc] using
    CostStepComposition.letE (callsPath a false n s _)
      (CostStepComposition.letE (shiftedPath a true k s (.word a.x) _)
        (CostStepComposition.binary (op := .wordGt) (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) rfl))
private theorem manual (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost isGe a n k) ⟨.eval (core isGe n k) (env a).values,frames,s⟩ ⟨.ret (result isGe a),frames,s⟩ := by
  cases isGe
  · exact orderedManual a n k s frames
  · simpa [cost,core,result,Nat.add_assoc] using CostStepComposition.unary (op := .boolNot) (orderedManual a n k s _) rfl

theorem original_ordered_word_static (isGe : Bool) (n k : Nat) :
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source isGe n k) = some (core isGe n k,.bool) ∧
    RecursiveLocalComputationHasType inputs.names inputs.context (source isGe n k) .bool ∧ Core.HasType inputs.context.values (core isGe n k) .bool := by
  have typed : RecursiveLocalComputationHasType inputs.names inputs.context (source isGe n k) .bool := by
    cases isGe; exact .less (callsTyped false n) (callsTyped true k); exact .greaterEqual (callsTyped false n) (callsTyped true k)
  exact ⟨elaborateRecursiveLocalComputation?_iff.mpr (elaboration isGe n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed),(elaboration isGe n k).core_hasType⟩

theorem actual_words_and_exact_paths (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates inputs.names (env a) s (source isGe n k) (result isGe a) s ∧
    Core.Evaluates (env a).values s (core isGe n k) (result isGe a) s ∧
    Core.Steps (cost isGe a n k) ⟨.eval (core isGe n k) (env a).values,frames,s⟩ ⟨.ret (result isGe a),frames,s⟩ := by
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,counted isGe a n k s⟩
  have fromManual := ((elaboration isGe n k).evaluatesWithCost_iff_steps (environment := env a) rfl).mpr (manual isGe a n k s [])
  exact ⟨raw,((elaboration isGe n k).evaluates_iff rfl).mp raw,fromManual.toStepsWithContinuation (elaboration isGe n k) rfl frames⟩

theorem actual_value_store_cost_jointly_unique (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    {value : Core.Value} {finalStore : Core.Store} {steps : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isGe n k) value finalStore steps) :
    value = result isGe a ∧ finalStore = s ∧ steps = charge n a.m+charge k a.t+(if isGe then 11 else 9) :=
  other.deterministic (counted isGe a n k s)

theorem arbitrary_caller_insertion (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading++suffix = (env a).values) :
    RecursiveLocalComputationFragment ((core isGe n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost isGe a n k) ⟨.eval ((core isGe n k).weakenAt leading.length) (leading++inserted::suffix),frames,s⟩ ⟨.ret (result isGe a),frames,s⟩ := by
  have literal : RecursiveLocalComputationFragment (ordered n k) :=
    .letE (callsElab false n).core_fragment
      (.letE ((callsElab true k).core_fragment.weakenAt 0) (.pure (.binary .var .var)))
  have fragment : RecursiveLocalComputationFragment (core isGe n k) := by
    cases isGe; exact literal; exact .unary literal
  have original := Core.steps_from_initial_sound (manual isGe a n k s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost,paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (cost isGe a n k) (.initial (core isGe n k) (leading++suffix) s) (.final (result isGe a) s) := by rw [split]; exact manual isGe a n k s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length,fun frames => same ▸ (paths frames).2⟩
private def outer (isGe : Bool) : List Core.Frame := if isGe then [.unaryApply .boolNot] else []
private def first (isGe : Bool) (a : Actual) (k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret (.word a.x),.letBody (tailCore k) (env a).values::outer isGe,s⟩
private def second (isGe : Bool) (a : Actual) (s : Core.Store) : Core.State :=
  ⟨.ret (.word a.y),.letBody comparisonCore (.word a.x::(env a).values)::outer isGe,s⟩
private def pending (isGe : Bool) (a : Actual) (s : Core.Store) : Core.State :=
  ⟨.ret (.word a.x),.binaryApply .wordGt (.word a.y)::outer isGe,s⟩
private theorem beginPath (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) {steps : Nat} {cp : Core.State}
    (path : Core.Steps steps ⟨.eval (ordered n k) (env a).values,outer isGe,s⟩ cp) :
    Core.Steps (steps+(if isGe then 1 else 0)) (.initial (core isGe n k) (env a).values s) cp := by
  cases isGe
  · simpa [core,outer,Core.State.initial] using path
  · simpa [core,outer,Core.State.initial,Nat.add_comm] using Core.Steps.cons .enterUnary path
theorem generated_bindings_and_comparison_checkpoints (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    Core.runStateful (charge n a.m+1+(if isGe then 1 else 0)) (.initial (core isGe n k) (env a).values s) = .outOfFuel (first isGe a k s) ∧
    Core.runStateful (charge n a.m+charge k a.t+3+(if isGe then 1 else 0)) (.initial (core isGe n k) (env a).values s) = .outOfFuel (second isGe a s) ∧
    Core.runStateful (charge n a.m+charge k a.t+8+(if isGe then 1 else 0)) (.initial (core isGe n k) (env a).values s) = .outOfFuel (pending isGe a s) ∧
    Core.runStateful (charge n a.m+charge k a.t+10) (.initial (core true n k) (env a).values s) =
      .outOfFuel ⟨.ret (.bool (compared a)),[.unaryApply .boolNot],s⟩ := by
  have p1 : Core.Steps (charge n a.m+1) ⟨.eval (ordered n k) (env a).values,outer isGe,s⟩ (first isGe a k s) := by
    simpa [ordered,first,depth,childWord,Nat.add_comm] using Core.Steps.cons .enterLet (callsPath a false n s _)
  have p2 : Core.Steps (charge n a.m+charge k a.t+3) ⟨.eval (ordered n k) (env a).values,outer isGe,s⟩ (second isGe a s) := by
    have count : charge n a.m+charge k a.t+3 = (charge n a.m+1)+((charge k a.t+1)+1) := by omega
    rw [count]
    exact p1.trans (.cons .bindLet (.cons .enterLet (shiftedPath a true k s (.word a.x) _)))
  have p3 : Core.Steps (charge n a.m+charge k a.t+8) ⟨.eval (ordered n k) (env a).values,outer isGe,s⟩ (pending isGe a s) := by
    simpa [second,pending,comparisonCore,Nat.add_assoc] using
      p2.trans (.cons .bindLet (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight (.cons (.var rfl) .refl)))))
  refine ⟨Core.runStateful_outOfFuel_complete (beginPath isGe a n k s p1) (Core.advance_next_iff.mpr .bindLet),
    Core.runStateful_outOfFuel_complete (beginPath isGe a n k s p2) (Core.advance_next_iff.mpr .bindLet),
    Core.runStateful_outOfFuel_complete (beginPath isGe a n k s p3) (Core.advance_next_iff.mpr (.applyBinary rfl)),?_⟩
  apply Core.runStateful_outOfFuel_complete
  · simpa [core,Core.State.initial,Nat.add_assoc,Nat.add_left_comm] using Core.Steps.cons .enterUnary (orderedManual a n k s [.unaryApply .boolNot])
  · exact Core.advance_next_iff.mpr (.applyUnary rfl)

theorem all_fuels_residual_and_full_resume (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core isGe n k) (env a).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core isGe n k) (env a).values s) = .done (result isGe a) s ↔ cost isGe a n k ≤ fuel) ∧
    spent < cost isGe a n k ∧ Core.Steps (cost isGe a n k-spent) cp (.final (result isGe a) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent+additional) (.initial (core isGe n k) (env a).values s) := by
  have path := manual isGe a n k s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff,residual.1,residual.2,Core.runStateful_resume exhausted additional⟩

theorem fixed_source_actual_body_cost_is_unbounded (isGe : Bool) (limit : Nat) (x y : Core.Word) (leftCapture rightCapture : Core.Environment) (s : Core.Store) :
    ∃ a : Actual, RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isGe 1 1) (result isGe a) s (cost isGe a 1 1) ∧ limit < cost isGe a 1 1 := by
  let a : Actual := ⟨x,y,limit,0,leftCapture,rightCapture⟩
  exact ⟨a,counted isGe a 1 1 s,by cases isGe <;> simp [cost,charge,a] <;> omega⟩
private def guarded (skipped : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.conditional (ref .c) ⟨span.source,100,101⟩ (ref .x) ⟨span.source,400,401⟩ skipped⟩
theorem pure_overlap_with_skipped_original_operand (isGe : Bool) (a : Actual) (s : Core.Store) (skipped : Syntax.Expr) :
    LocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isGe (guarded skipped) (ref .y)) (result isGe a) s (if isGe then 16 else 14) ∧
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isGe (guarded skipped) (ref .y)) (result isGe a) s (if isGe then 16 else 14) := by
  have old : LocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isGe (guarded skipped) (ref .y)) (result isGe a) s (if isGe then 16 else 14) := by
    cases isGe
    · exact .pure (.less (.ifTrue (atomCost a .c s) (atomCost a .x s)) (atomCost a .y s))
    · exact .pure (.greaterEqual (.ifTrue (atomCost a .c s) (atomCost a .x s)) (atomCost a .y s))
  have new : RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isGe (guarded skipped) (ref .y)) (result isGe a) s (if isGe then 16 else 14) := by
    cases isGe
    · exact .less (.ifTrue (.pure (atomCost a .c s)) (.pure (atomCost a .x s))) (.pure (atomCost a .y s))
    · exact .greaterEqual (.ifTrue (.pure (atomCost a .c s)) (.pure (atomCost a .x s))) (.pure (atomCost a .y s))
  have same := new.deterministic old.toRecursiveLocalComputation
  exact ⟨old,same.2.2 ▸ new⟩
private def body (isGe : Bool) (n k : Nat) : Syntax.Block := ⟨span,
  [⟨span,.letDecl ⟨span,"r"⟩ none (some (source isGe n k))⟩,⟨span,.returnStmt (some ⟨span,.identifier ⟨span,"r"⟩⟩)⟩]⟩
private theorem bodyElab (isGe : Bool) (n k : Nat) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isGe n k) (.letE (core isGe n k) (.var 0)) .bool :=
  .inferred (elaboration isGe n k)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCost (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isGe n k) (result isGe a) s (cost isGe a n k+3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost,body,Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted isGe a n k s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost isGe a n k+3) ⟨.eval (.letE (core isGe n k) (.var 0)) (env a).values,frames,s⟩ ⟨.ret (result isGe a),frames,s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual isGe a n k s (.letBody (.var 0) (env a).values::frames)) (.cons (.var rfl) .refl)
private theorem oldElab (isGe : Bool) :
    LocalComputationElaborates inputs.names inputs.context (source isGe 0 0) (core isGe 0 0) .bool := by
  cases oldLeaf .x with
  | pure lr ll lt =>
      cases oldLeaf .y with
      | pure rr rl rt =>
          cases isGe
          · exact .pure (.less lr rr) (.wordLt ll rl) (.wordLt lt rt)
          · exact .pure (.greaterEqual lr rr) (.unary (.wordLt ll rl)) (.unary (.wordLt lt rt))
      | application child => cases child
  | application child => cases child
theorem old_original_body_embeddings (isGe : Bool) (a : Actual) (s : Core.Store) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isGe 0 0) (.letE (core isGe 0 0) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isGe 0 0) (result isGe a) s (if isGe then 16 else 14) := by
  have oldStatic : LocalComputationReturnTreeElaborates [] owner inputs (body isGe 0 0) (.letE (core isGe 0 0) (.var 0)) .bool :=
    .inferred (by change ¬"r" ∈ ["f","x","g","y","c"]; decide) (oldElab isGe)
      (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
  have child : LocalComputationEvaluatesWithCost inputs.names (env a) s (source isGe 0 0) (result isGe a) s (if isGe then 13 else 11) := by
    cases isGe; exact .pure (.less (atomCost a .x s) (atomCost a .y s)); exact .pure (.greaterEqual (atomCost a .x s) (atomCost a .y s))
  have oldCost : LocalComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isGe 0 0) (result isGe a) s (if isGe then 16 else 14) := by
    cases isGe <;> exact .inferred child (.expression (.pure (.identifier .head .head)))
  exact ⟨oldStatic.toRecursiveComputationReturnTree,oldCost.toRecursiveComputationReturnTree⟩

theorem shared_body_original_source_and_actual_cost (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner inputs (body isGe n k) = some (.letE (core isGe n k) (.var 0),.bool) ∧
    Core.HasType inputs.context.values (.letE (core isGe n k) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isGe n k) (result isGe a) s (cost isGe a n k+3) ∧
    Core.Steps (cost isGe a n k+3) ⟨.eval (.letE (core isGe n k) (.var 0)) (env a).values,frames,s⟩ ⟨.ret (result isGe a),frames,s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab isGe n k) (environment := env a) rfl).mpr (bodyManual isGe a n k s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab isGe n k),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab isGe n k),costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCost isGe a n k s) (bodyElab isGe n k) rfl frames⟩

end Tests.FrontendRecursiveOrderedComparison
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveTupleProperties
/-! Flat tuples of arbitrary length have literal right-associated paths, without
a terminal Unit. Store invariance below is only for the explicit delayed bodies;
arbitrary static component tags do not constrain the actual opaque payloads. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveTuple
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Tuple",by decide⟩],by decide⟩⟩,64⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"tuple.sol"⟩,0,1024⟩
private def tupleSpan : Syntax.SourceSpan := ⟨span.source,1,1023⟩
private inductive Key | f | x | g | y | c
private def index : Key → Nat | .f => 0 | .x => 1 | .g => 2 | .y => 3 | .c => 4
private def name : Key → String | .f => "f" | .x => "x" | .g => "g" | .y => "y" | .c => "c"
private def typeOf (A B : Core.Ty) : Key → Core.Ty
  | .f => .function A A | .x => A | .g => .function B B | .y => B | .c => .bool
private def inputs (A B : Core.Ty) : LocalTypeInputs := ⟨[⟨"f",id 0,.function A A⟩,⟨"x",id 1,A⟩,
  ⟨"g",id 2,.function B B⟩,⟨"y",id 3,B⟩,⟨"c",id 4,.bool⟩],by change [id 0,id 1,id 2,id 3,id 4].Nodup; decide⟩
private def ref (key : Key) : Syntax.Expr := ⟨span,.identifier ⟨span,name key⟩⟩
private def calls (side : Bool) : Nat → Syntax.Expr
  | 0 => ref (if side then .y else .x)
  | n+1 => ⟨span,.call (ref (if side then .g else .f)) ⟨span,[calls side n]⟩⟩
private def callCore (side : Bool) : Nat → Core.Expr
  | 0 => .var (if side then 3 else 1)
  | n+1 => .apply (.var (if side then 2 else 0)) (callCore side n)
private def tailElements (left right : Syntax.Expr) : Nat → List Syntax.Expr
  | 0 => [right] | r+1 => left :: tailElements left right r
private def elements (left right : Syntax.Expr) (r : Nat) := left :: tailElements left right r
private def tuple (left right : Syntax.Expr) (r : Nat) : Syntax.Expr := ⟨span,.tuple ⟨tupleSpan,elements left right r⟩⟩
private def source (r n k : Nat) := tuple (calls false n) (calls true k) r
private def chain {α : Type} (pair : α → α → α) (left right : α) : Nat → α
  | 0 => pair left right | r+1 => pair left (chain pair left right r)
private def core (r n k : Nat) := chain Core.Expr.pair (callCore false n) (callCore true k) r
private def type (A B : Core.Ty) (r : Nat) := chain Core.Ty.product A B r
private theorem oldLeaf (A B : Core.Ty) (key : Key) :
    LocalComputationElaborates (inputs A B).names (inputs A B).context (ref key) (.var (index key)) (typeOf A B key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem leafTyped (A B : Core.Ty) (key : Key) :
    RecursiveLocalComputationHasType (inputs A B).names (inputs A B).context (ref key) (typeOf A B key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem callsElab (A B : Core.Ty) (side : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates (inputs A B).names (inputs A B).context (calls side n) (callCore side n) (if side then B else A) := by
  induction n with
  | zero => cases side <;> exact (oldLeaf A B _).toRecursiveLocalComputation
  | succ n ih => exact .application (by cases side <;> exact (oldLeaf A B _).toRecursiveLocalComputation) ih
private theorem callsTyped (A B : Core.Ty) (side : Bool) (n : Nat) :
    RecursiveLocalComputationHasType (inputs A B).names (inputs A B).context (calls side n) (if side then B else A) := by
  induction n with
  | zero => cases side <;> exact leafTyped A B _
  | succ n ih => exact .application (by cases side <;> exact leafTyped A B _) ih
private theorem elaboration (A B : Core.Ty) (r n k : Nat) :
    RecursiveLocalComputationElaborates (inputs A B).names (inputs A B).context (source r n k) (core r n k) (type A B r) := by
  induction r with
  | zero => exact .pair (callsElab A B false n) (callsElab A B true k)
  | succ r ih => cases r <;> exact .many (callsElab A B false n) ih
private def delay : Nat → Nat → Core.Expr | 0,i => .var i | m+1,i => .letE (.var 0) (delay m (i+1))
private structure Actual where
  x : Core.Value
  y : Core.Value
  m : Nat
  t : Nat
  leftCapture : Core.Environment
  rightCapture : Core.Environment
private def payload (a : Actual) (side : Bool) := if side then a.y else a.x
private def depth (a : Actual) (side : Bool) := if side then a.t else a.m
private def capture (a : Actual) (side : Bool) := if side then a.rightCapture else a.leftCapture
private def actual (A B : Core.Ty) (a : Actual) : Key → Core.Value
  | .f => .closure A A (delay a.m 0) a.leftCapture | .x => a.x
  | .g => .closure B B (delay a.t 0) a.rightCapture | .y => a.y | .c => .bool true
private def env (A B : Core.Ty) (a : Actual) : Resolved.Environment :=
  [(id 0,actual A B a .f),(id 1,a.x),(id 2,actual A B a .g),(id 3,a.y),(id 4,.bool true)]
private def charge (n m : Nat) := n*(3*m+5)+1
private def cost (a : Actual) (r n k : Nat) := (r+1)*(charge n a.m+3)+charge k a.t
private def result (a : Actual) (r : Nat) := chain Core.Value.pair a.x a.y r
private theorem atomCost (A B : Core.Ty) (a : Actual) (key : Key) (s : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs A B).names (env A B a) s (ref key) (actual A B a key) s 1 :=
  .identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl))
private theorem delayed (m i : Nat) (value : Core.Value) (rest : Core.Environment) (s : Core.Store) (frames : List Core.Frame)
    (found : (value::rest)[i]? = some value) :
    Core.Steps (3*m+1) ⟨.eval (delay m i) (value::rest),frames,s⟩ ⟨.ret value,frames,s⟩ := by
  induction m generalizing i rest frames with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay,Nat.mul_add,Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (i+1) (value::rest) frames (by simpa using found))))
private theorem callsCost (A B : Core.Ty) (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (calls side n) (payload a side) s (charge n (depth a side)) := by
  induction n with
  | zero =>
      cases side
      · simpa [calls,payload,charge,actual] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost A B a .x s)
      · simpa [calls,payload,charge,actual] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost A B a .y s)
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact .application (parameterType := if side then B else A) (resultType := if side then B else A)
        (.pure (by cases side; exact atomCost A B a .f s; exact atomCost A B a .g s)) ih
        (delayed (depth a side) 0 (payload a side) (capture a side) s [] rfl)
private theorem callsPath (A B : Core.Ty) (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n (depth a side)) ⟨.eval (callCore side n) (env A B a).values,frames,s⟩ ⟨.ret (payload a side),frames,s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge,Nat.zero_mul,Nat.zero_add]; exact .cons (.var (by cases side <;> rfl)) .refl
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (parameterType := if side then B else A) (resultType := if side then B else A)
        (.cons (.var (by cases side <;> rfl)) .refl) (ih _)
        (delayed (depth a side) 0 (payload a side) (capture a side) s [] rfl)
private theorem counted (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (source r n k) (result a r) s (cost a r n k) := by
  induction r with
  | zero => simpa [source,tuple,elements,tailElements,result,chain,payload,cost,depth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      RecursiveLocalComputationEvaluatesWithCost.pair (callsCost A B a false n s) (callsCost A B a true k s)
  | succ r ih =>
      have count : cost a (r+1) n k = charge n a.m+cost a r n k+3 := by simp [cost,Nat.add_mul]; omega
      rw [count]; cases r <;> exact .many (callsCost A B a false n s) ih
private theorem pairPath {environment : Core.Environment} {s t u : Core.Store} {left right : Core.Expr}
    {x y : Core.Value} {frames : List Core.Frame} {l r : Nat}
    (lp : Core.Steps l ⟨.eval left environment,.pairRight right environment::frames,s⟩ ⟨.ret x,.pairRight right environment::frames,t⟩)
    (rp : Core.Steps r ⟨.eval right environment,.pairApply x::frames,t⟩ ⟨.ret y,.pairApply x::frames,u⟩) :
    Core.Steps (l+r+3) ⟨.eval (.pair left right) environment,frames,s⟩ ⟨.ret (.pair x y),frames,u⟩ := by
  simpa only [Nat.add_assoc] using Core.Steps.cons .enterPair (lp.trans (.cons .enterPairRight (rp.trans (.cons .applyPair .refl))))
private theorem manual (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost a r n k) ⟨.eval (core r n k) (env A B a).values,frames,s⟩ ⟨.ret (result a r),frames,s⟩ := by
  induction r generalizing frames with
  | zero => simpa [core,result,chain,payload,cost,depth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using pairPath (frames := frames) (callsPath A B a false n s _) (callsPath A B a true k s _)
  | succ r ih =>
      have count : cost a (r+1) n k = charge n a.m+cost a r n k+3 := by simp [cost,Nat.add_mul]; omega
      rw [count]; exact pairPath (callsPath A B a false n s _) (ih _)

theorem original_flat_tuple_static (A B : Core.Ty) (r n k : Nat) :
    (elements (calls false n) (calls true k) r).length = r+2 ∧
    elaborateRecursiveLocalComputation? (inputs A B).names (inputs A B).context (source r n k) = some (core r n k,type A B r) ∧
    RecursiveLocalComputationHasType (inputs A B).names (inputs A B).context (source r n k) (type A B r) ∧
    Core.HasType (inputs A B).context.values (core r n k) (type A B r) := by
  have typed : RecursiveLocalComputationHasType (inputs A B).names (inputs A B).context (source r n k) (type A B r) := by
    induction r with
    | zero => exact .pair (callsTyped A B false n) (callsTyped A B true k)
    | succ r ih => cases r <;> exact .many (callsTyped A B false n) ih
  have length : (elements (calls false n) (calls true k) r).length = r+2 := by
    clear typed
    simp only [elements,List.length_cons]
    have tail : (tailElements (calls false n) (calls true k) r).length = r+1 := by induction r <;> simp_all [tailElements]
    omega
  exact ⟨length,elaborateRecursiveLocalComputation?_iff.mpr (elaboration A B r n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed),(elaboration A B r n k).core_hasType⟩

theorem actual_opaque_values_and_exact_paths (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates (inputs A B).names (env A B a) s (source r n k) (result a r) s ∧
    Core.Evaluates (env A B a).values s (core r n k) (result a r) s ∧
    Core.Steps (cost a r n k) ⟨.eval (core r n k) (env A B a).values,frames,s⟩ ⟨.ret (result a r),frames,s⟩ := by
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,counted A B a r n k s⟩
  have fromManual := ((elaboration A B r n k).evaluatesWithCost_iff_steps (environment := env A B a) rfl).mpr (manual A B a r n k s [])
  exact ⟨raw,((elaboration A B r n k).evaluates_iff rfl).mp raw,fromManual.toStepsWithContinuation (elaboration A B r n k) rfl frames⟩

theorem actual_value_store_cost_jointly_unique (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store)
    {value : Core.Value} {finalStore : Core.Store} {steps : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (source r n k) value finalStore steps) :
    value = result a r ∧ finalStore = s ∧ steps = (r+1)*(charge n a.m+3)+charge k a.t :=
  other.deterministic (counted A B a r n k s)

theorem arbitrary_caller_insertion (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading++suffix = (env A B a).values) :
    RecursiveLocalComputationFragment ((core r n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost a r n k) ⟨.eval ((core r n k).weakenAt leading.length) (leading++inserted::suffix),frames,s⟩ ⟨.ret (result a r),frames,s⟩ := by
  have fragment : RecursiveLocalComputationFragment (core r n k) := by
    induction r with
    | zero => exact .pair (callsElab A B false n).core_fragment (callsElab A B true k).core_fragment
    | succ r ih => exact .pair (callsElab A B false n).core_fragment ih
  have original := Core.steps_from_initial_sound (manual A B a r n k s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost,paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (cost a r n k) (.initial (core r n k) (leading++suffix) s) (.final (result a r) s) := by rw [split]; exact manual A B a r n k s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length,fun frames => same ▸ (paths frames).2⟩

private def tailCore (r n k : Nat) := match r with | 0 => callCore true k | r+1 => core r n k
private def tailValue (a : Actual) (r : Nat) := match r with | 0 => a.y | r+1 => result a r
private def tailCost (a : Actual) (r n k : Nat) := match r with | 0 => charge k a.t | r+1 => cost a r n k
private def first (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret a.x,[.pairRight (tailCore r n k) (env A B a).values],s⟩
private def second (a : Actual) (r : Nat) (s : Core.Store) : Core.State := ⟨.ret (tailValue a r),[.pairApply a.x],s⟩
theorem actual_pair_frames_are_checkpoints (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) :
    Core.runStateful (charge n a.m+1) (.initial (core r n k) (env A B a).values s) = .outOfFuel (first A B a r n k s) ∧
    Core.runStateful (cost a r n k-1) (.initial (core r n k) (env A B a).values s) = .outOfFuel (second a r s) := by
  have p1 : Core.Steps (charge n a.m+1) (.initial (core r n k) (env A B a).values s) (first A B a r n k s) := by
    have path := Core.Steps.cons .enterPair (callsPath A B a false n s [.pairRight (tailCore r n k) (env A B a).values])
    cases r <;> simpa [core,chain,tailCore,first,Core.State.initial,payload,depth] using path
  have tail : Core.Steps (tailCost a r n k) ⟨.eval (tailCore r n k) (env A B a).values,[.pairApply a.x],s⟩ (second a r s) := by
    cases r; exact callsPath A B a true k s _; exact manual A B a _ n k s _
  have count : cost a r n k-1 = (charge n a.m+1)+(tailCost a r n k+1) := by
    cases r <;> simp [cost,tailCost,Nat.add_mul] <;> omega
  refine ⟨Core.runStateful_outOfFuel_complete p1 (Core.advance_next_iff.mpr .enterPairRight),?_⟩
  apply Core.runStateful_outOfFuel_complete (by rw [count]; exact p1.trans (.cons .enterPairRight tail))
  exact Core.advance_next_iff.mpr .applyPair

theorem all_fuels_residual_and_full_resume (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core r n k) (env A B a).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core r n k) (env A B a).values s) = .done (result a r) s ↔ cost a r n k ≤ fuel) ∧
    spent < cost a r n k ∧ Core.Steps (cost a r n k-spent) cp (.final (result a r) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent+additional) (.initial (core r n k) (env A B a).values s) := by
  have path := manual A B a r n k s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff,residual.1,residual.2,Core.runStateful_resume exhausted additional⟩

theorem fixed_source_actual_body_cost_is_unbounded (A B : Core.Ty) (r limit : Nat) (x y : Core.Value)
    (leftCapture rightCapture : Core.Environment) (s : Core.Store) :
    ∃ a : Actual, RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (source r 1 1) (result a r) s (cost a r 1 1) ∧ limit < cost a r 1 1 := by
  let a : Actual := ⟨x,y,limit,0,leftCapture,rightCapture⟩
  refine ⟨a,counted A B a r 1 1 s,?_⟩
  have enough : 3*limit+9 ≤ (r+1)*(3*limit+9) := by induction r <;> simp_all [Nat.add_mul] <;> omega
  simp [cost,charge,a,Nat.add_assoc]; omega
private def guarded (skipped : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.conditional (ref .c) ⟨span.source,100,101⟩ (ref .x) ⟨span.source,400,401⟩ skipped⟩
theorem pure_overlap_keeps_unselected_original_syntax (A B : Core.Ty) (a : Actual) (s : Core.Store) (skipped : Syntax.Expr) :
    LocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (tuple (guarded skipped) (ref .y) 0) (.pair a.x a.y) s 8 ∧
    RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (tuple (guarded skipped) (ref .y) 0) (.pair a.x a.y) s 8 := by
  have old : LocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (tuple (guarded skipped) (ref .y) 0) (.pair a.x a.y) s 8 :=
    .pure (.pair (.ifTrue (atomCost A B a .c s) (atomCost A B a .x s)) (atomCost A B a .y s))
  have new : RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (tuple (guarded skipped) (ref .y) 0) (.pair a.x a.y) s 8 :=
    .pair (.ifTrue (.pure (atomCost A B a .c s)) (.pure (atomCost A B a .x s))) (.pure (atomCost A B a .y s))
  exact ⟨old,(new.deterministic old.toRecursiveLocalComputation).2.2 ▸ new⟩
private def body (r n k : Nat) : Syntax.Block := ⟨span,
  [⟨span,.letDecl ⟨span,"r"⟩ none (some (source r n k))⟩,⟨span,.returnStmt (some ⟨span,.identifier ⟨span,"r"⟩⟩)⟩]⟩
private theorem bodyElab (A B : Core.Ty) (r n k : Nat) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs A B) (body r n k) (.letE (core r n k) (.var 0)) (type A B r) :=
  .inferred (elaboration A B r n k)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCost (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs A B).names (env A B a) s (body r n k) (result a r) s (cost a r n k+3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost,body,Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted A B a r n k s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost a r n k+3) ⟨.eval (.letE (core r n k) (.var 0)) (env A B a).values,frames,s⟩ ⟨.ret (result a r),frames,s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual A B a r n k s (.letBody (.var 0) (env A B a).values::frames)) (.cons (.var rfl) .refl)
theorem old_original_body_embeddings (A B : Core.Ty) (a : Actual) (s : Core.Store) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs A B) (body 0 0 0) (.letE (core 0 0 0) (.var 0)) (.product A B) ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs A B).names (env A B a) s (body 0 0 0) (.pair a.x a.y) s 8 := by
  have old : LocalComputationElaborates (inputs A B).names (inputs A B).context (source 0 0 0) (core 0 0 0) (.product A B) := by
    cases oldLeaf A B .x with
    | pure lr ll lt =>
        cases oldLeaf A B .y with
        | pure rr rl rt => exact .pure (.pair lr rr) (.pair ll rl) (.pair lt rt)
        | application child => cases child
    | application child => cases child
  have static : LocalComputationReturnTreeElaborates [] owner (inputs A B) (body 0 0 0) (.letE (core 0 0 0) (.var 0)) (.product A B) :=
    .inferred (by change ¬"r" ∈ ["f","x","g","y","c"]; decide) old (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
  have counted : LocalComputationReturnTreeEvaluatesWithCost owner (inputs A B).names (env A B a) s (body 0 0 0) (.pair a.x a.y) s 8 :=
    .inferred (.pure (.pair (atomCost A B a .x s) (atomCost A B a .y s))) (.expression (.pure (.identifier .head .head)))
  exact ⟨static.toRecursiveComputationReturnTree,counted.toRecursiveComputationReturnTree⟩
theorem shared_body_original_source_and_actual_cost (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner (inputs A B) (body r n k) = some (.letE (core r n k) (.var 0),type A B r) ∧
    Core.HasType (inputs A B).context.values (.letE (core r n k) (.var 0)) (type A B r) ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs A B).names (env A B a) s (body r n k) (result a r) s (cost a r n k+3) ∧
    Core.Steps (cost a r n k+3) ⟨.eval (.letE (core r n k) (.var 0)) (env A B a).values,frames,s⟩ ⟨.ret (result a r),frames,s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab A B r n k) (environment := env A B a) rfl).mpr (bodyManual A B a r n k s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab A B r n k),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab A B r n k),costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCost A B a r n k s) (bodyElab A B r n k) rfl frames⟩

end Tests.FrontendRecursiveTuple
end
