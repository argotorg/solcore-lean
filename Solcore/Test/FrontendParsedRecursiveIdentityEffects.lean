import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties
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
        by rw [shape]; exact .binary .add (by simpa only [Core.BinaryOp.leftType,same.1] using a.evidence) (by simpa only [Core.BinaryOp.rightType,same.2] using b.evidence)⟩ else throw (IO.userError "static operands")
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
