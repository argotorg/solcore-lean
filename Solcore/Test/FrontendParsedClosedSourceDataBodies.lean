import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.Computation
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Syntax.Parser.Term
/- Original gate/Closed/old-cost certificates precede every successful search.
Actual mixed endpoints enter both image laws before any IO projection. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceDataBodies
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"DataBodies",by decide⟩],by decide⟩⟩,174⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=901},700⟩
private def up (e : Resolved.Environment) := e.map (fun row => (row.1,RuntimeValue.ofCore row.2))
private structure EC (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (src : Syntax.Expr) (v : Core.Value) (cost : Nat) : Type where
  gate : ClosedSourceDataExpression src
  closed : ClosedSourceExpressionEvaluates owner t (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore v) (s.map RuntimeValue.ofCore)
  old : LocalExpressionEvaluatesWithCost t e s src v s cost
private structure BC (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (src : Syntax.Block) (v : Core.Value) (cost : Nat) : Type where
  gate : ClosedSourceDataBody src
  closed : ClosedSourceBodyEvaluates owner t (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore v) (s.map RuntimeValue.ofCore)
  old : ComputationReturnTreeEvaluatesWithCost LocalExpressionEvaluatesWithCost owner t e s src v s cost
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail different _ ih => exact .tail different ih
private theorem freshNe {t : LocalNameTable} {name : String} {i : Resolved.LocalId}
    (h : LocalNameTable.Lookup t name i) : Resolved.freshLocalId owner (t.map Prod.snd) ≠ i := by
  intro same
  apply Resolved.freshLocalId_not_mem owner (t.map Prod.snd)
  rw [same]; exact List.mem_map.mpr ⟨(name,i),h.mem,rfl⟩
private def ref (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr)
    (name : String) (i : Resolved.LocalId) (v : Core.Value)
    (n : LocalNameTable.Lookup t name i) (f : Resolved.LocalScope.Lookup e i v) : IO (EC t e s src v 1) := do
  match shape : src with
  | ⟨_,.identifier actual⟩ =>
    if h : actual.value=name then return by rw [shape]; exact ⟨.reference,.reference (h ▸ n) (mapped f),.identifier (h ▸ n) f⟩
    else throw (IO.userError "original identifier spelling")
  | _ => throw (IO.userError "original identifier shape")
private def ret (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block)
    (name : String) (i : Resolved.LocalId) (v : Core.Value)
    (n : LocalNameTable.Lookup t name i) (f : Resolved.LocalScope.Lookup e i v) : IO (BC t e s src v 1) := do
  match shape : src with
  | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ =>
    let h ← ref t e s child name i v n f
    return by rw [shape]; exact ⟨.expression h.gate,.expression h.closed,.expression h.old⟩
  | _ => throw (IO.userError "original expression return")
private def branch {t : LocalNameTable} {e : Resolved.Environment} {s : Core.Store}
    {bs marker : Syntax.SourceSpan} {guard : Syntax.Expr} {yes no : Syntax.Block}
    {c : Bool} {x y : Core.Value} {a b : Nat} (h : EC t e s guard (.bool c) 1)
    (ht : BC t e s yes x a) (hf : BC t e s no y b) :
    BC t e s ⟨bs,[⟨marker,.ifThen guard yes (some no)⟩]⟩ (if c then x else y) (1+(if c then a else b)+2) := by
  refine ⟨.conditional h.gate ht.gate hf.gate,?_,?_⟩
  · cases c
    · exact .ifFalse (by simpa only [RuntimeValue.ofCore] using h.closed) hf.closed
    · exact .ifTrue (by simpa only [RuntimeValue.ofCore] using h.closed) ht.closed
  · cases c <;> first | exact .ifTrue h.old ht.old | exact .ifFalse h.old hf.old
private def mainWitness (src : Syntax.Block) (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (x saved : Core.Value) (c d : Bool)
    (nx : LocalNameTable.Lookup t "x" (sid 7)) (ns : LocalNameTable.Lookup t "saved" (sid 3))
    (nc : LocalNameTable.Lookup t "c" (sid 31)) (nd : LocalNameTable.Lookup t "d" (sid 11))
    (fx : Resolved.LocalScope.Lookup e (sid 7) x) (fs : Resolved.LocalScope.Lookup e (sid 3) saved)
    (fc : Resolved.LocalScope.Lookup e (sid 31) (.bool c)) (fd : Resolved.LocalScope.Lookup e (sid 11) (.bool d)) :
    IO (BC t e s src (if c then x else if d then .unit else saved) (if c then 17 else 20)) := do
  match shape : src with
  | ⟨bs,[⟨ls,.letDecl ⟨xs,"x"⟩ (some ann) (some ⟨gs,.group init⟩)⟩,⟨ys,.letDecl ⟨yns,"y"⟩ none (some savedSrc)⟩,
      ⟨ps,.expression ⟨pairSpan,.tuple ⟨ts,[left,right]⟩⟩ true⟩,
      ⟨innerSpan,.block [⟨ifSpan,.ifThen guard yes (some ⟨elseSpan,[⟨dSpan,.ifThen dg ⟨bareSpan,[⟨rs,.returnStmt none⟩]⟩ (some no)⟩]⟩)⟩]⟩]⟩ =>
        check (bs.startByte==0 && bs.endByte==88 && gs.startByte==12 && gs.endByte==15 && pairSpan==ts) "original main/group/tuple spans"
        let i := Resolved.freshLocalId owner (t.map Prod.snd)
        let t1 := ("x",i)::t; let e1 := (i,x)::e
        let j := Resolved.freshLocalId owner (t1.map Prod.snd)
        let t2 := ("y",j)::t1; let e2 := (j,saved)::e1
        let hi ← ref t e s init "x" (sid 7) x nx fx
        let hs ← ref t1 e1 s savedSrc "saved" (sid 3) saved (.tail (by decide) ns) (.tail (freshNe ns) fs)
        let hl ← ref t2 e2 s left "x" i x (.tail (by decide) .head) (.tail (Resolved.freshLocalId_cons_fresh_ne owner _) .head)
        let hr ← ref t2 e2 s right "y" j saved .head .head
        let hc ← ref t2 e2 s guard "c" (sid 31) (.bool c) (.tail (by decide) (.tail (by decide) nc))
          (.tail (freshNe (t:=t1) (.tail (by decide) nc)) (.tail (freshNe nc) fc))
        let hd ← ref t2 e2 s dg "d" (sid 11) (.bool d) (.tail (by decide) (.tail (by decide) nd))
          (.tail (freshNe (t:=t1) (.tail (by decide) nd)) (.tail (freshNe nd) fd))
        let ht ← ret t2 e2 s yes "x" i x (.tail (by decide) .head) (.tail (Resolved.freshLocalId_cons_fresh_ne owner _) .head)
        let hf ← ret t2 e2 s no "y" j saved .head .head
        let hb : BC t2 e2 s ⟨bareSpan,[⟨rs,.returnStmt none⟩]⟩ .unit 1 := ⟨.bare,by simpa only [RuntimeValue.ofCore] using ClosedSourceBodyEvaluates.bare,.bare⟩
        let tail := branch (bs:=innerSpan) (marker:=ifSpan) hc ht (branch (bs:=elseSpan) (marker:=dSpan) hd hb hf)
        return by
          rw [shape]
          refine ⟨.binding (.group hi.gate) (.binding hs.gate (.discard (.pair hl.gate hr.gate) (.block tail.gate))),?_,?_⟩
          · apply ClosedSourceBodyEvaluates.binding (.group hi.closed)
            apply ClosedSourceBodyEvaluates.inferred (by simpa only [t1,e1,i,up,List.map_cons] using hs.closed)
            have p := ClosedSourceExpressionEvaluates.pair (span:=pairSpan) (tupleSpan:=ts) hl.closed hr.closed
            simpa only [t2,t1,e2,e1,j,i,up,List.map_cons,RuntimeValue.ofCore] using ClosedSourceBodyEvaluates.discard p (.block tail.closed)
          · have h := ComputationReturnTreeEvaluatesWithCost.discard (blockSpan:=bs) (statementSpan:=ps)
              (LocalExpressionEvaluatesWithCost.pair (span:=pairSpan) (tupleSpan:=ts) hl.old hr.old)
              (ComputationReturnTreeEvaluatesWithCost.block (outerSpan:=bs) tail.old)
            have h := ComputationReturnTreeEvaluatesWithCost.inferred (name:=⟨yns,"y"⟩) (letSpan:=ys) hs.old h
            have h := ComputationReturnTreeEvaluatesWithCost.binding (name:=⟨xs,"x"⟩) (annotation:=ann) (letSpan:=ls)
              (LocalExpressionEvaluatesWithCost.group (span:=gs) hi.old) h
            cases c <;> cases d <;> exact h
  | _ => throw (IO.userError "original main body")
private def bindWitness (src : Syntax.Block) (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (spelling : String) (id : Resolved.LocalId) (v : Core.Value) (grouped : Bool)
    (n : LocalNameTable.Lookup t spelling id) (f : Resolved.LocalScope.Lookup e id v) : IO (BC t e s src v 4) := do
  match shape : src with
  | ⟨bs,⟨ls,.letDecl ⟨xs,"x"⟩ ann (some init)⟩::rest⟩ =>
    let hi : EC t e s init v 1 ← if grouped then
      match gi : init with
      | ⟨_,.group child⟩ =>
        let h ← ref t e s child spelling id v n f
        pure (by rw [gi]; exact ⟨.group h.gate,.group h.closed,.group h.old⟩)
      | _ => throw (IO.userError "original grouped initializer")
    else ref t e s init spelling id v n f
    let i := Resolved.freshLocalId owner (t.map Prod.snd)
    let ht ← ret (("x",i)::t) ((i,v)::e) s ⟨bs,rest⟩ "x" i v .head .head
    return by
      rw [shape]; refine ⟨.binding hi.gate ht.gate,?_,?_⟩
      · have htail := ht.closed
        simp only [up,List.map_cons] at htail
        cases ann <;> first | exact .binding hi.closed htail | exact .inferred hi.closed htail
      · cases ann with
        | none => exact ComputationReturnTreeEvaluatesWithCost.inferred (name:=⟨xs,"x"⟩) hi.old ht.old
        | some a => exact ComputationReturnTreeEvaluatesWithCost.binding (name:=⟨xs,"x"⟩) (annotation:=a) hi.old ht.old
  | _ => throw (IO.userError "original single initialized let")
private def shadow (src : Syntax.Block) (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (v : Core.Value) (wrapped : Bool) (n : LocalNameTable.Lookup t "saved" (sid 3))
    (f : Resolved.LocalScope.Lookup e (sid 3) v) : IO (BC t e s src v 4) := do
  if wrapped then
    match shape : src with
    | ⟨_,[⟨inner,.block rest⟩]⟩ =>
      let h ← bindWitness ⟨inner,rest⟩ t e s "saved" (sid 3) v false n f
      return by rw [shape]; exact ⟨.block h.gate,.block h.closed,.block h.old⟩
    | _ => throw (IO.userError "original explicit scope block")
  else bindWitness src t e s "saved" (sid 3) v false n f
private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",sid 7,.unit⟩,⟨"saved",sid 3,.unit⟩,⟨"c",sid 31,.bool⟩,
  ⟨"d",sid 11,.bool⟩,⟨"tag",foreign,.word⟩],by decide⟩
private def environment (x saved : Core.Value) (c d : Bool) (tag : Core.Value) : Resolved.Environment :=
  [(sid 7,x),(sid 3,saved),(sid 31,.bool c),(sid 11,.bool d),(foreign,tag)]
private def parsed (text : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"data-bodies.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.block .require (Syntax.Parser.State.initial file lexed) with
  | .ok body next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && body.span==Syntax.SourceSpan.fullFile file) "original whole block/EOF/spans"
    return body
  | _ => throw (IO.userError "original block parser")
private def scopeWitness (src : Syntax.Block) (x saved : Core.Value) (c : Bool) (tag : Core.Value)
    (s : Core.Store) (swapped wrapped : Bool) :
    IO (BC inputs.names (environment x saved c true tag) s src
      (if c=swapped then x else saved) (if c=swapped then 4 else 7)) := do
  let e := environment x saved c true tag
  match shape : src with
  | ⟨bs,[⟨marker,.ifThen guard yes (some no)⟩]⟩ =>
    let hc ← ref inputs.names e s guard "c" (sid 31) (.bool c)
      (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
    if hs : swapped then
      let ht ← ret inputs.names e s yes "x" (sid 7) x .head .head
      let hf ← shadow no inputs.names e s saved wrapped (.tail (by decide) .head) (.tail (by decide) .head)
      return by rw [shape]; have h := branch (bs:=bs) (marker:=marker) hc ht hf; cases swapped <;> cases c <;> simp_all <;> exact h
    else
      let ht ← shadow yes inputs.names e s saved wrapped (.tail (by decide) .head) (.tail (by decide) .head)
      let hf ← ret inputs.names e s no "x" (sid 7) x .head .head
      return by rw [shape]; have h := branch (bs:=bs) (marker:=marker) hc ht hf; cases swapped <;> cases c <;> simp_all <;> exact h
  | _ => throw (IO.userError "original scope conditional")
private def exercise (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block)
    (v : Core.Value) (cost depth : Nat) (h : BC t e s src v cost) (withCore : Bool) : IO Unit := do
  let old := (computationReturnTreeEvaluates_iff_exists_cost localExpressionEvaluates_iff_exists_cost).mpr ⟨cost,h.old⟩
  for budget in [0,depth-1,depth,depth+2] do
    match ran : evaluateClosedSourceBody? budget owner t (up e) (s.map RuntimeValue.ofCore) src with
    | none => check (budget<depth) "closed depth exhaustion"
    | some (mv,ms) =>
      have actual := evaluateClosedSourceBody?_sound ran
      have rawImage := h.gate.local_evaluates_iff.mp actual
      proof (show mv=RuntimeValue.ofCore v ∧ ms=s.map RuntimeValue.ofCore from by
        obtain ⟨a,b,hv,hs,ev⟩ := rawImage
        obtain ⟨k,hk⟩ := (computationReturnTreeEvaluates_iff_exists_cost localExpressionEvaluates_iff_exists_cost).mp ev
        obtain ⟨vv,ss,_⟩ := hk.deterministic (fun aa bb => aa.deterministic bb) h.old
        exact ⟨hv.trans (congrArg _ vv),hs.trans (congrArg _ ss)⟩)
      proof (h.gate.local_evaluates_iff.mpr rawImage)
      proof ((h.gate.local_evaluates_iff.mpr ⟨v,s,rfl,rfl,old⟩).deterministic h.closed)
      if withCore then
        if ht : t=inputs.names then
          if aligned : e.ids=inputs.context.ids then
            match accepted : elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs src with
            | none => throw (IO.userError "whole checker")
            | some (core,ty) =>
              have image := (h.gate.core_evaluates_iff accepted aligned).mp (ht ▸ actual)
              proof image
              check (ty==.unit) "actual whole checked type"
              for fuel in [0,cost-1,cost,cost+1] do
                match runCore : Core.runStateful fuel (.initial core e.values s) with
                | .done a b =>
                  have ev := Core.runStateful_evaluation_sound runCore
                  proof (show ClosedSourceBodyEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) src mv ms from by
                    obtain ⟨x,y,hx,hy,oldCore⟩ := image
                    have ⟨vx,vs⟩ := Core.evaluation_deterministic oldCore ev
                    exact (h.gate.core_evaluates_iff accepted aligned).mpr ⟨a,b,hx.trans (congrArg _ vx),hy.trans (congrArg _ vs),ev⟩)
                  check (a==v && b==s && cost<=fuel && mv.toCore?==some a && ms.mapM RuntimeValue.toCore?==some b) "actual whole payload/store and transition cost"
                | .outOfFuel _ => check (fuel<cost) "Core transition exhaustion"
                | .fault _ _ => throw (IO.userError "unexpected Core fault")
          else throw (IO.userError "full runtime ID order")
        else throw (IO.userError "unique static names")
      check (mv.toCore?==some v && ms.mapM RuntimeValue.toCore?==some s && depth<=budget) "actual raw full image"
private def missingWitness (src : Syntax.Block) (typed : LocalTypeInputs) (x saved tag : Core.Value) (s : Core.Store)
    (nx : LocalNameTable.Lookup typed.names "x" (sid 7)) (nc : LocalNameTable.Lookup typed.names "c" (sid 31)) :
    IO (BC typed.names (environment x saved true true tag) s src x 4) := do
  let e := environment x saved true true tag
  match shape : src with
  | ⟨_,[⟨_,.ifThen guard yes (some ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier missing⟩)⟩]⟩)⟩]⟩ =>
    check (missing.value=="missing") "original unselected missing name"
    let hg ← ref typed.names e s guard "c" (sid 31) (.bool true) nc (.tail (by decide) (.tail (by decide) .head))
    let ht ← ret typed.names e s yes "x" (sid 7) x nx .head
    return by rw [shape]; exact ⟨.conditional hg.gate ht.gate (.expression .reference),
      .ifTrue (by simpa only [RuntimeValue.ofCore] using hg.closed) ht.closed,
      ComputationReturnTreeEvaluatesWithCost.ifTrue hg.old ht.old⟩
  | _ => throw (IO.userError "original missing conditional")
end ParsedClosedSourceDataBodies
open Solcore Solcore.Frontend ParsedClosedSourceDataBodies
def frontendParsedClosedSourceDataBodyTests : IO Unit := do
  let src ← parsed "{let x:Unit=(x);let y=saved;(x,y);{if(c){return x;}else{if(d){return;}else{return y;}}}}"
  let x : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let saved : Core.Value := .hostFunction .storageWrite
  let tag : Core.Value := .cellRef (.function .word .word) 700
  for c in [true,false] do
    for d in [true,false] do
      for s in [[],[x,tag]] do
        let e := environment x saved c d tag
        let h ← mainWitness src inputs.names e s x saved c d .head (.tail (by decide) .head)
          (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
          .head (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
          (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
        exercise inputs.names e s src (if c then x else if d then .unit else saved) (if c then 17 else 20) (if c || d then 7 else 8) h true
        for extra in [[],[(sid 7,tag),(foreign,x),(sid 32,saved)]] do
          let t := inputs.names++[("x",sid 7),("saved",sid 3),("foreignAlias",foreign)]
          let raw : Resolved.Environment := [(sid 3,saved),(sid 7,x),(sid 31,.bool c),(sid 11,.bool d),(foreign,tag),(sid 7,tag),(sid 32,tag),(sid 33,x)]++extra
          check (Resolved.freshLocalId owner (t.map Prod.snd)==sid 32 && Resolved.freshLocalId owner (sid 32::t.map Prod.snd)==sid 33) "fresh names ignore environment-only poison"
          let hr ← mainWitness src t raw s x saved c d .head (.tail (by decide) .head)
            (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
            (.tail (by decide) .head) .head (.tail (by decide) (.tail (by decide) .head))
            (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
          exercise t raw s src (if c then x else if d then .unit else saved) (if c then 17 else 20) (if c || d then 7 else 8) hr false
  let unknown ← parsed "{let x:Unknown=(x);return x;}"
  let eu := environment x saved true true tag
  let hu ← bindWitness unknown inputs.names eu [x,tag] "x" (sid 7) x true .head .head
  exercise inputs.names eu [x,tag] unknown x 4 3 hu false
  check ((elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs unknown).isNone) "unknown annotation leaves raw rules unchanged"
  for variant in [0,1,2] do
    let source ← parsed (if variant==0 then "{if(c){let x=saved;return x;}else{return x;}}" else if variant==1 then
      "{if(c){{let x=saved;return x;}}else{return x;}}" else "{if(c){return x;}else{let x=saved;return x;}}")
    for c in [true,false] do
      let swapped := variant==2; let wrapped := variant==1
      let h ← scopeWitness source x saved c tag [x,tag] swapped wrapped
      exercise inputs.names (environment x saved c true tag) [x,tag] source (if c=swapped then x else saved)
        (if c=swapped then 4 else 7) (if c=swapped then 3 else if wrapped then 5 else 4) h (variant != 0)
      check ((elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs source).isSome==(variant != 0)) "then-only name protection and explicit block"
  let missing ← parsed "{if(c){return x;}else{return missing;}}"
  let extended : LocalTypeInputs := ⟨inputs.bindings++[⟨"missing",sid 99,.unit⟩],by decide⟩
  for present in [false,true] do
    let typed := if present then extended else inputs
    let h ← missingWitness missing typed x saved tag [x,tag] (by cases present <;> exact .head)
      (by cases present <;> exact .tail (by decide) (.tail (by decide) .head))
    exercise typed.names eu [x,tag] missing x 4 3 h false
    check ((elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner typed missing).isSome==present &&
      decide (eu.ids=typed.context.ids)==(!present)) "missing spelling versus missing runtime ID: whole acceptance and exact alignment differ"
    let visited := environment x saved false true tag
    check ((evaluateClosedSourceBody? 40 owner typed.names (up visited) ([x,tag].map RuntimeValue.ofCore) missing).isNone) "visited missing name or ID is actual None"
  IO.println "ADR0294 parsed body image, independent depth/cost, raw rows, annotations and scopes GREEN"
end Tests
