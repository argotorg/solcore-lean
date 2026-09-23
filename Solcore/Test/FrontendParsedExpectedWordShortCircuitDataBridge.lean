import Solcore.Frontend.Expected
import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Syntax.Parser.Term
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Tests.ParsedExpectedWordShortCircuitDataBridge
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedWordShortCircuit",by decide⟩],by decide⟩⟩,299⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def caller : Resolved.DeclarationId := {owner with declarationIndex:=991}
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"a",sid 7,.bool⟩,⟨"b",sid 31,.bool⟩,⟨"w",sid 11,.word⟩,
  ⟨"p",sid 12,.word⟩,⟨"extra",cid 700,.unit⟩,⟨"p",cid 701,.word⟩],by decide⟩
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def heap (s : Core.Store) := s.map RuntimeValue.ofCore
private def environment (a b : Bool) (w : Core.Word) (q : Core.Value) : Resolved.Environment :=
  [(sid 7,.bool a),(sid 31,.bool b),(sid 11,.word w),(sid 12,q),(cid 700,.cellRef .word 900),(cid 701,q)]
private abbrev Child (n : LocalNameTable) (t : Resolved.Context) (s : Syntax.Expr) (c : Core.Expr) (v : Core.Ty) :=
  ∃ r, ResolvesLocalExpression n s r ∧ Resolved.Lowers t.ids r c ∧ Resolved.HasType t r v
private structure EC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  depth : Nat
  gate : ClosedSourceDataExpression src
  elaboration : Child t.names t.context src core type
  old : LocalExpressionEvaluatesWithCost t.names e s src value s cost
  closed : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s) src (RuntimeValue.ofCore value) (heap s)
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail ne _ ih => exact .tail ne ih
private theorem path {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids) (k : List Core.Frame) :
    Core.Steps h.cost ⟨.eval h.core e.values,k,s⟩ ⟨.ret h.value,k,s⟩ := by
  obtain ⟨r,res,low,_⟩ := h.elaboration; exact h.old.toStepsWithContinuation res (same ▸ low) k
private def logical {t e s left right} (o : Bool) (ss os : Syntax.SourceSpan)
    (l : EC t e s left) (r : EC t e s right) :
    IO (EC t e s ⟨ss,.binary left ⟨os,if o then .logicalOr else .logicalAnd⟩ right⟩) := do
  if typed : l.type=.bool ∧ r.type=.bool then
    match lv : l.value, rv : r.value with
    | .bool a,.bool b =>
      let v := if o then a || b else a && b
      let k := if a==o then l.cost+3 else l.cost+r.cost+2
      let d := if a==o then l.depth+1 else max l.depth r.depth+1
      let c := if o then Core.Expr.ifE l.core (.bool true) r.core else .ifE l.core r.core (.bool false)
      have admitted : ClosedSourceDataExpression ⟨ss,.binary left ⟨os,if o then .logicalOr else .logicalAnd⟩ right⟩ := by
        cases o; exact .logicalAnd l.gate r.gate; exact .logicalOr l.gate r.gate
      have el : Child t.names t.context ⟨ss,.binary left ⟨os,if o then .logicalOr else .logicalAnd⟩ right⟩ c .bool := by
        obtain ⟨lr,la,ll,lt⟩ := l.elaboration; obtain ⟨rr,ra,rl,rt⟩ := r.elaboration
        cases o
        · exact ⟨.ifE lr rr (.bool false),.logicalAnd la ra,.ifE ll rl .bool,.ifE (typed.1 ▸ lt) (typed.2 ▸ rt) .bool⟩
        · exact ⟨.ifE lr (.bool true) rr,.logicalOr la ra,.ifE ll .bool rl,.ifE (typed.1 ▸ lt) .bool (typed.2 ▸ rt)⟩
      have old : LocalExpressionEvaluatesWithCost t.names e s
          ⟨ss,.binary left ⟨os,if o then .logicalOr else .logicalAnd⟩ right⟩ (.bool v) s k := by
        cases o <;> cases a
        · exact .andFalse (lv ▸ l.old)
        · exact .andTrue (lv ▸ l.old) (rv ▸ r.old)
        · exact .orFalse (lv ▸ l.old) (rv ▸ r.old)
        · exact .orTrue (lv ▸ l.old)
      have closed : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s)
          ⟨ss,.binary left ⟨os,if o then .logicalOr else .logicalAnd⟩ right⟩ (.bool v) (heap s) := by
        cases o <;> cases a
        · exact .andFalse (by simpa only [lv,RuntimeValue.ofCore] using l.closed)
        · exact .andTrue (by simpa only [lv,RuntimeValue.ofCore] using l.closed) (by simpa [rv,RuntimeValue.ofCore,v] using r.closed)
        · exact .orFalse (by simpa only [lv,RuntimeValue.ofCore] using l.closed) (by simpa [rv,RuntimeValue.ofCore,v] using r.closed)
        · exact .orTrue (by simpa only [lv,RuntimeValue.ofCore] using l.closed)
      return ⟨c,.bool,.bool v,k,d,admitted,el,old,by simpa only [RuntimeValue.ofCore] using closed⟩
    | _,_ => throw (IO.userError "checked guard requires actual Bool children")
  else throw (IO.userError "whole guard Bool checking")
private def expr (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) : IO (EC t e s src) := do
  match shape : src with
  | ⟨_,.identifier name⟩ =>
    match named : t.names.lookup? name.value with
    | some i => match typed : t.context.lookup? i, found : e.lookup? i, indexed : Resolved.LocalScope.index? t.context.ids i with
      | some ty,some v,some n => return ⟨.var n,ty,v,1,1,by rw [shape]; exact .reference,
          by rw [shape]; exact ⟨.var i,.identifier (LocalNameTable.lookup?_iff.mp named),.var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩,
          by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
          by rw [shape]; exact .reference (LocalNameTable.lookup?_iff.mp named) (mapped (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | _,_,_ => throw (IO.userError "independent original row")
    | none => throw (IO.userError "independent original name")
  | ⟨_,.group child⟩ =>
    let h ← expr t e s child
    return ⟨h.core,h.type,h.value,h.cost,h.depth+1,by rw [shape]; exact .group h.gate,
      by obtain ⟨r,a,b,c⟩ := h.elaboration; rw [shape]; exact ⟨r,.group a,b,c⟩,
      by rw [shape]; exact .group h.old,by rw [shape]; exact .group h.closed⟩
  | ⟨_,.unary ⟨_,.bitNot⟩ child⟩ =>
    let h ← expr t e s child
    if ht : h.type=.word then
      match hv : h.value with
      | .word w => return ⟨.unary .wordNot h.core,.word,.word w.bitNot,h.cost+2,h.depth+1,by rw [shape]; exact .bitNot h.gate,
          by obtain ⟨r,a,b,c⟩ := h.elaboration; rw [shape]; exact ⟨.unary .wordNot r,.bitNot a,.unary b,.unary (by simpa only [ht,Core.UnaryOp.operandType] using c)⟩,
          by rw [shape]; exact .bitNot (hv ▸ h.old),by rw [shape]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.bitNot (by simpa only [hv,RuntimeValue.ofCore] using h.closed)⟩
      | _ => throw (IO.userError "independent Word operand")
    else throw (IO.userError "whole Word unary checking")
  | ⟨ss,.binary left ⟨os,op⟩ right⟩ =>
    let l ← expr t e s left; let r ← expr t e s right
    match hop : op with
    | .logicalAnd => let h ← logical false ss os l r; return (by simpa only [shape,hop,Bool.false_eq_true,↓reduceIte] using h)
    | .logicalOr => let h ← logical true ss os l r; return (by simpa only [shape,hop,Bool.false_eq_true,↓reduceIte] using h)
    | _ => throw (IO.userError "only short-circuit binary")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
    let g ← expr t e s guard; let y ← expr t e s yes; let n ← expr t e s no
    if typed : g.type=.bool ∧ y.type=.word ∧ n.type=.word then
      match gv : g.value with
      | .bool b =>
        have el : Child t.names t.context src (.ifE g.core y.core n.core) .word := by
          obtain ⟨gr,ga,gl,gt⟩ := g.elaboration; obtain ⟨yr,ya,yl,yt⟩ := y.elaboration; obtain ⟨nr,na,nl,nt⟩ := n.elaboration
          rw [shape]; exact ⟨.ifE gr yr nr,.conditional ga ya na,.ifE gl yl nl,.ifE (typed.1 ▸ gt) (typed.2.1 ▸ yt) (typed.2.2 ▸ nt)⟩
        return ⟨.ifE g.core y.core n.core,.word,(if b then y.value else n.value),g.cost+(if b then y.cost else n.cost)+2,max g.depth (if b then y.depth else n.depth)+1,
          by rw [shape]; exact .conditional g.gate y.gate n.gate,el,
          by rw [shape]; cases b; exact .ifFalse (gv ▸ g.old) n.old; exact .ifTrue (gv ▸ g.old) y.old,
          by rw [shape]; cases b; exact .conditionalFalse (by simpa only [gv,RuntimeValue.ofCore] using g.closed) n.closed; exact .conditionalTrue (by simpa only [gv,RuntimeValue.ofCore] using g.closed) y.closed⟩
      | _ => throw (IO.userError "actual conditional Bool guard")
    else throw (IO.userError "both Word branches checked")
  | _ => throw (IO.userError "bounded original expression")
termination_by sizeOf src
private def exprImages {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids) {v st}
    (actual : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s) src v st) : IO Unit := do
  have eq : v=RuntimeValue.ofCore h.value ∧ st=heap s := by
    obtain ⟨r,res,low,_⟩ := h.elaboration
    have old := h.old.erase; have core := Core.steps_from_initial_sound (path h same [])
    have localBack : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s) src (RuntimeValue.ofCore h.value) (heap s) := h.gate.local_evaluates_iff.mpr ⟨h.value,s,rfl,rfl,old⟩
    have both : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s) src v st := h.gate.local_evaluates_iff.mpr (h.gate.local_evaluates_iff.mp actual)
    have ci := h.gate.core_evaluates_iff res (same ▸ low) (owner:=owner) (initialStore:=s) (actualValue:=v) (actualFinal:=st)
    obtain ⟨a,b,hv,hs,run⟩ := ci.mp both
    obtain ⟨ve,se⟩ := Core.evaluation_deterministic run core
    exact (ci.mpr ⟨h.value,s,hv.trans (congrArg RuntimeValue.ofCore ve),hs.trans (congrArg heap se),core⟩).deterministic localBack
  proof eq
  check (v.toCore?==some h.value && st.mapM RuntimeValue.toCore?==some s) "all actual expression images"
private def text (o : Bool) := if o then "(lam(p){return(a||b)?p:~p;})(w)" else "(lam(p){return(a&&b)?p:~p;})(w)"
private def file (s : String) : Syntax.SourceFile := ⟨⟨.main,"parsed-word-short-circuit.sol"⟩,s⟩
private def sp (a b : Nat) : Syntax.SourceSpan := ⟨(file "").id,a,b⟩
private def ref (a b : Nat) (n : String) : Syntax.Expr := ⟨sp a b,.identifier ⟨sp a b,n⟩⟩
private def expected (o : Bool) : Syntax.Expr :=
  let guard : Syntax.Expr := ⟨sp 14 20,.group ⟨sp 15 19,.binary (ref 15 16 "a") ⟨sp 16 18,if o then .logicalOr else .logicalAnd⟩ (ref 18 19 "b")⟩⟩
  let b : Syntax.Block := ⟨sp 7 27,[⟨sp 8 26,.returnStmt (some ⟨sp 14 25,.conditional guard (sp 20 21) (ref 21 22 "p") (sp 22 23)
    ⟨sp 23 25,.unary ⟨sp 23 24,.bitNot⟩ (ref 24 25 "p")⟩⟩)⟩]⟩
  let f : Syntax.Expr := ⟨sp 1 27,.lambda (sp 1 4) ⟨sp 4 7,[⟨sp 5 6,.inferred ⟨sp 5 6,"p"⟩⟩]⟩ none b⟩
  ⟨sp 0 31,.call ⟨sp 0 28,.group f⟩ ⟨sp 28 31,[ref 29 30 "w"]⟩⟩
private def savedExpected : Syntax.Expr := ⟨sp 0 9,.call (ref 0 6 "picked") ⟨sp 6 9,[ref 7 8 "w"]⟩⟩
private def parsed (s : String) (want : Syntax.Expr) : IO Syntax.Expr := do
  let f := file s
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok src next => check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && src.span==Syntax.SourceSpan.fullFile f && src==want) "exact original AST/full ranges/EOF/diagnostics"; return src
  | _ => throw (IO.userError "parser")
private def names : LocalNameTable := [("picked",cid 7),("w",cid 900),("a",cid 42),("p",sid 12),("picked",cid 7)]
private def rows (fn : RuntimeValue) (w : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(cid 900,.word w),(cid 7,fn),(cid 42,.bool false),(sid 12,fn),(cid 7,.unit),(cid 701,fn)]
private def coreRuns {e s c v k} (p : Core.Steps k (.initial c e s) (.final v s)) : IO Unit := do
  proof p
  for fuel in [0,k-1,k,k+3] do
    match run : Core.runStateful fuel (.initial c e s) with
    | .done value final => proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound run) (Core.steps_from_initial_sound p)); check (fuel≥k && value==v && final==s) "independent Core cost/endpoints"
    | .outOfFuel _ => check (fuel<k) "independent Core exhaustion"
    | .fault _ _ => throw (IO.userError "Core fault")
private def closedRuns {o n e s src v} (d : Nat) (old : ClosedSourceExpressionEvaluates o n e s src v s)
    (after : ∀ {a z}, ClosedSourceExpressionEvaluates o n e s src a z → IO Unit) : IO Unit := do
  proof old
  for fuel in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? fuel o n e s src with
    | none => check (fuel<d) "independent closed depth exhaustion"
    | some _ => have actual := evaluateClosedSourceExpression?_sound run; proof (actual.deterministic old); after actual; check (fuel≥d) "independent closed depth/actual endpoints"
private def consume {p : Prop} {e s c v a z} (old : Core.Evaluates e s c v s)
    (image : p ↔ ∃ x t, a=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e s c x t) (actual : p) : IO Unit := do
  have forward := image.mp actual; proof forward
  have eq : a=RuntimeValue.ofCore v ∧ z=heap s := by
    obtain ⟨x,t,hx,ht,run⟩ := forward; obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic run old; exact ⟨hx,ht⟩
  proof (image.mpr ⟨v,s,eq.1,eq.2,old⟩)
  check (a.toCore?==some v && z.mapM RuntimeValue.toCore?==some s) "full actual image with independent reverse witness"
private def exercise (o a b : Bool) (w : Core.Word) (q : Core.Value) (s : Core.Store) : IO Unit := do
  let src ← parsed (text o) (expected o); let picked ← parsed "picked(w)" savedExpected; let e := environment a b w q
  match original : src, savedShape : picked with
  | ⟨cs,.call ⟨gs,.group fs⟩ ⟨args,[arg]⟩⟩,⟨pcs,.call ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ ⟨pas,[⟨ws,.identifier ⟨wn,"w"⟩⟩]⟩⟩ =>
    match fsShape : fs with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred p⟩]⟩ none body⟩ =>
      match bodyShape : body with
      | ⟨bs,[⟨rs,.returnStmt (some returned)⟩]⟩ =>
        have shape : SourceUnaryLambdaShape fs p body := by rw [fsShape]; exact .inferred
        let ac ← expr inputs e s arg
        let inner := inputs.bindFresh owner p.value .word
        let ie : Resolved.Environment := (Resolved.freshLocalId owner inputs.ids,ac.value)::e
        have same : e.ids=inputs.context.ids := rfl
        have same1 : ie.ids=inner.context.ids := by simpa only [ie,inner,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
        let bc ← expr inner ie s returned
        if bt : bc.type=.word then
          have gate : ClosedSourceDataBody body := by rw [bodyShape]; exact .expression bc.gate
          have checkedBody : ComputationReturnTreeElaborates Child [] owner inner body bc.core .word := by rw [bodyShape]; exact .expression (bt ▸ bc.elaboration)
          have oldBody : ComputationReturnTreeEvaluates LocalExpressionEvaluates owner inner.names ie s body bc.value s := by rw [bodyShape]; exact .expression bc.old.erase
          have cb : ClosedSourceBodyEvaluates owner inner.names (up ie) (heap s) body (RuntimeValue.ofCore bc.value) (heap s) := by rw [bodyShape]; exact .expression bc.closed
          have beta : ClosedSourceBodyEvaluates owner ((p.value,Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
              ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),RuntimeValue.ofCore ac.value)::up e) (heap s) body (RuntimeValue.ofCore bc.value) (heap s) := by
            simpa only [ie,inner,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using cb
          let saved := RuntimeValue.sourceClosure fs owner inputs.names (up e)
          have madeOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ saved (heap s) := .group (.creation shape)
          have whole : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) src (RuntimeValue.ofCore bc.value) (heap s) := by rw [original]; exact .call shape madeOld ac.closed beta
          let direct : Syntax.Expr := ⟨cs,.call fs ⟨args,[arg]⟩⟩
          have directOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) direct (RuntimeValue.ofCore bc.value) (heap s) := .call shape (.creation shape) ac.closed beta
          have betaPath (k) : Core.Steps bc.cost ⟨.eval bc.core (ac.value::e.values),k,s⟩ ⟨.ret bc.value,k,s⟩ := by simpa only [ie,Resolved.LocalScope.values,List.map_cons] using path bc same1 k
          let core := Core.Expr.apply (.lambda .word .word bc.core) ac.core
          have full : Core.Steps (1+ac.cost+bc.cost+3) (.initial core e.values s) (.final bc.value s) := CostStepComposition.apply (.cons .lambda .refl) (path ac same _) (betaPath [])
          proof ac.old; proof bc.old; proof oldBody; proof cb; proof whole; proof directOld; proof full
          let d := max 2 (max ac.depth (bc.depth+1))+1
          check (decide (ac.value=.word w ∧ ac.core=.var 2 ∧ ac.cost=1 ∧ ac.depth=1 ∧ bc.depth=4 ∧ d=6 ∧
            bc.core=.ifE (if o then .ifE (.var 1) (.bool true) (.var 2) else .ifE (.var 1) (.var 2) (.bool false)) (.var 0) (.unary .wordNot (.var 0)) ∧
            bc.value=.word (if (if o then a||b else a&&b) then w else w.bitNot) ∧ bc.cost=(if (if o then a||b else a&&b) then 7 else 9) ∧
            p.value="p" ∧ Resolved.freshLocalId owner inputs.ids=sid 32)) "independent literal Word/guard/shadow/depth/cost"
          have declaration : ExpectedUnaryLambdaHeaderDeclares [] owner inputs fs (.function .word .word) ⟨inner,body,.word,.word⟩ := by rw [fsShape]; exact .lambda .inferred .omitted
          have checked := (elaborateExpectedComputationLambda?_iff elaborateLocalExpression?_iff).mpr (.lambda declaration .word .word checkedBody)
          have bodyChecked := (elaborateComputationReturnTree?_iff elaborateLocalExpression?_iff).mpr checkedBody
          have bodyImage {v z} : ClosedSourceBodyEvaluates owner inner.names (up ie) (heap s) body v z ↔
              ∃ x t, v=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates ie.values s bc.core x t := gate.core_evaluates_iff bodyChecked same1
          proof (gate.local_evaluates_iff.mp cb); proof (gate.local_evaluates_iff.mpr ⟨bc.value,s,rfl,rfl,oldBody⟩ : ClosedSourceBodyEvaluates owner inner.names (up ie) (heap s) body (RuntimeValue.ofCore bc.value) (heap s))
          for fuel in [0,bc.depth,bc.depth+1,bc.depth+4] do
            match brun : evaluateClosedSourceBody? fuel owner inner.names (up ie) (heap s) body with
            | none => check (fuel<bc.depth+1) "body adjacent exhaustion"
            | some _ => consume (Core.steps_from_initial_sound (path bc same1 [])) bodyImage (evaluateClosedSourceBody?_sound brun); check (fuel≥bc.depth+1) "body adjacent success"
          coreRuns full; coreRuns (betaPath []); coreRuns (path ac same [])
          closedRuns ac.depth ac.closed (exprImages ac same)
          closedRuns 2 madeOld (fun actual => proof (actual.deterministic madeOld))
          match made : evaluateClosedSourceExpression? 2 owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ with
          | none => throw (IO.userError "actual grouped creation")
          | some (actualClosure,creationStore) =>
            have madeEq := (evaluateClosedSourceExpression?_sound made).deterministic madeOld
            proof madeEq
            check ((match actualClosure with
              | .sourceClosure sf so sn se => sf==fs && so==owner && sn==inputs.names && se.mapM (fun r => (r.2.toCore?).map (r.1,·))==some e
              | _ => false) && creationStore.mapM RuntimeValue.toCore?==some s) "all actual saved closure fields and creation store"
            match arun : evaluateClosedSourceExpression? ac.depth owner inputs.names (up e) creationStore arg with
            | none => throw (IO.userError "actual argument after creation")
            | some (actualArg,argumentStore) =>
              have ae := evaluateClosedSourceExpression?_sound arun
              have ae0 : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) arg actualArg argumentStore := by simpa only [madeEq.2] using ae
              let argEq := ae0.deterministic ac.closed
              exprImages ac same ae0
              match brun : evaluateClosedSourceBody? (bc.depth+1) owner inner.names ((Resolved.freshLocalId owner inputs.ids,actualArg)::up e) argumentStore body with
              | none => throw (IO.userError "actual body after actual argument store")
              | some (v,z) => consume (a:=v) (z:=z) (Core.steps_from_initial_sound (path bc same1 [])) bodyImage (by simpa only [argEq.1,argEq.2,ie,up,List.map_cons] using evaluateClosedSourceBody?_sound brun)
              have fn := evaluateClosedSourceExpression?_sound made
              have argEv : ClosedSourceExpressionEvaluates owner inputs.names (up e) creationStore arg (RuntimeValue.ofCore ac.value) (heap s) := by simpa only [argEq.1,argEq.2] using ae
              have fnEval : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ (.sourceClosure fs owner inputs.names (up e)) creationStore := by simpa only [madeEq.1,saved] using fn
              closedRuns d whole (fun {a z} actual => consume (a:=a) (z:=z) (Core.steps_from_initial_sound (betaPath [])) (closedSourceExpectedDataLambda_invocation_core_iff (callSpan:=cs) (argumentsSpan:=args) shape gate checked same fnEval argEv) (by simpa only [original] using actual))
              have directImage {v z} : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) direct v z ↔ ∃ x t, v=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e.values s core x t := by
                obtain ⟨r,res,low,_⟩ := ac.elaboration; exact closedSourceExpectedDataLambda_application_core_iff shape gate checked same ac.gate res (same ▸ low)
              closedRuns d directOld (fun actual => consume (Core.steps_from_initial_sound full) directImage actual)
              let cr := rows actualClosure w
              have fetched : ClosedSourceExpressionEvaluates caller names cr creationStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ saved creationStore := by rw [← madeEq.1]; exact .reference .head (.tail (by decide) .head)
              if aw : ac.value=.word w then
                let savedCode := Core.Expr.apply (.var 0) (.var 1)
                let savedRows := [Core.Value.closure .word .word bc.core e.values,.word w]
                have savedPath : Core.Steps (1+1+bc.cost+3) (.initial savedCode savedRows s) (.final bc.value s) :=
                  CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (by simpa only [aw,Core.State.initial,Core.State.final] using betaPath [])
                coreRuns savedPath
                have argOld : ClosedSourceExpressionEvaluates caller names cr creationStore ⟨ws,.identifier ⟨wn,"w"⟩⟩ (RuntimeValue.ofCore ac.value) (heap s) := by rw [madeEq.2,aw]; simp only [RuntimeValue.ofCore]; exact .reference (.tail (by change ("picked" : String) ≠ "w"; decide) .head) .head
                have savedOld : ClosedSourceExpressionEvaluates caller names cr creationStore picked (RuntimeValue.ofCore bc.value) creationStore := by rw [savedShape]; simpa only [madeEq.2] using ClosedSourceExpressionEvaluates.call shape fetched argOld beta
                match frun : evaluateClosedSourceExpression? 1 caller names cr creationStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ with
                | none => throw (IO.userError "actual saved fetch")
                | some (actualFn,calleeStore) =>
                  have feq := (evaluateClosedSourceExpression?_sound frun).deterministic fetched
                  match sar : evaluateClosedSourceExpression? 1 caller names cr calleeStore ⟨ws,.identifier ⟨wn,"w"⟩⟩ with
                  | none => throw (IO.userError "actual saved argument")
                  | some (sa,sas) =>
                    have sae := evaluateClosedSourceExpression?_sound sar
                    have seq := (show ClosedSourceExpressionEvaluates caller names cr creationStore ⟨ws,.identifier ⟨wn,"w"⟩⟩ sa sas from by simpa only [feq.2] using sae).deterministic argOld
                    match sbr : evaluateClosedSourceBody? (bc.depth+1) owner inner.names ((Resolved.freshLocalId owner inputs.ids,sa)::up e) sas body with
                    | none => throw (IO.userError "actual saved body")
                    | some (sv,ss) => consume (a:=sv) (z:=ss) (Core.steps_from_initial_sound (path bc same1 [])) bodyImage (by simpa only [seq.1,seq.2,ie,up,List.map_cons] using evaluateClosedSourceBody?_sound sbr)
                    have sf : ClosedSourceExpressionEvaluates caller names cr creationStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ (.sourceClosure fs owner inputs.names (up e)) calleeStore := by simpa only [feq.1,saved] using evaluateClosedSourceExpression?_sound frun
                    have se : ClosedSourceExpressionEvaluates caller names cr calleeStore ⟨ws,.identifier ⟨wn,"w"⟩⟩ (RuntimeValue.ofCore ac.value) (heap s) := by simpa only [seq.1,seq.2] using sae
                    closedRuns d savedOld (fun {a z} actual => consume (a:=a) (z:=z) (Core.steps_from_initial_sound (betaPath []))
                      (closedSourceExpectedDataLambda_invocation_core_iff (callSpan:=pcs) (argumentsSpan:=pas) shape gate checked same sf se) (by simpa only [savedShape] using actual))
              else throw (IO.userError "argument Word image")
        else throw (IO.userError "whole Word return checking")
      | _ => throw (IO.userError "original single return body")
    | _ => throw (IO.userError "original inferred lambda")
  | _,_ => throw (IO.userError "original grouped/direct and saved calls")
end Tests.ParsedExpectedWordShortCircuitDataBridge
open Tests.ParsedExpectedWordShortCircuitDataBridge in
def Tests.frontendParsedExpectedWordShortCircuitDataBridgeTests : IO Unit := do
  let q := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  for o in [false,true] do
    for a in [false,true] do
      for b in [false,true] do
        for w in [Solcore.Core.Word.ofNatModulo 0,Solcore.Core.Word.ofNatModulo 1,Solcore.Core.Word.ofNatModulo (2^256-1)] do
          for s in [[],[q,.cellRef .word 900,.hostFunction .storageWrite,.unit]] do exercise o a b w q s
