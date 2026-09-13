import Solcore.Frontend.BoundedCalleeLambdaDepthDecisionProperties
import Solcore.Syntax.Parser.Term

/- Actual independent creations feed an inner call outside the data gate. Its
original witness and direct depth-three run precede every outer decision law.
All saved fields, caller payloads and complete stores remain explicit. -/
set_option autoImplicit false
namespace Tests.ParsedBoundedCalleeDepth
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def so : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedBoundedCallee",by decide⟩],by decide⟩⟩,307⟩
private def mo : Resolved.DeclarationId := {so with declarationIndex:=607}
private def co : Resolved.DeclarationId := {so with declarationIndex:=907}
private def sid (n : Nat) : Resolved.LocalId := ⟨so,n⟩
private def mid (n : Nat) : Resolved.LocalId := ⟨mo,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def mn : LocalNameTable := [("p",mid 8),("z",mid 2),("p",mid 99)]
private def sn : LocalNameTable := [("z",sid 2),("q",sid 8),("y",cid 40),("z",sid 99),("q",sid 99)]
private def sr (v core : V) (missing : Bool) (tail : Resolved.LocalScope V) :=
  (if missing then [] else [(sid 2,v),(sid 2,.unit)])++[(sid 8,core),(cid 40,core),(sid 99,.bool false)]++tail
private def cn (missing : Bool) : LocalNameTable :=
  [("f",cid 1),("x",cid 2),("z",cid 5)]++(if missing then [] else [("y",cid 3),("y",cid 99)])++[("f",cid 99)]
private def cr (maker target argument other : V) : Resolved.LocalScope V :=
  [(cid 1,maker),(cid 1,other),(cid 2,target),(cid 2,other),(cid 5,other),(cid 3,argument),(cid 3,.unit),(cid 99,other)]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (name : String) : Syntax.Expr :=
  ⟨span f a b,.identifier ⟨span f a b,name⟩⟩
private def expectedLambda (parameter key : String) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 17,.lambda (span f 0 3) ⟨span f 3 6,[⟨span f 4 5,.inferred ⟨span f 4 5,parameter⟩⟩]⟩ none
    ⟨span f 6 17,[⟨span f 7 16,.returnStmt (some (ref f 14 15 key))⟩]⟩⟩
private def expectedCall (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 7,.call ⟨span f 0 4,.call (ref f 0 1 "f") ⟨span f 1 4,[ref f 2 3 "x"]⟩⟩
    ⟨span f 4 7,[ref f 5 6 "y"]⟩⟩
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.call callee ⟨a,[argument]⟩⟩ => [s]++spans callee++[a]++spans argument
  | ⟨s,.lambda k ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨b,[⟨r,.returnStmt (some e)⟩]⟩⟩ => [s,k,ps,p,n.span,b,r]++spans e
  | _ => []
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-bounded-callee.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "bounded callee lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / zero diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==ranges) "every actual range"
    return actual
  | _ => throw (IO.userError "bounded callee parser")
private inductive Outcome (R : V → List V → Prop) (st : List V) where
  | ok (v : V) (original : R v st)
  | bad (original : ∀ v final, ¬ R v final)
private def reference (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope V)
    (st : List V) (s : Syntax.SourceSpan) (key : Syntax.Identifier) :
    Outcome (fun v final => E o n e st ⟨s,.identifier key⟩ v final) st :=
  match hn : LocalNameTable.lookup? n key.value with
  | none => .bad (by
    intro v final original; cases original with
    | creation impossible => cases impossible
    | reference named _ => have h := LocalNameTable.lookup?_iff.mpr named; rw [hn] at h; cases h)
  | some id => match he : Resolved.LocalScope.lookup? e id with
    | some v => .ok v (.reference (LocalNameTable.lookup?_iff.mp hn) (Resolved.LocalScope.lookup?_iff.mp he))
    | none => .bad (by
      intro v final original; cases original with
      | creation impossible => cases impossible
      | reference named found =>
        cases named.id_unique (LocalNameTable.lookup?_iff.mp hn)
        have h := Resolved.LocalScope.lookup?_iff.mpr found; rw [he] at h; cases h)
private def create {source : Syntax.Expr} {parameter : Syntax.Identifier} {body : Syntax.Block}
    (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope V) (st : List V)
    (shape : SourceUnaryLambdaShape source parameter body) : IO {ep : V × List V // ep=(.sourceClosure source o n e,st)} := do
  have original : E o n e st source (.sourceClosure source o n e) st := .creation shape
  proof original
  match ran : evaluateClosedSourceExpression? 1 o n e st source with
  | some (v,final) =>
    have same := (evaluateClosedSourceExpression?_sound ran).deterministic original
    proof same; return ⟨(v,final),Prod.ext same.1 same.2⟩
  | none => throw (IO.userError "actual independent creation")
private theorem rejectCall {o so n sn e se st source name body argument callee cs als}
    (shape : SourceUnaryLambdaShape source name body) (picked : E o n e st callee (.sourceClosure source so sn se) st)
    (result : Outcome (fun v final => E o n e st argument v final) st)
    (noBody : ∀ v, E o n e st argument v st → ∀ actual final,
      ¬ ClosedSourceBodyEvaluates so ((name.value,Resolved.freshLocalId so (sn.map Prod.snd))::sn)
        ((Resolved.freshLocalId so (sn.map Prod.snd),v)::se) st body actual final) :
    ∀ actual final, ¬ E o n e st ⟨cs,.call callee ⟨als,[argument]⟩⟩ actual final := by
  intro actual final original; cases original with
  | creation impossible => cases impossible
  | call actualShape actualCallee actualArgument actualBody =>
    obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic picked
    cases sameCallee; cases sameStore
    obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
      ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans (sourceUnaryLambdaShape?_iff.mpr shape)))
    cases sameName; cases sameBody
    cases result with
    | bad absent => exact absent _ _ actualArgument
    | ok v independent =>
      obtain ⟨sameArgument,sameArgumentStore⟩ := actualArgument.deterministic independent
      cases sameArgument; cases sameArgumentStore; exact noBody _ independent _ _ actualBody
private def consume {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {owner : Resolved.DeclarationId} {names : LocalNameTable} {captured : Resolved.LocalScope V}
    {n : LocalNameTable} {e : Resolved.LocalScope V} {st : List V} {cs als : Syntax.SourceSpan}
    (shape : SourceUnaryLambdaShape source name body)
    (ag : ClosedSourceDataExpression argument) (bg : ClosedSourceDataBody body)
    (selection : evaluateClosedSourceExpression? 3 co n e st callee = some (.sourceClosure source owner names captured,st))
    (result : Outcome (fun v final => E co n e st ⟨cs,.call callee ⟨als,[argument]⟩⟩ v final) st)
    (depth : Nat) (bad : Bool) : IO Unit := do
  let call : Syntax.Expr := ⟨cs,.call callee ⟨als,[argument]⟩⟩
  let bound := boundedCalleeLambdaDepthBound 3 argument body
  proof selection; check (bound==depth) "actual selected saved-body / callee maximum plus one"
  match result with
  | .bad impossible =>
    proof impossible; check bad "planned original whole-call exclusion"
    have absent := (boundedCalleeLambda_evaluate_depth_none_iff shape ag bg selection (Nat.le_refl bound)).mpr impossible
    have all := (boundedCalleeLambda_evaluate_depth_none_iff_all_budgets shape ag bg selection).mp absent
    proof absent; proof all
    proof ((boundedCalleeLambda_evaluate_depth_none_iff shape ag bg selection (Nat.le_refl bound)).mp absent)
    for budget in [0,bound-1,bound,bound+3] do
      proof (all budget); check ((evaluateClosedSourceExpression? budget co n e st call).isNone) "actual whole failure neighbors"
  | .ok value original =>
    proof original; check (!bad) "planned independently original success"
    for budget in [0,bound-1,bound,bound+3] do
      match ran : evaluateClosedSourceExpression? budget co n e st call with
      | none => check (budget<bound) "exact fixture depth"
      | some (actual,final) =>
        have actualOriginal := evaluateClosedSourceExpression?_sound ran
        proof (show actual=value ∧ final=st from actualOriginal.deterministic original)
        if enough : bound≤budget then
          proof ((boundedCalleeLambda_evaluate_at_depthBound_iff shape ag bg selection enough).mp ran)
          proof ((boundedCalleeLambda_evaluate_at_depthBound_iff shape ag bg selection enough).mpr actualOriginal)
        else throw (IO.userError "unexpected smaller-depth success")
  for extra in [0,3] do
    proof (boundedCalleeLambda_evaluate_depth_stable shape ag bg selection (Nat.le_add_right bound extra)
      (callSpan:=cs) (argumentsSpan:=als))
private def exercise (maker source whole : Syntax.Expr) (sv av core other : V) (tail : Resolved.LocalScope V)
    (callStore : List V) (mc ma : Bool) : IO Unit := do
  let se := sr sv core mc tail
  let me : Resolved.LocalScope V := [(mid 8,core),(mid 8,other),(mid 99,other),(mid 100,core)]
  match hm : maker, hs : source, hw : whole with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred mp⟩]⟩ _ ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩⟩,
    ⟨_,.lambda _ ⟨_,[⟨_,.inferred parameter⟩]⟩ _ body⟩,
    ⟨cs,.call ⟨ics,.call ⟨fs,.identifier f⟩ ⟨ials,[⟨ixs,.identifier ix⟩]⟩⟩ ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
    have makerShape : SourceUnaryLambdaShape maker mp ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ := by rw [hm]; exact .inferred
    have shape : SourceUnaryLambdaShape source parameter body := by rw [hs]; exact .inferred
    if names : f.value="f" ∧ ix.value="x" ∧ mk.value=mp.value then
      let m ← create mo mn me [core,.unit] makerShape
      let t ← create so sn se [other,.unit,core] shape
      match mm : m.val, tt : t.val with
      | (.sourceClosure ms mo mn me,mst),(.sourceClosure ts to tn te,tst) =>
        have mEqual := mm.symm.trans m.property
        have tEqual := tt.symm.trans t.property
        have mf := RuntimeValue.sourceClosure.inj (Prod.mk.inj mEqual).1
        have mshape : SourceUnaryLambdaShape ms mp ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ := mf.1.symm ▸ makerShape
        proof mf; proof (Prod.mk.inj mEqual).2; proof (Prod.mk.inj tEqual).2
        check (mo != to && mo != co && to != co && mst.length != callStore.length && tst.length != callStore.length) "two actual saved owners/creation stores versus caller"
        let closure := RuntimeValue.sourceClosure ts to tn te
        let n := cn ma; let e := cr (.sourceClosure ms mo mn me) closure av other
        let callee : Syntax.Expr := ⟨ics,.call ⟨fs,.identifier f⟩ ⟨ials,[⟨ixs,.identifier ix⟩]⟩⟩
        let fresh := Resolved.freshLocalId mo (mn.map Prod.snd)
        have beta : ClosedSourceBodyEvaluates mo ((mp.value,fresh)::mn) ((fresh,closure)::me) callStore
            ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ closure callStore :=
          .expression (.reference (names.2.2 ▸ LocalNameTable.Lookup.head) .head)
        have betaRun : evaluateClosedSourceBody? 2 mo ((mp.value,fresh)::mn) ((fresh,closure)::me) callStore
            ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ = some (closure,callStore) := by
          simp [evaluateClosedSourceBody?,evaluateClosedSourceExpression?,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,names.2.2]
        have pick : E co n e callStore ⟨fs,.identifier f⟩ (.sourceClosure ms mo mn me) callStore :=
          .reference (names.1 ▸ LocalNameTable.Lookup.head) .head
        have target : E co n e callStore ⟨ixs,.identifier ix⟩ closure callStore :=
          .reference (names.2.1 ▸ LocalNameTable.Lookup.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
        have originalInner : E co n e callStore callee closure callStore := .call mshape pick target beta
        have directInner : evaluateClosedSourceExpression? 3 co n e callStore callee = some (closure,callStore) := by
          simpa [callee,evaluateClosedSourceExpression?,n,e,cn,cr,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,
            names.1,names.2.1,show cid 1 ≠ cid 2 from by decide,sourceUnaryLambdaShape?_iff.mpr mshape] using betaRun
        have notData : ¬ ClosedSourceDataExpression callee := by intro impossible; dsimp only [callee] at impossible; cases impossible
        proof beta; proof originalInner; proof directInner; proof notData
        for budget in [0,2] do
          check ((evaluateClosedSourceExpression? budget co n e callStore callee).isNone) "independent inner depth-three boundary"
        match irun : evaluateClosedSourceExpression? 3 co n e callStore callee with
        | some (.sourceClosure actualSource actualOwner actualNames actualCaptured,cst) =>
          have equal := (evaluateClosedSourceExpression?_sound irun).deterministic originalInner
          have fields := RuntimeValue.sourceClosure.inj (equal.1.trans (Prod.mk.inj tEqual).1)
          have actualShape : SourceUnaryLambdaShape actualSource parameter body := fields.1.symm ▸ shape
          have selected : evaluateClosedSourceExpression? 3 co n e callStore callee =
              some (.sourceClosure actualSource actualOwner actualNames actualCaptured,callStore) := equal.2 ▸ irun
          have picked : E co n e callStore callee (.sourceClosure actualSource actualOwner actualNames actualCaptured) callStore := equal.1.symm ▸ originalInner
          proof fields; proof equal.2; proof picked; proof selected
          match hb : body with
          | ⟨_,[⟨_,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
            have bg : ClosedSourceDataBody body := by rw [hb]; exact .expression .reference
            match reference co n e callStore xs x with
            | .bad absent =>
              check (ma && x.value=="y") "caller argument missing while selected callee succeeds"
              match reference actualOwner actualNames actualCaptured callStore xs x with
              | .ok _ savedRead => proof savedRead
              | .bad _ => throw (IO.userError "saved y independently exists, but cannot supply caller y")
              have noCall := rejectCall (cs:=cs) (als:=als) actualShape picked (.bad absent)
                (by intro v ev; exact False.elim (absent v callStore ev))
              proof (show ∀ v final, ¬ E co n e callStore whole v final from hw ▸ noCall)
              consume actualShape .reference bg selected (.bad noCall) 4 true
            | .ok argument arg =>
              proof arg
              if hx : x.value="y" then
                if hm : ma=false then
                  have independentArgument : E co n e callStore ⟨xs,.identifier x⟩ av callStore := by
                    apply ClosedSourceExpressionEvaluates.reference (id:=cid 3) _
                      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
                    rw [hx]
                    change LocalNameTable.Lookup (cn ma) "y" (cid 3)
                    rw [hm]; exact .tail (by decide) (.tail (by decide) (.tail (by decide) .head))
                  proof (arg.deterministic independentArgument)
                else throw (IO.userError "missing caller argument cannot succeed")
              else throw (IO.userError "actual fixed caller argument y")
              let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
              let bn := (parameter.value,fresh)::actualNames; let be := (fresh,argument)::actualCaptured
              match reference actualOwner bn be callStore ys key with
              | .bad absent =>
                have noBody : ∀ v final, ¬ ClosedSourceBodyEvaluates actualOwner bn be callStore body v final := by
                  intro v final original; rw [hb] at original; cases original with | expression child => exact absent _ _ child
                have noCall := rejectCall (cs:=cs) (als:=als) actualShape picked (.ok argument arg) (by
                  intro v ev; obtain ⟨same,_⟩ := ev.deterministic arg; cases same; exact noBody)
                proof noBody; check (mc && key.value=="z") "actual selected body fails, no alternate callee fallback"
                proof (show ∀ v final, ¬ E co n e callStore whole v final from hw ▸ noCall)
                consume actualShape .reference bg selected (.bad noCall) 4 true
              | .ok value child =>
                if same : key.value=parameter.value then
                  have freshRead : E actualOwner bn be callStore ⟨ys,.identifier key⟩ argument callStore :=
                    .reference (same ▸ LocalNameTable.Lookup.head) .head
                  proof (child.deterministic freshRead)
                else if hy : key.value="z" then
                  if hp : parameter.value="q" then
                    if hm : mc=false then
                      have savedRead : E actualOwner bn be callStore ⟨ys,.identifier key⟩ sv callStore := by
                        rcases fields with ⟨_,rfl,rfl,rfl⟩
                        apply ClosedSourceExpressionEvaluates.reference (id:=sid 2) _ (Resolved.LocalScope.Lookup.tail (by decide) ?_)
                        · rw [hy]; exact .tail (by simpa only [hp] using (by decide : "q" ≠ "z")) .head
                        · change Resolved.LocalScope.Lookup (sr sv core mc tail) (sid 2) sv
                          rw [hm]; exact .head
                      proof (child.deterministic savedRead)
                    else throw (IO.userError "missing selected saved capture cannot succeed")
                  else throw (IO.userError "actual saved parameter q")
                else throw (IO.userError "actual selected saved free reference z")
                have originalBody : ClosedSourceBodyEvaluates actualOwner bn be callStore body value callStore := by
                  rw [hb]; exact .expression child
                have originalCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape picked arg originalBody
                proof originalBody; proof (show E co n e callStore whole value callStore from hw ▸ originalCall)
                match brun : evaluateClosedSourceBody? 2 actualOwner bn be callStore body with
                | some (bv,bs) =>
                  have actualBody := evaluateClosedSourceBody?_sound brun
                  proof (actualBody.deterministic originalBody)
                  have actualCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape picked arg actualBody
                  have sameStore := (actualBody.deterministic originalBody).2
                  consume actualShape .reference bg selected (.ok bv (sameStore ▸ actualCall)) 4 false
                | none => throw (IO.userError "actual selected saved body must succeed")
          | _ => throw (IO.userError "actual saved body reference")
        | _ => throw (IO.userError "actual inner call must return the independently created target")
      | _,_ => throw (IO.userError "two actual source closure creations")
    else throw (IO.userError "actual f/x and identity maker return")
  | _,_,_ => throw (IO.userError "two saved lambdas and actual f(x)(y)")
end Tests.ParsedBoundedCalleeDepth
open Solcore Solcore.Frontend Tests.ParsedBoundedCalleeDepth in
def Tests.frontendParsedBoundedCalleeDepthTests : IO Unit := do
  let ranges := [(0,17),(0,3),(3,6),(4,5),(4,5),(6,17),(7,16),(14,15),(14,15)]
  let p ← parsed "lam(p){return p;}" (expectedLambda "p" "p") ranges
  let q ← parsed "lam(q){return q;}" (expectedLambda "q" "q") ranges
  let z ← parsed "lam(q){return z;}" (expectedLambda "q" "z") ranges
  let whole ← parsed "f(x)(y)" expectedCall [(0,7),(0,4),(0,1),(0,1),(1,4),(2,3),(2,3),(4,7),(5,6),(5,6)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let other := RuntimeValue.sourceClosure p co [("p",cid 77),("p",cid 88)] [(cid 77,core),(cid 77,.word Core.Word.maximum)]
  let mut count := 0
  for (sv,av) in [(other,RuntimeValue.pair (.word Core.Word.maximum) core),(core,other),
      (RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef .word 900),(RuntimeValue.pair core other,RuntimeValue.bool false)] do
    for (tail,st) in [([],[]),([(sid 8,other),(sid 100,core),(cid 40,other)],
        [other,core,RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef .word 900])] do
      for (target,mc,ma) in [(q,false,false),(z,false,false),(z,true,false),(q,false,true)] do
        exercise p target whole sv av core other tail st mc ma
        count := count+1
  check (count==32) "four higher-order outcomes / four mixed payload pairs / two full contexts"
