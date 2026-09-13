import Solcore.Frontend.BoundedInputsLambdaDepthDecisionProperties
import Solcore.Syntax.Parser.Term

/- Both supplied finite input runs precede every outer decision law. The actual
callee store feeds g(x); its actual endpoint feeds the selected fresh saved body.
No data gate for the call argument, nor a decision for unsuccessful inputs. -/
set_option autoImplicit false
namespace Tests.ParsedBoundedInputsDepth
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def so : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedBoundedInputs",by decide⟩],by decide⟩⟩,308⟩
private def mo : Resolved.DeclarationId := {so with declarationIndex:=608}
private def co : Resolved.DeclarationId := {so with declarationIndex:=908}
private def sid (n : Nat) : Resolved.LocalId := ⟨so,n⟩
private def mid (n : Nat) : Resolved.LocalId := ⟨mo,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def mn : LocalNameTable := [("p",mid 8),("z",mid 2),("p",mid 99)]
private def sn : LocalNameTable := [("z",sid 2),("q",sid 8),("x",cid 40),("z",sid 99),("q",sid 99)]
private def sr (v core : V) (missing : Bool) (tail : Resolved.LocalScope V) :=
  (if missing then [] else [(sid 2,v),(sid 2,.unit)])++[(sid 8,core),(cid 40,core),(sid 99,.bool false)]++tail
private def cn : LocalNameTable := [("f",cid 1),("g",cid 2),("x",cid 3),("z",cid 5),("f",cid 99),("x",cid 99)]
private def cr (target maker argument other : V) : Resolved.LocalScope V :=
  [(cid 1,target),(cid 1,other),(cid 2,maker),(cid 2,other),(cid 3,argument),(cid 3,.unit),(cid 5,other),(cid 99,other)]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (name : String) : Syntax.Expr :=
  ⟨span f a b,.identifier ⟨span f a b,name⟩⟩
private def expectedLambda (parameter key : String) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 17,.lambda (span f 0 3) ⟨span f 3 6,[⟨span f 4 5,.inferred ⟨span f 4 5,parameter⟩⟩]⟩ none
    ⟨span f 6 17,[⟨span f 7 16,.returnStmt (some (ref f 14 15 key))⟩]⟩⟩
private def expectedCall (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 7,.call (ref f 0 1 "f") ⟨span f 1 7,
    [⟨span f 2 6,.call (ref f 2 3 "g") ⟨span f 3 6,[ref f 4 5 "x"]⟩⟩]⟩⟩
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.call callee ⟨a,[argument]⟩⟩ => [s]++spans callee++[a]++spans argument
  | ⟨s,.lambda k ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨b,[⟨r,.returnStmt (some e)⟩]⟩⟩ => [s,k,ps,p,n.span,b,r]++spans e
  | _ => []
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-bounded-inputs.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "bounded inputs lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / zero diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==ranges) "every actual range"
    return actual
  | _ => throw (IO.userError "bounded inputs parser")
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
private theorem rejectCall {o so n sn e se st cst ast source name body argument callee cs als av}
    (shape : SourceUnaryLambdaShape source name body) (picked : E o n e st callee (.sourceClosure source so sn se) cst)
    (supplied : E o n e cst argument av ast)
    (noBody : ∀ actual final, ¬ ClosedSourceBodyEvaluates so
      ((name.value,Resolved.freshLocalId so (sn.map Prod.snd))::sn)
      ((Resolved.freshLocalId so (sn.map Prod.snd),av)::se) ast body actual final) :
    ∀ actual final, ¬ E o n e st ⟨cs,.call callee ⟨als,[argument]⟩⟩ actual final := by
  intro actual final original; cases original with
  | creation impossible => cases impossible
  | call actualShape actualCallee actualArgument actualBody =>
    obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic picked
    cases sameCallee; cases sameStore
    obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
      ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans (sourceUnaryLambdaShape?_iff.mpr shape)))
    cases sameName; cases sameBody
    obtain ⟨sameArgument,sameArgumentStore⟩ := actualArgument.deterministic supplied
    cases sameArgument; cases sameArgumentStore; exact noBody _ _ actualBody
private def consume {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {owner : Resolved.DeclarationId} {names : LocalNameTable} {captured : Resolved.LocalScope V}
    {n : LocalNameTable} {e : Resolved.LocalScope V} {st cst ast finalStore : List V} {cs als : Syntax.SourceSpan} {av : V}
    (shape : SourceUnaryLambdaShape source name body) (bg : ClosedSourceDataBody body)
    (selected : evaluateClosedSourceExpression? 1 co n e st callee = some (.sourceClosure source owner names captured,cst))
    (supplied : evaluateClosedSourceExpression? 3 co n e cst argument = some (av,ast))
    (result : Outcome (fun v final => E co n e st ⟨cs,.call callee ⟨als,[argument]⟩⟩ v final) finalStore)
    (bad : Bool) : IO Unit := do
  let call : Syntax.Expr := ⟨cs,.call callee ⟨als,[argument]⟩⟩
  let bound := boundedInputsLambdaDepthBound 1 3 body
  proof selected; proof supplied; check (bound==4) "actual saved body / two supplied input budgets"
  match result with
  | .bad impossible =>
    proof impossible; check bad "planned original whole-call exclusion despite successful inputs"
    have absent := (boundedInputsLambda_evaluate_depth_none_iff shape bg selected supplied (Nat.le_refl bound)).mpr impossible
    have all := (boundedInputsLambda_evaluate_depth_none_iff_all_budgets shape bg selected supplied).mp absent
    proof absent; proof all
    proof ((boundedInputsLambda_evaluate_depth_none_iff shape bg selected supplied (Nat.le_refl bound)).mp absent)
    for budget in [0,bound-1,bound,bound+3] do
      proof (all budget); check ((evaluateClosedSourceExpression? budget co n e st call).isNone) "actual failure neighbors"
  | .ok value original =>
    proof original; check (!bad) "planned independent original success"
    for budget in [0,bound-1,bound,bound+3] do
      match ran : evaluateClosedSourceExpression? budget co n e st call with
      | none => check (budget<bound) "exact fixture depth"
      | some (actual,final) =>
        have actualOriginal := evaluateClosedSourceExpression?_sound ran
        proof (show actual=value ∧ final=finalStore from actualOriginal.deterministic original)
        if enough : bound≤budget then
          proof ((boundedInputsLambda_evaluate_at_depthBound_iff shape bg selected supplied enough).mp ran)
          proof ((boundedInputsLambda_evaluate_at_depthBound_iff shape bg selected supplied enough).mpr actualOriginal)
        else throw (IO.userError "unexpected smaller-depth success")
  for extra in [0,3] do
    proof (boundedInputsLambda_evaluate_depth_stable shape bg selected supplied (Nat.le_add_right bound extra)
      (callSpan:=cs) (argumentsSpan:=als))
private def exercise (maker source whole : Syntax.Expr) (sv av core other : V) (tail : Resolved.LocalScope V)
    (callStore : List V) (mc : Bool) : IO Unit := do
  let se := sr sv core mc tail
  let me : Resolved.LocalScope V := [(mid 8,core),(mid 8,other),(mid 99,other),(mid 100,core)]
  match hm : maker, hs : source, hw : whole with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred mp⟩]⟩ _ ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩⟩,
    ⟨_,.lambda _ ⟨_,[⟨_,.inferred parameter⟩]⟩ _ body⟩,
    ⟨cs,.call ⟨fs,.identifier f⟩ ⟨als,[⟨ics,.call ⟨gs,.identifier g⟩ ⟨ials,[⟨xs,.identifier x⟩]⟩⟩]⟩⟩ =>
    have makerShape : SourceUnaryLambdaShape maker mp ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ := by rw [hm]; exact .inferred
    have shape : SourceUnaryLambdaShape source parameter body := by rw [hs]; exact .inferred
    if names : f.value="f" ∧ g.value="g" ∧ x.value="x" ∧ mk.value=mp.value then
      let m ← create mo mn me [core,.unit] makerShape
      let t ← create so sn se [other,.unit,core] shape
      match mm : m.val, tt : t.val with
      | (.sourceClosure ms mo mn me,mst),(.sourceClosure ts to tn te,tst) =>
        have mEqual := mm.symm.trans m.property; have tEqual := tt.symm.trans t.property
        have mf := RuntimeValue.sourceClosure.inj (Prod.mk.inj mEqual).1
        have mshape : SourceUnaryLambdaShape ms mp ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ := mf.1.symm ▸ makerShape
        proof mf; proof (Prod.mk.inj mEqual).2; proof (Prod.mk.inj tEqual).2
        check (mo != to && mo != co && to != co && mst.length != callStore.length && tst.length != callStore.length) "two actual saved owners/creation stores versus caller"
        let n := cn; let e := cr (.sourceClosure ts to tn te) (.sourceClosure ms mo mn me) av other
        let callee : Syntax.Expr := ⟨fs,.identifier f⟩
        let argument : Syntax.Expr := ⟨ics,.call ⟨gs,.identifier g⟩ ⟨ials,[⟨xs,.identifier x⟩]⟩⟩
        have originalPick : E co n e callStore callee (.sourceClosure ts to tn te) callStore :=
          .reference (names.1 ▸ LocalNameTable.Lookup.head) .head
        proof originalPick
        match crun : evaluateClosedSourceExpression? 1 co n e callStore callee with
        | some (.sourceClosure actualSource actualOwner actualNames actualCaptured,cst) =>
          have equal := (evaluateClosedSourceExpression?_sound crun).deterministic originalPick
          have fields := RuntimeValue.sourceClosure.inj (equal.1.trans (Prod.mk.inj tEqual).1)
          have actualShape : SourceUnaryLambdaShape actualSource parameter body := fields.1.symm ▸ shape
          have picked : E co n e callStore callee (.sourceClosure actualSource actualOwner actualNames actualCaptured) cst := by
            rw [equal.1,equal.2]; exact originalPick
          proof fields; proof equal.2; proof picked; proof crun
          let fresh := Resolved.freshLocalId mo (mn.map Prod.snd)
          have beta : ClosedSourceBodyEvaluates mo ((mp.value,fresh)::mn) ((fresh,av)::me) cst
              ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ av cst :=
            .expression (.reference (names.2.2.2 ▸ LocalNameTable.Lookup.head) .head)
          have betaRun : evaluateClosedSourceBody? 2 mo ((mp.value,fresh)::mn) ((fresh,av)::me) cst
              ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ = some (av,cst) := by
            simp [evaluateClosedSourceBody?,evaluateClosedSourceExpression?,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,names.2.2.2]
          have gPick : E co n e cst ⟨gs,.identifier g⟩ (.sourceClosure ms mo mn me) cst :=
            .reference (names.2.1 ▸ LocalNameTable.Lookup.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
          have xPick : E co n e cst ⟨xs,.identifier x⟩ av cst :=
            .reference (names.2.2.1 ▸ LocalNameTable.Lookup.tail (by decide) (.tail (by decide) .head))
              (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
          have originalInner : E co n e cst argument av cst := .call mshape gPick xPick beta
          have directInner : evaluateClosedSourceExpression? 3 co n e cst argument = some (av,cst) := by
            simpa [argument,evaluateClosedSourceExpression?,n,e,cn,cr,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,
              names.2.1,names.2.2.1,show cid 1 ≠ cid 2 from by decide,show cid 1 ≠ cid 3 from by decide,
              show cid 2 ≠ cid 3 from by decide,sourceUnaryLambdaShape?_iff.mpr mshape] using betaRun
          have notData : ¬ ClosedSourceDataExpression argument := by intro impossible; dsimp only [argument] at impossible; cases impossible
          proof beta; proof gPick; proof xPick; proof originalInner; proof directInner; proof notData
          match xrun : evaluateClosedSourceExpression? 1 co n e cst ⟨xs,.identifier x⟩ with
          | some (_,_) => proof ((evaluateClosedSourceExpression?_sound xrun).deterministic xPick)
          | none => throw (IO.userError "planned caller x must succeed independently")
          for budget in [0,2] do
            check ((evaluateClosedSourceExpression? budget co n e cst argument).isNone) "independent inner argument depth three"
          match arun : evaluateClosedSourceExpression? 3 co n e cst argument with
          | some (argumentValue,ast) =>
            have aequal := (evaluateClosedSourceExpression?_sound arun).deterministic originalInner
            have argumentOriginal : E co n e cst argument argumentValue ast := by rw [aequal.1,aequal.2]; exact originalInner
            proof aequal; proof argumentOriginal; proof arun
            match hb : body with
            | ⟨_,[⟨_,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
              have bg : ClosedSourceDataBody body := by rw [hb]; exact .expression .reference
              let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
              let bn := (parameter.value,fresh)::actualNames; let be := (fresh,argumentValue)::actualCaptured
              match reference actualOwner bn be ast ys key with
              | .bad absent =>
                have noBody : ∀ v final, ¬ ClosedSourceBodyEvaluates actualOwner bn be ast body v final := by
                  intro v final original; rw [hb] at original; cases original with | expression child => exact absent _ _ child
                have noCall := rejectCall (cs:=cs) (als:=als) actualShape picked argumentOriginal noBody
                proof noBody; check ((mc && key.value=="z") || key.value=="w") "missing selected capture/name after two successful inputs"
                proof (show ∀ v final, ¬ E co n e callStore whole v final from hw ▸ noCall)
                consume (finalStore:=ast) actualShape bg crun arun (.bad noCall) true
              | .ok value child =>
                if same : key.value=parameter.value then
                  have freshRead : E actualOwner bn be ast ⟨ys,.identifier key⟩ argumentValue ast :=
                    .reference (same ▸ LocalNameTable.Lookup.head) .head
                  proof (child.deterministic freshRead)
                else if hy : key.value="z" then
                  if hp : parameter.value="q" then
                    if hmc : mc=false then
                      have savedRead : E actualOwner bn be ast ⟨ys,.identifier key⟩ sv ast := by
                        rcases fields with ⟨_,rfl,rfl,rfl⟩
                        apply ClosedSourceExpressionEvaluates.reference (id:=sid 2) _ (Resolved.LocalScope.Lookup.tail (by decide) ?_)
                        · rw [hy]; exact .tail (by simpa only [hp] using (by decide : "q" ≠ "z")) .head
                        · change Resolved.LocalScope.Lookup (sr sv core mc tail) (sid 2) sv
                          rw [hmc]; exact .head
                      proof (child.deterministic savedRead)
                    else throw (IO.userError "missing selected saved capture cannot succeed")
                  else throw (IO.userError "actual saved parameter q")
                else throw (IO.userError "actual selected saved free reference z")
                have originalBody : ClosedSourceBodyEvaluates actualOwner bn be ast body value ast := by rw [hb]; exact .expression child
                have originalCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape picked argumentOriginal originalBody
                proof originalBody; proof (show E co n e callStore whole value ast from hw ▸ originalCall)
                match brun : evaluateClosedSourceBody? 2 actualOwner bn be ast body with
                | some (bv,bs) =>
                  have actualBody := evaluateClosedSourceBody?_sound brun
                  proof (actualBody.deterministic originalBody)
                  have actualCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape picked argumentOriginal actualBody
                  consume actualShape bg crun arun (.ok bv actualCall) false
                | none => throw (IO.userError "actual selected saved body must succeed")
            | _ => throw (IO.userError "actual saved body reference")
          | none => throw (IO.userError "actual inner argument must preserve the independent caller payload")
        | _ => throw (IO.userError "actual callee must select the independently created target")
      | _,_ => throw (IO.userError "two actual source closure creations")
    else throw (IO.userError "actual f/g/x and identity maker return")
  | _,_,_ => throw (IO.userError "two saved lambdas and actual f(g(x))")
end Tests.ParsedBoundedInputsDepth
open Solcore Solcore.Frontend Tests.ParsedBoundedInputsDepth in
def Tests.frontendParsedBoundedInputsDepthTests : IO Unit := do
  let ranges := [(0,17),(0,3),(3,6),(4,5),(4,5),(6,17),(7,16),(14,15),(14,15)]
  let p ← parsed "lam(p){return p;}" (expectedLambda "p" "p") ranges
  let q ← parsed "lam(q){return q;}" (expectedLambda "q" "q") ranges
  let z ← parsed "lam(q){return z;}" (expectedLambda "q" "z") ranges
  let w ← parsed "lam(q){return w;}" (expectedLambda "q" "w") ranges
  let whole ← parsed "f(g(x))" expectedCall [(0,7),(0,1),(0,1),(1,7),(2,6),(2,3),(2,3),(3,6),(4,5),(4,5)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let other := RuntimeValue.sourceClosure p co [("p",cid 77),("p",cid 88)] [(cid 77,core),(cid 77,.word Core.Word.maximum)]
  let mut count := 0
  for (sv,av) in [(other,RuntimeValue.pair (.word Core.Word.maximum) core),(core,other),
      (RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef .word 900),(RuntimeValue.pair core other,RuntimeValue.bool false)] do
    for (tail,st) in [([],[]),([(sid 8,other),(sid 100,core),(cid 40,other)],
        [other,core,RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef .word 900])] do
      for (target,mc) in [(q,false),(z,false),(z,true),(w,false)] do
        exercise p target whole sv av core other tail st mc
        count := count+1
  check (count==32) "four saved-body outcomes / four mixed payload pairs / two full contexts"
