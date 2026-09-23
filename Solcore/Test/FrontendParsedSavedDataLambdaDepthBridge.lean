import Solcore.Frontend.SavedDataLambdaDepth
import Solcore.Syntax.Parser.Term

/- Actual saved creation fields feed first-match caller pickup. Original lookup,
argument and fresh saved-body witnesses or exclusions precede depth decisions.
Creation stores differ from invocation stores; no typing or Core-cost claim. -/
set_option autoImplicit false
namespace Tests.ParsedSavedDataLambdaDepth
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def savedOwner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedSavedDepth",by decide⟩],by decide⟩⟩,305⟩
private def callerOwner : Resolved.DeclarationId := {savedOwner with declarationIndex:=905}
private def sid (n : Nat) : Resolved.LocalId := ⟨savedOwner,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨callerOwner,n⟩
private def savedNames : LocalNameTable := [("y",sid 2),("p",sid 8),("x",cid 40),("y",sid 99),("p",sid 99)]
private def savedRows (v core : V) (missing : Bool) (tail : Resolved.LocalScope V) :=
  (if missing then [] else [(sid 2,v),(sid 2,.unit)])++[(sid 8,core),(cid 40,core),(sid 99,.bool false)]++tail
private def callerNames (missing : Bool) : LocalNameTable :=
  [("f",cid 1)]++(if missing then [] else [("x",cid 2),("x",cid 99)])++[("y",cid 3),("f",cid 99)]
private def callerRows (closure argument core : V) : Resolved.LocalScope V :=
  [(cid 1,closure),(cid 1,core),(cid 2,argument),(cid 2,.unit),(cid 3,.word Core.Word.maximum),(cid 99,core)]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (name : String) : Syntax.Expr :=
  ⟨span f a b,.identifier ⟨span f a b,name⟩⟩
private def expectedLambda (key : String) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 17,.lambda (span f 0 3) ⟨span f 3 6,[⟨span f 4 5,.inferred ⟨span f 4 5,"p"⟩⟩]⟩ none
    ⟨span f 6 17,[⟨span f 7 16,.returnStmt (some (ref f 14 15 key))⟩]⟩⟩
private def expectedCall (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 4,.call (ref f 0 1 "f") ⟨span f 1 4,[ref f 2 3 "x"]⟩⟩
private def refSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span] | _ => []
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.lambda k ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨b,[⟨r,.returnStmt (some e)⟩]⟩⟩ =>
    [s,k,ps,p,n.span,b,r]++refSpans e
  | ⟨s,.call callee ⟨a,[argument]⟩⟩ => [s]++refSpans callee++[a]++refSpans argument
  | _ => []
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr)
    (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-saved-data-depth.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "saved depth lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / diagnostics zero"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==ranges) "every actual saved and caller span"
    return actual
  | _ => throw (IO.userError "saved depth parser")
private inductive Outcome (R : V → List V → Prop) (st : List V) where
  | ok (v : V) (original : R v st)
  | bad (original : ∀ v final, ¬ R v final)
private def reference (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope V)
    (st : List V) (s : Syntax.SourceSpan) (key : Syntax.Identifier) :
    Outcome (fun v final => E o n e st ⟨s,.identifier key⟩ v final) st :=
  match hn : LocalNameTable.lookup? n key.value with
  | none => .bad (by
    intro v final original
    cases original with
    | creation impossible => cases impossible
    | reference named _ => have h := LocalNameTable.lookup?_iff.mpr named; rw [hn] at h; cases h)
  | some id => match he : Resolved.LocalScope.lookup? e id with
    | some v => .ok v (.reference (LocalNameTable.lookup?_iff.mp hn) (Resolved.LocalScope.lookup?_iff.mp he))
    | none => .bad (by
      intro v final original
      cases original with
      | creation impossible => cases impossible
      | reference named found =>
        cases named.id_unique (LocalNameTable.lookup?_iff.mp hn)
        have h := Resolved.LocalScope.lookup?_iff.mpr found; rw [he] at h; cases h)
private theorem rejectCall {o so n sn e se st source name body argument callee cs als}
    (shape : SourceUnaryLambdaShape source name body)
    (picked : E o n e st callee (.sourceClosure source so sn se) st)
    (result : Outcome (fun v final => E o n e st argument v final) st)
    (noBody : ∀ v, E o n e st argument v st → ∀ actual final,
      ¬ ClosedSourceBodyEvaluates so ((name.value,Resolved.freshLocalId so (sn.map Prod.snd))::sn)
        ((Resolved.freshLocalId so (sn.map Prod.snd),v)::se) st body actual final) :
    ∀ actual final, ¬ E o n e st ⟨cs,.call callee ⟨als,[argument]⟩⟩ actual final := by
  intro actual final original
  cases original with
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
      cases sameArgument; cases sameArgumentStore
      exact noBody _ independent _ _ actualBody
private def consume {source argument : Syntax.Expr} {name calleeName : Syntax.Identifier} {body : Syntax.Block}
    {so : Resolved.DeclarationId} {sn : LocalNameTable} {se : Resolved.LocalScope V}
    {n : LocalNameTable} {e : Resolved.LocalScope V} {st : List V} {id : Resolved.LocalId}
    {cs fs als : Syntax.SourceSpan} (shape : SourceUnaryLambdaShape source name body)
    (ag : ClosedSourceDataExpression argument) (bg : ClosedSourceDataBody body)
    (named : LocalNameTable.Lookup n calleeName.value id)
    (found : Resolved.LocalScope.Lookup e id (.sourceClosure source so sn se))
    (result : Outcome (fun v final => E callerOwner n e st
      ⟨cs,.call ⟨fs,.identifier calleeName⟩ ⟨als,[argument]⟩⟩ v final) st) (bad : Bool) : IO Unit := do
  let call : Syntax.Expr := ⟨cs,.call ⟨fs,.identifier calleeName⟩ ⟨als,[argument]⟩⟩
  let bound := savedDataLambdaDepthBound argument body
  check (bound==3) "actual saved return-reference bound three"
  match result with
  | .bad impossible =>
    proof impossible; check bad "planned original lexical failure"
    have absent := (savedDataLambda_evaluate_depth_none_iff shape ag bg named found (Nat.le_refl bound)).mpr impossible
    have all := (savedDataLambda_evaluate_depth_none_iff_all_budgets shape ag bg named found).mp absent
    proof absent; proof all
    proof ((savedDataLambda_evaluate_depth_none_iff shape ag bg named found (Nat.le_refl bound)).mp absent)
    for budget in [0,bound-1,bound,bound+3] do
      proof (all budget)
      check ((evaluateClosedSourceExpression? budget callerOwner n e st call).isNone) "actual all-budget negative neighbors"
  | .ok value original =>
    proof original; check (!bad) "planned independent original success"
    for budget in [0,bound-1,bound,bound+3] do
      match ran : evaluateClosedSourceExpression? budget callerOwner n e st call with
      | none => check (budget<bound) "exact saved return-reference depth"
      | some (actual,final) =>
        have actualOriginal := evaluateClosedSourceExpression?_sound ran
        proof (actualOriginal.deterministic original)
        proof (show actual=value ∧ final=st from actualOriginal.deterministic original)
        if enough : bound≤budget then
          proof ((savedDataLambda_evaluate_at_depthBound_iff shape ag bg named found enough).mp ran)
          proof ((savedDataLambda_evaluate_at_depthBound_iff shape ag bg named found enough).mpr actualOriginal)
        else throw (IO.userError "unexpected smaller-depth success")
  for extra in [0,3] do
    proof (savedDataLambda_evaluate_depth_stable shape ag bg named found (Nat.le_add_right bound extra)
      (callerOwner:=callerOwner) (initialStore:=st) (callSpan:=cs) (calleeSpan:=fs) (argumentsSpan:=als))
private def exercise (source whole : Syntax.Expr) (savedValue argument core : V)
    (tail : Resolved.LocalScope V) (creationStore callStore : List V) (missingCapture missingArgument : Bool) : IO Unit := do
  let se := savedRows savedValue core missingCapture tail
  match hs : source, hw : whole with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred parameter⟩]⟩ _ body⟩,
      ⟨cs,.call ⟨fs,.identifier callee⟩ ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
    if hf : callee.value="f" then
      have shape : SourceUnaryLambdaShape source parameter body := by rw [hs]; exact .inferred
      have created : E savedOwner savedNames se creationStore source
          (.sourceClosure source savedOwner savedNames se) creationStore := .creation shape
      proof created
      match made : evaluateClosedSourceExpression? 1 savedOwner savedNames se creationStore source with
      | some (.sourceClosure actualSource actualOwner actualNames actualCaptured,actualCreationStore) =>
        have equal := (evaluateClosedSourceExpression?_sound made).deterministic created
        have fields := RuntimeValue.sourceClosure.inj equal.1
        have actualShape : SourceUnaryLambdaShape actualSource parameter body := fields.1.symm ▸ shape
        proof fields; proof equal.2
        check (actualOwner != callerOwner && creationStore.length != callStore.length)
          "actual saved owner and creation store remain distinct from caller and invocation"
        let closure := RuntimeValue.sourceClosure actualSource actualOwner actualNames actualCaptured
        let n := callerNames missingArgument
        let e := callerRows closure argument core
        have named : LocalNameTable.Lookup n callee.value (cid 1) := hf ▸ LocalNameTable.Lookup.head
        have found : Resolved.LocalScope.Lookup e (cid 1) closure := .head
        have picked : E callerOwner n e callStore ⟨fs,.identifier callee⟩ closure callStore := .reference named found
        proof picked
        let ar := reference callerOwner n e callStore xs x
        match hb : body with
        | ⟨bs,[⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
          have bg : ClosedSourceDataBody body := by rw [hb]; exact .expression .reference
          let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
          match ar with
          | .bad absent =>
            check (missingArgument && x.value=="x") "planned caller x absence despite saved x"
            match reference actualOwner actualNames actualCaptured callStore xs x with
            | .ok _ savedRead => proof savedRead
            | .bad _ => throw (IO.userError "saved x must independently exist")
            have noCall := rejectCall (cs:=cs) (als:=als) actualShape picked (.bad absent) (by intro v ev; exact False.elim (absent v callStore ev))
            proof (show ∀ v final, ¬ E callerOwner n e callStore whole v final from hw ▸ noCall)
            consume actualShape .reference bg named found (.bad noCall) true
          | .ok av arg =>
            proof arg
            if hx : x.value="x" then
              if hm : missingArgument=false then
                have independentArgument : E callerOwner n e callStore ⟨xs,.identifier x⟩ argument callStore := by
                  apply ClosedSourceExpressionEvaluates.reference _ (.tail (by decide) (.tail (by decide) .head))
                  rw [hx]
                  change LocalNameTable.Lookup (callerNames missingArgument) "x" (cid 2)
                  rw [hm]
                  exact .tail (by decide) .head
                proof (arg.deterministic independentArgument)
              else throw (IO.userError "missing caller argument cannot succeed")
            else throw (IO.userError "actual fixed caller argument x")
            let bn := (parameter.value,fresh)::actualNames
            let be := (fresh,av)::actualCaptured
            match reference actualOwner bn be callStore ys key with
            | .bad absent =>
              have noBody : ∀ actual final, ¬ ClosedSourceBodyEvaluates actualOwner bn be callStore body actual final := by
                intro actual final original; rw [hb] at original
                cases original with | expression child => exact absent _ _ child
              have noCall := rejectCall (cs:=cs) (als:=als) actualShape picked (.ok av arg) (by
                intro v ev; obtain ⟨same,_⟩ := ev.deterministic arg; cases same; exact noBody)
              proof noBody
              check (missingCapture && key.value=="y") "saved capture absence is not filled by caller y"
              match reference callerOwner n e callStore ys key with
              | .ok _ callerRead => proof callerRead
              | .bad _ => throw (IO.userError "caller y must independently exist")
              proof (show ∀ v final, ¬ E callerOwner n e callStore whole v final from hw ▸ noCall)
              consume actualShape .reference bg named found (.bad noCall) true
            | .ok value child =>
              have originalBody : ClosedSourceBodyEvaluates actualOwner bn be callStore body value callStore := by
                rw [hb]; exact .expression child
              proof originalBody
              if same : key.value=parameter.value then
                have freshReference : E actualOwner bn be callStore ⟨ys,.identifier key⟩ av callStore :=
                  .reference (same ▸ LocalNameTable.Lookup.head) .head
                proof (child.deterministic freshReference)
              else if hy : key.value="y" then
                if hp : parameter.value="p" then
                  if hm : missingCapture=false then
                    have freeReference : E actualOwner bn be callStore ⟨ys,.identifier key⟩ savedValue callStore := by
                      rcases fields with ⟨_,rfl,rfl,rfl⟩
                      apply ClosedSourceExpressionEvaluates.reference (id:=sid 2) _ (Resolved.LocalScope.Lookup.tail (by decide) ?_)
                      · rw [hy]
                        exact .tail (by simpa only [hp] using (by decide : "p" ≠ "y")) .head
                      · change Resolved.LocalScope.Lookup (savedRows savedValue core missingCapture tail) (sid 2) savedValue
                        rw [hm]
                        exact .head
                    proof (child.deterministic freeReference)
                  else throw (IO.userError "missing saved capture cannot succeed")
                else throw (IO.userError "actual saved parameter p")
              else throw (IO.userError "actual saved free key y")
              have originalCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape picked arg originalBody
              proof (show E callerOwner n e callStore whole value callStore from hw ▸ originalCall)
              match brun : evaluateClosedSourceBody? 2 actualOwner bn be callStore body with
              | some (bv,bs) =>
                have actualBody := evaluateClosedSourceBody?_sound brun
                proof (actualBody.deterministic originalBody)
                proof (show bv=value ∧ bs=callStore from actualBody.deterministic originalBody)
                have actualCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape picked arg actualBody
                have sameStore := (actualBody.deterministic originalBody).2
                consume actualShape .reference bg named found (.ok bv (sameStore ▸ actualCall)) false
              | none => throw (IO.userError "actual saved body should succeed")
        | _ => throw (IO.userError "actual saved return reference")
      | _ => throw (IO.userError "actual original creation closure")
    else throw (IO.userError "actual callee f")
  | _,_ => throw (IO.userError "actual saved source and fixed caller syntax")
end Tests.ParsedSavedDataLambdaDepth
open Solcore Solcore.Frontend Tests.ParsedSavedDataLambdaDepth in
def Tests.frontendParsedSavedDataLambdaDepthTests : IO Unit := do
  let parameter ← parsed "lam(p){return p;}" (expectedLambda "p")
    [(0,17),(0,3),(3,6),(4,5),(4,5),(6,17),(7,16),(14,15),(14,15)]
  let free ← parsed "lam(p){return y;}" (expectedLambda "y")
    [(0,17),(0,3),(3,6),(4,5),(4,5),(6,17),(7,16),(14,15),(14,15)]
  let caller ← parsed "f(x)" expectedCall [(0,4),(0,1),(0,1),(1,4),(2,3),(2,3)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let saved := RuntimeValue.sourceClosure parameter callerOwner [("p",cid 77),("p",cid 88)]
    [(cid 77,core),(cid 77,.word Core.Word.maximum)]
  let mut count := 0
  for (sv,av) in [(saved,RuntimeValue.pair (.word Core.Word.maximum) core),(core,saved)] do
    for tail in [[],[(sid 8,saved),(sid 100,core),(cid 40,saved)]] do
      for callStore in [[],[saved,core,RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef (.function .word .word) 900]] do
        for (source,mc,ma) in [(parameter,false,false),(free,false,false),(free,true,false),(parameter,false,true)] do
          exercise source caller sv av core tail [core,.unit] callStore mc ma
          count := count+1
  check (count==32) "four actual saved-call scenarios / eight mixed duplicate-row contexts"
