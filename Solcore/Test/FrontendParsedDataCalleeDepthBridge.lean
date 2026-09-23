import Solcore.Frontend.DataCalleeLambdaDepth
import Solcore.Syntax.Parser.Term

/- Independent original callee selection is required, never inferred from a new
depth law. Actual creation fields, selected saved body and complete stores flow
through every call. Handwritten ASTs include all delimiters and operator spans. -/
set_option autoImplicit false
namespace Tests.ParsedDataCalleeDepth
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def so : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedDataCallee",by decide⟩],by decide⟩⟩,306⟩
private def co : Resolved.DeclarationId := {so with declarationIndex:=906}
private def sid (n : Nat) : Resolved.LocalId := ⟨so,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def sn : LocalNameTable := [("y",sid 2),("p",sid 8),("x",cid 40),("y",sid 99),("p",sid 99)]
private def sr (v core : V) (missing : Bool) (tail : Resolved.LocalScope V) :=
  (if missing then [] else [(sid 2,v),(sid 2,.unit)])++[(sid 8,core),(cid 40,core),(sid 99,.bool false)]++tail
private def cn (missing : Bool) : LocalNameTable :=
  [("f",cid 1),("b",cid 4),("z",cid 5)]++(if missing then [] else [("x",cid 2),("x",cid 99)])++[("f",cid 99)]
private def cr (closure argument other : V) (flag : Bool) : Resolved.LocalScope V :=
  [(cid 1,closure),(cid 1,other),(cid 4,.bool flag),(cid 5,other),(cid 2,argument),(cid 2,.unit),(cid 99,other)]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (name : String) : Syntax.Expr :=
  ⟨span f a b,.identifier ⟨span f a b,name⟩⟩
private def expectedLambda (key : String) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 17,.lambda (span f 0 3) ⟨span f 3 6,[⟨span f 4 5,.inferred ⟨span f 4 5,"p"⟩⟩]⟩ none
    ⟨span f 6 17,[⟨span f 7 16,.returnStmt (some (ref f 14 15 key))⟩]⟩⟩
private def expectedCall (mode : Nat) (f : Syntax.SourceFile) : Syntax.Expr :=
  let stop := if mode=0 then 3 else if mode=1 then 11 else 8
  let inner := if mode=0 then ref f 1 2 "f" else if mode=1 then
    ⟨span f 1 10,.conditional (ref f 1 2 "b") (span f 3 4) (ref f 5 6 "f") (span f 7 8) (ref f 9 10 "z")⟩ else
    ⟨span f 1 7,.binary (ref f 1 2 "b") ⟨span f 3 5,if mode=2 then .logicalAnd else .logicalOr⟩ (ref f 6 7 "f")⟩
  ⟨span f 0 (stop+3),.call ⟨span f 0 stop,.group inner⟩ ⟨span f stop (stop+3),[ref f (stop+1) (stop+2) "x"]⟩⟩
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.group e⟩ => s::spans e
  | ⟨s,.conditional c q t k e⟩ => [s]++spans c++[q]++spans t++[k]++spans e
  | ⟨s,.binary l op r⟩ => [s]++spans l++[op.span]++spans r
  | ⟨s,.call callee ⟨a,[argument]⟩⟩ => [s]++spans callee++[a]++spans argument
  | ⟨s,.lambda k ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨b,[⟨r,.returnStmt (some e)⟩]⟩⟩ => [s,k,ps,p,n.span,b,r]++spans e
  | _ => []
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-data-callee.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "data callee lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole independent AST / EOF / zero diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==ranges) "every actual expression / operator / name / delimiter span"
    return actual
  | _ => throw (IO.userError "data callee parser")
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
private structure Selection (missing flag : Bool) (closure argument other : V) (st : List V) (callee : Syntax.Expr) : Type where
  gate : ClosedSourceDataExpression callee
  original : E co (cn missing) (cr closure argument other flag) st callee closure st
private def selected (missing flag : Bool) (closure argument other : V) (st : List V) (callee : Syntax.Expr) :
    IO (Selection missing flag closure argument other st callee) := do
  let n := cn missing; let e := cr closure argument other flag
  have pick : ∀ s (f : Syntax.Identifier), f.value="f" → E co n e st ⟨s,.identifier f⟩ closure st :=
    fun _ _ hf => .reference (hf ▸ LocalNameTable.Lookup.head) .head
  have test : ∀ s (b : Syntax.Identifier), b.value="b" → E co n e st ⟨s,.identifier b⟩ (.bool flag) st :=
    fun _ _ hb => .reference (hb ▸ LocalNameTable.Lookup.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
  match h : callee with
  | ⟨_,.group ⟨fs,.identifier f⟩⟩ =>
    if hf : f.value="f" then return ⟨by rw [h]; exact .group .reference,by rw [h]; exact .group (pick fs f hf)⟩
    else throw (IO.userError "grouped first saved f")
  | ⟨_,.group ⟨_,.conditional ⟨bs,.identifier b⟩ _ ⟨fs,.identifier f⟩ _ ⟨_,.identifier z⟩⟩⟩ =>
    if hb : b.value="b" then
      if hf : f.value="f" then
        if ht : flag=true then
          check (z.value=="z") "unselected runtime candidate z"
          return ⟨by rw [h]; exact .group (.conditional .reference .reference .reference),
            by rw [h]; exact .group (.conditionalTrue (ht ▸ test bs b hb) (pick fs f hf))⟩
        else throw (IO.userError "conditional true selects f")
      else throw (IO.userError "conditional selected f")
    else throw (IO.userError "conditional b")
  | ⟨_,.group ⟨_,.binary ⟨bs,.identifier b⟩ ⟨_,op⟩ ⟨fs,.identifier f⟩⟩⟩ =>
    if hb : b.value="b" then
      if hf : f.value="f" then
        match hop : op with
        | .logicalAnd =>
          if ht : flag=true then return ⟨by rw [h,hop]; exact .group (.logicalAnd .reference .reference),
            by rw [h,hop]; exact .group (.andTrue (ht ▸ test bs b hb) (pick fs f hf))⟩
          else throw (IO.userError "and true selects f")
        | .logicalOr =>
          if ht : flag=false then return ⟨by rw [h,hop]; exact .group (.logicalOr .reference .reference),
            by rw [h,hop]; exact .group (.orFalse (ht ▸ test bs b hb) (pick fs f hf))⟩
          else throw (IO.userError "or false selects f")
        | _ => throw (IO.userError "actual logical operator")
      else throw (IO.userError "logical selected f")
    else throw (IO.userError "logical b")
  | _ => throw (IO.userError "actual admitted callee form")
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
    (shape : SourceUnaryLambdaShape source name body) (cg : ClosedSourceDataExpression callee)
    (ag : ClosedSourceDataExpression argument) (bg : ClosedSourceDataBody body)
    (selection : E co n e st callee (.sourceClosure source owner names captured) st)
    (result : Outcome (fun v final => E co n e st ⟨cs,.call callee ⟨als,[argument]⟩⟩ v final) st)
    (depth : Nat) (bad : Bool) : IO Unit := do
  let call : Syntax.Expr := ⟨cs,.call callee ⟨als,[argument]⟩⟩
  let bound := dataCalleeLambdaDepthBound callee argument body
  proof selection; check (bound==depth) "actual selected saved-body / callee maximum plus one"
  match result with
  | .bad impossible =>
    proof impossible; check bad "planned original whole-call exclusion"
    have absent := (dataCalleeLambda_evaluate_depth_none_iff shape cg ag bg selection (Nat.le_refl bound)).mpr impossible
    have all := (dataCalleeLambda_evaluate_depth_none_iff_all_budgets shape cg ag bg selection).mp absent
    proof absent; proof all
    proof ((dataCalleeLambda_evaluate_depth_none_iff shape cg ag bg selection (Nat.le_refl bound)).mp absent)
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
          proof ((dataCalleeLambda_evaluate_at_depthBound_iff shape cg ag bg selection enough).mp ran)
          proof ((dataCalleeLambda_evaluate_at_depthBound_iff shape cg ag bg selection enough).mpr actualOriginal)
        else throw (IO.userError "unexpected smaller-depth success")
  for extra in [0,3] do
    proof (dataCalleeLambda_evaluate_depth_stable shape cg ag bg selection (Nat.le_add_right bound extra)
      (callSpan:=cs) (argumentsSpan:=als))
private def exercise (source whole : Syntax.Expr) (sv av core other : V) (tail : Resolved.LocalScope V)
    (creationStore callStore : List V) (mc ma flag : Bool) (depth : Nat) : IO Unit := do
  let se := sr sv core mc tail
  match hs : source, hw : whole with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred parameter⟩]⟩ _ body⟩,⟨cs,.call callee ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
    have shape : SourceUnaryLambdaShape source parameter body := by rw [hs]; exact .inferred
    have created : E so sn se creationStore source (.sourceClosure source so sn se) creationStore := .creation shape
    proof created
    match made : evaluateClosedSourceExpression? 1 so sn se creationStore source with
    | some (.sourceClosure actualSource actualOwner actualNames actualCaptured,actualCreationStore) =>
      have equal := (evaluateClosedSourceExpression?_sound made).deterministic created
      have fields := RuntimeValue.sourceClosure.inj equal.1
      have actualShape : SourceUnaryLambdaShape actualSource parameter body := fields.1.symm ▸ shape
      proof fields; proof equal.2
      check (actualOwner != co && creationStore.length != callStore.length) "separate actual creation and caller owner/store"
      let closure := RuntimeValue.sourceClosure actualSource actualOwner actualNames actualCaptured
      let n := cn ma; let e := cr closure av other flag
      let choice ← selected ma flag closure av other callStore callee
      proof choice.original
      let actualSelection ← (show IO (PLift (E co n e callStore callee closure callStore)) from do
        match crun : evaluateClosedSourceExpression? (depth-1) co n e callStore callee with
        | some (cv,cst) => do
          have actual := evaluateClosedSourceExpression?_sound crun
          have equal := actual.deterministic choice.original
          proof (show cv=closure ∧ cst=callStore from equal)
          return ⟨by rcases equal with ⟨rfl,rfl⟩; exact actual⟩
        | none => throw (IO.userError "independently selected callee must actually succeed"))
      have chosen := actualSelection.down
      match hb : body with
      | ⟨_,[⟨_,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
        have bg : ClosedSourceDataBody body := by rw [hb]; exact .expression .reference
        match reference co n e callStore xs x with
        | .bad absent =>
          check (ma && x.value=="x") "caller argument missing while selected callee succeeds"
          match reference actualOwner actualNames actualCaptured callStore xs x with
          | .ok _ savedRead => proof savedRead
          | .bad _ => throw (IO.userError "saved x independently exists, but cannot supply caller x")
          have noCall := rejectCall (cs:=cs) (als:=als) actualShape choice.original (.bad absent)
            (by intro v ev; exact False.elim (absent v callStore ev))
          proof (show ∀ v final, ¬ E co n e callStore whole v final from hw ▸ noCall)
          consume actualShape choice.gate .reference bg chosen (.bad noCall) depth true
        | .ok argument arg =>
          proof arg
          if hx : x.value="x" then
            if hm : ma=false then
              have independentArgument : E co n e callStore ⟨xs,.identifier x⟩ av callStore := by
                apply ClosedSourceExpressionEvaluates.reference (id:=cid 2) _
                  (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
                rw [hx]
                change LocalNameTable.Lookup (cn ma) "x" (cid 2)
                rw [hm]; exact .tail (by decide) (.tail (by decide) (.tail (by decide) .head))
              proof (arg.deterministic independentArgument)
            else throw (IO.userError "missing caller argument cannot succeed")
          else throw (IO.userError "actual fixed caller argument x")
          let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
          let bn := (parameter.value,fresh)::actualNames; let be := (fresh,argument)::actualCaptured
          match reference actualOwner bn be callStore ys key with
          | .bad absent =>
            have noBody : ∀ v final, ¬ ClosedSourceBodyEvaluates actualOwner bn be callStore body v final := by
              intro v final original; rw [hb] at original; cases original with | expression child => exact absent _ _ child
            have noCall := rejectCall (cs:=cs) (als:=als) actualShape choice.original (.ok argument arg) (by
              intro v ev; obtain ⟨same,_⟩ := ev.deterministic arg; cases same; exact noBody)
            proof noBody; check (mc && key.value=="y") "actual selected body fails, no alternate callee fallback"
            proof (show ∀ v final, ¬ E co n e callStore whole v final from hw ▸ noCall)
            consume actualShape choice.gate .reference bg chosen (.bad noCall) depth true
          | .ok value child =>
            if same : key.value=parameter.value then
              have freshRead : E actualOwner bn be callStore ⟨ys,.identifier key⟩ argument callStore :=
                .reference (same ▸ LocalNameTable.Lookup.head) .head
              proof (child.deterministic freshRead)
            else if hy : key.value="y" then
              if hp : parameter.value="p" then
                if hm : mc=false then
                  have savedRead : E actualOwner bn be callStore ⟨ys,.identifier key⟩ sv callStore := by
                    rcases fields with ⟨_,rfl,rfl,rfl⟩
                    apply ClosedSourceExpressionEvaluates.reference (id:=sid 2) _ (Resolved.LocalScope.Lookup.tail (by decide) ?_)
                    · rw [hy]; exact .tail (by simpa only [hp] using (by decide : "p" ≠ "y")) .head
                    · change Resolved.LocalScope.Lookup (sr sv core mc tail) (sid 2) sv
                      rw [hm]; exact .head
                  proof (child.deterministic savedRead)
                else throw (IO.userError "missing selected saved capture cannot succeed")
              else throw (IO.userError "actual saved parameter p")
            else throw (IO.userError "actual selected saved free reference y")
            have originalBody : ClosedSourceBodyEvaluates actualOwner bn be callStore body value callStore := by
              rw [hb]; exact .expression child
            have originalCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape choice.original arg originalBody
            proof originalBody; proof (show E co n e callStore whole value callStore from hw ▸ originalCall)
            match brun : evaluateClosedSourceBody? 2 actualOwner bn be callStore body with
            | some (bv,bs) =>
              have actualBody := evaluateClosedSourceBody?_sound brun
              proof (actualBody.deterministic originalBody)
              have actualCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape chosen arg actualBody
              have sameStore := (actualBody.deterministic originalBody).2
              consume actualShape choice.gate .reference bg chosen (.ok bv (sameStore ▸ actualCall)) depth false
            | none => throw (IO.userError "actual selected saved body must succeed")
      | _ => throw (IO.userError "actual saved body reference")
    | _ => throw (IO.userError "actual original source closure creation")
  | _,_ => throw (IO.userError "actual source lambda and whole unary call")
end Tests.ParsedDataCalleeDepth
open Solcore Solcore.Frontend Tests.ParsedDataCalleeDepth in
def Tests.frontendParsedDataCalleeDepthTests : IO Unit := do
  let p ← parsed "lam(p){return p;}" (expectedLambda "p") [(0,17),(0,3),(3,6),(4,5),(4,5),(6,17),(7,16),(14,15),(14,15)]
  let y ← parsed "lam(p){return y;}" (expectedLambda "y") [(0,17),(0,3),(3,6),(4,5),(4,5),(6,17),(7,16),(14,15),(14,15)]
  let grouped ← parsed "(f)(x)" (expectedCall 0) [(0,6),(0,3),(1,2),(1,2),(3,6),(4,5),(4,5)]
  let conditional ← parsed "(b ? f : z)(x)" (expectedCall 1)
    [(0,14),(0,11),(1,10),(1,2),(1,2),(3,4),(5,6),(5,6),(7,8),(9,10),(9,10),(11,14),(12,13),(12,13)]
  let andCall ← parsed "(b && f)(x)" (expectedCall 2) [(0,11),(0,8),(1,7),(1,2),(1,2),(3,5),(6,7),(6,7),(8,11),(9,10),(9,10)]
  let orCall ← parsed "(b || f)(x)" (expectedCall 3) [(0,11),(0,8),(1,7),(1,2),(1,2),(3,5),(6,7),(6,7),(8,11),(9,10),(9,10)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let other := RuntimeValue.sourceClosure p co [("p",cid 77),("p",cid 88)] [(cid 77,core),(cid 77,.word Core.Word.maximum)]
  let mut count := 0
  for (sv,av,bad,tail,st) in [(other,RuntimeValue.pair (.word Core.Word.maximum) core,core,[],[]),
      (core,other,other,[(sid 8,other),(sid 100,core),(cid 40,other)],
        [other,core,RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef .word 900])] do
    for (source,mc,ma) in [(p,false,false),(y,false,false),(y,true,false),(p,false,true)] do
      for (whole,flag,depth) in [(grouped,true,3),(conditional,true,4),(andCall,true,4),(orCall,false,4)] do
        exercise source whole sv av core bad tail [core,.unit] st mc ma flag depth
        count := count+1
  check (count==32) "four callee forms / four selected outcomes / two complete mixed contexts"
