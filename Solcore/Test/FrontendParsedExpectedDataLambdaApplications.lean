import Solcore.Frontend.ExpectedDataLambdaInvocationProperties
import Solcore.Frontend.ClosedSourceDataBodyProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.LocalExpressionCostCorrespondence
import Solcore.Frontend.LocalExpressionEvaluatorProperties
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.WordLessCostStepComposition
import Solcore.Frontend.LocalFunctionApplicationStepComposition
import Solcore.Syntax.Parser.Term
/- Original whole-written certificates precede search. The actual grouped call
uses invocation; no direct-call AST or source/Core closure equality is invented. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedExpectedDataLambdaApplications
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedApplications",by decide⟩],by decide⟩⟩,175⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign (n : Nat) : Resolved.LocalId := ⟨{owner with declarationIndex:=901},n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"x",sid 7,.bool⟩,⟨"saved",sid 31,.unit⟩,⟨"c",sid 11,.bool⟩,
  ⟨"d",sid 20,.bool⟩,⟨"arg",sid 9,.unit⟩,⟨"other",foreign 700,.unit⟩,⟨"x",foreign 701,.word⟩],by decide⟩
private def types : TypeNameTable := [(["Unit"],.unit),(["Word"],.word)]
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def env (a o q : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(sid 7,.bool false),(sid 31,q),(sid 11,.bool c),(sid 20,.bool d),(sid 9,a),(foreign 700,o),(foreign 701,.word (Core.Word.ofNatModulo 99))]
private abbrev Child (n : LocalNameTable) (t : Resolved.Context) (s : Syntax.Expr) (c : Core.Expr) (v : Core.Ty) :=
  ∃ r, ResolvesLocalExpression n s r ∧ Resolved.Lowers t.ids r c ∧ Resolved.HasType t r v
private structure EC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  gate : ClosedSourceDataExpression src
  elaboration : Child t.names t.context src core type
  old : LocalExpressionEvaluatesWithCost t.names e s src value s cost
  closed : ClosedSourceExpressionEvaluates owner t.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore value) (s.map RuntimeValue.ofCore)
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail different _ ih => exact .tail different ih
private theorem path {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids) (k : List Core.Frame) :
    Core.Steps h.cost ⟨.eval h.core e.values,k,s⟩ ⟨.ret h.value,k,s⟩ := by
  obtain ⟨r,res,low,_⟩ := h.elaboration
  exact h.old.toStepsWithContinuation res (same ▸ low) k
private def expr (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) : IO (EC t e s src) := do
  match shape : src with
  | ⟨_,.identifier name⟩ =>
    match named : t.names.lookup? name.value with
    | some i => match typed : t.context.lookup? i, found : e.lookup? i, indexed : Resolved.LocalScope.index? t.context.ids i with
      | some ty,some v,some n => return ⟨.var n,ty,v,1,by rw [shape]; exact .reference,
          by rw [shape]; exact ⟨.var i,.identifier (LocalNameTable.lookup?_iff.mp named),.var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩,
          by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
          by rw [shape]; exact .reference (LocalNameTable.lookup?_iff.mp named) (mapped (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | _,_,_ => throw (IO.userError "independent original reference row")
    | none => throw (IO.userError "independent original name")
  | ⟨span,.group child⟩ =>
    check (span.startByte+1==child.span.startByte && child.span.endByte+1==span.endByte) "original group margins"
    let h ← expr t e s child
    return ⟨h.core,h.type,h.value,h.cost,by rw [shape]; exact .group h.gate,
      by obtain ⟨r,a,b,c⟩ := h.elaboration; rw [shape]; exact ⟨r,.group a,b,c⟩,
      by rw [shape]; exact .group h.old,by rw [shape]; exact .group h.closed⟩
  | ⟨span,.tuple ⟨ts,[left,right]⟩⟩ =>
    check (span==ts && span.contains left.span && span.contains right.span && left.span.endByte<right.span.startByte) "original pair ranges"
    let l ← expr t e s left; let r ← expr t e s right
    return ⟨.pair l.core r.core,.product l.type r.type,.pair l.value r.value,l.cost+r.cost+3,
      by rw [shape]; exact .pair l.gate r.gate,
      by obtain ⟨a,ar,al,alt⟩ := l.elaboration; obtain ⟨b,br,bl,bt⟩ := r.elaboration; rw [shape]; exact ⟨.pair a b,.pair ar br,.pair al bl,.pair alt bt⟩,
      by rw [shape]; exact .pair l.old r.old,by rw [shape]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.pair l.closed r.closed⟩
  | ⟨span,.conditional guard qm yes colon no⟩ =>
    check (span.contains guard.span && span.contains yes.span && span.contains no.span && qm.endByte==qm.startByte+1 && colon.endByte==colon.startByte+1 && guard.span.endByte==qm.startByte && qm.endByte==yes.span.startByte && yes.span.endByte==colon.startByte && colon.endByte==no.span.startByte) "original conditional children and markers"
    let g ← expr t e s guard; let a ← expr t e s yes; let b ← expr t e s no
    if typed : g.type=.bool ∧ a.type=b.type then
      match value : g.value with
      | .bool c => return ⟨.ifE g.core a.core b.core,a.type,if c then a.value else b.value,g.cost+(if c then a.cost else b.cost)+2,
          by rw [shape]; exact .conditional g.gate a.gate b.gate,
          by obtain ⟨r,rr,rl,rt⟩ := g.elaboration; obtain ⟨u,ur,ul,ut⟩ := a.elaboration; obtain ⟨v,vr,vl,vt⟩ := b.elaboration
             rw [shape]; exact ⟨.ifE r u v,.conditional rr ur vr,.ifE rl ul vl,.ifE (typed.1 ▸ rt) ut (typed.2 ▸ vt)⟩,
          by rw [shape]; cases c <;> first | exact .ifTrue (value ▸ g.old) a.old | exact .ifFalse (value ▸ g.old) b.old,
          by rw [shape]; cases c <;> first | exact .conditionalTrue (by simpa only [value,RuntimeValue.ofCore] using g.closed) a.closed | exact .conditionalFalse (by simpa only [value,RuntimeValue.ofCore] using g.closed) b.closed⟩
      | _ => throw (IO.userError "original Bool guard payload")
    else throw (IO.userError "independent original conditional types")
  | _ => throw (IO.userError "bounded original certificate profile")
termination_by sizeOf src
private structure Meaning (src : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types src type
private def meaning (src : Syntax.TypeExpr) : IO (Meaning src) := do
  match shape : src with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some ty => return ⟨ty,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
    | none => throw (IO.userError "original annotation meaning")
  | ⟨_,.tuple [a,b]⟩ => let l ← meaning a; let r ← meaning b; return ⟨.product l.type r.type,by rw [shape]; exact .pair l.evidence r.evidence⟩
  | _ => throw (IO.userError "original annotation profile")
termination_by sizeOf src
private structure BC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) where
  core : Core.Expr
  value : Core.Value
  cost : Nat
  gate : ClosedSourceDataBody src
  elaboration : ComputationReturnTreeElaborates Child types owner t src core (.product .unit .unit)
  old : ComputationReturnTreeEvaluatesWithCost LocalExpressionEvaluatesWithCost owner t.names e s src value s cost
  closed : ClosedSourceBodyEvaluates owner t.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore value) (s.map RuntimeValue.ofCore)
  path : ∀ k, Core.Steps cost ⟨.eval core e.values,k,s⟩ ⟨.ret value,k,s⟩
private def body (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) (same : e.ids=t.context.ids) : IO (BC t e s src) := do
  match shape : src with
  | ⟨bs,[⟨ls,.letDecl name (some ann) (some init)⟩,⟨rs,.returnStmt (some result)⟩]⟩ =>
    let h ← expr t e s init; let m ← meaning ann
    if typed : m.type=.unit ∧ h.type=.unit then
      let t1 := t.bindFresh owner name.value .unit
      let e1 : Resolved.Environment := (Resolved.freshLocalId owner t.ids,h.value)::e
      have same1 : e1.ids=t1.context.ids := by simpa only [e1,t1,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
      let r ← expr t1 e1 s result
      if rt : r.type=.product .unit .unit then
        return ⟨.letE h.core r.core,r.value,h.cost+r.cost+2,by rw [shape]; exact .binding h.gate (.expression r.gate),
          by rw [shape]; exact .binding (typed.1 ▸ m.evidence) (typed.2 ▸ h.elaboration) (.expression (rt ▸ r.elaboration)),
          by rw [shape]; apply ComputationReturnTreeEvaluatesWithCost.binding h.old
             simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluatesWithCost.expression (blockSpan:=bs) (returnSpan:=rs) (owner:=owner) r.old,
          by rw [shape]; apply ClosedSourceBodyEvaluates.binding h.closed
             simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using ClosedSourceBodyEvaluates.expression (blockSpan:=bs) (returnSpan:=rs) r.closed,
          fun k => CostStepComposition.letE (path h same _) (by simpa only [e1,Resolved.LocalScope.values,List.map_cons] using path r same1 k)⟩
      else throw (IO.userError "independent pair result type")
    else throw (IO.userError "independent Unit local shadow")
  | _ => throw (IO.userError "original typed shadow and conditional return")
private structure Header (src : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape src name body
  declaration : ExpectedUnaryLambdaHeaderDeclares types owner inputs src (.function .unit (.product .unit .unit))
    ⟨inputs.bindFresh owner name.value .unit,body,.unit,.product .unit .unit⟩
private def header (src : Syntax.Expr) : IO (Header src) := do
  match shape : src with
  | ⟨span,.lambda keyword ⟨pspan,[p]⟩ returns b⟩ =>
    check (span.contains keyword && span.contains pspan && pspan.contains p.span && span.contains b.span && returns.toList.all (fun a => span.contains a.span) && b.value.all (fun st => b.span.contains st.span)) "original lambda/header/body ranges"
    let ⟨n,param,raw⟩ : Σ n, PLift (ExpectedLambdaParameterDeclares types owner inputs p .unit (inputs.bindFresh owner n.value .unit)) × PLift (SourceUnaryLambdaShape src n b) ←
      match ps : p with
      | ⟨_,.inferred n⟩ => pure ⟨n,⟨by rw [ps]; exact .inferred⟩,⟨by rw [shape,ps]; exact .inferred⟩⟩
      | ⟨_,.typed none n ann⟩ => do
        let m ← meaning ann
        if h : m.type=.unit then pure ⟨n,⟨by rw [ps]; exact .typed (h ▸ m.evidence)⟩,⟨by rw [shape,ps]; exact .typed⟩⟩
        else throw (IO.userError "original parameter Unit")
      | _ => throw (IO.userError "original unmarked unary parameter")
    match present : returns with
    | none => return ⟨n,b,raw.down,by rw [shape,present]; exact .lambda param.down .omitted⟩
    | some ann =>
      let m ← meaning ann
      if h : m.type=.product .unit .unit then return ⟨n,b,raw.down,by rw [shape,present]; exact .lambda param.down (.annotated (h ▸ m.evidence))⟩
      else throw (IO.userError "original expected pair annotation")
  | _ => throw (IO.userError "original direct lambda child")
private def parsed (text : String) : IO Syntax.Expr := do
  let f : Syntax.SourceFile := ⟨⟨.main,"expected-data-applications.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && src.span==Syntax.SourceSpan.fullFile f) "original source, complete EOF and diagnostics"
    return src
  | _ => throw (IO.userError "original expression parser")
private def mainText := "(lam(x:Unit)->(Unit,Unit){let x:Unit=(x);return c?(x,saved):(saved,x);})(d?arg:other)"
private def inferredText := "(lam(x){let x:Unit=(x);return c?(x,saved):(saved,x);})(d?arg:other)"
private def literalBody : Core.Expr := .letE (.var 0) (.ifE (.var 4) (.pair (.var 0) (.var 3)) (.pair (.var 3) (.var 0)))
private def exercise (text : String) (a o q : Core.Value) (c d : Bool) (s : Core.Store) : IO Unit := do
  let src ← parsed text; let e := env a o q c d
  match original : src with
  | ⟨cs,.call ⟨gs,.group fs⟩ ⟨args,[arg]⟩⟩ =>
    let h ← header fs; let ac ← expr inputs e s arg
    let inner := inputs.bindFresh owner h.name.value .unit
    let ie : Resolved.Environment := (Resolved.freshLocalId owner inputs.ids,ac.value)::e
    have same : e.ids=inputs.context.ids := rfl
    have same1 : ie.ids=inner.context.ids := by simpa only [ie,inner,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
    let bc ← body inner ie s h.body same1
    have originalExpected : ExpectedComputationLambdaElaborates Child types owner inputs fs (.lambda .unit (.product .unit .unit) bc.core) (.function .unit (.product .unit .unit)) :=
      .lambda h.declaration .unit (.product .unit .unit) bc.elaboration
    have callee : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ (.sourceClosure fs owner inputs.names (up e)) (s.map RuntimeValue.ofCore) := .group (.creation h.shape)
    have closed : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore bc.value) (s.map RuntimeValue.ofCore) := by
      rw [original]; apply ClosedSourceExpressionEvaluates.call h.shape callee ac.closed
      simpa only [ie,inner,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using bc.closed
    have beta (k) : Core.Steps bc.cost ⟨.eval bc.core (ac.value::e.values),k,s⟩ ⟨.ret bc.value,k,s⟩ := by simpa only [ie,Resolved.LocalScope.values,List.map_cons] using bc.path k
    let core := Core.Expr.apply (.lambda .unit (.product .unit .unit) bc.core) ac.core
    have full (k) : Core.Steps (1+ac.cost+bc.cost+3) ⟨.eval core e.values,k,s⟩ ⟨.ret bc.value,k,s⟩ := CostStepComposition.apply (.cons .lambda .refl) (path ac same _) (beta [])
    proof closed; proof (Core.steps_from_initial_sound (full [])); proof originalExpected
    check (decide (bc.core=literalBody ∧ ac.core=.ifE (.var 3) (.var 4) (.var 5) ∧ ac.cost=4 ∧ bc.cost=11 ∧ h.name.value="x" ∧ Resolved.freshLocalId owner inputs.ids=sid 32 ∧ Resolved.freshLocalId owner inner.ids=sid 33)) "independent literal Core/cost and fresh shadow rows"
    check (decide (ac.value=(if d then a else o) ∧ bc.value=(if c then .pair ac.value q else .pair q ac.value))) "independent full opaque argument and pair endpoint"
    check (cs.startByte==0 && gs.startByte==0 && fs.span.startByte==1 && fs.span.endByte+1==gs.endByte && args.startByte==gs.endByte && args.endByte==cs.endByte) "actual grouped callee retained in whole original call"
    have independentChecked := (elaborateExpectedComputationLambda?_iff elaborateLocalExpression?_iff).mpr originalExpected
    proof independentChecked
    check (decide (elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs fs (.function .unit (.product .unit .unit))=some (.lambda .unit (.product .unit .unit) bc.core))) "actual expected checker agrees with independent original"
    check (elaborateComputationReturnTree? elaborateLocalExpression? types owner inner h.body==some (bc.core,.product .unit .unit)) "actual original shared body checker"
    check ((elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs ⟨gs,.group fs⟩ (.function .unit (.product .unit .unit))).isNone && (elaborateLocalExpression? inputs.names inputs.context src).isNone) "grouped callee and whole call are not old checked expressions"
    check (decide (evaluateLocalExpressionWithCost? inputs.names e arg=some (ac.value,ac.cost))) "actual old argument value/cost"
    match resolved : resolveLocalExpression? inputs.names arg with
    | some r => check (r.lower? e.ids==some ac.core) "actual original argument resolution and lowering"; proof (resolveLocalExpression?_sound resolved)
    | none => throw (IO.userError "actual original argument resolution")
    for depth in [0,1,2,3,4,5,6,9] do
      match run : evaluateClosedSourceExpression? depth owner inputs.names (up e) (s.map RuntimeValue.ofCore) src with
      | none => check (depth<6) "actual original depth below 6"
      | some (mv,ms) => proof ((evaluateClosedSourceExpression?_sound run).deterministic closed); check (depth≥6) "actual depth 6, separate Core cost 19"
    match made : evaluateClosedSourceExpression? 2 owner inputs.names (up e) (s.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ with
    | none => throw (IO.userError "actual grouped creation depth 2")
    | some (actualFn,calleeStore) =>
      have fnEq := (evaluateClosedSourceExpression?_sound made).deterministic callee
      match argRun : evaluateClosedSourceExpression? 2 owner inputs.names (up e) calleeStore arg with
      | none => throw (IO.userError "actual argument after actual callee store")
      | some (actualArg,argumentStore) =>
        have argEq := (evaluateClosedSourceExpression?_sound (fnEq.2 ▸ argRun)).deterministic ac.closed
        have fnEval : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ (.sourceClosure fs owner inputs.names (up e)) calleeStore := by simpa only [fnEq.1] using evaluateClosedSourceExpression?_sound made
        have argEval : ClosedSourceExpressionEvaluates owner inputs.names (up e) calleeStore arg (RuntimeValue.ofCore ac.value) (s.map RuntimeValue.ofCore) := by simpa only [argEq.1,argEq.2] using evaluateClosedSourceExpression?_sound argRun
        have image {v st} := closedSourceExpectedDataLambda_invocation_core_iff h.shape bc.gate independentChecked same fnEval argEval (callSpan:=cs) (argumentsSpan:=args) (actualValue:=v) (actualFinal:=st)
        match actualRun : evaluateClosedSourceExpression? 6 owner inputs.names (up e) (s.map RuntimeValue.ofCore) src, coreRun : Core.runStateful 19 (.initial core e.values s) with
        | some (mv,ms),.done cv final =>
          have actual := evaluateClosedSourceExpression?_sound actualRun
          have actualCore := Core.runStateful_evaluation_sound coreRun
          have forward := (image (v:=mv) (st:=ms)).mp (by simpa only [original] using actual)
          have equal : mv=RuntimeValue.ofCore cv ∧ ms=final.map RuntimeValue.ofCore := by
            obtain ⟨v,st,hv,hs,ev⟩ := forward
            have both := Core.evaluation_deterministic (Core.Evaluates.apply (parameterType:=.unit) (resultType:=.product .unit .unit) Core.Evaluates.lambda (Core.steps_from_initial_sound (path ac same [])) ev) actualCore
            simpa only [both.1,both.2] using And.intro hv hs
          have actualBeta : Core.Evaluates (ac.value::e.values) s bc.core cv final := by
            change Core.Evaluates e.values s (.apply (.lambda .unit (.product .unit .unit) bc.core) ac.core) cv final at actualCore
            cases actualCore with
            | apply f a b =>
              cases f
              obtain ⟨ha,hs⟩ := Core.evaluation_deterministic a (Core.steps_from_initial_sound (path ac same []))
              cases ha; cases hs; exact b
          proof ((image (v:=mv) (st:=ms)).mpr ⟨cv,final,equal.1,equal.2,actualBeta⟩)
          proof ((image (v:=RuntimeValue.ofCore cv) (st:=final.map RuntimeValue.ofCore)).mpr ⟨cv,final,rfl,rfl,actualBeta⟩); proof equal
          check (mv.toCore?==some cv && (ms.mapM RuntimeValue.toCore?)==some final) "actual full mixed value/store projected only after both directions"
        | _,_ => throw (IO.userError "actual whole closed/Core completion")
    match bodyRun : evaluateClosedSourceBody? 5 owner inner.names (up ie) (s.map RuntimeValue.ofCore) h.body with
    | some (_,_) => proof ((evaluateClosedSourceBody?_sound bodyRun).deterministic bc.closed)
    | none => throw (IO.userError "actual body depth 5")
    for fuel in [0,1,18,19,23] do
      match run : Core.runStateful fuel (.initial core e.values s) with
      | .done v final => check (decide (fuel≥19 ∧ v=bc.value ∧ final=s)) "actual Core full endpoint and cost"; proof (Core.runStateful_evaluation_sound run)
      | .outOfFuel _ => check (fuel<19) "actual Core cost 19"
      | .fault _ _ => throw (IO.userError "unexpected Core fault")
  | _ => throw (IO.userError "original grouped application")
end Tests.ParsedExpectedDataLambdaApplications
open Tests.ParsedExpectedDataLambdaApplications in
def Tests.frontendParsedExpectedDataLambdaApplicationTests : IO Unit := do
  let a := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let o := Solcore.Core.Value.cellRef (.function .unit .word) 900
  let q := Solcore.Core.Value.hostFunction .storageWrite
  for text in [mainText,inferredText] do
    for c in [false,true] do
      for d in [false,true] do exercise text a o q c d [o,q,a,.unit]
