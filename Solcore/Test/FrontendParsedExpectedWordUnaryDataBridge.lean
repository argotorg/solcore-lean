import Solcore.Frontend.Expected
import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Syntax.Parser.Term
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Tests.ParsedExpectedWordUnaryDataBridge
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedWordData",by decide⟩],by decide⟩⟩,297⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign (n : Nat) : Resolved.LocalId := ⟨{owner with declarationIndex:=901},n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"p",sid 7,.word⟩,⟨"q",sid 31,.unit⟩,⟨"w",sid 11,.word⟩,⟨"extra",foreign 700,.unit⟩,⟨"p",foreign 701,.word⟩],by decide⟩
private def types : TypeNameTable := [(["Word"],.word)]
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def heap (s : Core.Store) := s.map RuntimeValue.ofCore
private def env (w : Core.Word) (q : Core.Value) : Resolved.Environment := [(sid 7,.word w),(sid 31,q),(sid 11,.word w),(foreign 700,.cellRef .word 900),(foreign 701,.word w)]
private abbrev Child (n : LocalNameTable) (t : Resolved.Context) (s : Syntax.Expr) (c : Core.Expr) (v : Core.Ty) := ∃ r, ResolvesLocalExpression n s r ∧ Resolved.Lowers t.ids r c ∧ Resolved.HasType t r v
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
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value} (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail different _ ih => exact .tail different ih
private theorem path {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids) (k : List Core.Frame) : Core.Steps h.cost ⟨.eval h.core e.values,k,s⟩ ⟨.ret h.value,k,s⟩ := by
  obtain ⟨r,res,low,_⟩ := h.elaboration; exact h.old.toStepsWithContinuation res (same ▸ low) k
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
  | ⟨_,.unary ⟨_,.bitNot⟩ child⟩ =>
    let h ← expr t e s child
    if ht : h.type=.word then
      match hv : h.value with
      | .word w => return ⟨.unary .wordNot h.core,.word,.word w.bitNot,h.cost+2,h.depth+1,by rw [shape]; exact .bitNot h.gate,
          by obtain ⟨r,a,b,c⟩ := h.elaboration; rw [shape]; exact ⟨.unary .wordNot r,.bitNot a,.unary b,.unary (by simpa only [ht,Core.UnaryOp.operandType] using c)⟩,
          by rw [shape]; exact .bitNot (hv ▸ h.old),by rw [shape]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.bitNot (by simpa only [hv,RuntimeValue.ofCore] using h.closed)⟩
      | _ => throw (IO.userError "independent Word operand payload")
    else throw (IO.userError "independent Word static operand")
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
    let l ← expr t e s left; let r ← expr t e s right
    return ⟨.pair l.core r.core,.product l.type r.type,.pair l.value r.value,l.cost+r.cost+3,max l.depth r.depth+1,
      by rw [shape]; exact .pair l.gate r.gate,
      by obtain ⟨a,ar,al,aty⟩ := l.elaboration; obtain ⟨b,br,bl,bt⟩ := r.elaboration; rw [shape]; exact ⟨.pair a b,.pair ar br,.pair al bl,.pair aty bt⟩,
      by rw [shape]; exact .pair l.old r.old,by rw [shape]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.pair l.closed r.closed⟩
  | _ => throw (IO.userError "bounded identifier/unary/pair original")
termination_by sizeOf src
private structure BC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) where
  core : Core.Expr
  value : Core.Value
  cost : Nat
  depth : Nat
  gate : ClosedSourceDataBody src
  elaboration : ComputationReturnTreeElaborates Child types owner t src core (.product .word .unit)
  old : ComputationReturnTreeEvaluates LocalExpressionEvaluates owner t.names e s src value s
  oldCost : ComputationReturnTreeEvaluatesWithCost LocalExpressionEvaluatesWithCost owner t.names e s src value s cost
  closed : ClosedSourceBodyEvaluates owner t.names (up e) (heap s) src (RuntimeValue.ofCore value) (heap s)
  path : ∀ k, Core.Steps cost ⟨.eval core e.values,k,s⟩ ⟨.ret value,k,s⟩
private def body (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) (same : e.ids=t.context.ids) : IO (BC t e s src) := do
  match shape : src with
  | ⟨bs,[⟨_,.letDecl name (some ⟨_,.named ann none⟩) (some init)⟩,⟨rs,.returnStmt (some result)⟩]⟩ =>
    let h ← expr t e s init
    if typed : types.lookup? (qualifiedTypeNameKey ann)=some .word ∧ h.type=.word then
      let t1 := t.bindFresh owner name.value .word
      let e1 : Resolved.Environment := (Resolved.freshLocalId owner t.ids,h.value)::e
      have same1 : e1.ids=t1.context.ids := by simpa only [e1,t1,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
      let r ← expr t1 e1 s result
      if rt : r.type=.product .word .unit then
        return ⟨.letE h.core r.core,r.value,h.cost+r.cost+2,max h.depth (r.depth+1)+1,by rw [shape]; exact .binding h.gate (.expression r.gate),
          by rw [shape]; exact .binding (.named (TypeNameTable.lookup?_iff.mp typed.1)) (typed.2 ▸ h.elaboration) (.expression (rt ▸ r.elaboration)),
          by rw [shape]; apply ComputationReturnTreeEvaluates.binding h.old.erase; simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluates.expression (blockSpan:=bs) (returnSpan:=rs) (owner:=owner) r.old.erase,
          by rw [shape]; apply ComputationReturnTreeEvaluatesWithCost.binding h.old; simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluatesWithCost.expression (blockSpan:=bs) (returnSpan:=rs) (owner:=owner) r.old,
          by rw [shape]; apply ClosedSourceBodyEvaluates.binding h.closed; simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using ClosedSourceBodyEvaluates.expression (blockSpan:=bs) (returnSpan:=rs) r.closed,
          fun k => CostStepComposition.letE (path h same _) (by simpa only [e1,Resolved.LocalScope.values,List.map_cons] using path r same1 k)⟩
      else throw (IO.userError "independent Word/opaque pair")
    else throw (IO.userError "independent Word shadow")
  | _ => throw (IO.userError "original shadow/return")
private def exprImages {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids) {v st} (actual : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s) src v st) : IO Unit := do
  have imageEq : v=RuntimeValue.ofCore h.value ∧ st=heap s := by
    obtain ⟨r,res,low,_⟩ := h.elaboration
    have lb := (h.gate.local_evaluates_iff (owner:=owner)).mpr (h.gate.local_evaluates_iff.mp actual)
    have ci := h.gate.core_evaluates_iff res (same ▸ low) (owner:=owner) (initialStore:=s) (actualValue:=v) (actualFinal:=st)
    have cb := ci.mpr (ci.mp lb)
    obtain ⟨a,b,hv,hs,ev⟩ := ci.mp cb
    have eq := Core.evaluation_deterministic ev (Core.steps_from_initial_sound (path h same [])); simpa only [eq.1,eq.2,heap] using And.intro hv hs
  proof imageEq; check (v.toCore?==some h.value && st.mapM RuntimeValue.toCore?==some s) "actual argument image after both directions"
private def bodyImages {t e s src} (h : BC t e s src) (same : e.ids=t.context.ids) {v st} (actual : ClosedSourceBodyEvaluates owner t.names (up e) (heap s) src v st) : IO Unit := do
  have checked := (elaborateComputationReturnTree?_iff elaborateLocalExpression?_iff).mpr h.elaboration
  let localImage := h.gate.local_evaluates_iff
  let coreImage := h.gate.core_evaluates_iff checked same
  proof (localImage.mp actual); proof (localImage.mpr (localImage.mp actual)); proof (coreImage.mp actual); proof (coreImage.mpr (coreImage.mp actual))
  have imageEq : v=RuntimeValue.ofCore h.value ∧ st=heap s := by obtain ⟨a,b,hv,hs,ev⟩ := coreImage.mp actual; have eq := Core.evaluation_deterministic ev (Core.steps_from_initial_sound (h.path [])); simpa only [eq.1,eq.2,heap] using And.intro hv hs
  proof imageEq; check (v.toCore?==some h.value && st.mapM RuntimeValue.toCore?==some s) "actual body image after both directions"
private def text := "(lam(p){let p:Word=~p;return(p,q);})(~w)"
private def file (s : String) : Syntax.SourceFile := ⟨⟨.main,"parsed-word-unary-data.sol"⟩,s⟩
private def sp (a b : Nat) : Syntax.SourceSpan := ⟨(file text).id,a,b⟩
private def ref (a b : Nat) (n : String) : Syntax.Expr := ⟨sp a b,.identifier ⟨sp a b,n⟩⟩
private def expected : Syntax.Expr :=
  let b : Syntax.Block := ⟨sp 7 35,[⟨sp 8 22,.letDecl ⟨sp 12 13,"p"⟩ (some ⟨sp 14 18,.named ⟨sp 14 18,⟨⟨⟨sp 14 18,"Word"⟩,[]⟩⟩⟩ none⟩) (some ⟨sp 19 21,.unary ⟨sp 19 20,.bitNot⟩ (ref 20 21 "p")⟩)⟩,
    ⟨sp 22 34,.returnStmt (some ⟨sp 28 33,.tuple ⟨sp 28 33,[ref 29 30 "p",ref 31 32 "q"]⟩⟩)⟩]⟩
  let f : Syntax.Expr := ⟨sp 1 35,.lambda (sp 1 4) ⟨sp 4 7,[⟨sp 5 6,.inferred ⟨sp 5 6,"p"⟩⟩]⟩ none b⟩
  ⟨sp 0 40,.call ⟨sp 0 36,.group f⟩ ⟨sp 36 40,[⟨sp 37 39,.unary ⟨sp 37 38,.bitNot⟩ (ref 38 39 "w")⟩]⟩⟩
private def savedExpected : Syntax.Expr := ⟨sp 0 10,.call (ref 0 6 "picked") ⟨sp 6 10,[⟨sp 7 9,.unary ⟨sp 7 8,.bitNot⟩ (ref 8 9 "w")⟩]⟩⟩
private def parsed (s : String) (want : Syntax.Expr) : IO Syntax.Expr := do
  let f := file s
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok src next => check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && src.span==Syntax.SourceSpan.fullFile f && src==want) "exact original AST, every range/source, EOF/diagnostics"; return src
  | _ => throw (IO.userError "parser")
private def caller : Resolved.DeclarationId := {owner with declarationIndex:=299}
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def names : LocalNameTable := [("picked",cid 7),("w",cid 900),("q",cid 42),("picked",cid 7)]
private def rows (fn : RuntimeValue) (w : Core.Word) : Resolved.LocalScope RuntimeValue := [(cid 900,.word w),(cid 7,fn),(cid 42,fn),(cid 7,.unit),(foreign 999,fn)]
private def coreRuns {e s c v k} (p : Core.Steps k (.initial c e s) (.final v s)) : IO Unit := do
  proof p
  for fuel in [0,k-1,k,k+3] do
    match run : Core.runStateful fuel (.initial c e s) with
    | .done value final => proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound run) (Core.steps_from_initial_sound p)); check (fuel≥k && value==v && final==s) "Core independently counted endpoint"
    | .outOfFuel _ => check (fuel<k) "Core independently counted exhaustion"
    | .fault _ _ => throw (IO.userError "Core fault")
private def closedRuns {o n e s src v} (d : Nat) (old : ClosedSourceExpressionEvaluates o n e s src v s)
    (after : ∀ {a z}, ClosedSourceExpressionEvaluates o n e s src a z → IO Unit) : IO Unit := do
  proof old
  for fuel in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? fuel o n e s src with
    | none => check (fuel<d) "independent depth exhaustion"
    | some (_,_) => have actual := evaluateClosedSourceExpression?_sound run; proof (actual.deterministic old); after actual; check (fuel≥d) "independent closed depth/full endpoint"
private def consume {p : Prop} {e s c v a z} (old : Core.Evaluates e s c v s)
    (image : p ↔ ∃ value final, a=RuntimeValue.ofCore value ∧ z=heap final ∧ Core.Evaluates e s c value final) (actual : p) : IO Unit := do
  have forward := image.mp actual; proof forward; proof (image.mpr forward)
  have equal : a=RuntimeValue.ofCore v ∧ z=heap s := by obtain ⟨x,t,hx,ht,run⟩ := forward; have eq := Core.evaluation_deterministic run old; simpa only [eq.1,eq.2] using And.intro hx ht
  proof equal; check (a.toCore?==some v && z.mapM RuntimeValue.toCore?==some s) "full actual call image after mp/mpr"
private def reject {o n e s src} (no : ∀ a z, ¬ ClosedSourceExpressionEvaluates o n e s src a z) : IO Unit := do
  proof no
  for d in [0,1,4,5,8] do
    match run : evaluateClosedSourceExpression? d o n e s src with
    | none => pure ()
    | some _ => False.elim (no _ _ (evaluateClosedSourceExpression?_sound run))
private def exercise (w : Core.Word) (q : Core.Value) (s : Core.Store) : IO Unit := do
  let src ← parsed text expected; let picked ← parsed "picked(~w)" savedExpected; let e := env w q
  match original : src, savedShape : picked with
  | ⟨cs,.call ⟨gs,.group fs⟩ ⟨args,[arg]⟩⟩,⟨pcs,.call ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ ⟨pas,[⟨uas,.unary ⟨uos,.bitNot⟩ ⟨ws,.identifier ⟨wn,"w"⟩⟩⟩]⟩⟩ =>
    match fsShape : fs with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred p⟩]⟩ none b⟩ =>
      have shape : SourceUnaryLambdaShape fs p b := by rw [fsShape]; exact .inferred
      let ac ← expr inputs e s arg
      let inner := inputs.bindFresh owner p.value .word
      let ie : Resolved.Environment := (Resolved.freshLocalId owner inputs.ids,ac.value)::e
      have same : e.ids=inputs.context.ids := rfl
      have same1 : ie.ids=inner.context.ids := by simpa only [ie,inner,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
      let bc ← body inner ie s b same1
      have declaration : ExpectedUnaryLambdaHeaderDeclares types owner inputs fs (.function .word (.product .word .unit)) ⟨inner,b,.word,.product .word .unit⟩ := by rw [fsShape]; exact .lambda .inferred .omitted
      have expectedLambda : ExpectedComputationLambdaElaborates Child types owner inputs fs (.lambda .word (.product .word .unit) bc.core) (.function .word (.product .word .unit)) := .lambda declaration .word (.product .word .unit) bc.elaboration
      have checked := (elaborateExpectedComputationLambda?_iff elaborateLocalExpression?_iff).mpr expectedLambda
      let saved := RuntimeValue.sourceClosure fs owner inputs.names (up e)
      have creation : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ saved (heap s) := .group (.creation shape)
      have directCreation : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) fs saved (heap s) := .creation shape
      have beta : ClosedSourceBodyEvaluates owner ((p.value,Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names) ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),RuntimeValue.ofCore ac.value)::up e) (heap s) b (RuntimeValue.ofCore bc.value) (heap s) := by simpa only [ie,inner,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using bc.closed
      have whole : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) src (RuntimeValue.ofCore bc.value) (heap s) := by rw [original]; exact .call shape creation ac.closed beta
      let direct : Syntax.Expr := ⟨cs,.call fs ⟨args,[arg]⟩⟩
      have directOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) direct (RuntimeValue.ofCore bc.value) (heap s) := .call shape directCreation ac.closed beta
      have betaPath (k) : Core.Steps bc.cost ⟨.eval bc.core (ac.value::e.values),k,s⟩ ⟨.ret bc.value,k,s⟩ := by simpa only [ie,Resolved.LocalScope.values,List.map_cons] using bc.path k
      let core := Core.Expr.apply (.lambda .word (.product .word .unit) bc.core) ac.core
      have full (k) : Core.Steps (1+ac.cost+bc.cost+3) ⟨.eval core e.values,k,s⟩ ⟨.ret bc.value,k,s⟩ := CostStepComposition.apply (.cons .lambda .refl) (path ac same _) (betaPath [])
      let depth := max 2 (max ac.depth bc.depth)+1
      proof expectedLambda; proof ac.old; proof bc.oldCost; proof whole; proof directOld; proof (full [])
      check (decide (ac.core=.unary .wordNot (.var 2) ∧ bc.core=.letE (.unary .wordNot (.var 0)) (.pair (.var 0) (.var 3)) ∧ ac.cost=3 ∧ bc.cost=10 ∧ depth=5 ∧ p.value="p" ∧ Resolved.freshLocalId owner inputs.ids=sid 32 ∧ Resolved.freshLocalId owner inner.ids=sid 33 ∧ ac.value=.word w.bitNot ∧ bc.value=.pair (.word w.bitNot.bitNot) q)) "independent literal typing/Core/cost/depth/endpoints"
      if argValue : ac.value=.word w.bitNot then
        let savedCore := Core.Expr.apply (.var 0) (.unary .wordNot (.var 1))
        let savedCoreRows := [Core.Value.closure .word (.product .word .unit) bc.core e.values,.word w,q]
        have savedPath : Core.Steps (1+3+bc.cost+3) (.initial savedCore savedCoreRows s) (.final bc.value s) :=
          CostStepComposition.apply (.cons (.var rfl) .refl) (CostStepComposition.unary (.cons (.var rfl) .refl) rfl) (by simpa only [argValue,Core.State.initial,Core.State.final] using betaPath [])
        coreRuns savedPath
        coreRuns (full []); coreRuns (betaPath []); coreRuns (path ac same [])
        match made : evaluateClosedSourceExpression? 2 owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ with
        | none => throw (IO.userError "actual grouped creation")
        | some (actualClosure,calleeStore) =>
          have madeEq := (evaluateClosedSourceExpression?_sound made).deterministic creation
          match arun : evaluateClosedSourceExpression? ac.depth owner inputs.names (up e) calleeStore arg with
          | none => throw (IO.userError "actual argument after callee store")
          | some (actualArg,argumentStore) =>
            have ae := evaluateClosedSourceExpression?_sound arun
            have ae0 : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) arg actualArg argumentStore := by rw [madeEq.2] at ae; exact ae
            exprImages ac same ae0
            have argEq := ae0.deterministic ac.closed
            have fnEval : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ saved calleeStore := by simpa only [madeEq.1] using evaluateClosedSourceExpression?_sound made
            have argEval : ClosedSourceExpressionEvaluates owner inputs.names (up e) calleeStore arg (RuntimeValue.ofCore ac.value) (heap s) := by simpa only [argEq.1,argEq.2] using ae
            match brun : evaluateClosedSourceBody? bc.depth owner inner.names ((Resolved.freshLocalId owner inputs.ids,actualArg)::up e) argumentStore b with
            | none => throw (IO.userError "actual body after argument store")
            | some (bv,bst) =>
              have be := evaluateClosedSourceBody?_sound brun
              have normalized : ClosedSourceBodyEvaluates owner inner.names (up ie) (heap s) b bv bst := by simpa only [argEq.1,argEq.2,ie,up,List.map_cons] using be
              bodyImages bc same1 normalized
            closedRuns depth whole (fun {a z} actual => consume (a:=a) (z:=z) (Core.steps_from_initial_sound (betaPath [])) (closedSourceExpectedDataLambda_invocation_core_iff shape bc.gate checked same fnEval argEval (callSpan:=cs) (argumentsSpan:=args) (actualValue:=a) (actualFinal:=z)) (by simpa only [original] using actual))
            have directImage {a z} : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) direct a z ↔ ∃ v t, a=RuntimeValue.ofCore v ∧ z=heap t ∧ Core.Evaluates e.values s core v t := by
              obtain ⟨r,res,low,_⟩ := ac.elaboration
              exact closedSourceExpectedDataLambda_application_core_iff shape bc.gate checked same ac.gate res (same ▸ low)
            closedRuns depth directOld (fun actual => consume (Core.steps_from_initial_sound (full [])) directImage actual)
            let cr := rows actualClosure w
            have fn : ClosedSourceExpressionEvaluates caller names cr calleeStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ saved calleeStore := by rw [← madeEq.1]; exact .reference .head (.tail (by decide) .head)
            have savedArg : ClosedSourceExpressionEvaluates caller names cr calleeStore ⟨uas,.unary ⟨uos,.bitNot⟩ ⟨ws,.identifier ⟨wn,"w"⟩⟩⟩ (RuntimeValue.ofCore ac.value) (heap s) := by rw [madeEq.2,argValue]; simp only [RuntimeValue.ofCore]; apply ClosedSourceExpressionEvaluates.bitNot; exact .reference (.tail (by change "picked" ≠ "w"; decide) .head) .head
            have savedOld : ClosedSourceExpressionEvaluates caller names cr calleeStore picked (RuntimeValue.ofCore bc.value) calleeStore := by rw [madeEq.2,savedShape]; exact .call shape (by simpa only [madeEq.2] using fn) (by simpa only [madeEq.2] using savedArg) beta
            proof fn; proof savedArg; proof savedOld
            match fetched : evaluateClosedSourceExpression? 1 caller names cr calleeStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ with
            | none => throw (IO.userError "actual saved callee")
            | some (actualFn,savedCalleeStore) =>
              have feq := (evaluateClosedSourceExpression?_sound fetched).deterministic fn
              match sar : evaluateClosedSourceExpression? 2 caller names cr savedCalleeStore ⟨uas,.unary ⟨uos,.bitNot⟩ ⟨ws,.identifier ⟨wn,"w"⟩⟩⟩ with
              | none => throw (IO.userError "actual saved argument")
              | some (sa,sas) =>
                have sae := evaluateClosedSourceExpression?_sound sar
                have sae0 : ClosedSourceExpressionEvaluates caller names cr calleeStore ⟨uas,.unary ⟨uos,.bitNot⟩ ⟨ws,.identifier ⟨wn,"w"⟩⟩⟩ sa sas := by rw [feq.2] at sae; exact sae
                have seq := sae0.deterministic savedArg
                have sf : ClosedSourceExpressionEvaluates caller names cr calleeStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ saved savedCalleeStore := by simpa only [feq.1] using evaluateClosedSourceExpression?_sound fetched
                have se : ClosedSourceExpressionEvaluates caller names cr savedCalleeStore ⟨uas,.unary ⟨uos,.bitNot⟩ ⟨ws,.identifier ⟨wn,"w"⟩⟩⟩ (RuntimeValue.ofCore ac.value) (heap s) := by simpa only [seq.1,seq.2] using sae
                match sbr : evaluateClosedSourceBody? bc.depth owner inner.names ((Resolved.freshLocalId owner inputs.ids,sa)::up e) sas b with
                | none => throw (IO.userError "actual saved body")
                | some (sv,ss) => bodyImages bc same1 (v:=sv) (st:=ss) (by simpa only [seq.1,seq.2,ie,up,List.map_cons] using evaluateClosedSourceBody?_sound sbr)
                closedRuns depth savedOld (fun {a z} actual => consume (a:=a) (z:=z) (Core.steps_from_initial_sound (betaPath [])) (closedSourceExpectedDataLambda_invocation_core_iff shape bc.gate checked same sf se (callSpan:=pcs) (argumentsSpan:=pas) (actualValue:=a) (actualFinal:=z)) (by simpa only [savedShape] using actual))
        let wrong : Syntax.Expr := ⟨cs,.unary ⟨cs,.bitNot⟩ (ref 0 1 "bad")⟩
        have admitted : ClosedSourceDataExpression wrong := .bitNot .reference
        have badOperand : ClosedSourceExpressionEvaluates owner [("bad",sid 1)] [(sid 1,.bool true)] (heap s) (ref 0 1 "bad") (.bool true) (heap s) := .reference .head .head
        have impossible : ∀ a z, ¬ ClosedSourceExpressionEvaluates owner [("bad",sid 1)] [(sid 1,.bool true)] (heap s) wrong a z := by
          intro a z ev; dsimp only [wrong] at ev; cases ev with | bitNot child => have eq := child.deterministic badOperand; cases eq.1 | creation sh => cases sh
        proof admitted; proof badOperand; reject impossible
        let over : Syntax.Expr := ⟨cs,.unary ⟨cs,.bitNot⟩ src⟩
        have excluded : ¬ ClosedSourceDataExpression over := by intro gate; dsimp only [over] at gate; cases gate with | bitNot child => rw [original] at child; cases child
        proof excluded
        match val : bc.value with
        | .pair x y =>
          have no : ∀ a z, ¬ ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) over a z := by
            intro a z ev; dsimp only [over] at ev; cases ev with
            | bitNot child => have eq := child.deterministic whole; simp only [val,RuntimeValue.ofCore] at eq; cases eq.1
            | creation sh => cases sh
          reject no
        | _ => throw (IO.userError "independent original pair endpoint required")
      else throw (IO.userError "independent argument endpoint")
    | _ => throw (IO.userError "actual inferred lambda")
  | _,_ => throw (IO.userError "actual grouped and saved call")
end Tests.ParsedExpectedWordUnaryDataBridge
open Tests.ParsedExpectedWordUnaryDataBridge in
def Tests.frontendParsedExpectedWordUnaryDataBridgeTests : IO Unit := do
  let q := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  for w in [Solcore.Core.Word.ofNatModulo 0,Solcore.Core.Word.ofNatModulo 1,Solcore.Core.Word.ofNatModulo (2^256-1)] do
    for s in [[],[q,.cellRef .word 900,.hostFunction .storageWrite,.unit]] do exercise w q s
