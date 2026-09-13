import Solcore.Frontend.ExpectedDataLambdaApplicationProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.LocalExpressionCostCorrespondence
import Solcore.Frontend.LocalExpressionCostErasureProperties
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.WordLessCostStepComposition
import Solcore.Frontend.LocalFunctionApplicationStepComposition
import Solcore.Syntax.Parser.Term
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedExpectedBoolUnaryDataBridge
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"UnaryData",by decide⟩],by decide⟩⟩,297⟩
private def caller := {owner with declarationIndex := 298}
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def fid (n : Nat) : Resolved.LocalId := ⟨{owner with declarationIndex := 901},n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"q",sid 7,.unit⟩,⟨"c",sid 31,.bool⟩,⟨"q",fid 900,.word⟩],by decide⟩
private def types : TypeNameTable := [(["Bool"],.bool)]
private def env (b : Bool) (q : Core.Value) : Resolved.Environment := [(sid 7,q),(sid 31,.bool b),(fid 900,.word (Core.Word.ofNatModulo 99))]
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
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
  | ⟨_,.identifier name⟩ => match named : t.names.lookup? name.value with
    | some i => match typed : t.context.lookup? i, found : e.lookup? i, indexed : Resolved.LocalScope.index? t.context.ids i with
      | some ty,some v,some n => return ⟨.var n,ty,v,1,1,by rw [shape]; exact .reference,
          by rw [shape]; exact ⟨.var i,.identifier (LocalNameTable.lookup?_iff.mp named),.var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩,
          by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
          by rw [shape]; exact .reference (LocalNameTable.lookup?_iff.mp named) (mapped (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | _,_,_ => throw (IO.userError "original reference row")
    | none => throw (IO.userError "original reference name")
  | ⟨_,.group child⟩ =>
    let h ← expr t e s child
    return ⟨h.core,h.type,h.value,h.cost,h.depth+1,by rw [shape]; exact .group h.gate,
      by obtain ⟨r,a,b,c⟩ := h.elaboration; rw [shape]; exact ⟨r,.group a,b,c⟩,
      by rw [shape]; exact .group h.old,by rw [shape]; exact .group h.closed⟩
  | ⟨_,.unary ⟨_,.logicalNot⟩ child⟩ =>
    let h ← expr t e s child
    if typed : h.type=.bool then match value : h.value with
      | .bool b => return ⟨.unary .boolNot h.core,.bool,.bool (!b),h.cost+2,h.depth+1,
          by rw [shape]; exact .logicalNot h.gate,
          by obtain ⟨r,a,b,c⟩ := h.elaboration; rw [shape]; exact ⟨.unary .boolNot r,.logicalNot a,.unary b,.unary (by rw [typed] at c; exact c)⟩,
          by rw [shape]; exact .logicalNot (value ▸ h.old),
          by rw [shape]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.logicalNot (by simpa only [value,RuntimeValue.ofCore] using h.closed)⟩
      | _ => throw (IO.userError "original runtime Bool")
    else throw (IO.userError "original static Bool")
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
    let l ← expr t e s left; let r ← expr t e s right
    return ⟨.pair l.core r.core,.product l.type r.type,.pair l.value r.value,l.cost+r.cost+3,max l.depth r.depth+1,
      by rw [shape]; exact .pair l.gate r.gate,
      by obtain ⟨a,ar,al,alt⟩ := l.elaboration; obtain ⟨b,br,bl,bt⟩ := r.elaboration; rw [shape]; exact ⟨.pair a b,.pair ar br,.pair al bl,.pair alt bt⟩,
      by rw [shape]; exact .pair l.old r.old,by rw [shape]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.pair l.closed r.closed⟩
  | _ => throw (IO.userError "bounded original data expression")
termination_by sizeOf src
private structure BC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) where
  core : Core.Expr
  value : Core.Value
  cost : Nat
  depth : Nat
  gate : ClosedSourceDataBody src
  elaboration : ComputationReturnTreeElaborates Child types owner t src core (.product .bool .unit)
  old : ComputationReturnTreeEvaluates LocalExpressionEvaluates owner t.names e s src value s
  closed : ClosedSourceBodyEvaluates owner t.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore value) (s.map RuntimeValue.ofCore)
  path : ∀ k, Core.Steps cost ⟨.eval core e.values,k,s⟩ ⟨.ret value,k,s⟩
private def body (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) (same : e.ids=t.context.ids) : IO (BC t e s src) := do
  match shape : src with
  | ⟨bs,[⟨_,.letDecl name (some ⟨_,.named ann none⟩) (some init)⟩,⟨rs,.returnStmt (some result)⟩]⟩ =>
    let h ← expr t e s init
    match found : types.lookup? (qualifiedTypeNameKey ann) with
    | some ty =>
      if typed : ty=.bool ∧ h.type=.bool then
        let t1 := t.bindFresh owner name.value .bool
        let e1 : Resolved.Environment := (Resolved.freshLocalId owner t.ids,h.value)::e
        have same1 : e1.ids=t1.context.ids := by simpa only [e1,t1,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
        let r ← expr t1 e1 s result
        if rt : r.type=.product .bool .unit then
          return ⟨.letE h.core r.core,r.value,h.cost+r.cost+2,max h.depth (r.depth+1)+1,
            by rw [shape]; exact .binding h.gate (.expression r.gate),
            by rw [shape]; exact .binding (.named (typed.1 ▸ TypeNameTable.lookup?_iff.mp found)) (typed.2 ▸ h.elaboration) (.expression (rt ▸ r.elaboration)),
            by rw [shape]; apply ComputationReturnTreeEvaluates.binding h.old.erase
               simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluates.expression (blockSpan:=bs) (returnSpan:=rs) (owner:=owner) r.old.erase,
            by rw [shape]; apply ClosedSourceBodyEvaluates.binding h.closed
               simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using ClosedSourceBodyEvaluates.expression (blockSpan:=bs) (returnSpan:=rs) r.closed,
            fun k => CostStepComposition.letE (path h same _) (by simpa only [e1,Resolved.LocalScope.values,List.map_cons] using path r same1 k)⟩
        else throw (IO.userError "pair result type")
      else throw (IO.userError "Bool typed shadow")
    | none => throw (IO.userError "annotation name")
  | _ => throw (IO.userError "original shadow/return body")
private def spans (src : Syntax.Expr) : List Syntax.SourceSpan :=
  match src with
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.group e⟩ => s :: spans e
  | ⟨s,.unary op e⟩ => s :: op.span :: spans e
  | ⟨s,.tuple ⟨ts,[a,b]⟩⟩ => [s,ts] ++ spans a ++ spans b
  | ⟨s,.call f ⟨args,[a]⟩⟩ => [s,args] ++ spans f ++ spans a
  | ⟨s,.lambda kw ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨bs,[⟨ls,.letDecl name (some ⟨as,.named ⟨ns,⟨⟨tn,[]⟩⟩⟩ none⟩) (some init)⟩,⟨rs,.returnStmt (some result)⟩]⟩⟩ =>
      [s,kw,ps,p,n.span,bs,ls,name.span,as,ns,tn.span,rs] ++ spans init ++ spans result
  | _ => []
termination_by sizeOf src
private def parsed (text : String) (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"bool-unary-data-"++text++".sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && src.span==Syntax.SourceSpan.fullFile file) "whole original SourceFile/EOF"
    check ((spans src).all (fun s => s.isValidFor file) && (spans src).map (fun s => (s.startByte,s.endByte))==ranges) "complete handwritten nesting/operator ranges"
    return src
  | _ => throw (IO.userError "parser")
private theorem core_endpoint {P : RuntimeValue → List RuntimeValue → Prop} {e : Core.Environment} {s : Core.Store} {c : Core.Expr} {v : Core.Value}
    (original : Core.Evaluates e s c v s)
    (image : ∀ a t, P a t ↔ ∃ w u, a=RuntimeValue.ofCore w ∧ t=u.map RuntimeValue.ofCore ∧ Core.Evaluates e s c w u)
    {a t} (actual : P a t) : P a t ∧ a=RuntimeValue.ofCore v ∧ t=s.map RuntimeValue.ofCore := by
  obtain ⟨w,u,hv,hs,ev⟩ := (image a t).mp actual
  obtain ⟨vw,ss⟩ := Core.evaluation_deterministic ev original
  rw [vw] at hv; rw [ss] at hs
  have back := (image a t).mpr ⟨v,s,hv,hs,original⟩
  exact ⟨back,hv,hs⟩
private def expressionImages {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids)
    {a st} (actual : ClosedSourceExpressionEvaluates owner t.names (up e) (s.map RuntimeValue.ofCore) src a st) : IO Unit := do
  proof h.closed; proof h.old.erase
  have localForward := h.gate.local_evaluates_iff.mp actual
  proof ((h.gate.local_evaluates_iff (owner:=owner)).mpr localForward)
  proof (show ClosedSourceExpressionEvaluates owner t.names (up e) (s.map RuntimeValue.ofCore) src a st ∧ a=RuntimeValue.ofCore h.value ∧ st=s.map RuntimeValue.ofCore from by
    obtain ⟨r,res,low,_⟩ := h.elaboration
    exact core_endpoint (Core.steps_from_initial_sound (path h same [])) (fun _ _ => h.gate.core_evaluates_iff res (same ▸ low)) actual)
private def bodyImages {t e s src} (h : BC t e s src) (same : e.ids=t.context.ids)
    {a st} (actual : ClosedSourceBodyEvaluates owner t.names (up e) (s.map RuntimeValue.ofCore) src a st) : IO Unit := do
  proof h.closed; proof h.old
  have localForward := h.gate.local_evaluates_iff.mp actual
  proof (h.gate.local_evaluates_iff.mpr localForward)
  have checked := (elaborateComputationReturnTree?_iff elaborateLocalExpression?_iff).mpr h.elaboration
  proof (core_endpoint (Core.steps_from_initial_sound (h.path [])) (fun _ _ => h.gate.core_evaluates_iff checked same) actual)
private def pairedRun {own ns rows src e s c v} (d k : Nat)
    (original : ClosedSourceExpressionEvaluates own ns rows (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore v) (s.map RuntimeValue.ofCore))
    (steps : Core.Steps k (.initial c e s) (.final v s))
    (images : ∀ a st, ClosedSourceExpressionEvaluates own ns rows (s.map RuntimeValue.ofCore) src a st → a=RuntimeValue.ofCore v ∧ st=s.map RuntimeValue.ofCore)
    (start : List RuntimeValue) (startEq : start=s.map RuntimeValue.ofCore) : IO Unit := do
  proof original; proof steps
  for budget in [0,k-1,k,k+3] do
    match r : Core.runStateful budget (.initial c e s) with
    | .done cv fs => proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound r) (Core.steps_from_initial_sound steps)); check (budget≥k) "Core lower cost"
    | .outOfFuel _ => check (budget<k) "Core required cost"
    | _ => throw (IO.userError "Core stuck")
  for budget in [0,d-1,d,d+3] do
    match r : evaluateClosedSourceExpression? budget own ns rows start src with
    | none => check (budget<d) "closed required depth"
    | some (a,st) =>
      have endpoints := images a st (by simpa only [startEq] using evaluateClosedSourceExpression?_sound r)
      match cr : Core.runStateful k (.initial c e s) with
      | .done cv fs =>
        have same := Core.evaluation_deterministic (Core.runStateful_evaluation_sound cr) (Core.steps_from_initial_sound steps)
        proof (show a=RuntimeValue.ofCore cv ∧ st=fs.map RuntimeValue.ofCore from by simpa only [same.1,same.2] using endpoints)
        check (budget≥d && a.toCore?==some cv && st.mapM RuntimeValue.toCore?==some fs) "both actual whole images"
      | _ => throw (IO.userError "actual Core endpoint")
private def callerNames : LocalNameTable := [("picked",cid 7),("c",cid 31),("picked",cid 7),("q",fid 900)]
private def callerRows (fn : RuntimeValue) (b : Bool) := [(cid 7,fn),(cid 31,RuntimeValue.bool b),(cid 7,.unit),(fid 900,fn)]
private def exercise (b : Bool) (q : Core.Value) (s : Core.Store) : IO Unit := do
  let src ← parsed "(lam(p){let p:Bool=!p;return(p,q);})(!c)"
    [(0,40),(36,40),(0,36),(1,35),(1,4),(4,7),(5,6),(5,6),(7,35),(8,22),(12,13),(14,18),(14,18),(14,18),(22,34),(19,21),(19,20),(20,21),(20,21),(28,33),(28,33),(29,30),(29,30),(31,32),(31,32),(37,39),(37,38),(38,39),(38,39)]
  let invoked ← parsed "picked(!c)" [(0,10),(6,10),(0,6),(0,6),(7,9),(7,8),(8,9),(8,9)]
  let e := env b q
  match outer : src, savedShape : invoked with
  | ⟨cs,.call ⟨gs,.group fs⟩ ⟨args,[arg]⟩⟩,⟨ics,.call ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ ⟨iargs,[⟨iaSpan,.unary ⟨opSpan,.logicalNot⟩ ⟨iaRefSpan,.identifier ⟨iaName,"c"⟩⟩⟩]⟩⟩ =>
    let fn : Syntax.Expr := ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩
    let ia : Syntax.Expr := ⟨iaSpan,.unary ⟨opSpan,.logicalNot⟩ ⟨iaRefSpan,.identifier ⟨iaName,"c"⟩⟩⟩
    proof outer; proof savedShape
    match lambda : fs with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred name⟩]⟩ none bs⟩ =>
      have shape : SourceUnaryLambdaShape fs name bs := by rw [lambda]; exact .inferred
      let ac ← expr inputs e s arg
      if av : ac.value=.bool (!b) then
        let inner := inputs.bindFresh owner name.value .bool
        let ie : Resolved.Environment := (Resolved.freshLocalId owner inputs.ids,ac.value)::e
        have aligned : e.ids=inputs.context.ids := rfl
        have aligned1 : ie.ids=inner.context.ids := by simpa only [ie,inner,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) aligned
        let bc ← body inner ie s bs aligned1
        have header : ExpectedUnaryLambdaHeaderDeclares types owner inputs fs (.function .bool (.product .bool .unit)) ⟨inner,bs,.bool,.product .bool .unit⟩ := by rw [lambda]; exact .lambda .inferred .omitted
        have expected : ExpectedComputationLambdaElaborates Child types owner inputs fs (.lambda .bool (.product .bool .unit) bc.core) (.function .bool (.product .bool .unit)) := .lambda header .bool (.product .bool .unit) bc.elaboration
        have checked := (elaborateExpectedComputationLambda?_iff elaborateLocalExpression?_iff).mpr expected
        have beta : Core.Steps bc.cost (.initial bc.core (ac.value::e.values) s) (.final bc.value s) := by simpa only [ie,Resolved.LocalScope.values,List.map_cons,Core.State.initial,Core.State.final] using bc.path []
        let core := Core.Expr.apply (.lambda .bool (.product .bool .unit) bc.core) ac.core
        have full : Core.Steps (1+ac.cost+bc.cost+3) (.initial core e.values s) (.final bc.value s) := CostStepComposition.apply (.cons .lambda .refl) (path ac aligned _) beta
        let closure := RuntimeValue.sourceClosure fs owner inputs.names (up e)
        have actualBody : ClosedSourceBodyEvaluates owner ((name.value,Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
            ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),RuntimeValue.ofCore ac.value)::up e) (s.map RuntimeValue.ofCore) bs (RuntimeValue.ofCore bc.value) (s.map RuntimeValue.ofCore) := by
          simpa only [ie,inner,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using bc.closed
        have creation : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ closure (s.map RuntimeValue.ofCore) := .group (.creation shape)
        proof checked; proof bc.old; proof actualBody; proof full; proof creation
        check (ac.depth==2 && ac.cost==3 && bc.depth==4 && bc.cost==10 && bc.value==Core.Value.pair (.bool b) q) "independent D and K and shadow endpoint"
        pairedRun ac.depth ac.cost ac.closed (path ac aligned []) (fun v st h => by
          obtain ⟨r,res,low,_⟩ := ac.elaboration
          exact (core_endpoint (Core.steps_from_initial_sound (path ac aligned [])) (fun _ _ => ac.gate.core_evaluates_iff res (aligned ▸ low)) h).2) (s.map RuntimeValue.ofCore) rfl
        for k in [0,bc.cost-1,bc.cost,bc.cost+3] do
          match cr : Core.runStateful k (.initial bc.core (ac.value::e.values) s) with
          | .done v st => proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound cr) (Core.steps_from_initial_sound beta)); check (k≥bc.cost) "Core body lower cost"
          | .outOfFuel _ => check (k<bc.cost) "Core body required cost"
          | _ => throw (IO.userError "Core body stuck")
        let execute (own : Resolved.DeclarationId) (ns : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue) (cspan aspan : Syntax.SourceSpan) (callee argument : Syntax.Expr) (fd : Nat) (start : List RuntimeValue) (startEq : start=s.map RuntimeValue.ofCore)
            (f : ClosedSourceExpressionEvaluates own ns rows (s.map RuntimeValue.ofCore) callee closure (s.map RuntimeValue.ofCore))
            (a : ClosedSourceExpressionEvaluates own ns rows (s.map RuntimeValue.ofCore) argument (RuntimeValue.ofCore ac.value) (s.map RuntimeValue.ofCore))
            (validate : ∀ v st, ClosedSourceExpressionEvaluates own ns rows (s.map RuntimeValue.ofCore) argument v st → IO Unit) : IO Unit := do
          have original := ClosedSourceExpressionEvaluates.call (span:=cspan) (argumentsSpan:=aspan) shape f a actualBody
          proof original
          match fr : evaluateClosedSourceExpression? fd own ns rows start callee with
          | none => throw (IO.userError "actual callee")
          | some (actualFn,calleeStore) =>
            have fe := (evaluateClosedSourceExpression?_sound (startEq ▸ fr)).deterministic f
            match ar : evaluateClosedSourceExpression? ac.depth own ns rows calleeStore argument with
            | none => throw (IO.userError "actual argument after calleeStore")
            | some (actualArg,bodyStore) =>
              have ae := (evaluateClosedSourceExpression?_sound (fe.2 ▸ ar)).deterministic a
              validate actualArg bodyStore (by simpa only [fe.2] using evaluateClosedSourceExpression?_sound ar)
              let entryRows := (Resolved.freshLocalId owner inputs.ids,actualArg)::up e
              have entrySame : entryRows=up ie := by simp only [entryRows,ie,up,List.map_cons,ae.1]
              for depth in [0,bc.depth-1,bc.depth,bc.depth+3] do
                match br : evaluateClosedSourceBody? depth owner inner.names entryRows bodyStore bs with
                | none => check (depth<bc.depth) "body depth"
                | some (v,st) => bodyImages bc aligned1 (a:=v) (st:=st) (by simpa only [entrySame,ae.2] using evaluateClosedSourceBody?_sound br); check (depth≥bc.depth) "body lower depth"
              have fActual : ClosedSourceExpressionEvaluates own ns rows (s.map RuntimeValue.ofCore) callee closure calleeStore := by simpa only [startEq,fe.1] using evaluateClosedSourceExpression?_sound fr
              have aActual : ClosedSourceExpressionEvaluates own ns rows calleeStore argument (RuntimeValue.ofCore ac.value) (s.map RuntimeValue.ofCore) := by simpa only [ae.1,ae.2] using evaluateClosedSourceExpression?_sound ar
              pairedRun (max fd (max ac.depth bc.depth)+1) (1+ac.cost+bc.cost+3) original full (fun v st h =>
                (core_endpoint (Core.steps_from_initial_sound beta) (fun _ _ => closedSourceExpectedDataLambda_invocation_core_iff shape bc.gate checked aligned fActual aActual) h).2) start startEq
        execute owner inputs.names (up e) cs args ⟨gs,.group fs⟩ arg 2 (s.map RuntimeValue.ofCore) rfl creation ac.closed (fun _ _ h => expressionImages ac aligned h)
        match made : evaluateClosedSourceExpression? 2 owner inputs.names (up e) (s.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ with
        | none => throw (IO.userError "actual closure creation")
        | some (returned,creationStore) =>
          have ce := (evaluateClosedSourceExpression?_sound made).deterministic creation
          proof ce
          execute caller callerNames (callerRows returned b) ics iargs fn ia 1 creationStore ce.2
            (by rw [← ce.1]; exact .reference .head .head)
            (by simp only [av,RuntimeValue.ofCore]; exact .logicalNot (.reference (id:=cid 31) (.tail (by change "picked"≠"c"; decide) .head) (.tail (by decide) .head)))
            (fun _ _ h => proof h)
        have direct := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=args) shape (.creation shape) ac.closed actualBody
        pairedRun (max 1 (max ac.depth bc.depth)+1) (1+ac.cost+bc.cost+3) direct full (fun v st h => by
          obtain ⟨r,res,low,_⟩ := ac.elaboration
          exact (core_endpoint (Core.steps_from_initial_sound full) (fun _ _ => closedSourceExpectedDataLambda_application_core_iff shape bc.gate checked aligned ac.gate res (aligned ▸ low)) h).2) (s.map RuntimeValue.ofCore) rfl
      else throw (IO.userError "original argument endpoint")
    | _ => throw (IO.userError "original inferred lambda")
  | _,_ => throw (IO.userError "original grouped and saved calls")
private def boundaries : IO Unit := do
  let wrong ← parsed "!c" [(0,2),(0,1),(1,2),(1,2)]
  match original : wrong with
  | ⟨_,.unary ⟨_,.logicalNot⟩ ⟨refSpan,.identifier name⟩⟩ =>
    let ns : LocalNameTable := [(name.value,sid 0)]
    let rows : Resolved.LocalScope RuntimeValue := [(sid 0,.word (Core.Word.ofNatModulo 0))]
    have gate : ClosedSourceDataExpression wrong := by rw [original]; exact .logicalNot .reference
    have impossible (a st) : ¬ ClosedSourceExpressionEvaluates owner ns rows [.unit] wrong a st := by
      rw [original]; intro ev; cases ev with
      | logicalNot child =>
          have reference : ClosedSourceExpressionEvaluates owner ns rows [.unit] ⟨refSpan,.identifier name⟩ (.word (Core.Word.ofNatModulo 0)) [.unit] := .reference .head .head
          have same := child.deterministic reference; cases same.1
      | creation shape => cases shape
    proof gate; proof impossible
    for d in [0,1,2,5] do
      match run : evaluateClosedSourceExpression? d owner ns rows [.unit] wrong with
      | none => pure ()
      | some _ => proof (impossible _ _ (evaluateClosedSourceExpression?_sound run)); throw (IO.userError "impossible wrong operand")
  | _ => throw (IO.userError "wrong unary source")
  let outside ← parsed "!picked(!c)" [(0,11),(0,1),(1,11),(7,11),(1,7),(1,7),(8,10),(8,9),(9,10),(9,10)]
  match original : outside with
  | ⟨_,.unary ⟨_,.logicalNot⟩ ⟨_,.call _ _⟩⟩ =>
    proof (show ¬ ClosedSourceDataExpression outside from by rw [original]; intro h; cases h with | logicalNot child => cases child)
    check ((evaluateClosedSourceExpression? 20 owner [] [] [.unit] outside).isNone) "nongated missing callee"
  | _ => throw (IO.userError "unary call source")
end Tests.ParsedExpectedBoolUnaryDataBridge
open Tests.ParsedExpectedBoolUnaryDataBridge in
def Tests.frontendParsedExpectedBoolUnaryDataBridgeTests : IO Unit := do
  let q := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700]
  for b in [false,true] do
    for s in [[],[q,.hostFunction .storageWrite,.cellRef (.function .word .word) 900,.unit]] do exercise b q s
  boundaries
