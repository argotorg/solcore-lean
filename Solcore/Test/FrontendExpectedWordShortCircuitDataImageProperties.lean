import Solcore.Frontend.Expected
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalTypeInputs
import Solcore.Resolved.LocalScope

set_option autoImplicit false
namespace Tests.ExpectedWordShortCircuitDataImages
open Solcore Solcore.Frontend

private def up (e : Resolved.Environment) := e.map (fun r => (r.1, RuntimeValue.ofCore r.2))
private def heap (s : Core.Store) := s.map RuntimeValue.ofCore
private def ref (s : Syntax.SourceSpan) (n : String) : Syntax.Expr := ⟨s, .identifier ⟨s,n⟩⟩
private def guard (s : Nat → Syntax.SourceSpan) (o : Bool) : Syntax.Expr :=
  ⟨s 0, .group ⟨s 1, .binary (ref (s 2) "a") ⟨s 3, if o then .logicalOr else .logicalAnd⟩ (ref (s 4) "b")⟩⟩
private def expr (s : Nat → Syntax.SourceSpan) (o : Bool) : Syntax.Expr :=
  ⟨s 5, .conditional (guard s o) (s 6) (ref (s 7) "p") (s 8)
    ⟨s 9, .unary ⟨s 10,.bitNot⟩ (ref (s 11) "p")⟩⟩
private def body (s : Nat → Syntax.SourceSpan) (o : Bool) : Syntax.Block :=
  ⟨s 12,[⟨s 13,.returnStmt (some (expr s o))⟩]⟩
private def source (s : Nat → Syntax.SourceSpan) (o : Bool) : Syntax.Expr :=
  ⟨s 14,.lambda (s 15) ⟨s 16,[⟨s 17,.inferred ⟨s 18,"p"⟩⟩]⟩ none (body s o)⟩
private def call (s : Nat → Syntax.SourceSpan) (fn arg : Syntax.Expr) : Syntax.Expr :=
  ⟨s 19,.call fn ⟨s 20,[arg]⟩⟩
private def choose (o a b : Bool) : Bool := if o then a || b else a && b
private def result (o a b : Bool) (w : Core.Word) : Core.Value :=
  .word (if choose o a b then w else w.bitNot)
private def guardCore (o : Bool) (a b : Nat) : Core.Expr :=
  if o then .ifE (.var a) (.bool true) (.var b) else .ifE (.var a) (.var b) (.bool false)
private def code (o : Bool) (a b : Nat) : Core.Expr :=
  .ifE (guardCore o (a+1) (b+1)) (.var 0) (.unary .wordNot (.var 0))
private def entry (owner : Resolved.DeclarationId) (t : LocalTypeInputs) := t.bindFresh owner "p" .word
private def env (owner : Resolved.DeclarationId) (t : LocalTypeInputs) (e : Resolved.Environment) (w : Core.Word) : Resolved.Environment :=
  (Resolved.freshLocalId owner t.ids, Core.Value.word w) :: e
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail ne _ ih => exact .tail ne ih
private theorem fresh_ne {o : Resolved.DeclarationId} {t : LocalTypeInputs} {i : Resolved.LocalId} {ty : Core.Ty}
    (h : Resolved.LocalScope.Lookup t.context i ty) : Resolved.freshLocalId o t.ids ≠ i := by
  intro eq; apply Resolved.freshLocalId_not_mem o t.ids
  rw [eq, ← LocalTypeInputs.context_ids]; exact List.mem_map.mpr ⟨(i,ty),h.mem,rfl⟩
private theorem gate (s : Nat → Syntax.SourceSpan) (o : Bool) : ClosedSourceDataExpression (expr s o) := by
  apply ClosedSourceDataExpression.conditional
  · apply ClosedSourceDataExpression.group; cases o
    · exact .logicalAnd .reference .reference
    · exact .logicalOr .reference .reference
  · exact .reference
  · exact .bitNot .reference

private structure Frame where
  spans : Nat → Syntax.SourceSpan
  owner : Resolved.DeclarationId
  inputs : LocalTypeInputs
  environment : Resolved.Environment
  isOr : Bool
  left : Bool
  right : Bool
  aid : Resolved.LocalId
  bid : Resolved.LocalId
  ai : Nat
  bi : Nat
  aligned : environment.ids = inputs.context.ids
  an : LocalNameTable.Lookup inputs.names "a" aid
  bn : LocalNameTable.Lookup inputs.names "b" bid
  aTyped : Resolved.LocalScope.Lookup inputs.context aid .bool
  bTyped : Resolved.LocalScope.Lookup inputs.context bid .bool
  av : Resolved.LocalScope.Lookup environment aid (.bool left)
  bv : Resolved.LocalScope.Lookup environment bid (.bool right)
  ax : Resolved.LocalScope.IndexOf inputs.context.ids aid ai
  bx : Resolved.LocalScope.IndexOf inputs.context.ids bid bi
private theorem facts (f : Frame) (s : Core.Store) (w : Core.Word) :
    elaborateComputationReturnTree? elaborateLocalExpression? [] f.owner (entry f.owner f.inputs)
      (body f.spans f.isOr) = some (code f.isOr f.ai f.bi,.word) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] f.owner f.inputs
      (source f.spans f.isOr) (.function .word .word) = some (.lambda .word .word (code f.isOr f.ai f.bi)) ∧
    ClosedSourceBodyEvaluates f.owner (entry f.owner f.inputs).names (up (env f.owner f.inputs f.environment w))
      (heap s) (body f.spans f.isOr) (RuntimeValue.ofCore (result f.isOr f.left f.right w)) (heap s) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates f.owner (entry f.owner f.inputs).names
      (env f.owner f.inputs f.environment w) s (body f.spans f.isOr) (result f.isOr f.left f.right w) s ∧
    Core.Evaluates (.word w :: f.environment.values) s (code f.isOr f.ai f.bi) (result f.isOr f.left f.right w) s := by
  have an : LocalNameTable.Lookup (entry f.owner f.inputs).names "a" f.aid := .tail (by change ("p" : String) ≠ "a"; decide) f.an
  have bn : LocalNameTable.Lookup (entry f.owner f.inputs).names "b" f.bid := .tail (by change ("p" : String) ≠ "b"; decide) f.bn
  have aTyped : Resolved.LocalScope.Lookup (entry f.owner f.inputs).context f.aid .bool := .tail (fresh_ne f.aTyped) f.aTyped
  have bTyped : Resolved.LocalScope.Lookup (entry f.owner f.inputs).context f.bid .bool := .tail (fresh_ne f.bTyped) f.bTyped
  have av : Resolved.LocalScope.Lookup (env f.owner f.inputs f.environment w) f.aid (.bool f.left) := .tail (fresh_ne f.aTyped) f.av
  have bv : Resolved.LocalScope.Lookup (env f.owner f.inputs f.environment w) f.bid (.bool f.right) := .tail (fresh_ne f.bTyped) f.bv
  have ax : Resolved.LocalScope.IndexOf (entry f.owner f.inputs).context.ids f.aid (f.ai+1) := .tail (fresh_ne f.aTyped) f.ax
  have bx : Resolved.LocalScope.IndexOf (entry f.owner f.inputs).context.ids f.bid (f.bi+1) := .tail (fresh_ne f.bTyped) f.bx
  have checkExpr : elaborateLocalExpression? (entry f.owner f.inputs).names (entry f.owner f.inputs).context
      (expr f.spans f.isOr) = some (code f.isOr f.ai f.bi,.word) := by
    cases ho : f.isOr
    · exact elaborateLocalExpression?_complete (.conditional (.group (.logicalAnd (.identifier an) (.identifier bn)))
        (.identifier .head) (.bitNot (.identifier .head))) (.ifE (.ifE (.var ax) (.var bx) .bool) (.var .head) (.unary (.var .head)))
        (.ifE (.ifE (.var aTyped) (.var bTyped) .bool) (.var .head) (.unary (.var .head)))
    · exact elaborateLocalExpression?_complete (.conditional (.group (.logicalOr (.identifier an) (.identifier bn)))
        (.identifier .head) (.bitNot (.identifier .head))) (.ifE (.ifE (.var ax) .bool (.var bx)) (.var .head) (.unary (.var .head)))
        (.ifE (.ifE (.var aTyped) .bool (.var bTyped)) (.var .head) (.unary (.var .head)))
  have checked : ComputationReturnTreeElaborates (fun n t e c ty => elaborateLocalExpression? n t e = some (c,ty))
      [] f.owner (entry f.owner f.inputs) (body f.spans f.isOr) (code f.isOr f.ai f.bi) .word := .expression checkExpr
  have cg : ClosedSourceExpressionEvaluates f.owner (entry f.owner f.inputs).names
      (up (env f.owner f.inputs f.environment w)) (heap s) (guard f.spans f.isOr)
      (.bool (choose f.isOr f.left f.right)) (heap s) := by
    apply ClosedSourceExpressionEvaluates.group
    cases ho : f.isOr <;> cases ha : f.left
    · exact .andFalse (.reference an (by simpa only [ha,RuntimeValue.ofCore] using mapped av))
    · exact .andTrue (.reference an (by simpa only [ha,RuntimeValue.ofCore] using mapped av)) (.reference bn (by simpa [RuntimeValue.ofCore,choose] using mapped bv))
    · exact .orFalse (.reference an (by simpa only [ha,RuntimeValue.ofCore] using mapped av)) (.reference bn (by simpa [RuntimeValue.ofCore,choose] using mapped bv))
    · exact .orTrue (.reference an (by simpa only [ha,RuntimeValue.ofCore] using mapped av))
  have lg : LocalExpressionEvaluates (entry f.owner f.inputs).names (env f.owner f.inputs f.environment w)
      s (guard f.spans f.isOr) (.bool (choose f.isOr f.left f.right)) s := by
    apply LocalExpressionEvaluates.group
    cases ho : f.isOr <;> cases ha : f.left
    · exact .andFalse (.identifier an (ha ▸ av))
    · exact .andTrue (.identifier an (ha ▸ av)) (.identifier bn bv)
    · exact .orFalse (.identifier an (ha ▸ av)) (.identifier bn bv)
    · exact .orTrue (.identifier an (ha ▸ av))
  have ac : f.environment.values[f.ai]? = some (.bool f.left) :=
    (Resolved.LocalScope.lookup_iff_getElem? (f.aligned.symm ▸ f.ax)).mp f.av
  have bc : f.environment.values[f.bi]? = some (.bool f.right) :=
    (Resolved.LocalScope.lookup_iff_getElem? (f.aligned.symm ▸ f.bx)).mp f.bv
  have kg : Core.Evaluates (.word w :: f.environment.values) s (guardCore f.isOr (f.ai+1) (f.bi+1))
      (.bool (choose f.isOr f.left f.right)) s := by
    cases ho : f.isOr <;> cases ha : f.left
    · exact .ifFalse (.var (by simpa only [List.getElem?_cons_succ,ha] using ac)) .bool
    · exact .ifTrue (.var (by simpa only [List.getElem?_cons_succ,ha] using ac)) (.var bc)
    · exact .ifFalse (.var (by simpa only [List.getElem?_cons_succ,ha] using ac)) (.var bc)
    · exact .ifTrue (.var (by simpa only [List.getElem?_cons_succ,ha] using ac)) .bool
  have ce : ClosedSourceExpressionEvaluates f.owner (entry f.owner f.inputs).names
      (up (env f.owner f.inputs f.environment w)) (heap s) (expr f.spans f.isOr)
      (RuntimeValue.ofCore (result f.isOr f.left f.right w)) (heap s) := by
    cases hc : choose f.isOr f.left f.right <;> simp only [result,hc,Bool.false_eq_true,↓reduceIte,RuntimeValue.ofCore,up,env,List.map_cons]
    · exact .conditionalFalse (by simpa only [hc,up,env,List.map_cons,RuntimeValue.ofCore] using cg) (.bitNot (.reference .head .head))
    · exact .conditionalTrue (by simpa only [hc,up,env,List.map_cons,RuntimeValue.ofCore] using cg) (.reference .head .head)
  have le : LocalExpressionEvaluates (entry f.owner f.inputs).names (env f.owner f.inputs f.environment w)
      s (expr f.spans f.isOr) (result f.isOr f.left f.right w) s := by
    cases hc : choose f.isOr f.left f.right <;> simp only [result,hc,Bool.false_eq_true,↓reduceIte]
    · exact .ifFalse (hc ▸ lg) (.bitNot (.identifier .head .head))
    · exact .ifTrue (hc ▸ lg) (.identifier .head .head)
  have ke : Core.Evaluates (.word w :: f.environment.values) s (code f.isOr f.ai f.bi)
      (result f.isOr f.left f.right w) s := by
    cases hc : choose f.isOr f.left f.right <;> simp only [result,hc,Bool.false_eq_true,↓reduceIte]
    · exact .ifFalse (hc ▸ kg) (.unary (.var rfl) rfl)
    · exact .ifTrue (hc ▸ kg) (.var rfl)
  have expressionImages := (gate f.spans f.isOr).local_evaluates_iff (owner:=f.owner)
    (names:=(entry f.owner f.inputs).names) (environment:=env f.owner f.inputs f.environment w)
    (initialStore:=s) (actualValue:=RuntimeValue.ofCore (result f.isOr f.left f.right w)) (actualFinal:=heap s)
  obtain ⟨lv,ls,lvEq,lsEq,localRun⟩ := expressionImages.mp ce
  obtain ⟨lve,lse⟩ := localRun.deterministic le
  have independentReverse := expressionImages.mpr ⟨_,s,lvEq.trans (congrArg RuntimeValue.ofCore lve),
    lsEq.trans (congrArg heap lse),le⟩
  have ⟨resolved,resolution,lowering,_⟩ := elaborateLocalExpression?_iff.mp checkExpr
  have same : (env f.owner f.inputs f.environment w).ids = (entry f.owner f.inputs).context.ids := by
    simpa only [env,entry,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) f.aligned
  have coreImage := (gate f.spans f.isOr).core_evaluates_iff resolution (same ▸ lowering) (owner:=f.owner)
    (initialStore:=s) (actualValue:=RuntimeValue.ofCore (result f.isOr f.left f.right w)) (actualFinal:=heap s)
  obtain ⟨kv,ks,kvEq,ksEq,coreRun⟩ := coreImage.mp independentReverse
  have originalCore : Core.Evaluates (env f.owner f.inputs f.environment w).values s
      (code f.isOr f.ai f.bi) (result f.isOr f.left f.right w) s := by
    simpa only [env,Resolved.LocalScope.values,List.map_cons] using ke
  obtain ⟨kve,kse⟩ := Core.evaluation_deterministic coreRun originalCore
  have rebuilt := coreImage.mpr ⟨_,s,kvEq.trans (congrArg RuntimeValue.ofCore kve),
    ksEq.trans (congrArg heap kse),originalCore⟩
  exact ⟨(elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr checked,
    (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
      (.lambda (.lambda .inferred .omitted) .word .word checked), .expression rebuilt, .expression le, ke⟩
private theorem exactImage {P : RuntimeValue → List RuntimeValue → Prop} {e s c v}
    (old : Core.Evaluates e s c v s)
    (image : ∀ a z, P a z ↔ ∃ x t, a=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e s c x t) :
    ∀ a z, P a z ↔ a=RuntimeValue.ofCore v ∧ z=heap s := by
  intro a z; constructor
  · intro actual; obtain ⟨x,t,hx,ht,run⟩ := (image a z).mp actual
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic run old; exact ⟨hx,ht⟩
  · rintro ⟨rfl,rfl⟩; exact (image _ _).mpr ⟨v,s,rfl,rfl,old⟩

theorem body_original_and_all_actual_images
    (spans : Nat → Syntax.SourceSpan) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (environment : Resolved.Environment) (store : Core.Store) (isOr left right : Bool) (word : Core.Word)
    (aid bid : Resolved.LocalId) (aligned : environment.ids=inputs.context.ids)
    (an : LocalNameTable.Lookup inputs.names "a" aid) (bn : LocalNameTable.Lookup inputs.names "b" bid)
    (aTyped : Resolved.LocalScope.Lookup inputs.context aid .bool) (bTyped : Resolved.LocalScope.Lookup inputs.context bid .bool)
    (av : Resolved.LocalScope.Lookup environment aid (.bool left)) (bv : Resolved.LocalScope.Lookup environment bid (.bool right)) :
    ∃ ai bi, ClosedSourceDataBody (body spans isOr) ∧
      elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner inputs (source spans isOr)
        (.function .word .word) = some (.lambda .word .word (code isOr ai bi)) ∧
      ClosedSourceBodyEvaluates owner (entry owner inputs).names (up (env owner inputs environment word))
        (heap store) (body spans isOr) (RuntimeValue.ofCore (result isOr left right word)) (heap store) ∧
      ComputationReturnTreeEvaluates LocalExpressionEvaluates owner (entry owner inputs).names
        (env owner inputs environment word) store (body spans isOr) (result isOr left right word) store ∧
      Core.Evaluates (.word word :: environment.values) store (code isOr ai bi) (result isOr left right word) store ∧
      (∀ actual final, ClosedSourceBodyEvaluates owner (entry owner inputs).names (up (env owner inputs environment word))
        (heap store) (body spans isOr) actual final ↔ actual=RuntimeValue.ofCore (result isOr left right word) ∧ final=heap store) := by
  obtain ⟨ai,ax,_⟩ := aTyped.indexed; obtain ⟨bi,bx,_⟩ := bTyped.indexed
  let f : Frame := ⟨spans,owner,inputs,environment,isOr,left,right,aid,bid,ai,bi,aligned,an,bn,aTyped,bTyped,av,bv,ax,bx⟩
  have h := facts f store word
  have g : ClosedSourceDataBody (body spans isOr) := .expression (gate spans isOr)
  have same : (env owner inputs environment word).ids=(entry owner inputs).context.ids := by
    simpa only [env,entry,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) aligned
  have localBack := g.local_evaluates_iff.mpr ⟨_,store,rfl,rfl,h.2.2.2.1⟩
  have localBoth := g.local_evaluates_iff.mpr (g.local_evaluates_iff.mp localBack)
  refine ⟨ai,bi,g,h.2.1,localBoth,h.2.2.2.1,h.2.2.2.2,?_⟩
  exact exactImage (by simpa only [env,Resolved.LocalScope.values,List.map_cons] using h.2.2.2.2)
    (fun _ _ => g.core_evaluates_iff h.1 same)

theorem calls_original_and_all_actual_images
    (spans : Nat → Syntax.SourceSpan) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (environment : Resolved.Environment) (store : Core.Store) (isOr left right : Bool) (word : Core.Word)
    (aid bid wid : Resolved.LocalId) (aligned : environment.ids=inputs.context.ids)
    (an : LocalNameTable.Lookup inputs.names "a" aid) (bn : LocalNameTable.Lookup inputs.names "b" bid)
    (aTyped : Resolved.LocalScope.Lookup inputs.context aid .bool) (bTyped : Resolved.LocalScope.Lookup inputs.context bid .bool)
    (av : Resolved.LocalScope.Lookup environment aid (.bool left)) (bv : Resolved.LocalScope.Lookup environment bid (.bool right))
    (wn : LocalNameTable.Lookup inputs.names "w" wid) (wv : Resolved.LocalScope.Lookup environment wid (.word word))
    (caller : Resolved.DeclarationId) (callerNames : LocalNameTable) (callerRows : Resolved.LocalScope RuntimeValue)
    (callee : Syntax.Expr) (actualClosure : RuntimeValue) (creationStore : List RuntimeValue)
    (created : ClosedSourceExpressionEvaluates owner inputs.names (up environment) (heap store)
      (source spans isOr) actualClosure creationStore)
    (fetched : ClosedSourceExpressionEvaluates caller callerNames callerRows creationStore callee actualClosure creationStore)
    (argument : Syntax.Expr) (argumentOld : ClosedSourceExpressionEvaluates caller callerNames callerRows creationStore
      argument (.word word) (heap store)) :
    actualClosure = .sourceClosure (source spans isOr) owner inputs.names (up environment) ∧ creationStore=heap store ∧
    ∃ ai bi wi, Core.Evaluates environment.values store
      (.apply (.lambda .word .word (code isOr ai bi)) (.var wi)) (result isOr left right word) store ∧
      ClosedSourceExpressionEvaluates owner inputs.names (up environment) (heap store)
        (call spans (source spans isOr) (ref (spans 21) "w")) (RuntimeValue.ofCore (result isOr left right word)) (heap store) ∧
      ClosedSourceExpressionEvaluates caller callerNames callerRows creationStore (call spans callee argument)
        (RuntimeValue.ofCore (result isOr left right word)) (heap store) ∧
      (∀ a z, ClosedSourceExpressionEvaluates owner inputs.names (up environment) (heap store)
        (call spans (source spans isOr) (ref (spans 21) "w")) a z ↔ a=RuntimeValue.ofCore (result isOr left right word) ∧ z=heap store) ∧
      (∀ a z, ClosedSourceExpressionEvaluates caller callerNames callerRows creationStore (call spans callee argument) a z ↔
        a=RuntimeValue.ofCore (result isOr left right word) ∧ z=heap store) := by
  obtain ⟨ai,ax,_⟩ := aTyped.indexed; obtain ⟨bi,bx,_⟩ := bTyped.indexed; obtain ⟨wi,wx,wget⟩ := wv.indexed
  let f : Frame := ⟨spans,owner,inputs,environment,isOr,left,right,aid,bid,ai,bi,aligned,an,bn,aTyped,bTyped,av,bv,ax,bx⟩
  have h := facts f store word
  have made : ClosedSourceExpressionEvaluates owner inputs.names (up environment) (heap store)
      (source spans isOr) (.sourceClosure (source spans isOr) owner inputs.names (up environment)) (heap store) := .creation .inferred
  have equal := created.deterministic made
  have originalArg : ClosedSourceExpressionEvaluates owner inputs.names (up environment) (heap store)
      (ref (spans 21) "w") (.word word) (heap store) := .reference wn (by simpa only [RuntimeValue.ofCore] using mapped wv)
  have beta : ClosedSourceBodyEvaluates owner (("p",Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
      ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),.word word)::up environment)
      (heap store) (body spans isOr) (RuntimeValue.ofCore (result isOr left right word)) (heap store) := by
    simpa only [f,entry,env,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using h.2.2.1
  have savedCallee : ClosedSourceExpressionEvaluates caller callerNames callerRows creationStore callee
      (.sourceClosure (source spans isOr) owner inputs.names (up environment)) creationStore := equal.1 ▸ fetched
  have directOld := ClosedSourceExpressionEvaluates.call (span:=spans 19) (argumentsSpan:=spans 20) .inferred made originalArg beta
  have savedOld := ClosedSourceExpressionEvaluates.call (span:=spans 19) (argumentsSpan:=spans 20) .inferred savedCallee argumentOld beta
  have core : Core.Evaluates environment.values store (.apply (.lambda .word .word (code isOr ai bi)) (.var wi))
      (result isOr left right word) store := .apply .lambda (.var wget) h.2.2.2.2
  refine ⟨equal.1,equal.2,ai,bi,wi,core,directOld,savedOld,?_,?_⟩
  · exact exactImage core (fun _ _ => closedSourceExpectedDataLambda_application_core_iff .inferred
      (.expression (gate spans isOr)) h.2.1 aligned .reference (.identifier wn) (.var wx))
  · exact exactImage h.2.2.2.2 (fun _ _ => closedSourceExpectedDataLambda_invocation_core_iff .inferred
      (.expression (gate spans isOr)) h.2.1 aligned savedCallee (by simpa only [RuntimeValue.ofCore,heap] using argumentOld))
end Tests.ExpectedWordShortCircuitDataImages
