import Solcore.Frontend.ExpectedDataLambdaApplicationProperties
import Solcore.Frontend.LocalExpressionCostCorrespondence
import Solcore.Frontend.LocalExpressionCostErasureProperties
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.LocalFunctionApplicationStepComposition
set_option autoImplicit false
namespace Tests.ExpectedWordStrictDataImages
open Solcore Solcore.Frontend
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def heap (s : Core.Store) := s.map RuntimeValue.ofCore
private def one : Core.Word := Core.Word.ofNatModulo 1
private def two : Core.Word := Core.Word.ofNatModulo 2
private def ref (s : Nat → Syntax.SourceSpan) (i : Nat) (n : String) : Syntax.Expr :=
  ⟨s i,.identifier ⟨s (i+1),n⟩⟩
private def lit (s : Nat → Syntax.SourceSpan) (i : Nat) (n : String) : Syntax.Expr :=
  ⟨s i,.literal ⟨s (i+1),.decimal n⟩⟩
private def init (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 4,.binary (ref s 0 "p") ⟨s 5,.add⟩ (lit s 2 "1")⟩
private def returned (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 23,.conditional ⟨s 12,.group ⟨s 10,.binary (ref s 6 "p") ⟨s 11,.less⟩ (lit s 8 "2")⟩⟩
    (s 24) ⟨s 17,.binary (ref s 13 "p") ⟨s 18,.multiply⟩ (lit s 15 "2")⟩
    (s 25) ⟨s 21,.unary ⟨s 22,.bitNot⟩ (ref s 19 "p")⟩⟩
private def annotation (s : Nat → Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s 26,.named ⟨s 27,⟨⟨⟨s 28,"Word"⟩,[]⟩⟩⟩ none⟩
private def body (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 29,[⟨s 30,.letDecl ⟨s 31,"p"⟩ (some (annotation s)) (some (init s))⟩,
    ⟨s 32,.returnStmt (some (returned s))⟩]⟩
private def source (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 33,.lambda (s 34) ⟨s 35,[⟨s 36,.inferred ⟨s 37,"p"⟩⟩]⟩ none (body s)⟩
private def call (s : Nat → Syntax.SourceSpan) (fn arg : Syntax.Expr) : Syntax.Expr := ⟨s 38,.call fn ⟨s 39,[arg]⟩⟩
private def argument (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 44,.binary (ref s 40 "c") ⟨s 45,.add⟩ (lit s 42 "1")⟩
private def decision (w : Core.Word) := decide (w.add one < two)
private def value (w : Core.Word) : Core.Value := .word (if decision w then (w.add one).mul two else (w.add one).bitNot)
private def retCore : Core.Expr := .ifE ((Core.Expr.var 0).wordLt (.word two))
  (.binary .wordMul (.var 0) (.word two)) (.unary .wordNot (.var 0))
private def core : Core.Expr := .letE (.binary .wordAdd (.var 0) (.word one)) retCore
private def cost (w : Core.Word) : Nat := 5 + (11 + (if decision w then 5 else 3) + 2) + 2
private def entry (o : Resolved.DeclarationId) (t : LocalTypeInputs) := t.bindFresh o "p" .word
private def env (o : Resolved.DeclarationId) (t : LocalTypeInputs) (e : Resolved.Environment) (w : Core.Word) : Resolved.Environment :=
  (Resolved.freshLocalId o t.ids,.word w)::e
private theorem literalOne (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "1"⟩ one := interpretWordLiteral?_iff.mp (by rfl)
private theorem literalTwo (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "2"⟩ two := interpretWordLiteral?_iff.mp (by rfl)
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail ne _ ih => exact .tail ne ih
private theorem gate (s : Nat → Syntax.SourceSpan) : ClosedSourceDataBody (body s) := by
  refine .binding (.strictWordBinary .reference .literal (by decide) (by decide)) (.expression ?_)
  exact .conditional (.group (.strictWordBinary .reference .literal (by decide) (by decide)))
    (.strictWordBinary .reference .literal (by decide) (by decide)) (.bitNot .reference)
private theorem facts (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId) (t : LocalTypeInputs)
    (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) (same : e.ids=t.context.ids) :
    elaborateComputationReturnTree? elaborateLocalExpression? [(["Word"],.word)] o (entry o t) (body s) = some (core,.word) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [(["Word"],.word)] o t (source s)
      (.function .word .word) = some (.lambda .word .word core) ∧
    ClosedSourceBodyEvaluates o (entry o t).names (up (env o t e w)) (heap st) (body s) (RuntimeValue.ofCore (value w)) (heap st) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates o (entry o t).names (env o t e w) st (body s) (value w) st ∧
    (∀ k, Core.Steps (cost w) ⟨.eval core (.word w::e.values),k,st⟩ ⟨.ret (value w),k,st⟩) := by
  let ti := entry o t
  let ei := env o t e w
  let tr := entry o ti
  let er := env o ti ei (w.add one)
  have si : ei.ids=ti.context.ids := by
    simpa only [ei,ti,env,entry,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
  have sr : er.ids=tr.context.ids := by
    simpa only [er,tr,env,entry,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) si
  have ic : elaborateLocalExpression? ti.names ti.context (init s) = some (.binary .wordAdd (.var 0) (.word one),.word) :=
    elaborateLocalExpression?_complete (.add (.identifier .head) (.wordLiteral (literalOne _))) (.binary (.var .head) .word) (.binary (.var .head) .word)
  have rc : elaborateLocalExpression? tr.names tr.context (returned s) = some (retCore,.word) :=
    elaborateLocalExpression?_complete
      (.conditional (.group (.less (.identifier .head) (.wordLiteral (literalTwo _))))
        (.multiply (.identifier .head) (.wordLiteral (literalTwo _))) (.bitNot (.identifier .head)))
      (.ifE (.wordLt (.var .head) .word) (.binary (.var .head) .word) (.unary (.var .head)))
      (.ifE (.wordLt (.var .head) .word) (.binary (.var .head) .word) (.unary (.var .head)))
  have il : LocalExpressionEvaluatesWithCost ti.names ei st (init s) (.word (w.add one)) st 5 := by
    simp only [ti,ei,entry,env,LocalTypeInputs.bindFresh_names,init,ref,lit]
    apply LocalExpressionEvaluatesWithCost.add (leftValue:=w) (rightValue:=one) (leftCost:=1) (rightCost:=1)
    · exact .identifier .head .head
    · exact .wordLiteral (literalOne _)
  have ig : ClosedSourceExpressionEvaluates o ti.names (up ei) (heap st) (init s) (.word (w.add one)) (heap st) := by
    simp only [ti,ei,entry,env,LocalTypeInputs.bindFresh_names,up,List.map_cons,RuntimeValue.ofCore,init,ref,lit]
    simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.strictWordBinary
      (leftWord:=w) (rightWord:=one) (span:=s 4) (operatorSpan:=s 5)
      (.reference (span:=s 0) (name:=⟨s 1,"p"⟩) .head .head)
      (.wordLiteral (span:=s 2) (literalOne (s 3))) StrictWordBinaryDenotes.add
  have rl : LocalExpressionEvaluatesWithCost tr.names er st (returned s) (value w) st
      (11+(if decision w then 5 else 3)+2) := by
    have cmp : LocalExpressionEvaluatesWithCost tr.names er st
        ⟨s 12,.group ⟨s 10,.binary (ref s 6 "p") ⟨s 11,.less⟩ (lit s 8 "2")⟩⟩ (.bool (decision w)) st 11 := by
      simp only [decision,tr,er,entry,env,LocalTypeInputs.bindFresh_names,ref,lit]
      apply LocalExpressionEvaluatesWithCost.group
      apply LocalExpressionEvaluatesWithCost.less (leftValue:=w.add one) (rightValue:=two) (leftCost:=1) (rightCost:=1)
      · exact .identifier .head .head
      · exact .wordLiteral (literalTwo _)
    cases h : decision w <;> simp only [value,h,Bool.false_eq_true,↓reduceIte]
    · exact .ifFalse (h ▸ cmp) (.bitNot (.identifier .head .head))
    · apply LocalExpressionEvaluatesWithCost.ifTrue (h ▸ cmp)
      simp only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,ref,lit]
      apply LocalExpressionEvaluatesWithCost.multiply (leftValue:=w.add one) (rightValue:=two) (leftCost:=1) (rightCost:=1)
      · exact .identifier .head .head
      · exact .wordLiteral (literalTwo _)
  have rg : ClosedSourceExpressionEvaluates o tr.names (up er) (heap st) (returned s)
      (RuntimeValue.ofCore (value w)) (heap st) := by
    have cmp : ClosedSourceExpressionEvaluates o tr.names (up er) (heap st)
        ⟨s 12,.group ⟨s 10,.binary (ref s 6 "p") ⟨s 11,.less⟩ (lit s 8 "2")⟩⟩ (.bool (decision w)) (heap st) :=
      by
        simp only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,up,List.map_cons,RuntimeValue.ofCore,ref,lit,decision]
        apply ClosedSourceExpressionEvaluates.group
        simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.strictWordBinary
          (leftWord:=w.add one) (rightWord:=two) (span:=s 10) (operatorSpan:=s 11)
          (.reference (span:=s 6) (name:=⟨s 7,"p"⟩) .head .head)
          (.wordLiteral (span:=s 8) (literalTwo (s 9))) StrictWordBinaryDenotes.less
    cases h : decision w <;> simp only [value,h,Bool.false_eq_true,↓reduceIte,RuntimeValue.ofCore]
    · apply ClosedSourceExpressionEvaluates.conditionalFalse (h ▸ cmp)
      simp only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,up,List.map_cons,RuntimeValue.ofCore]
      exact .bitNot (.reference .head .head)
    · apply ClosedSourceExpressionEvaluates.conditionalTrue (h ▸ cmp)
      simp only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,up,List.map_cons,RuntimeValue.ofCore,ref,lit]
      simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.strictWordBinary
        (leftWord:=w.add one) (rightWord:=two) (span:=s 17) (operatorSpan:=s 18)
        (.reference (span:=s 13) (name:=⟨s 14,"p"⟩) .head .head)
        (.wordLiteral (span:=s 15) (literalTwo (s 16))) StrictWordBinaryDenotes.multiply
  have cb : ClosedSourceBodyEvaluates o ti.names (up ei) (heap st) (body s) (RuntimeValue.ofCore (value w)) (heap st) := by
    apply ClosedSourceBodyEvaluates.binding ig
    simpa only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using ClosedSourceBodyEvaluates.expression rg
  have lb : ComputationReturnTreeEvaluates LocalExpressionEvaluates o ti.names ei st (body s) (value w) st := by
    apply ComputationReturnTreeEvaluates.binding il.erase
    simpa only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluates.expression rl.erase
  have bc : ComputationReturnTreeElaborates (fun n t s c ty => elaborateLocalExpression? n t s=some (c,ty)) [(["Word"],.word)] o ti (body s) core .word :=
    .binding (.named .head) ic (.expression rc)
  obtain ⟨ri,resi,lowi,_⟩ := elaborateLocalExpression?_iff.mp ic
  obtain ⟨rr,resr,lowr,_⟩ := elaborateLocalExpression?_iff.mp rc
  have kp (k) := CostStepComposition.letE (il.toStepsWithContinuation resi (si ▸ lowi) _)
    (rl.toStepsWithContinuation resr (sr ▸ lowr) k)
  exact ⟨(elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr bc,
    (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
      (.lambda (.lambda .inferred .omitted) .word .word bc),cb,lb,
    fun k => by simpa only [ei,er,env,Resolved.LocalScope.values,List.map_cons,cost,core] using kp k⟩
private theorem exactImage {P : RuntimeValue → List RuntimeValue → Prop} {e st c v}
    (old : Core.Evaluates e st c v st)
    (image : ∀ a z, P a z ↔ ∃ x t, a=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e st c x t) :
    ∀ a z, P a z ↔ a=RuntimeValue.ofCore v ∧ z=heap st := by
  intro a z; constructor
  · intro actual; obtain ⟨x,t,hx,ht,run⟩ := (image a z).mp actual
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic run old; exact ⟨hx,ht⟩
  · rintro ⟨rfl,rfl⟩; exact (image _ _).mpr ⟨v,st,rfl,rfl,old⟩

theorem body_original_and_all_actual_images (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId)
    (t : LocalTypeInputs) (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) (same : e.ids=t.context.ids) :
    ClosedSourceDataBody (body s) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [(["Word"],.word)] o t (source s)
      (.function .word .word) = some (.lambda .word .word core) ∧
    ClosedSourceBodyEvaluates o (entry o t).names (up (env o t e w)) (heap st) (body s) (RuntimeValue.ofCore (value w)) (heap st) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates o (entry o t).names (env o t e w) st (body s) (value w) st ∧
    (∀ k, Core.Steps (cost w) ⟨.eval core (.word w::e.values),k,st⟩ ⟨.ret (value w),k,st⟩) ∧
    (∀ a z, ClosedSourceBodyEvaluates o (entry o t).names (up (env o t e w)) (heap st) (body s) a z ↔
      a=RuntimeValue.ofCore (value w) ∧ z=heap st) := by
  have h := facts s o t e st w same
  have si : (env o t e w).ids=(entry o t).context.ids := by
    simpa only [env,entry,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
  have original := h.2.2.1
  have localForward := (gate s).local_evaluates_iff.mp original
  have localReverse : ClosedSourceBodyEvaluates o (entry o t).names (up (env o t e w)) (heap st) (body s) (RuntimeValue.ofCore (value w)) (heap st) :=
    (gate s).local_evaluates_iff.mpr ⟨_,st,rfl,rfl,h.2.2.2.1⟩
  refine ⟨gate s,h.2.1,localReverse,h.2.2.2.1,h.2.2.2.2,?_⟩
  have coreOld : Core.Evaluates (env o t e w).values st core (value w) st := by
    simpa only [env,Resolved.LocalScope.values,List.map_cons] using Core.steps_from_initial_sound (h.2.2.2.2 [])
  intro a z
  have exactCore := exactImage coreOld (fun _ _ => (gate s).core_evaluates_iff h.1 si) a z
  constructor
  · intro actual
    have both := (gate s).local_evaluates_iff.mpr ((gate s).local_evaluates_iff.mp actual)
    exact exactCore.mp both
  · intro endpoint
    have actual := exactCore.mpr endpoint
    exact (gate s).local_evaluates_iff.mpr ((gate s).local_evaluates_iff.mp actual)

theorem calls_original_and_all_actual_images (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId)
    (t : LocalTypeInputs) (e : Resolved.Environment) (st : Core.Store) (c : Core.Word) (same : e.ids=t.context.ids)
    (id : Resolved.LocalId) (named : LocalNameTable.Lookup t.names "c" id)
    (found : Resolved.LocalScope.Lookup e id (.word c))
    (i : Nat) (ix : Resolved.LocalScope.IndexOf e.ids id i)
    (caller : Resolved.DeclarationId) (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue)
    (callee arg : Syntax.Expr) (actualClosure : RuntimeValue) (creationStore : List RuntimeValue)
    (created : ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (source s) actualClosure creationStore)
    (fetched : ClosedSourceExpressionEvaluates caller names rows creationStore callee actualClosure creationStore)
    (argumentOld : ClosedSourceExpressionEvaluates caller names rows creationStore arg (.word (c.add one)) (heap st)) :
    actualClosure=.sourceClosure (source s) o t.names (up e) ∧ creationStore=heap st ∧
    (∀ k, Core.Steps (1+5+cost (c.add one)+3)
      ⟨.eval (.apply (.lambda .word .word core) (.binary .wordAdd (.var i) (.word one))) e.values,k,st⟩
      ⟨.ret (value (c.add one)),k,st⟩) ∧
    ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (call s (source s) (argument s)) (RuntimeValue.ofCore (value (c.add one))) (heap st) ∧
    ClosedSourceExpressionEvaluates caller names rows creationStore (call s callee arg) (RuntimeValue.ofCore (value (c.add one))) (heap st) ∧
    (∀ a z, ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (call s (source s) (argument s)) a z ↔ a=RuntimeValue.ofCore (value (c.add one)) ∧ z=heap st) ∧
    (∀ a z, ClosedSourceExpressionEvaluates caller names rows creationStore (call s callee arg) a z ↔ a=RuntimeValue.ofCore (value (c.add one)) ∧ z=heap st) := by
  have h := facts s o t e st (c.add one) same
  have made : ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (source s) (.sourceClosure (source s) o t.names (up e)) (heap st) := .creation .inferred
  have ceq := created.deterministic made
  have mapped : Resolved.LocalScope.Lookup (up e) id (.word c) := by simpa only [RuntimeValue.ofCore] using mapped found
  have aold : ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (argument s) (.word (c.add one)) (heap st) := by
    simp only [argument,ref,lit]
    simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.strictWordBinary
      (leftWord:=c) (rightWord:=one) (span:=s 44) (operatorSpan:=s 45)
      (.reference (span:=s 40) (name:=⟨s 41,"c"⟩) named mapped)
      (.wordLiteral (span:=s 42) (literalOne (s 43))) StrictWordBinaryDenotes.add
  have al : LocalExpressionEvaluatesWithCost t.names e st (argument s) (.word (c.add one)) st 5 :=
    .add (.identifier named found) (.wordLiteral (literalOne _))
  have res : ResolvesLocalExpression t.names (argument s) (.binary .wordAdd (.var id) (.word one)) := .add (.identifier named) (.wordLiteral (literalOne _))
  have low : Resolved.Lowers e.ids (.binary .wordAdd (.var id) (.word one)) (.binary .wordAdd (.var i) (.word one)) := .binary (.var ix) .word
  have beta : ClosedSourceBodyEvaluates o (("p",Resolved.freshLocalId o (t.names.map Prod.snd))::t.names)
      ((Resolved.freshLocalId o (t.names.map Prod.snd),.word (c.add one))::up e) (heap st) (body s) (RuntimeValue.ofCore (value (c.add one))) (heap st) := by
    simpa only [entry,env,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using h.2.2.1
  have sf : ClosedSourceExpressionEvaluates caller names rows creationStore callee (.sourceClosure (source s) o t.names (up e)) creationStore := ceq.1 ▸ fetched
  have direct := ClosedSourceExpressionEvaluates.call (span:=s 38) (argumentsSpan:=s 39) .inferred made aold beta
  have saved := ClosedSourceExpressionEvaluates.call (span:=s 38) (argumentsSpan:=s 39) .inferred sf argumentOld beta
  have path (k) := CostStepComposition.apply (continuation:=k) (parameterType:=.word) (resultType:=.word)
    (.cons .lambda .refl) (al.toStepsWithContinuation res low _) (h.2.2.2.2 [])
  refine ⟨ceq.1,ceq.2,path,direct,saved,?_,?_⟩
  · exact exactImage (Core.steps_from_initial_sound (path [])) (fun _ _ => closedSourceExpectedDataLambda_application_core_iff .inferred
      (gate s) h.2.1 same (.strictWordBinary .reference .literal (by decide) (by decide)) res low)
  · exact exactImage (Core.steps_from_initial_sound (h.2.2.2.2 [])) (fun _ _ => closedSourceExpectedDataLambda_invocation_core_iff .inferred
      (gate s) h.2.1 same sf (by simpa only [RuntimeValue.ofCore,heap] using argumentOld))
end Tests.ExpectedWordStrictDataImages
