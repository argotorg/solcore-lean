import Solcore.Frontend.ExpectedDataLambdaApplicationProperties
import Solcore.Frontend.LocalExpressionCostCorrespondence
import Solcore.Frontend.LocalExpressionCostErasureProperties
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.WordLessCostStepComposition
import Solcore.Frontend.LocalFunctionApplicationStepComposition

set_option autoImplicit false
namespace Tests.ExpectedBoolStrictDataImages
open Solcore Solcore.Frontend
def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
def heap (s : Core.Store) := s.map RuntimeValue.ofCore
def one := Core.Word.ofNatModulo 1
def two := Core.Word.ofNatModulo 2
def ref (s : Syntax.SourceSpan) (n : String) : Syntax.Expr := ⟨s,.identifier ⟨s,n⟩⟩
def lit (s : Syntax.SourceSpan) (n : String) : Syntax.Expr := ⟨s,.literal ⟨s,.decimal n⟩⟩
def initializer (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 9,.binary (ref (s 10) "p") ⟨s 11,.add⟩ (lit (s 12) "1")⟩
def lessSource (s : Nat → Syntax.SourceSpan) : Syntax.Expr := ⟨s 18,.binary (ref (s 19) "p") ⟨s 20,.less⟩ (lit (s 21) "2")⟩
def leftSource (s : Nat → Syntax.SourceSpan) : Syntax.Expr := ⟨s 15,.unary ⟨s 16,.logicalNot⟩ ⟨s 17,.group (lessSource s)⟩⟩
def rightSource (s : Nat → Syntax.SourceSpan) : Syntax.Expr := ⟨s 23,.group ⟨s 24,.binary (ref (s 25) "p") ⟨s 26,.greaterEqual⟩ (lit (s 27) "2")⟩⟩
def returned (s : Nat → Syntax.SourceSpan) : Syntax.Expr := ⟨s 14,.binary (leftSource s) ⟨s 22,.logicalAnd⟩ (rightSource s)⟩
def annotation (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s,.named ⟨s,⟨⟨⟨s,"Word"⟩,[]⟩⟩⟩ none⟩
def body (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 5,[⟨s 6,.letDecl ⟨s 7,"p"⟩ (some (annotation (s 8))) (some (initializer s))⟩,
    ⟨s 13,.returnStmt (some (returned s))⟩]⟩
def source (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 0,.lambda (s 1) ⟨s 2,[⟨s 3,.inferred ⟨s 4,"p"⟩⟩]⟩ none (body s)⟩
def argument (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 28,.binary (ref (s 29) "c") ⟨s 30,.add⟩ (lit (s 31) "1")⟩
def call (s : Nat → Syntax.SourceSpan) (fn a : Syntax.Expr) : Syntax.Expr := ⟨s 32,.call fn ⟨s 33,[a]⟩⟩
def types : TypeNameTable := [(["Word"],.word)]
def predicate (w : Core.Word) := !(decide (w < two))
def result (w : Core.Word) : Core.Value := .bool (predicate (w.add one))
def tailCode : Core.Expr :=
  .ifE (.unary .boolNot ((Core.Expr.var 0).wordLt (.word two)))
    (.unary .boolNot ((Core.Expr.var 0).wordLt (.word two))) (.bool false)
def code : Core.Expr := .letE (.binary .wordAdd (.var 0) (.word one)) tailCode
def bodyCost (w : Core.Word) := 5 + (if predicate (w.add one) then 28 else 16) + 2
def entered (o : Resolved.DeclarationId) (t : LocalTypeInputs) := t.bindFresh o "p" .word
def entry (o : Resolved.DeclarationId) (t : LocalTypeInputs) (e : Resolved.Environment) (w : Core.Word) : Resolved.Environment :=
  (Resolved.freshLocalId o t.ids,.word w)::e
private theorem literalOne (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "1"⟩ one :=
  .decimal (by decide) (.cons (.decimal (digit:=1) (by decide) rfl) .nil)
private theorem literalTwo (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "2"⟩ two :=
  .decimal (by decide) (.cons (.decimal (digit:=2) (by decide) rfl) .nil)
theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail ne _ ih => exact .tail ne ih
private theorem tail_paths (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId)
    (n : LocalNameTable) (e : Resolved.Environment) (st : Core.Store) (i : Resolved.LocalId) (w : Core.Word) :
    ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st)
      (returned s) (RuntimeValue.ofCore (.bool (predicate w))) (heap st) ∧
    LocalExpressionEvaluatesWithCost (("p",i)::n) ((i,.word w)::e) st
      (returned s) (.bool (predicate w)) st (if predicate w then 28 else 16) := by
  have cl : ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st)
      (ref (s 19) "p") (.word w) (heap st) := by simp only [up,List.map_cons,RuntimeValue.ofCore]; exact .reference .head .head
  have cr : ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st)
      (ref (s 25) "p") (.word w) (heap st) := by simp only [up,List.map_cons,RuntimeValue.ofCore]; exact .reference .head .head
  have ll : LocalExpressionEvaluatesWithCost (("p",i)::n) ((i,.word w)::e) st (ref (s 19) "p") (.word w) st 1 := .identifier .head .head
  have lr : LocalExpressionEvaluatesWithCost (("p",i)::n) ((i,.word w)::e) st (ref (s 25) "p") (.word w) st 1 := .identifier .head .head
  have cmp : ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st) (lessSource s) (RuntimeValue.ofCore (.bool (decide (w<two)))) (heap st) := .strictWordBinary cl (.wordLiteral (literalTwo _)) .less
  have left : ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st) (leftSource s) (.bool (predicate w)) (heap st) :=
    .logicalNot (.group (by simpa only [RuntimeValue.ofCore] using cmp))
  have right : ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st) (rightSource s) (.bool (predicate w)) (heap st) := by
    apply ClosedSourceExpressionEvaluates.group
    rw [← RuntimeValue.ofCore.eq_2 (predicate w)]
    exact .strictWordBinary cr (.wordLiteral (literalTwo _)) .greaterEqual
  have oldLeft : LocalExpressionEvaluatesWithCost (("p",i)::n) ((i,.word w)::e) st (leftSource s) (.bool (predicate w)) st 13 := .logicalNot (.group (.less ll (.wordLiteral (literalTwo _))))
  have oldRight : LocalExpressionEvaluatesWithCost (("p",i)::n) ((i,.word w)::e) st (rightSource s) (.bool (predicate w)) st 13 := .group (.greaterEqual lr (.wordLiteral (literalTwo _)))
  cases h : predicate w <;> simp only [Bool.false_eq_true,↓reduceIte,RuntimeValue.ofCore]
  · exact ⟨.andFalse (by simpa only [predicate,RuntimeValue.ofCore] using h ▸ left),.andFalse (h ▸ oldLeft)⟩
  · exact ⟨.andTrue (by simpa only [predicate,RuntimeValue.ofCore] using h ▸ left) (by simpa only [predicate,RuntimeValue.ofCore] using h ▸ right),.andTrue (h ▸ oldLeft) (h ▸ oldRight)⟩
private theorem return_checked (s : Nat → Syntax.SourceSpan) (t : LocalTypeInputs)
    (o : Resolved.DeclarationId) :
    elaborateLocalExpression? (entered o t).names (entered o t).context (returned s) = some (tailCode,.bool) := by
  exact elaborateLocalExpression?_complete
    (.logicalAnd (.logicalNot (.group (.less (.identifier .head) (.wordLiteral (literalTwo _)))))
      (.group (.greaterEqual (.identifier .head) (.wordLiteral (literalTwo _)))))
    (.ifE (.unary (.wordLt (.var .head) .word)) (.unary (.wordLt (.var .head) .word)) .bool)
    (.ifE (.unary (.wordLt (.var .head) .word)) (.unary (.wordLt (.var .head) .word)) .bool)
theorem core_exact {P : RuntimeValue → List RuntimeValue → Prop} {e s c v}
    (original : Core.Evaluates e s c v s)
    (image : ∀ a z, P a z ↔ ∃ x t, a=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e s c x t) :
    ∀ a z, P a z ↔ a=RuntimeValue.ofCore v ∧ z=heap s := by
  intro a z; constructor
  · intro h; obtain ⟨x,t,hx,ht,old⟩ := (image a z).mp h
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic old original; exact ⟨hx,ht⟩
  · rintro ⟨rfl,rfl⟩; exact (image _ _).mpr ⟨v,s,rfl,rfl,original⟩
structure BodyEvidence (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId) (t : LocalTypeInputs)
    (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) : Prop where
  admitted : ClosedSourceDataBody (body s)
  checked : elaborateComputationReturnTree? elaborateLocalExpression? types o (entered o t) (body s) = some (code,.bool)
  expected : elaborateExpectedComputationLambda? elaborateLocalExpression? types o t (source s) (.function .word .bool) = some (.lambda .word .bool code)
  original : ClosedSourceBodyEvaluates o (entered o t).names (up (entry o t e w)) (heap st) (body s) (RuntimeValue.ofCore (result w)) (heap st)
  old : ComputationReturnTreeEvaluates LocalExpressionEvaluates o (entered o t).names (entry o t e w) st (body s) (result w) st
  steps : ∀ k, Core.Steps (bodyCost w) ⟨.eval code (.word w::e.values),k,st⟩ ⟨.ret (result w),k,st⟩
  localImage : ∀ a z, ClosedSourceBodyEvaluates o (entered o t).names (up (entry o t e w)) (heap st) (body s) a z ↔ a=RuntimeValue.ofCore (result w) ∧ z=heap st
  coreImage : ∀ a z, ClosedSourceBodyEvaluates o (entered o t).names (up (entry o t e w)) (heap st) (body s) a z ↔ a=RuntimeValue.ofCore (result w) ∧ z=heap st
theorem body_evidence (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId) (t : LocalTypeInputs)
    (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) (aligned : e.ids=t.context.ids) : BodyEvidence s o t e st w := by
  let t1 := entered o t
  let e1 := entry o t e w
  let t2 := entered o t1
  let e2 := entry o t1 e1 (w.add one)
  have a1 : e1.ids=t1.context.ids := by simpa only [e1,t1,entry,entered,Resolved.LocalScope.ids,LocalTypeInputs.bindFresh_context,List.map_cons] using congrArg (List.cons _) aligned
  have a2 : e2.ids=t2.context.ids := by simpa only [e2,t2,entry,entered,Resolved.LocalScope.ids,LocalTypeInputs.bindFresh_context,List.map_cons] using congrArg (List.cons _) a1
  have initOld : LocalExpressionEvaluatesWithCost t1.names e1 st (initializer s) (.word (w.add one)) st 5 := by
    simp only [t1,e1,entered,entry,LocalTypeInputs.bindFresh_names,initializer,ref,lit]
    refine .add (middleStore:=st) (leftValue:=w) (rightValue:=one) (leftCost:=1) (rightCost:=1) ?_ ?_
    · exact .identifier .head .head
    · exact .wordLiteral (literalOne _)
  have initRaw : ClosedSourceExpressionEvaluates o t1.names (up e1) (heap st) (initializer s) (.word (w.add one)) (heap st) := by
    rw [← RuntimeValue.ofCore.eq_3 (w.add one)]
    apply ClosedSourceExpressionEvaluates.strictWordBinary (leftWord:=w) (rightWord:=one) (meaning:=StrictWordBinaryDenotes.add)
    · simp only [t1,e1,entered,entry,LocalTypeInputs.bindFresh_names,up,List.map_cons,RuntimeValue.ofCore]; exact .reference .head .head
    · exact .wordLiteral (literalOne _)
  have tail := tail_paths s o t1.names e1 st (Resolved.freshLocalId o t1.ids) (w.add one)
  have initCheck : elaborateLocalExpression? t1.names t1.context (initializer s) = some (.binary .wordAdd (.var 0) (.word one),.word) :=
    elaborateLocalExpression?_complete (.add (.identifier .head) (.wordLiteral (literalOne _))) (.binary (.var .head) .word) (.binary (.var .head) .word)
  have tailCheck := return_checked s t1 o
  have tc : LocalExpressionEvaluatesWithCost t2.names e2 st (returned s) (result w) st (if predicate (w.add one) then 28 else 16) := by
    simpa only [t2,e2,entry,entered,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,result] using tail.2
  have tr : ClosedSourceExpressionEvaluates o t2.names (up e2) (heap st) (returned s) (RuntimeValue.ofCore (result w)) (heap st) := by
    simpa only [t2,e2,entry,entered,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,result] using tail.1
  have raw : ClosedSourceBodyEvaluates o t1.names (up e1) (heap st) (body s) (RuntimeValue.ofCore (result w)) (heap st) := by
    apply ClosedSourceBodyEvaluates.binding initRaw
    simpa only [t2,e2,entry,entered,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using ClosedSourceBodyEvaluates.expression (blockSpan:=s 5) (returnSpan:=s 13) tr
  have old : ComputationReturnTreeEvaluates LocalExpressionEvaluates o t1.names e1 st (body s) (result w) st := by
    apply ComputationReturnTreeEvaluates.binding initOld.erase
    simpa only [t2,e2,entry,entered,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluates.expression (owner:=o) (blockSpan:=s 5) (returnSpan:=s 13) tc.erase
  have paths : ∀ k, Core.Steps (bodyCost w) ⟨.eval code (.word w::e.values),k,st⟩ ⟨.ret (result w),k,st⟩ := by
    obtain ⟨ir,irs,il,_⟩ := elaborateLocalExpression?_sound initCheck
    obtain ⟨rr,rrs,rl,_⟩ := elaborateLocalExpression?_sound tailCheck
    intro k
    exact CostStepComposition.letE (initOld.toStepsWithContinuation irs (a1 ▸ il) _)
      (by simpa only [e1,e2,entry,Resolved.LocalScope.values,List.map_cons] using tc.toStepsWithContinuation rrs (a2 ▸ rl) k)
  have gate : ClosedSourceDataBody (body s) := .binding (.strictWordBinary .reference .literal (by decide) (by decide))
    (.expression (.logicalAnd (.logicalNot (.group (.strictWordBinary .reference .literal (by decide) (by decide)))) (.group (.strictWordBinary .reference .literal (by decide) (by decide)))))
  have compiled : ComputationReturnTreeElaborates (fun n c x k ty => elaborateLocalExpression? n c x = some (k,ty)) types o t1 (body s) code .bool :=
    .binding (.named .head) initCheck (.expression tailCheck)
  have checked := (elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr compiled
  refine ⟨gate,checked,(elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr (.lambda (.lambda .inferred .omitted) .word .bool compiled),raw,old,paths,?_,?_⟩
  · intro a z; constructor
    · intro h; obtain ⟨v,fs,hv,hs,localRun⟩ := gate.local_evaluates_iff.mp h
      exact (gate.local_evaluates_iff.mpr ⟨v,fs,hv,hs,localRun⟩).deterministic raw
    · rintro ⟨rfl,rfl⟩; exact gate.local_evaluates_iff.mpr ⟨result w,st,rfl,rfl,old⟩
  · exact core_exact (Core.steps_from_initial_sound (paths [])) (fun _ _ => by simpa only [t1,e1,entry,up,heap,Resolved.LocalScope.values,List.map_cons] using gate.core_evaluates_iff checked a1)
theorem argument_paths (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) (i : Resolved.LocalId) (index : Nat)
    (named : LocalNameTable.Lookup n "c" i) (found : Resolved.LocalScope.Lookup e i (.word w))
    (indexed : Resolved.LocalScope.IndexOf e.ids i index) :
    ClosedSourceDataExpression (argument s) ∧
    ResolvesLocalExpression n (argument s) (.binary .wordAdd (.var i) (.word one)) ∧
    Resolved.Lowers e.ids (.binary .wordAdd (.var i) (.word one)) (.binary .wordAdd (.var index) (.word one)) ∧
    LocalExpressionEvaluatesWithCost n e st (argument s) (.word (w.add one)) st 5 ∧
    ClosedSourceExpressionEvaluates o n (up e) (heap st) (argument s) (.word (w.add one)) (heap st) :=
  ⟨.strictWordBinary .reference .literal (by decide) (by decide),.add (.identifier named) (.wordLiteral (literalOne _)),
    .binary (.var indexed) .word,.add (.identifier named found) (.wordLiteral (literalOne _)),
    by rw [← RuntimeValue.ofCore.eq_3 (w.add one)]
       exact .strictWordBinary (.reference named (by simpa only [RuntimeValue.ofCore] using mapped found)) (.wordLiteral (literalOne _)) .add⟩
theorem calls_original_and_images (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId) (t : LocalTypeInputs)
    (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) (aligned : e.ids=t.context.ids)
    (i : Resolved.LocalId) (index : Nat) (named : LocalNameTable.Lookup t.names "c" i)
    (found : Resolved.LocalScope.Lookup e i (.word w)) (indexed : Resolved.LocalScope.IndexOf e.ids i index)
    (caller : Resolved.DeclarationId) (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue)
    (callee arg : Syntax.Expr) (actualClosure : RuntimeValue) (creationStore : List RuntimeValue)
    (created : ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (source s) actualClosure creationStore)
    (fetched : ClosedSourceExpressionEvaluates caller names rows creationStore callee actualClosure creationStore)
    (passed : ClosedSourceExpressionEvaluates caller names rows creationStore arg (.word (w.add one)) (heap st)) :
    actualClosure = .sourceClosure (source s) o t.names (up e) ∧ creationStore=heap st ∧
    ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (call s (source s) (argument s)) (RuntimeValue.ofCore (result (w.add one))) (heap st) ∧
    ClosedSourceExpressionEvaluates caller names rows creationStore (call s callee arg) (RuntimeValue.ofCore (result (w.add one))) (heap st) ∧
    (∀ a z, ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (call s (source s) (argument s)) a z ↔ a=RuntimeValue.ofCore (result (w.add one)) ∧ z=heap st) ∧
    (∀ a z, ClosedSourceExpressionEvaluates caller names rows creationStore (call s callee arg) a z ↔ a=RuntimeValue.ofCore (result (w.add one)) ∧ z=heap st) := by
  have b := body_evidence s o t e st (w.add one) aligned
  have a := argument_paths s o t.names e st w i index named found indexed
  have made : ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (source s) (.sourceClosure (source s) o t.names (up e)) (heap st) := .creation .inferred
  have same := created.deterministic made
  have calleeOriginal := same.1 ▸ fetched
  have beta : ClosedSourceBodyEvaluates o (("p",Resolved.freshLocalId o (t.names.map Prod.snd))::t.names)
      ((Resolved.freshLocalId o (t.names.map Prod.snd),.word (w.add one))::up e) (heap st) (body s) (RuntimeValue.ofCore (result (w.add one))) (heap st) := by
    simpa only [entered,entry,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using b.original
  have direct := ClosedSourceExpressionEvaluates.call (span:=s 32) (argumentsSpan:=s 33) .inferred made a.2.2.2.2 beta
  have saved := ClosedSourceExpressionEvaluates.call (span:=s 32) (argumentsSpan:=s 33) .inferred calleeOriginal passed beta
  have coreArg := a.2.2.2.1.toStepsWithContinuation a.2.1 a.2.2.1 []
  have coreBody := Core.steps_from_initial_sound (b.steps [])
  have coreCall := Core.Evaluates.apply (Core.Evaluates.lambda (parameterType:=.word) (resultType:=.bool)) (Core.steps_from_initial_sound coreArg) coreBody
  exact ⟨same.1,same.2,direct,saved,
    core_exact coreCall (fun _ _ => closedSourceExpectedDataLambda_application_core_iff .inferred b.admitted b.expected aligned a.1 a.2.1 a.2.2.1),
    core_exact coreBody (fun _ _ => closedSourceExpectedDataLambda_invocation_core_iff .inferred b.admitted b.expected aligned calleeOriginal (by simpa only [RuntimeValue.ofCore,heap] using passed))⟩
end Tests.ExpectedBoolStrictDataImages
