import Solcore.Frontend.BoundedInputsLambdaDepth

/- Both caller inputs succeed independently before a saved-body exclusion is
constructed. These laws do not classify unsuccessful callee or argument runs. -/
set_option autoImplicit false
namespace Tests.BoundedInputsDepthBoundaries
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (n : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier n⟩
private def call (s : Syntax.SourceSpan) (f x : Syntax.Expr) : Syntax.Expr := ⟨s,.call f ⟨s,[x]⟩⟩
private def body (s : Syntax.SourceSpan) (e : Syntax.Expr) : Syntax.Block := ⟨s,[⟨s,.returnStmt (some e)⟩]⟩
private def Failed (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope RuntimeValue)
    (st : List RuntimeValue) (s : Syntax.SourceSpan) (callee argument : Syntax.Expr) (b : Syntax.Block) : Prop :=
  evaluateClosedSourceExpression? (boundedInputsLambdaDepthBound 1 3 b) o n e st (call s callee argument) = none ∧
  (∀ budget, evaluateClosedSourceExpression? budget o n e st (call s callee argument) = none) ∧
  ∀ value final, ¬ E o n e st (call s callee argument) value final

section
variable {co mo so : Resolved.DeclarationId} {cn mn sn : LocalNameTable}
variable {ce me se : Resolved.LocalScope RuntimeValue}
variable (s : Syntax.SourceSpan) (st : List RuntimeValue)
variable (maker target : Syntax.Expr) (mp f g x : Syntax.Identifier)
variable (makerShape : SourceUnaryLambdaShape maker mp (body s (ref s mp)))
variable (fid gid xid : Resolved.LocalId) (value : RuntimeValue)
variable (fn : LocalNameTable.Lookup cn f.value fid)
variable (fv : Resolved.LocalScope.Lookup ce fid (.sourceClosure target so sn se))
variable (gn : LocalNameTable.Lookup cn g.value gid)
variable (gv : Resolved.LocalScope.Lookup ce gid (.sourceClosure maker mo mn me))
variable (xn : LocalNameTable.Lookup cn x.value xid) (xv : Resolved.LocalScope.Lookup ce xid value)
include makerShape fn fv gn gv xn xv

private theorem inputs :
    E co cn ce st (ref s f) (.sourceClosure target so sn se) st ∧
    evaluateClosedSourceExpression? 1 co cn ce st (ref s f) = some (.sourceClosure target so sn se,st) ∧
    E co cn ce st (call s (ref s g) (ref s x)) value st ∧
    evaluateClosedSourceExpression? 3 co cn ce st (call s (ref s g) (ref s x)) = some (value,st) ∧
    ¬ ClosedSourceDataExpression (call s (ref s g) (ref s x)) := by
  have selected : E co cn ce st (ref s f) (.sourceClosure target so sn se) st := .reference fn fv
  have supplied : E co cn ce st (call s (ref s g) (ref s x)) value st :=
    .call makerShape (.reference gn gv) (.reference xn xv) (.expression (.reference .head .head))
  refine ⟨selected,?_,supplied,?_,?_⟩
  · simp [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr fn,Resolved.LocalScope.lookup?_iff.mpr fv]
  · simp [call,ref,evaluateClosedSourceExpression?,evaluateClosedSourceBody?,body,
      LocalNameTable.lookup?_iff.mpr gn,Resolved.LocalScope.lookup?_iff.mpr gv,
      LocalNameTable.lookup?_iff.mpr xn,Resolved.LocalScope.lookup?_iff.mpr xv,
      sourceUnaryLambdaShape?_iff.mpr makerShape,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]
  · intro impossible; cases impossible

omit makerShape fn fv gn gv xn xv in
private theorem reject {source callee argument : Syntax.Expr} {parameter : Syntax.Identifier} {b : Syntax.Block}
    (shape : SourceUnaryLambdaShape source parameter b) (bg : ClosedSourceDataBody b)
    (selected : evaluateClosedSourceExpression? 1 co cn ce st callee = some (.sourceClosure source so sn se,st))
    (supplied : evaluateClosedSourceExpression? 3 co cn ce st argument = some (value,st))
    (original : ∀ actual final, ¬ E co cn ce st (call s callee argument) actual final) :
    Failed co cn ce st s callee argument b := by
  have absent := (boundedInputsLambda_evaluate_depth_none_iff shape bg selected supplied
    (Nat.le_refl _) (callSpan:=s) (argumentsSpan:=s)).mpr original
  exact ⟨absent,(boundedInputsLambda_evaluate_depth_none_iff_all_budgets shape bg selected supplied).mp absent,original⟩

/-- A successful non-data argument call cannot make the selected string-return body succeed. -/
theorem successful_argument_call_preserves_selected_body_failure
    (parameter : Syntax.Identifier) (text : String)
    (shape : SourceUnaryLambdaShape target parameter (body s ⟨s,.literal ⟨s,.string text⟩⟩)) :
    E co cn ce st (ref s f) (.sourceClosure target so sn se) st ∧
    evaluateClosedSourceExpression? 1 co cn ce st (ref s f) = some (.sourceClosure target so sn se,st) ∧
    E co cn ce st (call s (ref s g) (ref s x)) value st ∧
    evaluateClosedSourceExpression? 3 co cn ce st (call s (ref s g) (ref s x)) = some (value,st) ∧
    ¬ ClosedSourceDataExpression (call s (ref s g) (ref s x)) ∧
    Failed co cn ce st s (ref s f) (call s (ref s g) (ref s x)) (body s ⟨s,.literal ⟨s,.string text⟩⟩) := by
  obtain ⟨selected,calleeRun,supplied,argumentRun,notData⟩ := inputs s st maker target mp f g x makerShape fid gid xid value fn fv gn gv xn xv
  have absent : ∀ actual final, ¬ E co cn ce st (call s (ref s f) (call s (ref s g) (ref s x))) actual final := by
    intro actual final original
    cases original with
    | creation impossible => cases impossible
    | call actualShape actualCallee actualArgument actualBody =>
      obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic selected
      cases sameCallee; cases sameStore
      obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      obtain ⟨sameArgument,sameArgumentStore⟩ := actualArgument.deterministic supplied
      cases sameArgument; cases sameArgumentStore
      cases actualBody with
      | expression child => cases child with | wordLiteral meaning => cases meaning | creation impossible => cases impossible
  exact ⟨selected,calleeRun,supplied,argumentRun,notData,reject s st value shape (.expression .literal) calleeRun argumentRun absent⟩

/-- Caller success for a free name does not replace a missing saved capture after both inputs succeed. -/
theorem successful_inputs_do_not_repair_missing_saved_capture
    (parameter key : Syntax.Identifier) (shape : SourceUnaryLambdaShape target parameter (body s (ref s key)))
    (different : parameter.value ≠ key.value) (kid callerId : Resolved.LocalId) (callerValue : RuntimeValue)
    (savedName : LocalNameTable.Lookup sn key.value kid) (missing : Resolved.LocalScope.lookup? se kid = none)
    (callerName : LocalNameTable.Lookup cn key.value callerId) (callerFound : Resolved.LocalScope.Lookup ce callerId callerValue) :
    E co cn ce st (ref s f) (.sourceClosure target so sn se) st ∧
    evaluateClosedSourceExpression? 1 co cn ce st (ref s f) = some (.sourceClosure target so sn se,st) ∧
    E co cn ce st (call s (ref s g) (ref s x)) value st ∧
    evaluateClosedSourceExpression? 3 co cn ce st (call s (ref s g) (ref s x)) = some (value,st) ∧
    ¬ ClosedSourceDataExpression (call s (ref s g) (ref s x)) ∧ E co cn ce st (ref s key) callerValue st ∧
    Failed co cn ce st s (ref s f) (call s (ref s g) (ref s x)) (body s (ref s key)) := by
  obtain ⟨selected,calleeRun,supplied,argumentRun,notData⟩ := inputs s st maker target mp f g x makerShape fid gid xid value fn fv gn gv xn xv
  have caller : E co cn ce st (ref s key) callerValue st := .reference callerName callerFound
  have freshNe : Resolved.freshLocalId so (sn.map Prod.snd) ≠ kid := by
    intro same
    have member : kid ∈ sn.map Prod.snd := List.mem_map.mpr ⟨(key.value,kid),savedName.mem,rfl⟩
    rw [← same] at member
    exact Resolved.freshLocalId_not_mem so _ member
  have noBody : ∀ actual final, ¬ ClosedSourceBodyEvaluates so
      ((parameter.value,Resolved.freshLocalId so (sn.map Prod.snd))::sn)
      ((Resolved.freshLocalId so (sn.map Prod.snd),value)::se) st (body s (ref s key)) actual final := by
    intro actual final original
    cases original with
    | expression child =>
      cases child with
      | creation impossible => cases impossible
      | reference named found =>
        cases named.id_unique (LocalNameTable.Lookup.tail different savedName)
        have accepted := Resolved.LocalScope.lookup?_iff.mpr found
        simp only [Resolved.LocalScope.lookup?,if_neg freshNe,missing] at accepted
        cases accepted
  have absent : ∀ actual final, ¬ E co cn ce st (call s (ref s f) (call s (ref s g) (ref s x))) actual final := by
    intro actual final original
    cases original with
    | creation impossible => cases impossible
    | call actualShape actualCallee actualArgument actualBody =>
      obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic selected
      cases sameCallee; cases sameStore
      obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      obtain ⟨sameArgument,sameArgumentStore⟩ := actualArgument.deterministic supplied
      cases sameArgument; cases sameArgumentStore
      exact noBody _ _ actualBody
  exact ⟨selected,calleeRun,supplied,argumentRun,notData,caller,reject s st value shape (.expression .reference) calleeRun argumentRun absent⟩
end
end Tests.BoundedInputsDepthBoundaries

namespace Tests.BoundedInputsDepthBoundaries
open Solcore Solcore.Frontend
private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"BoundedInputsReview",by decide⟩],by decide⟩⟩,n⟩
private def co := owner 908
private def mo := owner 608
private def so := owner 308
private def cid (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def mid (n : Nat) : Resolved.LocalId := ⟨mo,n⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨so,n⟩
private def cs : Syntax.SourceSpan := ⟨⟨.main,"bounded-inputs.sol"⟩,0,1⟩
private def idn (n : String) : Syntax.Identifier := ⟨cs,n⟩
private def lambda (p : String) (b : Syntax.Block) : Syntax.Expr :=
  ⟨cs,.lambda cs ⟨cs,[⟨cs,.inferred (idn p)⟩]⟩ none b⟩
private def maker := lambda "m" (body cs (ref cs (idn "m")))
private def bad := lambda "p" (body cs ⟨cs,.literal ⟨cs,.string "bad"⟩⟩)
private def missing := lambda "p" (body cs (ref cs (idn "key")))
private def opaqueValue : RuntimeValue := RuntimeValue.ofCore
  (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
private def payload : RuntimeValue := .pair (.word Core.Word.maximum) opaqueValue
private def mn : LocalNameTable := [("m",mid 8),("m",mid 99)]
private def me : Resolved.LocalScope RuntimeValue := [(mid 8,opaqueValue),(mid 8,payload),(mid 99,.unit)]
private def sn : LocalNameTable := [("key",sid 3),("p",sid 8),("key",sid 99)]
private def se : Resolved.LocalScope RuntimeValue := [(sid 8,opaqueValue),(sid 8,payload),(sid 99,.bool false)]
private def cn : LocalNameTable := [("f",cid 1),("g",cid 2),("x",cid 3),("key",cid 4),("f",cid 99)]
private def ce (target : Syntax.Expr) : Resolved.LocalScope RuntimeValue :=
  [(cid 1,.sourceClosure target so sn se),(cid 1,opaqueValue),(cid 2,.sourceClosure maker mo mn me),
    (cid 3,payload),(cid 3,.unit),(cid 4,opaqueValue)]
private def store : List RuntimeValue :=
  [payload,.sourceClosure maker mo mn me,opaqueValue,.hostFunction .storageWrite,.cellRef .word 900]
private def argument := call cs (ref cs (idn "g")) (ref cs (idn "x"))
private def whole := call cs (ref cs (idn "f")) argument

example : co ≠ mo ∧ co ≠ so ∧ mo ≠ so ∧ store ≠ [] := by decide

example : evaluateClosedSourceExpression? 3 co cn (ce bad) store argument = some (payload,store) ∧
    (∀ budget, evaluateClosedSourceExpression? budget co cn (ce bad) store whole = none) := by
  have originalInputs := inputs (co:=co) (mo:=mo) (so:=so) (cn:=cn) (mn:=mn) (sn:=sn)
    (ce:=ce bad) (me:=me) (se:=se) cs store maker bad (idn "m") (idn "f") (idn "g") (idn "x")
    SourceUnaryLambdaShape.inferred (cid 1) (cid 2) (cid 3) payload .head .head
    (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
    (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
  obtain ⟨_,_,_,_,_,failed⟩ := successful_argument_call_preserves_selected_body_failure
    (co:=co) (mo:=mo) (so:=so) (cn:=cn) (mn:=mn) (sn:=sn) (ce:=ce bad) (me:=me) (se:=se)
    cs store maker bad (idn "m") (idn "f") (idn "g") (idn "x") SourceUnaryLambdaShape.inferred
    (cid 1) (cid 2) (cid 3) payload .head .head
    (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
    (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
    (idn "p") "bad" SourceUnaryLambdaShape.inferred
  exact ⟨originalInputs.2.2.2.1,failed.2.1⟩

example : E co cn (ce missing) store (ref cs (idn "key")) opaqueValue store ∧
    (∀ budget, evaluateClosedSourceExpression? budget co cn (ce missing) store whole = none) := by
  have originalInputs := inputs (co:=co) (mo:=mo) (so:=so) (cn:=cn) (mn:=mn) (sn:=sn)
    (ce:=ce missing) (me:=me) (se:=se) cs store maker missing (idn "m") (idn "f") (idn "g") (idn "x")
    SourceUnaryLambdaShape.inferred (cid 1) (cid 2) (cid 3) payload .head .head
    (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
    (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
  have caller : E co cn (ce missing) store (ref cs (idn "key")) opaqueValue store :=
    .reference (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
  obtain ⟨_,_,_,_,_,_,failed⟩ := successful_inputs_do_not_repair_missing_saved_capture
    (co:=co) (mo:=mo) (so:=so) (cn:=cn) (mn:=mn) (sn:=sn) (ce:=ce missing) (me:=me) (se:=se)
    cs store maker missing (idn "m") (idn "f") (idn "g") (idn "x") SourceUnaryLambdaShape.inferred
    (cid 1) (cid 2) (cid 3) payload .head .head
    (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
    (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
    (idn "p") (idn "key") SourceUnaryLambdaShape.inferred (by decide) (sid 3) (cid 4) opaqueValue
    .head (by rfl) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
    (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
  exact ⟨caller,failed.2.1⟩
end Tests.BoundedInputsDepthBoundaries
