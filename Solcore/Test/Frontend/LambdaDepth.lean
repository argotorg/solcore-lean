import Solcore.Frontend.BoundedCalleeLambdaDepth
import Solcore.Frontend.BoundedInputsLambdaDepth
import Solcore.Frontend.ClosedSource
import Solcore.Frontend.DataCalleeLambdaDepth
import Solcore.Frontend.DirectDataLambdaDepth
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.SavedDataLambdaDepth

/-!
# Lambda depth tests

Bounds on lambda depth: callee chains, inputs, data bodies and data callees, direct and saved data
lambdas, and nested arguments.
-/

section
-- leanmerge: from Solcore.Test.FrontendBoundedCalleeLambdaDepthBoundaryProperties
/- An independently successful inner identity call returns the actual outer
source closure. Original outer-call exclusions precede finite-depth decisions;
the inner application is deliberately outside the data-expression gate. -/
set_option autoImplicit false
namespace Tests.BoundedCalleeLambdaDepthBoundaries
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def unit (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.tuple ⟨s,[]⟩⟩
private def call (s : Syntax.SourceSpan) (callee argument : Syntax.Expr) : Syntax.Expr :=
  ⟨s,.call callee ⟨s,[argument]⟩⟩
private def identityBody (s : Syntax.SourceSpan) (parameter : Syntax.Identifier) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (ref s parameter))⟩]⟩
private def Failed (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope RuntimeValue) (st : List RuntimeValue)
    (s : Syntax.SourceSpan) (callee argument : Syntax.Expr) (body : Syntax.Block) : Prop :=
  evaluateClosedSourceExpression? (boundedCalleeLambdaDepthBound 3 argument body)
    o n e st (call s callee argument) = none ∧
  (∀ budget, evaluateClosedSourceExpression? budget o n e st (call s callee argument) = none) ∧
  ∀ value final, ¬ E o n e st (call s callee argument) value final

variable {co mo so : Resolved.DeclarationId} {cn mn sn : LocalNameTable}
variable {ce me se : Resolved.LocalScope RuntimeValue}
private theorem inner (s : Syntax.SourceSpan) (st : List RuntimeValue)
    {maker target : Syntax.Expr} {parameter functionName closureName : Syntax.Identifier}
    (shape : SourceUnaryLambdaShape maker parameter (identityBody s parameter))
    {fid xid : Resolved.LocalId}
    (fn : LocalNameTable.Lookup cn functionName.value fid)
    (fv : Resolved.LocalScope.Lookup ce fid (.sourceClosure maker mo mn me))
    (xn : LocalNameTable.Lookup cn closureName.value xid)
    (xv : Resolved.LocalScope.Lookup ce xid (.sourceClosure target so sn se)) :
    let callee := call s (ref s functionName) (ref s closureName)
    E co cn ce st callee (.sourceClosure target so sn se) st ∧
    evaluateClosedSourceExpression? 3 co cn ce st callee = some (.sourceClosure target so sn se,st) ∧
    ¬ ClosedSourceDataExpression callee := by
  intro callee
  have original : E co cn ce st callee (.sourceClosure target so sn se) st :=
    .call shape (.reference fn fv) (.reference xn xv) (.expression (.reference .head .head))
  refine ⟨original,?_,?_⟩
  · simp [callee,call,ref,evaluateClosedSourceExpression?,evaluateClosedSourceBody?,
      LocalNameTable.lookup?_iff.mpr fn,Resolved.LocalScope.lookup?_iff.mpr fv,
      LocalNameTable.lookup?_iff.mpr xn,Resolved.LocalScope.lookup?_iff.mpr xv,
      sourceUnaryLambdaShape?_iff.mpr shape,identityBody,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]
  · intro impossible
    dsimp only [callee,call] at impossible
    cases impossible

private theorem reject (s : Syntax.SourceSpan) (st : List RuntimeValue)
    {source callee argument : Syntax.Expr} {parameter : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source parameter body)
    (ag : ClosedSourceDataExpression argument) (bg : ClosedSourceDataBody body)
    (selected : evaluateClosedSourceExpression? 3 co cn ce st callee = some (.sourceClosure source so sn se,st))
    (original : ∀ value final, ¬ E co cn ce st (call s callee argument) value final) :
    Failed co cn ce st s callee argument body := by
  have absent := (boundedCalleeLambda_evaluate_depth_none_iff shape ag bg selected
    (Nat.le_refl _) (callSpan:=s) (argumentsSpan:=s)).mpr original
  exact ⟨absent,(boundedCalleeLambda_evaluate_depth_none_iff_all_budgets shape ag bg selected).mp absent,original⟩

theorem returned_closure_bad_body_still_fails_after_inner_success
    (s : Syntax.SourceSpan) (st : List RuntimeValue)
    (maker target : Syntax.Expr) (makerParameter targetParameter functionName closureName : Syntax.Identifier)
    (makerShape : SourceUnaryLambdaShape maker makerParameter (identityBody s makerParameter))
    (text : String)
    (targetShape : SourceUnaryLambdaShape target targetParameter
      ⟨s,[⟨s,.returnStmt (some ⟨s,.literal ⟨s,.string text⟩⟩)⟩]⟩)
    (fid xid : Resolved.LocalId)
    (fn : LocalNameTable.Lookup cn functionName.value fid)
    (fv : Resolved.LocalScope.Lookup ce fid (.sourceClosure maker mo mn me))
    (xn : LocalNameTable.Lookup cn closureName.value xid)
    (xv : Resolved.LocalScope.Lookup ce xid (.sourceClosure target so sn se)) :
    let callee := call s (ref s functionName) (ref s closureName)
    E co cn ce st callee (.sourceClosure target so sn se) st ∧
    evaluateClosedSourceExpression? 3 co cn ce st callee = some (.sourceClosure target so sn se,st) ∧
    ¬ ClosedSourceDataExpression callee ∧
    Failed co cn ce st s callee (unit s) ⟨s,[⟨s,.returnStmt (some ⟨s,.literal ⟨s,.string text⟩⟩)⟩]⟩ := by
  intro callee
  obtain ⟨selected,ran,notData⟩ := inner (co:=co) s st makerShape fn fv xn xv
  refine ⟨selected,ran,notData,reject s st targetShape .unit (.expression .literal) ran ?_⟩
  intro value final original
  cases original with
  | creation impossible => cases impossible
  | call actualShape actualCallee _ actualBody =>
    obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic selected
    cases sameCallee; cases sameStore
    obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
      ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans (sourceUnaryLambdaShape?_iff.mpr targetShape)))
    cases sameName; cases sameBody
    cases actualBody with
    | expression child =>
      cases child with | wordLiteral meaning => cases meaning | creation impossible => cases impossible

theorem returned_closure_saved_value_cannot_fill_missing_outer_argument
    (s : Syntax.SourceSpan) (st : List RuntimeValue)
    (maker target : Syntax.Expr) (makerParameter targetParameter functionName closureName key : Syntax.Identifier)
    (makerShape : SourceUnaryLambdaShape maker makerParameter (identityBody s makerParameter))
    (body : Syntax.Block) (targetShape : SourceUnaryLambdaShape target targetParameter body)
    (bg : ClosedSourceDataBody body) (fid xid kid : Resolved.LocalId) (value : RuntimeValue)
    (fn : LocalNameTable.Lookup cn functionName.value fid)
    (fv : Resolved.LocalScope.Lookup ce fid (.sourceClosure maker mo mn me))
    (xn : LocalNameTable.Lookup cn closureName.value xid)
    (xv : Resolved.LocalScope.Lookup ce xid (.sourceClosure target so sn se))
    (kn : LocalNameTable.Lookup sn key.value kid) (kv : Resolved.LocalScope.Lookup se kid value)
    (missing : LocalNameTable.lookup? cn key.value = none) :
    let callee := call s (ref s functionName) (ref s closureName)
    E co cn ce st callee (.sourceClosure target so sn se) st ∧
    evaluateClosedSourceExpression? 3 co cn ce st callee = some (.sourceClosure target so sn se,st) ∧
    ¬ ClosedSourceDataExpression callee ∧ E so sn se st (ref s key) value st ∧
    Failed co cn ce st s callee (ref s key) body := by
  intro callee
  obtain ⟨selected,ran,notData⟩ := inner (co:=co) s st makerShape fn fv xn xv
  have saved : E so sn se st (ref s key) value st := .reference kn kv
  have absent : ∀ actual final, ¬ E co cn ce st (ref s key) actual final := by
    intro actual final original
    cases original with
    | creation impossible => cases impossible
    | reference named _ =>
      have accepted := LocalNameTable.lookup?_iff.mpr named
      rw [missing] at accepted; cases accepted
  refine ⟨selected,ran,notData,saved,reject s st targetShape .reference bg ran ?_⟩
  intro actual final original
  cases original with
  | creation impossible => cases impossible
  | call _ actualCallee actualArgument _ =>
    obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic selected
    cases sameCallee; cases sameStore
    exact absent _ _ actualArgument

end Tests.BoundedCalleeLambdaDepthBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendBoundedInputsDepthBoundaryProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendDataBodyDepthControlFlowProperties
/- Original conditional and ordered-choice witnesses precede depth contracts.
Mixed captures and complete stores remain arbitrary; no uniqueness or typing
premise is introduced. Visited match comparisons are not source-search depth. -/
set_option autoImplicit false
namespace Tests.DataBodyDepthControlFlow
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def bare (bodySpan returnSpan : Syntax.SourceSpan) : Syntax.Block :=
  ⟨bodySpan,[⟨returnSpan,.returnStmt none⟩]⟩
private def returning (bodySpan returnSpan expressionSpan : Syntax.SourceSpan)
    (name : Syntax.Identifier) : Syntax.Block :=
  ⟨bodySpan,[⟨returnSpan,.returnStmt (some (reference expressionSpan name))⟩]⟩
private def conditional (spans : Fin 8 → Syntax.SourceSpan)
    (guard payload : Syntax.Identifier) : Syntax.Block :=
  ⟨spans 0,[⟨spans 1,.ifThen (reference (spans 2) guard)
    (returning (spans 3) (spans 4) (spans 5) payload)
    (some (bare (spans 6) (spans 7)))⟩]⟩

/-- The unselected expression return makes H=3 conservative on the false path;
the true path needs all three levels even for an arbitrary mixed payload. -/
theorem conditional_mixed_endpoint_and_conservative_depth
    (spans : Fin 8 → Syntax.SourceSpan) (guard payload : Syntax.Identifier)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (guardId payloadId : Resolved.LocalId) (choice : Bool) (value : RuntimeValue)
    (namedGuard : LocalNameTable.Lookup names guard.value guardId)
    (foundGuard : Resolved.LocalScope.Lookup captured guardId (.bool choice))
    (namedPayload : LocalNameTable.Lookup names payload.value payloadId)
    (foundPayload : Resolved.LocalScope.Lookup captured payloadId value) (extra : Nat) :
    let body := conditional spans guard payload
    let result := if choice then value else .unit
    ClosedSourceDataBody body ∧ closedSourceDataBodyDepthBound body = 3 ∧
    ClosedSourceBodyEvaluates owner names captured store body result store ∧
    evaluateClosedSourceBody? 1 owner names captured store body = none ∧
    evaluateClosedSourceBody? 2 owner names captured store body =
      (if choice then none else some (.unit,store)) ∧
    (choice = true → ∀ budget, budget < 3 →
      evaluateClosedSourceBody? budget owner names captured store body = none) ∧
    evaluateClosedSourceBody? (3 + extra) owner names captured store body = some (result,store) ∧
    evaluateClosedSourceBody? (3 + extra) owner names captured store body =
      evaluateClosedSourceBody? (closedSourceDataBodyDepthBound body) owner names captured store body ∧
    (∀ actual final, evaluateClosedSourceBody? (3 + extra) owner names captured store body =
      some (actual,final) ↔ actual = result ∧ final = store) := by
  intro body result
  have original : ClosedSourceBodyEvaluates owner names captured store body result store := by
    cases choice with
    | false => exact .ifFalse (.reference namedGuard foundGuard) .bare
    | true => exact .ifTrue (.reference namedGuard foundGuard) (.expression (.reference namedPayload foundPayload))
  have gate : ClosedSourceDataBody body := .conditional .reference (.expression .reference) .bare
  have depth : closedSourceDataBodyDepthBound body = 3 := by
    simp only [body,conditional,returning,bare,reference,closedSourceDataBodyDepthBound,closedSourceDataDepthBound]
    omega
  have atOne : evaluateClosedSourceBody? 1 owner names captured store body = none := by
    simp only [body,conditional,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,bind,Option.bind_none]
  have atTwo : evaluateClosedSourceBody? 2 owner names captured store body =
      (if choice then none else some (.unit,store)) := by
    cases choice <;> simp only [body,conditional,reference,returning,bare,
      evaluateClosedSourceBody?,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr namedGuard,
      Resolved.LocalScope.lookup?_iff.mpr foundGuard,bind,pure,Option.bind_some,Bool.false_eq_true,↓reduceIte]
  have necessary : choice = true → ∀ budget, budget < 3 →
      evaluateClosedSourceBody? budget owner names captured store body = none := by
    intro chosen budget small
    cases budget with
    | zero => simp only [evaluateClosedSourceBody?]
    | succ budget =>
        cases budget with
        | zero => exact atOne
        | succ budget =>
            have zero : budget = 0 := by omega
            subst budget
            simpa only [chosen,↓reduceIte] using atTwo
  have enough : closedSourceDataBodyDepthBound body ≤ 3 + extra := by omega
  refine ⟨gate,depth,original,atOne,atTwo,necessary,gate.evaluates_at_depthBound original enough,
    gate.evaluate_depth_stable owner names captured store enough,?_⟩
  intro actual final
  rw [gate.evaluate_at_depthBound_iff enough]
  exact ⟨fun evaluated => evaluated.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩

private def one : Core.Word := ⟨1,by decide⟩
private def zeroCase (spans : Fin 8 → Syntax.SourceSpan) : Syntax.MatchCase :=
  ⟨spans 4,⟨⟨spans 5,.literal ⟨spans 5,.decimal "0"⟩⟩,bare (spans 6) (spans 7)⟩⟩
private def missedCases (spans : Fin 8 → Syntax.SourceSpan) : Nat → List Syntax.MatchCase
  | 0 => []
  | n + 1 => zeroCase spans :: missedCases spans n
private def matching (spans : Fin 8 → Syntax.SourceSpan) (n : Nat) : Syntax.Block :=
  ⟨spans 0,[⟨spans 1,.matchWith
    ⟨spans 2,⟨⟨spans 2,.literal ⟨spans 2,.decimal "1"⟩⟩,[]⟩⟩
    ⟨spans 3,⟨missedCases spans n,some (bare (spans 6) (spans 7))⟩⟩⟩]⟩

private theorem one_meaning (span : Syntax.SourceSpan) :
    WordLiteralDenotes ⟨span,.decimal "1"⟩ one :=
  .decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)
private theorem zero_pattern (spans : Fin 8 → Syntax.SourceSpan) :
    WordMatchPatternClassifies (zeroCase spans).value.pattern (some Core.Word.zero) :=
  .literal ⟨⟨spans 5,.decimal "0"⟩,rfl,
    .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)⟩

private theorem original_choice (spans : Fin 8 → Syntax.SourceSpan) (n : Nat) :
    RuntimeWordMatchChooses (.word one) (missedCases spans n)
      (some (bare (spans 6) (spans 7))) (bare (spans 6) (spans 7)) n := by
  induction n with
  | zero => exact .fallback
  | succ n ih => exact .miss (zero_pattern spans) (by decide) ih

private theorem all_branches (spans : Fin 8 → Syntax.SourceSpan) (n : Nat) :
    ∀ arm ∈ missedCases spans n, ClosedSourceDataBody arm.value.body := by
  induction n with
  | zero => intro arm member; cases member
  | succ n ih =>
      intro arm member
      simp only [missedCases,List.mem_cons] at member
      rcases member with same | member
      · cases same; exact .bare
      · exact ih arm member

private theorem branches_depth (spans : Fin 8 → Syntax.SourceSpan) (n : Nat) :
    closedSourceDataMatchDepthBound (missedCases spans n)
      (some (bare (spans 6) (spans 7))) = 1 := by
  induction n with
  | zero => simp only [missedCases,closedSourceDataMatchDepthBound,bare,closedSourceDataBodyDepthBound]
  | succ n ih =>
      rw [missedCases,closedSourceDataMatchDepthBound,ih]
      simp only [zeroCase,bare,closedSourceDataBodyDepthBound,Nat.max_self]

/-- All n visited literal comparisons are retained by the original ordered
choice, while the entire body has depth two independently of n. -/
theorem arbitrary_misses_keep_comparison_count_separate_from_depth
    (spans : Fin 8 → Syntax.SourceSpan) (n extra : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) :
    let body := matching spans n
    let fallback := bare (spans 6) (spans 7)
    RuntimeWordMatchChooses (.word one) (missedCases spans n) (some fallback) fallback n ∧
    chooseRuntimeWordMatch? (.word one) (missedCases spans n) (some fallback) = some (fallback,n) ∧
    (∀ selected tests, RuntimeWordMatchChooses (.word one) (missedCases spans n)
      (some fallback) selected tests ↔ selected = fallback ∧ tests = n) ∧
    ClosedSourceDataBody body ∧ closedSourceDataBodyDepthBound body = 2 ∧
    ClosedSourceBodyEvaluates owner names captured store body .unit store ∧
    evaluateClosedSourceBody? 1 owner names captured store body = none ∧
    evaluateClosedSourceBody? (2 + extra) owner names captured store body = some (.unit,store) ∧
    evaluateClosedSourceBody? (2 + extra) owner names captured store body =
      evaluateClosedSourceBody? (closedSourceDataBodyDepthBound body) owner names captured store body ∧
    (∀ actual final, evaluateClosedSourceBody? (2 + extra) owner names captured store body =
      some (actual,final) ↔ actual = .unit ∧ final = store) := by
  intro body fallback
  have choice := original_choice spans n
  have original : ClosedSourceBodyEvaluates owner names captured store body .unit store :=
    .wordMatch (.wordLiteral (one_meaning (spans 2))) choice .bare
  have gate : ClosedSourceDataBody body := .wordMatch .literal (all_branches spans n)
    (by intro source member; simp only [Option.toList_some,List.mem_singleton] at member; subst source; exact .bare)
  have depth : closedSourceDataBodyDepthBound body = 2 := by
    simp only [body,matching,closedSourceDataBodyDepthBound,closedSourceDataDepthBound,branches_depth]
    omega
  have atOne : evaluateClosedSourceBody? 1 owner names captured store body = none := by
    simp only [body,matching,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,bind,Option.bind_none]
  have enough : closedSourceDataBodyDepthBound body ≤ 2 + extra := by omega
  refine ⟨choice,chooseRuntimeWordMatch?_iff.mpr choice,?_,gate,depth,original,atOne,
    gate.evaluates_at_depthBound original enough,
    gate.evaluate_depth_stable owner names captured store enough,?_⟩
  · intro selected tests
    exact ⟨fun selectedChoice => selectedChoice.deterministic choice,by rintro ⟨rfl,rfl⟩; exact choice⟩
  · intro actual final
    rw [gate.evaluate_at_depthBound_iff enough]
    exact ⟨fun evaluated => evaluated.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩

end Tests.DataBodyDepthControlFlow
end

section
-- leanmerge: from Solcore.Test.FrontendDataBodyDepthShadowingProperties
/- Original fresh binding witnesses precede all bounded-search consequences.
Repeated shadowing retains arbitrary mixed values and the entire actual store. -/
set_option autoImplicit false
namespace Tests.DataBodyDepthShadowing
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def statements (spans : Fin 3 → Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Option Syntax.TypeExpr) : Nat → List Syntax.Statement
  | 0 => [⟨spans 0,.returnStmt (some (reference (spans 2) name))⟩]
  | n + 1 => ⟨spans 1,.letDecl name annotation (some (reference (spans 2) name))⟩ ::
      statements spans name annotation n
private def source (bodySpan : Syntax.SourceSpan) (spans : Fin 3 → Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat) : Syntax.Block :=
  ⟨bodySpan,statements spans name annotation n⟩

private theorem admitted_chain (bodySpan : Syntax.SourceSpan) (spans : Fin 3 → Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat) :
    ClosedSourceDataBody (source bodySpan spans name annotation n) := by
  induction n with
  | zero => exact .expression .reference
  | succ n ih => exact .binding .reference ih

private theorem bound (bodySpan : Syntax.SourceSpan) (spans : Fin 3 → Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat) :
    closedSourceDataBodyDepthBound (source bodySpan spans name annotation n) = n + 2 := by
  induction n with
  | zero => simp only [source,statements,closedSourceDataBodyDepthBound,reference,closedSourceDataDepthBound]
  | succ n ih =>
      change closedSourceDataBodyDepthBound
        ⟨bodySpan,⟨spans 1,.letDecl name annotation (some (reference (spans 2) name))⟩ ::
          statements spans name annotation n⟩ = _
      rw [closedSourceDataBodyDepthBound]
      change max (closedSourceDataDepthBound (reference (spans 2) name))
        (closedSourceDataBodyDepthBound (source bodySpan spans name annotation n)) + 1 = _
      rw [ih]
      simp only [reference,closedSourceDataDepthBound]
      omega

private theorem original (bodySpan : Syntax.SourceSpan) (spans : Fin 3 → Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) :
    ClosedSourceBodyEvaluates owner names captured store
      (source bodySpan spans name annotation n) value store := by
  induction n generalizing names captured id with
  | zero => exact .expression (.reference named found)
  | succ n ih =>
      have initializer : ClosedSourceExpressionEvaluates owner names captured store
          (reference (spans 2) name) value store := .reference named found
      have tail := ih ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
        ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured)
        (Resolved.freshLocalId owner (names.map Prod.snd)) .head .head
      cases annotation with
      | none => exact .inferred initializer tail
      | some annotation => exact .binding initializer tail

private theorem before (bodySpan : Syntax.SourceSpan) (spans : Fin 3 → Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (small : budget ≤ n + 1) :
    evaluateClosedSourceBody? budget owner names captured store
      (source bodySpan spans name annotation n) = none := by
  induction n generalizing budget names captured store with
  | zero =>
      cases budget with
      | zero => simp only [evaluateClosedSourceBody?]
      | succ budget =>
          have zero : budget = 0 := by omega
          subst budget
          simp only [source,statements,evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
  | succ n ih =>
      cases budget with
      | zero => simp only [evaluateClosedSourceBody?]
      | succ budget =>
          cases child : evaluateClosedSourceExpression? budget owner names captured store
              (reference (spans 2) name) with
          | none => simp only [source,statements,evaluateClosedSourceBody?,child,bind,Option.bind_none]
          | some endpoint =>
              obtain ⟨value,middleStore⟩ := endpoint
              have tail := ih budget
                ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
                ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured)
                middleStore (by omega)
              simpa only [source,statements,evaluateClosedSourceBody?,child,bind,Option.bind_some] using tail

/-- Every typed or inferred shadowing chain has the exact source-depth boundary,
without uniqueness, typing, foreign-owner exclusions or an empty store premise. -/
theorem arbitrary_fresh_shadowing_depth (bodySpan : Syntax.SourceSpan)
    (spans : Fin 3 → Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Option Syntax.TypeExpr) (n extra : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) :
    let body := source bodySpan spans name annotation n
    ClosedSourceDataBody body ∧ closedSourceDataBodyDepthBound body = n + 2 ∧
    ClosedSourceBodyEvaluates owner names captured store body value store ∧
    evaluateClosedSourceBody? (n + 1) owner names captured store body = none ∧
    evaluateClosedSourceBody? (n + 2 + extra) owner names captured store body = some (value,store) ∧
    (∀ actual final, evaluateClosedSourceBody? (n + 2 + extra) owner names captured store body =
      some (actual,final) ↔ actual = value ∧ final = store) := by
  intro body
  have gate := admitted_chain bodySpan spans name annotation n
  have depth : closedSourceDataBodyDepthBound body = n + 2 :=
    bound bodySpan spans name annotation n
  have enough : closedSourceDataBodyDepthBound body ≤ n + 2 + extra := by omega
  have witnessed := original bodySpan spans name annotation n owner names captured store id value named found
  refine ⟨gate,depth,witnessed,before bodySpan spans name annotation n _ owner names captured store (Nat.le_refl _),
    gate.evaluates_at_depthBound witnessed enough,?_⟩
  intro actual final
  rw [gate.evaluate_at_depthBound_iff enough]
  exact ⟨fun evaluated => evaluated.deterministic witnessed,by rintro ⟨rfl,rfl⟩; exact witnessed⟩

end Tests.DataBodyDepthShadowing
end

section
-- leanmerge: from Solcore.Test.FrontendDataCalleeLambdaDepthBoundaryProperties
/- Independent original selection and whole-call exclusion precede new depth laws.
An unselected good closure is not a fallback for a selected bad body, and a saved
value is not a caller argument. Actual mixed values and stores remain literal. -/
set_option autoImplicit false
namespace Tests.DataCalleeLambdaDepthBoundaries
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def unit (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.tuple ⟨s,[]⟩⟩
private def bare (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,[⟨s,.returnStmt none⟩]⟩
private def call (s : Syntax.SourceSpan) (callee argument : Syntax.Expr) : Syntax.Expr :=
  ⟨s,.call callee ⟨s,[argument]⟩⟩
private def choose (s : Syntax.SourceSpan) (guard first second : Syntax.Identifier) : Syntax.Expr :=
  ⟨s,.conditional (ref s guard) s (ref s first) s (ref s second)⟩
private def either (s : Syntax.SourceSpan) (guard selected : Syntax.Identifier) : Syntax.Expr :=
  ⟨s,.binary (ref s guard) ⟨s,.logicalOr⟩ (ref s selected)⟩
private def Failed (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope RuntimeValue) (st : List RuntimeValue)
    (s : Syntax.SourceSpan) (callee argument : Syntax.Expr) (body : Syntax.Block) : Prop :=
  evaluateClosedSourceExpression? (dataCalleeLambdaDepthBound callee argument body)
    o n e st (call s callee argument) = none ∧
  (∀ budget, evaluateClosedSourceExpression? budget o n e st (call s callee argument) = none) ∧
  ∀ value final, ¬ E o n e st (call s callee argument) value final

variable {co so : Resolved.DeclarationId} {cn sn : LocalNameTable}
variable {ce se : Resolved.LocalScope RuntimeValue}
private theorem reject (s : Syntax.SourceSpan) (st : List RuntimeValue)
    {source callee argument : Syntax.Expr} {parameter : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source parameter body)
    (cg : ClosedSourceDataExpression callee) (ag : ClosedSourceDataExpression argument)
    (bg : ClosedSourceDataBody body)
    (selected : E co cn ce st callee (.sourceClosure source so sn se) st)
    (original : ∀ value final, ¬ E co cn ce st (call s callee argument) value final) :
    Failed co cn ce st s callee argument body := by
  have absent := (dataCalleeLambda_evaluate_depth_none_iff shape cg ag bg selected
    (Nat.le_refl _) (callSpan:=s) (argumentsSpan:=s)).mpr original
  exact ⟨absent,(dataCalleeLambda_evaluate_depth_none_iff_all_budgets shape cg ag bg selected).mp absent,original⟩

theorem selected_bad_body_never_uses_unselected_good_closure
    (s : Syntax.SourceSpan) (st : List RuntimeValue) (guard first second parameter otherParameter : Syntax.Identifier)
    (source otherSource : Syntax.Expr) (text : String)
    (shape : SourceUnaryLambdaShape source parameter
      ⟨s,[⟨s,.returnStmt (some ⟨s,.literal ⟨s,.string text⟩⟩)⟩]⟩)
    (otherShape : SourceUnaryLambdaShape otherSource otherParameter (bare s))
    (otherOwner : Resolved.DeclarationId) (otherNames : LocalNameTable)
    (otherCaptured : Resolved.LocalScope RuntimeValue) (gid fid oid : Resolved.LocalId)
    (gn : LocalNameTable.Lookup cn guard.value gid) (gv : Resolved.LocalScope.Lookup ce gid (.bool true))
    (fn : LocalNameTable.Lookup cn first.value fid)
    (fv : Resolved.LocalScope.Lookup ce fid (.sourceClosure source so sn se))
    (on : LocalNameTable.Lookup cn second.value oid)
    (ov : Resolved.LocalScope.Lookup ce oid (.sourceClosure otherSource otherOwner otherNames otherCaptured)) :
    E co cn ce st (choose s guard first second) (.sourceClosure source so sn se) st ∧
    E co cn ce st (call s (ref s second) (unit s)) .unit st ∧
    Failed co cn ce st s (choose s guard first second) (unit s)
      ⟨s,[⟨s,.returnStmt (some ⟨s,.literal ⟨s,.string text⟩⟩)⟩]⟩ := by
  have selected : E co cn ce st (choose s guard first second) (.sourceClosure source so sn se) st :=
    .conditionalTrue (.reference gn gv) (.reference fn fv)
  have other : E co cn ce st (call s (ref s second) (unit s)) .unit st :=
    .call otherShape (.reference on ov) .unit .bare
  refine ⟨selected,other,reject s st shape (.conditional .reference .reference .reference)
    .unit (.expression .literal) selected ?_⟩
  intro value final original
  cases original with
  | creation impossible => cases impossible
  | call actualShape actualCallee _ actualBody =>
    obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic selected
    cases sameCallee; cases sameStore
    obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
      ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans (sourceUnaryLambdaShape?_iff.mpr shape)))
    cases sameName; cases sameBody
    cases actualBody with
    | expression child =>
      cases child with | wordLiteral meaning => cases meaning | creation impossible => cases impossible

theorem short_circuit_selected_saved_value_cannot_supply_caller_argument
    (s : Syntax.SourceSpan) (st : List RuntimeValue) (guard picked key parameter : Syntax.Identifier)
    (source : Syntax.Expr) (body : Syntax.Block)
    (shape : SourceUnaryLambdaShape source parameter body) (bg : ClosedSourceDataBody body)
    (gid fid savedId : Resolved.LocalId) (value : RuntimeValue)
    (gn : LocalNameTable.Lookup cn guard.value gid) (gv : Resolved.LocalScope.Lookup ce gid (.bool false))
    (fn : LocalNameTable.Lookup cn picked.value fid)
    (fv : Resolved.LocalScope.Lookup ce fid (.sourceClosure source so sn se))
    (savedName : LocalNameTable.Lookup sn key.value savedId)
    (savedValue : Resolved.LocalScope.Lookup se savedId value)
    (missing : LocalNameTable.lookup? cn key.value = none) :
    E co cn ce st (either s guard picked) (.sourceClosure source so sn se) st ∧
    E so sn se st (ref s key) value st ∧
    Failed co cn ce st s (either s guard picked) (ref s key) body := by
  have selected : E co cn ce st (either s guard picked) (.sourceClosure source so sn se) st :=
    .orFalse (.reference gn gv) (.reference fn fv)
  have saved : E so sn se st (ref s key) value st := .reference savedName savedValue
  have absent : ∀ value final, ¬ E co cn ce st (ref s key) value final := by
    intro value final original
    cases original with
    | creation impossible => cases impossible
    | reference named _ =>
      have accepted := LocalNameTable.lookup?_iff.mpr named
      rw [missing] at accepted; cases accepted
  refine ⟨selected,saved,reject s st shape (.logicalOr .reference .reference) .reference bg selected ?_⟩
  intro value final original
  cases original with
  | creation impossible => cases impossible
  | call _ actualCallee actualArgument _ =>
    obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic selected
    cases sameCallee; cases sameStore
    exact absent _ _ actualArgument

end Tests.DataCalleeLambdaDepthBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendDirectDataLambdaDepthBoundaryProperties
/- Independent original rejection precedes finite-depth decisions. Inert type
annotations do not repair a missing argument or a wrong mixed guard payload. -/
set_option autoImplicit false
namespace Tests.DirectDataLambdaDepthBoundaries
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def bare (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,[⟨s,.returnStmt none⟩]⟩
private def unit (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.tuple ⟨s,[]⟩⟩
private def call (s : Syntax.SourceSpan) (source argument : Syntax.Expr) : Syntax.Expr :=
  ⟨s,.call source ⟨s,[argument]⟩⟩
private def Failed (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope RuntimeValue) (st : List RuntimeValue)
    (s : Syntax.SourceSpan) (source argument : Syntax.Expr) (body : Syntax.Block) : Prop :=
  evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body)
    o n e st (call s source argument) = none ∧
  (∀ budget, evaluateClosedSourceExpression? budget o n e st (call s source argument) = none) ∧
  ∀ value final, ¬ E o n e st (call s source argument) value final

variable (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (n : LocalNameTable)
  (e : Resolved.LocalScope RuntimeValue) (st : List RuntimeValue)
private theorem reject {source argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (argGate : ClosedSourceDataExpression argument) (bodyGate : ClosedSourceDataBody body)
    (original : ∀ value final, ¬ E o n e st (call s source argument) value final) :
    Failed o n e st s source argument body := by
  have absent := (directDataLambda_evaluate_depth_none_iff shape argGate bodyGate
    (Nat.le_refl _) (callSpan := s) (argumentsSpan := s)).mpr original
  exact ⟨absent,(directDataLambda_evaluate_depth_none_iff_all_budgets shape argGate bodyGate).mp absent,original⟩

theorem missing_argument_never_reaches_a_valid_body
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body) (gate : ClosedSourceDataBody body)
    (key : Syntax.Identifier)
    (missing : LocalNameTable.lookup? n key.value = none ∨
      ∃ id, LocalNameTable.Lookup n key.value id ∧ Resolved.LocalScope.lookup? e id = none) :
    E o n e st source (.sourceClosure source o n e) st ∧
    Failed o n e st s source (ref s key) body := by
  have absent : ∀ value final, ¬ E o n e st (ref s key) value final := by
    intro value final evaluated
    cases evaluated with
    | reference named found =>
      rcases missing with missing | ⟨id,correct,missing⟩
      · have accepted := LocalNameTable.lookup?_iff.mpr named
        rw [missing] at accepted; cases accepted
      · cases named.id_unique correct
        have accepted := Resolved.LocalScope.lookup?_iff.mpr found
        rw [missing] at accepted; cases accepted
    | creation impossible => cases impossible
  have creation : E o n e st source (.sourceClosure source o n e) st := .creation shape
  refine ⟨creation,reject s o n e st shape .reference gate ?_⟩
  intro value final evaluated
  cases evaluated with
  | creation impossible => cases impossible
  | call _ callee argument _ =>
    obtain ⟨sameCallee,sameStore⟩ := callee.deterministic creation
    cases sameCallee; cases sameStore
    exact absent _ _ argument

theorem selected_string_body_cannot_be_fixed_by_annotations
    {source : Syntax.Expr} {name : Syntax.Identifier} (text : String)
    (shape : SourceUnaryLambdaShape source name
      ⟨s,[⟨s,.returnStmt (some ⟨s,.literal ⟨s,.string text⟩⟩)⟩]⟩) :
    E o n e st source (.sourceClosure source o n e) st ∧ E o n e st (unit s) .unit st ∧
    Failed o n e st s source (unit s) ⟨s,[⟨s,.returnStmt (some ⟨s,.literal ⟨s,.string text⟩⟩)⟩]⟩ := by
  have creation : E o n e st source (.sourceClosure source o n e) st := .creation shape
  have argument : E o n e st (unit s) .unit st := .unit
  refine ⟨creation,argument,reject s o n e st shape .unit (.expression .literal) ?_⟩
  intro value final evaluated
  cases evaluated with
  | creation impossible => cases impossible
  | call actualShape callee _ returned =>
    obtain ⟨sameCallee,sameStore⟩ := callee.deterministic creation
    cases sameCallee; cases sameStore
    obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
      ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans (sourceUnaryLambdaShape?_iff.mpr shape)))
    cases sameName; cases sameBody
    cases returned with
    | expression child =>
      cases child with | wordLiteral meaning => cases meaning | creation impossible => cases impossible

theorem first_duplicate_argument_is_the_actual_fresh_guard
    {source : Syntax.Expr} {parameter : Syntax.Identifier}
    (shape : SourceUnaryLambdaShape source parameter
      ⟨s,[⟨s,.ifThen (ref s parameter) (bare s) (some (bare s))⟩]⟩)
    (first later : Resolved.LocalId) (bad : RuntimeValue) (notBool : ∀ b, bad ≠ .bool b) :
    let names := ("x",first)::("x",later)::n
    let captured := (first,bad)::(first,.bool true)::(later,.bool false)::e
    E o names captured st (ref s ⟨s,"x"⟩) bad st ∧
    Failed o names captured st s source (ref s ⟨s,"x"⟩)
      ⟨s,[⟨s,.ifThen (ref s parameter) (bare s) (some (bare s))⟩]⟩ := by
  intro names captured
  have creation : E o names captured st source (.sourceClosure source o names captured) st := .creation shape
  have argument : E o names captured st (ref s ⟨s,"x"⟩) bad st := .reference .head .head
  refine ⟨argument,reject s o names captured st shape .reference (.conditional .reference .bare .bare) ?_⟩
  intro value final evaluated
  cases evaluated with
  | creation impossible => cases impossible
  | call actualShape callee actualArg returned =>
    obtain ⟨sameCallee,sameStore⟩ := callee.deterministic creation
    cases sameCallee; cases sameStore
    obtain ⟨sameArgument,sameArgumentStore⟩ := actualArg.deterministic argument
    cases sameArgument; cases sameArgumentStore
    obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
      ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans (sourceUnaryLambdaShape?_iff.mpr shape)))
    cases sameName; cases sameBody
    have head : E o ((parameter.value,Resolved.freshLocalId o (names.map Prod.snd))::names)
        ((Resolved.freshLocalId o (names.map Prod.snd),bad)::captured) st (ref s parameter) bad st :=
      .reference .head .head
    cases returned with
    | ifTrue tested _ => exact notBool true (head.deterministic tested).1
    | ifFalse tested _ => exact notBool false (head.deterministic tested).1

end Tests.DirectDataLambdaDepthBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendDirectDataLambdaDepthSymbolicProperties
/- Original direct-call witnesses and exact runner recursions are independent
of the new depth laws. Annotations are syntax only; all mixed rows and stores
remain literal. Saved callees and general recursive calls are outside scope. -/
set_option autoImplicit false
namespace Tests.DirectDataLambdaDepthSymbolic
open Solcore Solcore.Frontend

private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def groups (s : Syntax.SourceSpan) : Nat → Syntax.Expr → Syntax.Expr
  | 0, child => child
  | n+1, child => ⟨s,.group (groups s n child)⟩
private def nestedStatement (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Nat → Syntax.Statement
  | 0 => ⟨s,.returnStmt (some (ref s name))⟩
  | n+1 => ⟨s,.block [nestedStatement s name n]⟩
private def nested (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) : Syntax.Block :=
  ⟨s,[nestedStatement s name n]⟩
private def lambda (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (parameterAnnotation annotation : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,match parameterAnnotation with
    | none => .inferred name | some t => .typed none name t⟩]⟩ annotation body⟩
private def call (s : Syntax.SourceSpan) (source argument : Syntax.Expr) : Syntax.Expr :=
  ⟨s,.call source ⟨s,[argument]⟩⟩
private theorem shape (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (parameterAnnotation annotation : Option Syntax.TypeExpr) (body : Syntax.Block) :
    SourceUnaryLambdaShape (lambda s name parameterAnnotation annotation body) name body := by
  cases parameterAnnotation with | none => exact .inferred | some t => exact .typed

private theorem groups_original {s n owner names captured store child value}
    (original : ClosedSourceExpressionEvaluates owner names captured store child value store) :
    ClosedSourceExpressionEvaluates owner names captured store (groups s n child) value store := by
  induction n with | zero => exact original | succ n ih => exact .group ih
private theorem nested_original {s name n owner names captured store id value}
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) :
    ClosedSourceBodyEvaluates owner names captured store (nested s name n) value store := by
  induction n with | zero => exact .expression (.reference named found) | succ n ih => exact .block ih

private theorem groups_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceExpression? budget owner names captured store (groups s n (ref s name)) =
      if n+1 ≤ budget then some (value,store) else none := by
  induction n generalizing budget with
  | zero =>
      cases budget <;> simp [groups,ref,evaluateClosedSourceExpression?,
        LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
  | succ n ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceExpression?]
      | succ budget =>
          have arithmetic : (n+1+1 ≤ budget+1) ↔ n+1 ≤ budget := by omega
          simpa only [groups,evaluateClosedSourceExpression?,arithmetic] using ih budget

private theorem nested_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceBody? budget owner names captured store (nested s name n) =
      if n+2 ≤ budget then some (value,store) else none := by
  induction n generalizing budget with
  | zero =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          have arithmetic : (0+2 ≤ budget+1) ↔ 1 ≤ budget := by omega
          simpa only [groups,nested,nestedStatement,evaluateClosedSourceBody?,arithmetic,Nat.zero_add] using
            groups_run s name 0 budget owner names captured store id value named found
  | succ n ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          have arithmetic : (n+1+2 ≤ budget+1) ↔ n+2 ≤ budget := by omega
          simpa only [nested,nestedStatement,evaluateClosedSourceBody?,arithmetic] using ih budget

private theorem creation_run (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (body : Syntax.Block) (budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) :
    evaluateClosedSourceExpression? (budget+1) owner names captured store (lambda s name pa annotation body) =
      some (.sourceClosure (lambda s name pa annotation body) owner names captured,store) := by
  cases pa <;> simp [lambda,evaluateClosedSourceExpression?,sourceUnaryLambdaShape?]

private theorem sharp_run (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (a b budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceExpression? budget owner names captured store
      (call s (lambda s name pa annotation (nested s name b)) (groups s a (ref s name))) =
      if max (a+1) (b+2)+1 ≤ budget then some (value,store) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ budget =>
      cases budget with
      | zero => simp [call,evaluateClosedSourceExpression?]
      | succ budget =>
          have created := creation_run s name pa annotation (nested s name b) budget owner names captured store
          have argument := groups_run s name a (budget+1) owner names captured store id value named found
          have returned := nested_run s name b (budget+1) owner
            ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
            ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) store
            (Resolved.freshLocalId owner (names.map Prod.snd)) value .head .head
          have arithmetic : (max (a+1) (b+2)+1 ≤ budget+1+1) ↔
              a+1 ≤ budget+1 ∧ b+2 ≤ budget+1 := by omega
          by_cases ha : a+1 ≤ budget+1 <;> by_cases hb : b+2 ≤ budget+1 <;>
            simp only [call,evaluateClosedSourceExpression?,created,argument,returned,
              sourceUnaryLambdaShape?_iff.mpr (shape s name pa annotation (nested s name b)),
              ha,hb,arithmetic,and_self,and_false,false_and,↓reduceIte,bind,Option.bind_some,Option.bind_none]

private theorem groups_gate {s n child} (gate : ClosedSourceDataExpression child) :
    ClosedSourceDataExpression (groups s n child) := by
  induction n with | zero => exact gate | succ n ih => exact .group ih
private theorem nested_gate (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) :
    ClosedSourceDataBody (nested s name n) := by
  induction n with | zero => exact .expression .reference | succ n ih => exact .block ih
private theorem groups_depth (s : Syntax.SourceSpan) (n : Nat) (child : Syntax.Expr) :
    closedSourceDataDepthBound (groups s n child) = closedSourceDataDepthBound child+n := by
  induction n with
  | zero => simp [groups]
  | succ n ih => simp only [groups,closedSourceDataDepthBound,ih,Nat.add_assoc]
private theorem nested_depth (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) :
    closedSourceDataBodyDepthBound (nested s name n) = n+2 := by
  induction n with
  | zero => simp [nested,nestedStatement,ref,closedSourceDataBodyDepthBound,closedSourceDataDepthBound]
  | succ n ih => simpa only [nested,nestedStatement,closedSourceDataBodyDepthBound,Nat.add_right_comm] using congrArg (·+1) ih

/-- Direct inferred or arbitrarily annotated typed parameters freshly shadow
the original name; exact depth is proved by runner recursion before new laws. -/
theorem arbitrary_direct_shadowing_has_sharp_depth
    (s : Syntax.SourceSpan) (name : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr)
    (a b extra : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    let body := nested s name b
    let argument := groups s a (ref s name)
    let source := lambda s name pa annotation body
    let application := call s source argument
    let depth := max (a+1) (b+2)+1
    SourceUnaryLambdaShape source name body ∧ ClosedSourceDataExpression argument ∧ ClosedSourceDataBody body ∧
    ClosedSourceExpressionEvaluates owner names captured store application value store ∧
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured store application =
      if depth ≤ budget then some (value,store) else none) ∧
    directDataLambdaDepthBound argument body = depth ∧
    evaluateClosedSourceExpression? (depth+extra) owner names captured store application = some (value,store) ∧
    evaluateClosedSourceExpression? (depth+extra) owner names captured store application =
      evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body) owner names captured store application ∧
    (∀ actual final, evaluateClosedSourceExpression? (depth+extra) owner names captured store application =
      some (actual,final) ↔ actual=value ∧ final=store) := by
  intro body argument source application depth
  have shaped := shape s name pa annotation body
  have original : ClosedSourceExpressionEvaluates owner names captured store application value store :=
    .call shaped (.creation shaped) (groups_original (.reference named found)) (nested_original .head .head)
  have ran := fun budget => sharp_run s name pa annotation a b budget owner names captured store id value named found
  have ag : ClosedSourceDataExpression argument := groups_gate .reference
  have bg : ClosedSourceDataBody body := nested_gate s name b
  have bound : directDataLambdaDepthBound argument body = depth := by
    simp only [argument,body,directDataLambdaDepthBound,groups_depth,nested_depth,ref,closedSourceDataDepthBound]
    dsimp only [depth]; omega
  have enough : directDataLambdaDepthBound argument body ≤ depth+extra := by omega
  refine ⟨shaped,ag,bg,original,ran,bound,
    directDataLambda_evaluates_at_depthBound shaped ag bg original enough,
    directDataLambda_evaluate_depth_stable shaped ag bg enough,?_⟩
  intro actual final
  dsimp only [application,call,source]
  rw [directDataLambda_evaluate_at_depthBound_iff shaped ag bg enough]
  exact ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩

private def skippedArgument (s : Syntax.SourceSpan) (guard name : Syntax.Identifier)
    (depth : Nat) : Syntax.Expr :=
  ⟨s,.conditional (ref s guard) s (ref s name) s
    (groups s depth ⟨s,.literal ⟨s,.string "bad"⟩⟩)⟩

/-- A known true identifier guard skips arbitrarily deep invalid Word syntax;
the conservative call bound does not replace the independently selected depth. -/
theorem direct_call_skips_deep_argument_with_literal_endpoints
    (s : Syntax.SourceSpan) (guard name : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr)
    (b k extra : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (guardId id : Resolved.LocalId) (value : RuntimeValue)
    (namedGuard : LocalNameTable.Lookup names guard.value guardId)
    (foundGuard : Resolved.LocalScope.Lookup captured guardId (.bool true))
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    let body := nested s name b
    let argument := skippedArgument s guard name (b+k+2)
    let source := lambda s name pa annotation body
    let application := call s source argument
    SourceUnaryLambdaShape source name body ∧ ClosedSourceDataExpression argument ∧ ClosedSourceDataBody body ∧
    ClosedSourceExpressionEvaluates owner names captured store application value store ∧
    directDataLambdaDepthBound argument body = b+k+5 ∧
    evaluateClosedSourceExpression? (b+3) owner names captured store application = some (value,store) ∧
    evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body-1)
      owner names captured store application = some (value,store) ∧
    evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body+extra)
      owner names captured store application = some (value,store) ∧
    evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body+extra)
      owner names captured store application = evaluateClosedSourceExpression?
        (directDataLambdaDepthBound argument body) owner names captured store application ∧
    (∀ actual final, evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body+extra)
      owner names captured store application = some (actual,final) ↔ actual=value ∧ final=store) ∧
    (evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body)
      owner names captured store application ≠ none) ∧
    ¬ (∀ budget, evaluateClosedSourceExpression? budget owner names captured store application = none) := by
  intro body argument source application
  have shaped := shape s name pa annotation body
  have argOriginal : ClosedSourceExpressionEvaluates owner names captured store argument value store :=
    .conditionalTrue (.reference namedGuard foundGuard) (.reference named found)
  have original : ClosedSourceExpressionEvaluates owner names captured store application value store :=
    .call shaped (.creation shaped) argOriginal (nested_original .head .head)
  have argRun : evaluateClosedSourceExpression? (b+2) owner names captured store argument = some (value,store) := by
    simp [argument,skippedArgument,ref,evaluateClosedSourceExpression?,
      LocalNameTable.lookup?_iff.mpr namedGuard,Resolved.LocalScope.lookup?_iff.mpr foundGuard,
      LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
  have bodyRun := nested_run s name b (b+2) owner
    ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
    ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) store
    (Resolved.freshLocalId owner (names.map Prod.snd)) value .head .head
  have early : evaluateClosedSourceExpression? (b+3) owner names captured store application = some (value,store) := by
    have created := creation_run s name pa annotation body (b+1) owner names captured store
    simpa only [application,call,source,evaluateClosedSourceExpression?,created,argRun,
      sourceUnaryLambdaShape?_iff.mpr shaped,bind,Option.bind_some,Nat.le_refl,↓reduceIte] using bodyRun
  have ag : ClosedSourceDataExpression argument := .conditional .reference .reference (groups_gate .literal)
  have bg : ClosedSourceDataBody body := nested_gate s name b
  have bound : directDataLambdaDepthBound argument body = b+k+5 := by
    simp only [argument,skippedArgument,body,directDataLambdaDepthBound,closedSourceDataDepthBound,
      ref,groups_depth,nested_depth]
    omega
  have enough : directDataLambdaDepthBound argument body ≤ directDataLambdaDepthBound argument body+extra := by omega
  have nonempty : evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body)
      owner names captured store application ≠ none := by
    intro absent
    exact ((directDataLambda_evaluate_depth_none_iff shaped ag bg (Nat.le_refl _)).mp absent) value store original
  have notAll : ¬ (∀ budget, evaluateClosedSourceExpression? budget owner names captured store application = none) := by
    intro absent
    exact nonempty ((directDataLambda_evaluate_depth_none_iff_all_budgets shaped ag bg).mpr absent)
  refine ⟨shaped,ag,bg,original,bound,early,evaluateClosedSourceExpression?_monotone (by omega) early,
    directDataLambda_evaluates_at_depthBound shaped ag bg original enough,
    directDataLambda_evaluate_depth_stable shaped ag bg enough,?_,nonempty,notAll⟩
  intro actual final
  dsimp only [application,call,source]
  rw [directDataLambda_evaluate_at_depthBound_iff shaped ag bg enough]
  exact ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩

end Tests.DirectDataLambdaDepthSymbolic
end

section
-- leanmerge: from Solcore.Test.FrontendBoundedCalleeChainSymbolicProperties
/- A finite chain returns the same full saved identity datum passed by caller x.
Original creation/calls and direct runner recursion precede bounded-callee laws.
Inner calls are explicitly outside the data-expression gate; no budget search,
runtime typing, Core cost or equality of caller/saved lexical rows is assumed. -/
set_option autoImplicit false
namespace Tests.BoundedCalleeChainSymbolic
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def body (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (ref s name))⟩]⟩
private def lambda (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,match pa with | none => .inferred name | some t => .typed none name t⟩]⟩ annotation (body s name)⟩
private def call (s : Syntax.SourceSpan) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨s,.call callee ⟨s,[argument]⟩⟩
private def chain (s : Syntax.SourceSpan) (f x : Syntax.Identifier) : Nat → Syntax.Expr
  | 0 => call s (ref s f) (ref s x) | n+1 => call s (chain s f x n) (ref s x)
private def callee (s : Syntax.SourceSpan) (f x : Syntax.Identifier) : Nat → Syntax.Expr
  | 0 => ref s f | n+1 => chain s f x n
private def calleeBudget : Nat → Nat | 0 => 1 | n+1 => n+3
private theorem shape (s : Syntax.SourceSpan) (name : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr) :
    SourceUnaryLambdaShape (lambda s name pa annotation) name (body s name) := by
  cases pa with | none => exact .inferred | some t => exact .typed
private theorem chain_original {s name f x n pa annotation co so cn sn cc sc store fid aid}
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name pa annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid)
    (af : Resolved.LocalScope.Lookup cc aid (.sourceClosure (lambda s name pa annotation) so sn sc)) :
    E co cn cc store (chain s f x n) (.sourceClosure (lambda s name pa annotation) so sn sc) store := by
  induction n with
  | zero => exact .call (shape s name pa annotation) (.reference fn ff) (.reference an af) (.expression (.reference .head .head))
  | succ n ih => exact .call (shape s name pa annotation) ih (.reference an af) (.expression (.reference .head .head))
private theorem reference_run {s name owner names captured store id value}
    (budget : Nat) (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceExpression? budget owner names captured store (ref s name) =
      if 1 ≤ budget then some (value,store) else none := by
  cases budget <;> simp [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
private theorem body_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (value : RuntimeValue) :
    evaluateClosedSourceBody? budget owner ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) store (body s name) =
      if 2 ≤ budget then some (value,store) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceBody?]
  | succ budget => cases budget <;> simp [body,ref,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,
      LocalNameTable.lookup?_iff.mpr (.head : LocalNameTable.Lookup ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names) name.value _),
      Resolved.LocalScope.lookup?_iff.mpr (.head : Resolved.LocalScope.Lookup ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) _ value)]
private theorem chain_run (s : Syntax.SourceSpan) (name f x : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr)
    (n budget : Nat) (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (fid aid : Resolved.LocalId)
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name pa annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid)
    (af : Resolved.LocalScope.Lookup cc aid (.sourceClosure (lambda s name pa annotation) so sn sc)) :
    evaluateClosedSourceExpression? budget co cn cc store (chain s f x n) =
      if n+3 ≤ budget then some (.sourceClosure (lambda s name pa annotation) so sn sc,store) else none := by
  induction n generalizing budget with
  | zero =>
    cases budget with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ budget =>
      cases budget with
      | zero => simp [chain,call,evaluateClosedSourceExpression?]
      | succ budget =>
        have picked := reference_run (s:=s) (owner:=co) (store:=store) (budget+1) fn ff
        have argument := reference_run (s:=s) (owner:=co) (store:=store) (budget+1) an af
        have returned := body_run s name (budget+1) so sn sc store (.sourceClosure (lambda s name pa annotation) so sn sc)
        have arithmetic : (0+3 ≤ budget+1+1) ↔ 2 ≤ budget+1 := by omega
        simpa only [chain,call,evaluateClosedSourceExpression?,picked,argument,show 1 ≤ budget+1 by omega,↓reduceIte,
          sourceUnaryLambdaShape?_iff.mpr (shape s name pa annotation),arithmetic,bind,Option.bind_some] using returned
  | succ n ih =>
    cases budget with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ budget =>
      have arithmetic : (n+1+3 ≤ budget+1) ↔ n+3 ≤ budget := by omega
      by_cases enough : n+3 ≤ budget
      · have argument := reference_run (s:=s) (owner:=co) (store:=store) budget an af
        have returned := body_run s name budget so sn sc store (.sourceClosure (lambda s name pa annotation) so sn sc)
        simp only [chain,call,evaluateClosedSourceExpression?,ih budget,enough,↓reduceIte,argument,
          show 1 ≤ budget by omega,sourceUnaryLambdaShape?_iff.mpr (shape s name pa annotation),returned,
          show 2 ≤ budget by omega,arithmetic,bind,Option.bind_some]
      · simp only [chain,call,evaluateClosedSourceExpression?,ih budget,enough,arithmetic,↓reduceIte,bind,Option.bind_none]
private theorem chain_not_data (s : Syntax.SourceSpan) (f x : Syntax.Identifier) (n : Nat) :
    ¬ ClosedSourceDataExpression (chain s f x n) := by
  cases n <;> intro impossible <;> cases impossible
private def Consequences (s : Syntax.SourceSpan) (budget : Nat) (owner : Resolved.DeclarationId)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (selected argument : Syntax.Expr) (savedBody : Syntax.Block) (value : RuntimeValue) : Prop :=
  let H := boundedCalleeLambdaDepthBound budget argument savedBody
  (∀ extra, evaluateClosedSourceExpression? (H+extra) owner names captured store (call s selected argument) = some (value,store) ∧
    evaluateClosedSourceExpression? (H+extra) owner names captured store (call s selected argument) =
      evaluateClosedSourceExpression? H owner names captured store (call s selected argument) ∧
    ∀ actual final, evaluateClosedSourceExpression? (H+extra) owner names captured store (call s selected argument) =
      some (actual,final) ↔ actual=value ∧ final=store) ∧
  evaluateClosedSourceExpression? H owner names captured store (call s selected argument) ≠ none ∧
  ¬ (∀ fuel, evaluateClosedSourceExpression? fuel owner names captured store (call s selected argument) = none)
private theorem finish {s source selected argument name savedBody owner savedOwner names savedNames captured savedCaptured store value budget}
    (shaped : SourceUnaryLambdaShape source name savedBody) (ag : ClosedSourceDataExpression argument) (bg : ClosedSourceDataBody savedBody)
    (finite : evaluateClosedSourceExpression? budget owner names captured store selected = some (.sourceClosure source savedOwner savedNames savedCaptured,store))
    (original : E owner names captured store (call s selected argument) value store) :
    Consequences s budget owner names captured store selected argument savedBody value := by
  have nonempty : evaluateClosedSourceExpression? (boundedCalleeLambdaDepthBound budget argument savedBody)
      owner names captured store (call s selected argument) ≠ none := by
    intro absent
    exact ((boundedCalleeLambda_evaluate_depth_none_iff shaped ag bg finite (Nat.le_refl _)).mp absent) _ _ original
  refine ⟨?_,nonempty,?_⟩
  · intro extra
    have enough := Nat.le_add_right (boundedCalleeLambdaDepthBound budget argument savedBody) extra
    refine ⟨boundedCalleeLambda_evaluates_at_depthBound shaped ag bg finite original enough,
      boundedCalleeLambda_evaluate_depth_stable shaped ag bg finite enough,?_⟩
    intro actual final
    have raw : evaluateClosedSourceExpression? (_+extra) owner names captured store (call s selected argument) = some (actual,final) ↔
        E owner names captured store (call s selected argument) actual final :=
      boundedCalleeLambda_evaluate_at_depthBound_iff shaped ag bg finite enough
    exact raw.trans ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩
  · intro absent
    exact nonempty ((boundedCalleeLambda_evaluate_depth_none_iff_all_budgets shaped ag bg finite).mpr absent)

/-- Every finite higher-order identity chain has sharp depth n+3, including full
saved rows and stores. Each outer call composes its independently successful predecessor. -/
theorem saved_identity_chain_has_sharp_depth
    (s : Syntax.SourceSpan) (name f x : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr) (n : Nat)
    (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (creationStore invocationStore : List RuntimeValue) (fid aid : Resolved.LocalId)
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name pa annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid)
    (af : Resolved.LocalScope.Lookup cc aid (.sourceClosure (lambda s name pa annotation) so sn sc)) :
    let source := lambda s name pa annotation
    let saved := RuntimeValue.sourceClosure source so sn sc
    E so sn sc creationStore source saved creationStore ∧
    E co cn cc invocationStore (chain s f x n) saved invocationStore ∧
    (∀ budget, evaluateClosedSourceExpression? budget co cn cc invocationStore (chain s f x n) =
      if n+3 ≤ budget then some (saved,invocationStore) else none) ∧
    ¬ ClosedSourceDataExpression (chain s f x n) ∧
    evaluateClosedSourceExpression? (calleeBudget n) co cn cc invocationStore (callee s f x n) = some (saved,invocationStore) ∧
    boundedCalleeLambdaDepthBound (calleeBudget n) (ref s x) (body s name) = n+3 ∧
    Consequences s (calleeBudget n) co cn cc invocationStore (callee s f x n) (ref s x) (body s name) saved := by
  intro source saved
  have shaped := shape s name pa annotation
  have creation : E so sn sc creationStore source saved creationStore := .creation shaped
  have original : E co cn cc invocationStore (chain s f x n) saved invocationStore := chain_original fn ff an af
  have ran := fun budget => chain_run s name f x pa annotation n budget co so cn sn cc sc invocationStore fid aid fn ff an af
  have finite : evaluateClosedSourceExpression? (calleeBudget n) co cn cc invocationStore (callee s f x n) = some (saved,invocationStore) := by
    cases n with
    | zero => simpa [callee,calleeBudget] using reference_run (s:=s) (owner:=co) (store:=invocationStore) 1 fn ff
    | succ n => simpa only [callee,calleeBudget,Nat.le_refl,↓reduceIte] using
        chain_run s name f x pa annotation n (n+3) co so cn sn cc sc invocationStore fid aid fn ff an af
  have bound : boundedCalleeLambdaDepthBound (calleeBudget n) (ref s x) (body s name) = n+3 := by
    cases n <;> simp [calleeBudget,boundedCalleeLambdaDepthBound,ref,body,closedSourceDataDepthBound,closedSourceDataBodyDepthBound] <;> omega
  have whole : E co cn cc invocationStore (call s (callee s f x n) (ref s x)) saved invocationStore := by
    cases n <;> exact original
  exact ⟨creation,original,ran,chain_not_data s f x n,finite,bound,finish shaped .reference (.expression .reference) finite whole⟩

/-- Supplying a larger already successful callee budget gives a conservative,
nonminimal outer bound; no budget search or data admission for the inner call is used. -/
theorem successful_callee_budget_need_not_be_minimal
    (s : Syntax.SourceSpan) (name f x : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr) (n k : Nat)
    (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (creationStore invocationStore : List RuntimeValue) (fid aid : Resolved.LocalId)
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name pa annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid)
    (af : Resolved.LocalScope.Lookup cc aid (.sourceClosure (lambda s name pa annotation) so sn sc)) :
    let source := lambda s name pa annotation
    let saved := RuntimeValue.sourceClosure source so sn sc
    E so sn sc creationStore source saved creationStore ∧
    E co cn cc invocationStore (chain s f x n) saved invocationStore ∧
    E co cn cc invocationStore (chain s f x (n+1)) saved invocationStore ∧
    ¬ ClosedSourceDataExpression (chain s f x n) ∧
    evaluateClosedSourceExpression? (n+k+4) co cn cc invocationStore (chain s f x n) = some (saved,invocationStore) ∧
    boundedCalleeLambdaDepthBound (n+k+4) (ref s x) (body s name) = n+k+5 ∧
    evaluateClosedSourceExpression? (n+4) co cn cc invocationStore (chain s f x (n+1)) = some (saved,invocationStore) ∧
    evaluateClosedSourceExpression? (n+k+4) co cn cc invocationStore (chain s f x (n+1)) = some (saved,invocationStore) ∧
    Consequences s (n+k+4) co cn cc invocationStore (chain s f x n) (ref s x) (body s name) saved := by
  intro source saved
  have shaped := shape s name pa annotation
  have creation : E so sn sc creationStore source saved creationStore := .creation shaped
  have selected : E co cn cc invocationStore (chain s f x n) saved invocationStore := chain_original fn ff an af
  have original : E co cn cc invocationStore (chain s f x (n+1)) saved invocationStore :=
    .call shaped selected (.reference an af) (.expression (.reference .head .head))
  have finite : evaluateClosedSourceExpression? (n+k+4) co cn cc invocationStore (chain s f x n) = some (saved,invocationStore) := by
    simpa only [show n+3 ≤ n+k+4 by omega,↓reduceIte] using
      chain_run s name f x pa annotation n (n+k+4) co so cn sn cc sc invocationStore fid aid fn ff an af
  have early : evaluateClosedSourceExpression? (n+4) co cn cc invocationStore (chain s f x (n+1)) = some (saved,invocationStore) := by
    simpa only [show n+1+3 ≤ n+4 by omega,↓reduceIte] using
      chain_run s name f x pa annotation (n+1) (n+4) co so cn sn cc sc invocationStore fid aid fn ff an af
  have bound : boundedCalleeLambdaDepthBound (n+k+4) (ref s x) (body s name) = n+k+5 := by
    simp [boundedCalleeLambdaDepthBound,ref,body,closedSourceDataDepthBound,closedSourceDataBodyDepthBound]
  exact ⟨creation,selected,original,chain_not_data s f x n,finite,bound,early,
    evaluateClosedSourceExpression?_monotone (by omega) early,finish shaped .reference (.expression .reference) finite original⟩
end Tests.BoundedCalleeChainSymbolic
end

section
-- leanmerge: from Solcore.Test.FrontendDataCalleeLambdaDepthSymbolicProperties
/- Independent original selection is built before every new depth law. Caller
argument rows, saved fresh-body rows, creation store and invocation store remain
distinct. Exact runner recursion counts group/body depth, not Core transitions. -/
set_option autoImplicit false
namespace Tests.DataCalleeLambdaDepthSymbolic
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def groups (s : Syntax.SourceSpan) : Nat → Syntax.Expr → Syntax.Expr
  | 0, child => child | n+1, child => ⟨s,.group (groups s n child)⟩
private def nestedStatement (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Nat → Syntax.Statement
  | 0 => ⟨s,.returnStmt (some (ref s name))⟩ | n+1 => ⟨s,.block [nestedStatement s name n]⟩
private def nested (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) : Syntax.Block :=
  ⟨s,[nestedStatement s name n]⟩
private def lambda (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,match pa with | none => .inferred name | some t => .typed none name t⟩]⟩ annotation body⟩
private def call (s : Syntax.SourceSpan) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨s,.call callee ⟨s,[argument]⟩⟩
private theorem shape (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (body : Syntax.Block) :
    SourceUnaryLambdaShape (lambda s name pa annotation body) name body := by
  cases pa with | none => exact .inferred | some t => exact .typed
private theorem groups_original {s n owner names captured store child value}
    (original : E owner names captured store child value store) : E owner names captured store (groups s n child) value store := by
  induction n with | zero => exact original | succ n ih => exact .group ih
private theorem nested_original {s name n owner names captured store id value}
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    ClosedSourceBodyEvaluates owner names captured store (nested s name n) value store := by
  induction n with | zero => exact .expression (.reference named found) | succ n ih => exact .block ih
private theorem groups_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceExpression? budget owner names captured store (groups s n (ref s name)) =
      if n+1 ≤ budget then some (value,store) else none := by
  induction n generalizing budget with
  | zero => cases budget <;> simp [groups,ref,evaluateClosedSourceExpression?,
      LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
  | succ n ih =>
    cases budget with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ budget =>
      have arithmetic : (n+1+1 ≤ budget+1) ↔ n+1 ≤ budget := by omega
      simpa only [groups,evaluateClosedSourceExpression?,arithmetic] using ih budget
private theorem nested_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceBody? budget owner names captured store (nested s name n) =
      if n+2 ≤ budget then some (value,store) else none := by
  induction n generalizing budget with
  | zero =>
    cases budget with
    | zero => simp [evaluateClosedSourceBody?]
    | succ budget =>
      have arithmetic : (0+2 ≤ budget+1) ↔ 1 ≤ budget := by omega
      simpa only [groups,nested,nestedStatement,evaluateClosedSourceBody?,arithmetic,Nat.zero_add] using
        groups_run s name 0 budget owner names captured store id value named found
  | succ n ih =>
    cases budget with
    | zero => simp [evaluateClosedSourceBody?]
    | succ budget =>
      have arithmetic : (n+1+2 ≤ budget+1) ↔ n+2 ≤ budget := by omega
      simpa only [nested,nestedStatement,evaluateClosedSourceBody?,arithmetic] using ih budget
private theorem groups_gate {s n child} (gate : ClosedSourceDataExpression child) : ClosedSourceDataExpression (groups s n child) := by
  induction n with | zero => exact gate | succ n ih => exact .group ih
private theorem nested_gate (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) : ClosedSourceDataBody (nested s name n) := by
  induction n with | zero => exact .expression .reference | succ n ih => exact .block ih
private theorem groups_depth (s : Syntax.SourceSpan) (n : Nat) (child : Syntax.Expr) :
    closedSourceDataDepthBound (groups s n child) = closedSourceDataDepthBound child+n := by
  induction n with | zero => simp [groups] | succ n ih => simp only [groups,closedSourceDataDepthBound,ih,Nat.add_assoc]
private theorem nested_depth (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) : closedSourceDataBodyDepthBound (nested s name n) = n+2 := by
  induction n with
  | zero => simp [nested,nestedStatement,ref,closedSourceDataBodyDepthBound,closedSourceDataDepthBound]
  | succ n ih => simpa only [nested,nestedStatement,closedSourceDataBodyDepthBound,Nat.add_right_comm] using congrArg (·+1) ih
private def Consequences (s : Syntax.SourceSpan) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (callee argument : Syntax.Expr)
    (body : Syntax.Block) (value : RuntimeValue) : Prop :=
  let H := dataCalleeLambdaDepthBound callee argument body
  (∀ extra, evaluateClosedSourceExpression? (H+extra) owner names captured store (call s callee argument) = some (value,store) ∧
    evaluateClosedSourceExpression? (H+extra) owner names captured store (call s callee argument) =
      evaluateClosedSourceExpression? H owner names captured store (call s callee argument) ∧
    ∀ actual final, evaluateClosedSourceExpression? (H+extra) owner names captured store (call s callee argument) =
      some (actual,final) ↔ actual=value ∧ final=store) ∧
  evaluateClosedSourceExpression? H owner names captured store (call s callee argument) ≠ none ∧
  ¬ (∀ budget, evaluateClosedSourceExpression? budget owner names captured store (call s callee argument) = none)
private theorem finish {s source callee argument name body owner savedOwner names savedNames captured savedCaptured store value}
    (shaped : SourceUnaryLambdaShape source name body) (cg : ClosedSourceDataExpression callee)
    (ag : ClosedSourceDataExpression argument) (bg : ClosedSourceDataBody body)
    (selected : E owner names captured store callee (.sourceClosure source savedOwner savedNames savedCaptured) store)
    (original : E owner names captured store (call s callee argument) value store) :
    Consequences s owner names captured store callee argument body value := by
  have nonempty : evaluateClosedSourceExpression? (dataCalleeLambdaDepthBound callee argument body)
      owner names captured store (call s callee argument) ≠ none := by
    intro absent
    exact ((dataCalleeLambda_evaluate_depth_none_iff shaped cg ag bg selected (Nat.le_refl _)).mp absent) _ _ original
  refine ⟨?_,nonempty,?_⟩
  · intro extra
    have enough := Nat.le_add_right (dataCalleeLambdaDepthBound callee argument body) extra
    refine ⟨dataCalleeLambda_evaluates_at_depthBound shaped cg ag bg selected original enough,
      dataCalleeLambda_evaluate_depth_stable shaped cg ag bg selected enough,?_⟩
    intro actual final
    have raw : evaluateClosedSourceExpression? (_+extra) owner names captured store (call s callee argument) = some (actual,final) ↔
        E owner names captured store (call s callee argument) actual final :=
      dataCalleeLambda_evaluate_at_depthBound_iff shaped cg ag bg selected enough
    exact raw.trans ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩
  · intro absent
    exact nonempty ((dataCalleeLambda_evaluate_depth_none_iff_all_budgets shaped cg ag bg selected).mpr absent)
private theorem sharp_run (s : Syntax.SourceSpan) (parameter callee argument : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (c b budget : Nat)
    (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (fid aid : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup cn callee.value fid)
    (found : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s parameter pa annotation (nested s parameter b)) so sn sc))
    (an : LocalNameTable.Lookup cn argument.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    evaluateClosedSourceExpression? budget co cn cc store (call s (groups s c (ref s callee)) (ref s argument)) =
      if max (c+1) (b+2)+1 ≤ budget then some (value,store) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ budget =>
    cases budget with
    | zero => simp [call,evaluateClosedSourceExpression?]
    | succ budget =>
      have picked := groups_run s callee c (budget+1) co cn cc store _ _ named found
      have actualArg : evaluateClosedSourceExpression? (budget+1) co cn cc store (ref s argument) = some (value,store) := by
        simpa only [groups,Nat.zero_add,show 1 ≤ budget+1 by omega,↓reduceIte] using
          groups_run s argument 0 (budget+1) co cn cc store _ _ an af
      have returned := nested_run s parameter b (budget+1) so
        ((parameter.value,Resolved.freshLocalId so (sn.map Prod.snd))::sn)
        ((Resolved.freshLocalId so (sn.map Prod.snd),value)::sc) store (Resolved.freshLocalId so (sn.map Prod.snd)) value .head .head
      have arithmetic : (max (c+1) (b+2)+1 ≤ budget+1+1) ↔ c+1 ≤ budget+1 ∧ b+2 ≤ budget+1 := by omega
      by_cases hc : c+1 ≤ budget+1 <;> by_cases hb : b+2 ≤ budget+1 <;>
        simp only [call,evaluateClosedSourceExpression?,picked,actualArg,returned,
          sourceUnaryLambdaShape?_iff.mpr (shape s parameter pa annotation (nested s parameter b)),
          hc,hb,arithmetic,and_self,and_false,false_and,↓reduceIte,bind,Option.bind_some,Option.bind_none]

/-- Arbitrary grouped selected callee and saved body have independent sharp depths.
Creation captures saved rows; argument reads caller rows; fresh return reads saved rows. -/
theorem grouped_saved_callee_and_body_have_sharp_depth
    (s : Syntax.SourceSpan) (parameter calleeName argumentName : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (c b : Nat)
    (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (creationStore invocationStore : List RuntimeValue) (fid aid : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup cn calleeName.value fid)
    (found : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s parameter pa annotation (nested s parameter b)) so sn sc))
    (an : LocalNameTable.Lookup cn argumentName.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    let body := nested s parameter b
    let source := lambda s parameter pa annotation body
    let callee := groups s c (ref s calleeName)
    let argument := ref s argumentName
    E so sn sc creationStore source (.sourceClosure source so sn sc) creationStore ∧
    E co cn cc invocationStore callee (.sourceClosure source so sn sc) invocationStore ∧
    E co cn cc invocationStore (call s callee argument) value invocationStore ∧
    (∀ budget, evaluateClosedSourceExpression? budget co cn cc invocationStore (call s callee argument) =
      if max (c+1) (b+2)+1 ≤ budget then some (value,invocationStore) else none) ∧
    dataCalleeLambdaDepthBound callee argument body = max (c+1) (b+2)+1 ∧
    Consequences s co cn cc invocationStore callee argument body value := by
  intro body source callee argument
  have shaped := shape s parameter pa annotation body
  have creation : E so sn sc creationStore source (.sourceClosure source so sn sc) creationStore := .creation shaped
  have selected : E co cn cc invocationStore callee (.sourceClosure source so sn sc) invocationStore :=
    groups_original (.reference named found)
  have original : E co cn cc invocationStore (call s callee argument) value invocationStore :=
    .call shaped selected (.reference an af) (nested_original .head .head)
  have ran := fun budget => sharp_run s parameter calleeName argumentName pa annotation c b budget
    co so cn sn cc sc invocationStore fid aid value named found an af
  have bound : dataCalleeLambdaDepthBound callee argument body = max (c+1) (b+2)+1 := by
    simp only [callee,argument,body,dataCalleeLambdaDepthBound,groups_depth,nested_depth,ref,closedSourceDataDepthBound]; omega
  exact ⟨creation,selected,original,ran,bound,finish shaped (groups_gate .reference) .reference (nested_gate s parameter b) selected original⟩

private def skipped (s : Syntax.SourceSpan) (guard callee : Syntax.Identifier) (n : Nat) : Syntax.Expr :=
  ⟨s,.conditional (ref s guard) s (ref s callee) s (groups s n ⟨s,.literal ⟨s,.string "bad"⟩⟩)⟩
/-- A true conditional selects the entire actual saved closure without evaluating
the deeply grouped string alternative. The conservative bound is not minimal. -/
theorem conditional_selected_closure_skips_deep_bad_candidate
    (s : Syntax.SourceSpan) (parameter guard calleeName argumentName : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (b k : Nat)
    (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (creationStore invocationStore : List RuntimeValue) (gid fid aid : Resolved.LocalId) (value : RuntimeValue)
    (gn : LocalNameTable.Lookup cn guard.value gid) (gf : Resolved.LocalScope.Lookup cc gid (.bool true))
    (named : LocalNameTable.Lookup cn calleeName.value fid)
    (found : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s parameter pa annotation (nested s parameter b)) so sn sc))
    (an : LocalNameTable.Lookup cn argumentName.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    let body := nested s parameter b
    let source := lambda s parameter pa annotation body
    let callee := skipped s guard calleeName (b+k+2)
    let argument := ref s argumentName
    E so sn sc creationStore source (.sourceClosure source so sn sc) creationStore ∧
    E co cn cc invocationStore callee (.sourceClosure source so sn sc) invocationStore ∧
    E co cn cc invocationStore (call s callee argument) value invocationStore ∧
    dataCalleeLambdaDepthBound callee argument body = b+k+5 ∧
    evaluateClosedSourceExpression? (b+3) co cn cc invocationStore (call s callee argument) = some (value,invocationStore) ∧
    evaluateClosedSourceExpression? (dataCalleeLambdaDepthBound callee argument body-1)
      co cn cc invocationStore (call s callee argument) = some (value,invocationStore) ∧
    Consequences s co cn cc invocationStore callee argument body value := by
  intro body source callee argument
  have shaped := shape s parameter pa annotation body
  have creation : E so sn sc creationStore source (.sourceClosure source so sn sc) creationStore := .creation shaped
  have selected : E co cn cc invocationStore callee (.sourceClosure source so sn sc) invocationStore :=
    .conditionalTrue (.reference gn gf) (.reference named found)
  have original : E co cn cc invocationStore (call s callee argument) value invocationStore :=
    .call shaped selected (.reference an af) (nested_original .head .head)
  have calleeRun : evaluateClosedSourceExpression? (b+2) co cn cc invocationStore callee =
      some (.sourceClosure source so sn sc,invocationStore) := by
    simp [callee,skipped,ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr gn,
      Resolved.LocalScope.lookup?_iff.mpr gf,LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found,source,body]
  have argRun : evaluateClosedSourceExpression? (b+2) co cn cc invocationStore argument = some (value,invocationStore) := by
    simpa only [groups,Nat.zero_add,show 1 ≤ b+2 by omega,↓reduceIte,argument] using
      groups_run s argumentName 0 (b+2) co cn cc invocationStore aid value an af
  have bodyRun := nested_run s parameter b (b+2) so
    ((parameter.value,Resolved.freshLocalId so (sn.map Prod.snd))::sn)
    ((Resolved.freshLocalId so (sn.map Prod.snd),value)::sc) invocationStore (Resolved.freshLocalId so (sn.map Prod.snd)) value .head .head
  have early : evaluateClosedSourceExpression? (b+3) co cn cc invocationStore (call s callee argument) = some (value,invocationStore) := by
    simpa only [call,evaluateClosedSourceExpression?,calleeRun,argRun,source,
      sourceUnaryLambdaShape?_iff.mpr shaped,bind,Option.bind_some,Nat.le_refl,↓reduceIte,
      Nat.zero_add,show 1 ≤ b+2 by omega] using bodyRun
  have bound : dataCalleeLambdaDepthBound callee argument body = b+k+5 := by
    simp only [callee,skipped,argument,body,dataCalleeLambdaDepthBound,closedSourceDataDepthBound,ref,groups_depth,nested_depth]; omega
  exact ⟨creation,selected,original,bound,early,evaluateClosedSourceExpression?_monotone (by omega) early,
    finish shaped (.conditional .reference .reference (groups_gate .literal)) .reference (nested_gate s parameter b) selected original⟩
end Tests.DataCalleeLambdaDepthSymbolic
end

section
-- leanmerge: from Solcore.Test.FrontendNestedArgumentChainSymbolicProperties
/- Independent original identity calls and direct runner recursion precede the
two supplied-input laws. Nested arguments are call syntax outside the data gate.
Caller argument values are arbitrary mixed runtime data; all saved fields and
creation versus invocation stores remain separate, without typing or cost claims. -/
set_option autoImplicit false
namespace Tests.NestedArgumentChainSymbolic
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def body (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Block := ⟨s,[⟨s,.returnStmt (some (ref s name))⟩]⟩
private def lambda (s : Syntax.SourceSpan) (name : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,match pa with | none => .inferred name | some t => .typed none name t⟩]⟩ annotation (body s name)⟩
private def call (s : Syntax.SourceSpan) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨s,.call callee ⟨s,[argument]⟩⟩
private def chain (s : Syntax.SourceSpan) (f x : Syntax.Identifier) : Nat → Syntax.Expr
  | 0 => call s (ref s f) (ref s x) | n+1 => call s (ref s f) (chain s f x n)
private def argument (s : Syntax.SourceSpan) (f x : Syntax.Identifier) : Nat → Syntax.Expr
  | 0 => ref s x | n+1 => chain s f x n
private def argumentBudget : Nat → Nat | 0 => 1 | n+1 => n+3
private theorem shape (s : Syntax.SourceSpan) (name : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr) :
    SourceUnaryLambdaShape (lambda s name pa annotation) name (body s name) := by
  cases pa with | none => exact .inferred | some t => exact .typed
private theorem chain_original {s name f x n pa annotation co so cn sn cc sc store fid aid value}
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name pa annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    E co cn cc store (chain s f x n) value store := by
  induction n with
  | zero => exact .call (shape s name pa annotation) (.reference fn ff) (.reference an af) (.expression (.reference .head .head))
  | succ n ih => exact .call (shape s name pa annotation) (.reference fn ff) ih (.expression (.reference .head .head))
private theorem reference_run {s name owner names captured store id value}
    (budget : Nat) (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceExpression? budget owner names captured store (ref s name) =
      if 1 ≤ budget then some (value,store) else none := by
  cases budget <;> simp [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
private theorem body_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (value : RuntimeValue) :
    evaluateClosedSourceBody? budget owner ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) store (body s name) =
      if 2 ≤ budget then some (value,store) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceBody?]
  | succ budget => cases budget <;> simp [body,ref,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,
      LocalNameTable.lookup?_iff.mpr (.head : LocalNameTable.Lookup ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names) name.value _),
      Resolved.LocalScope.lookup?_iff.mpr (.head : Resolved.LocalScope.Lookup ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) _ value)]
private theorem chain_run (s : Syntax.SourceSpan) (name f x : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr)
    (n budget : Nat) (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (fid aid : Resolved.LocalId) (value : RuntimeValue)
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name pa annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    evaluateClosedSourceExpression? budget co cn cc store (chain s f x n) =
      if n+3 ≤ budget then some (value,store) else none := by
  induction n generalizing budget with
  | zero =>
    cases budget with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ budget =>
      cases budget with
      | zero => simp [chain,call,evaluateClosedSourceExpression?]
      | succ budget =>
        have picked := reference_run (s:=s) (owner:=co) (store:=store) (budget+1) fn ff
        have supplied := reference_run (s:=s) (owner:=co) (store:=store) (budget+1) an af
        have returned := body_run s name (budget+1) so sn sc store value
        have arithmetic : (0+3 ≤ budget+1+1) ↔ 2 ≤ budget+1 := by omega
        simpa only [chain,call,evaluateClosedSourceExpression?,picked,supplied,show 1 ≤ budget+1 by omega,↓reduceIte,
          sourceUnaryLambdaShape?_iff.mpr (shape s name pa annotation),arithmetic,bind,Option.bind_some] using returned
  | succ n ih =>
    cases budget with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ budget =>
      cases budget with
      | zero => simp [chain,call,evaluateClosedSourceExpression?]
      | succ budget =>
        have picked := reference_run (s:=s) (owner:=co) (store:=store) (budget+1) fn ff
        have arithmetic : (n+1+3 ≤ budget+1+1) ↔ n+3 ≤ budget+1 := by omega
        by_cases enough : n+3 ≤ budget+1
        · have returned := body_run s name (budget+1) so sn sc store value
          simp only [chain,call,evaluateClosedSourceExpression?,picked,show 1 ≤ budget+1 by omega,↓reduceIte,
            ih (budget+1),enough,sourceUnaryLambdaShape?_iff.mpr (shape s name pa annotation),returned,
            show 2 ≤ budget+1 by omega,arithmetic,bind,Option.bind_some]
        · simp only [chain,call,evaluateClosedSourceExpression?,picked,show 1 ≤ budget+1 by omega,↓reduceIte,
            ih (budget+1),enough,arithmetic,bind,Option.bind_some,Option.bind_none]
private theorem chain_not_data (s : Syntax.SourceSpan) (f x : Syntax.Identifier) (n : Nat) :
    ¬ ClosedSourceDataExpression (chain s f x n) := by
  cases n <;> intro impossible <;> cases impossible
private def Consequences (s : Syntax.SourceSpan) (C A : Nat) (owner : Resolved.DeclarationId)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (callee supplied : Syntax.Expr) (savedBody : Syntax.Block) (value : RuntimeValue) : Prop :=
  let H := boundedInputsLambdaDepthBound C A savedBody
  (∀ extra, evaluateClosedSourceExpression? (H+extra) owner names captured store (call s callee supplied) = some (value,store) ∧
    evaluateClosedSourceExpression? (H+extra) owner names captured store (call s callee supplied) =
      evaluateClosedSourceExpression? H owner names captured store (call s callee supplied) ∧
    ∀ actual final, evaluateClosedSourceExpression? (H+extra) owner names captured store (call s callee supplied) =
      some (actual,final) ↔ actual=value ∧ final=store) ∧
  evaluateClosedSourceExpression? H owner names captured store (call s callee supplied) ≠ none ∧
  ¬ (∀ budget, evaluateClosedSourceExpression? budget owner names captured store (call s callee supplied) = none)
private theorem finish {s source callee supplied name savedBody owner savedOwner names savedNames captured savedCaptured store value C A}
    (shaped : SourceUnaryLambdaShape source name savedBody) (bg : ClosedSourceDataBody savedBody)
    (finiteCallee : evaluateClosedSourceExpression? C owner names captured store callee = some (.sourceClosure source savedOwner savedNames savedCaptured,store))
    (finiteArgument : evaluateClosedSourceExpression? A owner names captured store supplied = some (value,store))
    (original : E owner names captured store (call s callee supplied) value store) :
    Consequences s C A owner names captured store callee supplied savedBody value := by
  have nonempty : evaluateClosedSourceExpression? (boundedInputsLambdaDepthBound C A savedBody)
      owner names captured store (call s callee supplied) ≠ none := by
    intro absent
    exact ((boundedInputsLambda_evaluate_depth_none_iff shaped bg finiteCallee finiteArgument (Nat.le_refl _)).mp absent) _ _ original
  refine ⟨?_,nonempty,?_⟩
  · intro extra
    have enough := Nat.le_add_right (boundedInputsLambdaDepthBound C A savedBody) extra
    refine ⟨boundedInputsLambda_evaluates_at_depthBound shaped bg finiteCallee finiteArgument original enough,
      boundedInputsLambda_evaluate_depth_stable shaped bg finiteCallee finiteArgument enough,?_⟩
    intro actual final
    have raw : evaluateClosedSourceExpression? (_+extra) owner names captured store (call s callee supplied) = some (actual,final) ↔
        E owner names captured store (call s callee supplied) actual final :=
      boundedInputsLambda_evaluate_at_depthBound_iff shaped bg finiteCallee finiteArgument enough
    exact raw.trans ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩
  · intro absent
    exact nonempty ((boundedInputsLambda_evaluate_depth_none_iff_all_budgets shaped bg finiteCallee finiteArgument).mpr absent)

/-- Nested argument calls preserve arbitrary mixed data with sharp depth n+3.
The successful predecessor argument is supplied independently, not admitted as data syntax. -/
theorem nested_arguments_have_sharp_depth
    (s : Syntax.SourceSpan) (name f x : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr) (n : Nat)
    (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (creationStore invocationStore : List RuntimeValue) (fid aid : Resolved.LocalId) (value : RuntimeValue)
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name pa annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    let source := lambda s name pa annotation
    E so sn sc creationStore source (.sourceClosure source so sn sc) creationStore ∧
    E co cn cc invocationStore (chain s f x n) value invocationStore ∧
    (∀ budget, evaluateClosedSourceExpression? budget co cn cc invocationStore (chain s f x n) =
      if n+3 ≤ budget then some (value,invocationStore) else none) ∧
    ¬ ClosedSourceDataExpression (chain s f x n) ∧
    evaluateClosedSourceExpression? 1 co cn cc invocationStore (ref s f) = some (.sourceClosure source so sn sc,invocationStore) ∧
    evaluateClosedSourceExpression? (argumentBudget n) co cn cc invocationStore (argument s f x n) = some (value,invocationStore) ∧
    boundedInputsLambdaDepthBound 1 (argumentBudget n) (body s name) = n+3 ∧
    Consequences s 1 (argumentBudget n) co cn cc invocationStore (ref s f) (argument s f x n) (body s name) value := by
  intro source
  have shaped := shape s name pa annotation
  have creation : E so sn sc creationStore source (.sourceClosure source so sn sc) creationStore := .creation shaped
  have original : E co cn cc invocationStore (chain s f x n) value invocationStore := chain_original fn ff an af
  have ran := fun budget => chain_run s name f x pa annotation n budget co so cn sn cc sc invocationStore fid aid value fn ff an af
  have finiteCallee : evaluateClosedSourceExpression? 1 co cn cc invocationStore (ref s f) = some (.sourceClosure source so sn sc,invocationStore) := by
    simpa only [Nat.le_refl,↓reduceIte] using reference_run (s:=s) (owner:=co) (store:=invocationStore) 1 fn ff
  have finiteArgument : evaluateClosedSourceExpression? (argumentBudget n) co cn cc invocationStore (argument s f x n) = some (value,invocationStore) := by
    cases n with
    | zero => simpa [argument,argumentBudget] using reference_run (s:=s) (owner:=co) (store:=invocationStore) 1 an af
    | succ n => simpa only [argument,argumentBudget,Nat.le_refl,↓reduceIte] using
        chain_run s name f x pa annotation n (n+3) co so cn sn cc sc invocationStore fid aid value fn ff an af
  have bound : boundedInputsLambdaDepthBound 1 (argumentBudget n) (body s name) = n+3 := by
    cases n <;> simp [argumentBudget,boundedInputsLambdaDepthBound,ref,body,closedSourceDataDepthBound,closedSourceDataBodyDepthBound] <;> omega
  have whole : E co cn cc invocationStore (call s (ref s f) (argument s f x n)) value invocationStore := by
    cases n <;> exact original
  exact ⟨creation,original,ran,chain_not_data s f x n,finiteCallee,finiteArgument,bound,
    finish shaped (.expression .reference) finiteCallee finiteArgument whole⟩

/-- Larger successful child budgets yield a nonminimal outer bound even though
the nested argument is outside the old data-expression admission boundary. -/
theorem supplied_input_budgets_need_not_be_minimal
    (s : Syntax.SourceSpan) (name f x : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr) (n k : Nat)
    (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (creationStore invocationStore : List RuntimeValue) (fid aid : Resolved.LocalId) (value : RuntimeValue)
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name pa annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    let source := lambda s name pa annotation
    E so sn sc creationStore source (.sourceClosure source so sn sc) creationStore ∧
    E co cn cc invocationStore (chain s f x n) value invocationStore ∧
    E co cn cc invocationStore (chain s f x (n+1)) value invocationStore ∧
    ¬ ClosedSourceDataExpression (chain s f x n) ∧
    evaluateClosedSourceExpression? (n+k+4) co cn cc invocationStore (ref s f) = some (.sourceClosure source so sn sc,invocationStore) ∧
    evaluateClosedSourceExpression? (n+k+4) co cn cc invocationStore (chain s f x n) = some (value,invocationStore) ∧
    boundedInputsLambdaDepthBound (n+k+4) (n+k+4) (body s name) = n+k+5 ∧
    evaluateClosedSourceExpression? (n+4) co cn cc invocationStore (chain s f x (n+1)) = some (value,invocationStore) ∧
    evaluateClosedSourceExpression? (n+k+4) co cn cc invocationStore (chain s f x (n+1)) = some (value,invocationStore) ∧
    Consequences s (n+k+4) (n+k+4) co cn cc invocationStore (ref s f) (chain s f x n) (body s name) value := by
  intro source
  have shaped := shape s name pa annotation
  have creation : E so sn sc creationStore source (.sourceClosure source so sn sc) creationStore := .creation shaped
  have supplied : E co cn cc invocationStore (chain s f x n) value invocationStore := chain_original fn ff an af
  have original : E co cn cc invocationStore (chain s f x (n+1)) value invocationStore :=
    .call shaped (.reference fn ff) supplied (.expression (.reference .head .head))
  have finiteCallee : evaluateClosedSourceExpression? (n+k+4) co cn cc invocationStore (ref s f) = some (.sourceClosure source so sn sc,invocationStore) := by
    simpa only [show 1 ≤ n+k+4 by omega,↓reduceIte] using reference_run (s:=s) (owner:=co) (store:=invocationStore) (n+k+4) fn ff
  have finiteArgument : evaluateClosedSourceExpression? (n+k+4) co cn cc invocationStore (chain s f x n) = some (value,invocationStore) := by
    simpa only [show n+3 ≤ n+k+4 by omega,↓reduceIte] using
      chain_run s name f x pa annotation n (n+k+4) co so cn sn cc sc invocationStore fid aid value fn ff an af
  have early : evaluateClosedSourceExpression? (n+4) co cn cc invocationStore (chain s f x (n+1)) = some (value,invocationStore) := by
    simpa only [show n+1+3 ≤ n+4 by omega,↓reduceIte] using
      chain_run s name f x pa annotation (n+1) (n+4) co so cn sn cc sc invocationStore fid aid value fn ff an af
  have bound : boundedInputsLambdaDepthBound (n+k+4) (n+k+4) (body s name) = n+k+5 := by
    simp [boundedInputsLambdaDepthBound,ref,body,closedSourceDataDepthBound,closedSourceDataBodyDepthBound]
  exact ⟨creation,supplied,original,chain_not_data s f x n,finiteCallee,finiteArgument,bound,early,
    evaluateClosedSourceExpression?_monotone (by omega) early,
    finish shaped (.expression .reference) finiteCallee finiteArgument original⟩
end Tests.NestedArgumentChainSymbolic
end

section
-- leanmerge: from Solcore.Test.FrontendParsedBoundedCalleeDepthBridge
/- Actual independent creations feed an inner call outside the data gate. Its
original witness and direct depth-three run precede every outer decision law.
All saved fields, caller payloads and complete stores remain explicit. -/
set_option autoImplicit false
namespace Tests.ParsedBoundedCalleeDepth
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def so : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedBoundedCallee",by decide⟩],by decide⟩⟩,307⟩
private def mo : Resolved.DeclarationId := {so with declarationIndex:=607}
private def co : Resolved.DeclarationId := {so with declarationIndex:=907}
private def sid (n : Nat) : Resolved.LocalId := ⟨so,n⟩
private def mid (n : Nat) : Resolved.LocalId := ⟨mo,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def mn : LocalNameTable := [("p",mid 8),("z",mid 2),("p",mid 99)]
private def sn : LocalNameTable := [("z",sid 2),("q",sid 8),("y",cid 40),("z",sid 99),("q",sid 99)]
private def sr (v core : V) (missing : Bool) (tail : Resolved.LocalScope V) :=
  (if missing then [] else [(sid 2,v),(sid 2,.unit)])++[(sid 8,core),(cid 40,core),(sid 99,.bool false)]++tail
private def cn (missing : Bool) : LocalNameTable :=
  [("f",cid 1),("x",cid 2),("z",cid 5)]++(if missing then [] else [("y",cid 3),("y",cid 99)])++[("f",cid 99)]
private def cr (maker target argument other : V) : Resolved.LocalScope V :=
  [(cid 1,maker),(cid 1,other),(cid 2,target),(cid 2,other),(cid 5,other),(cid 3,argument),(cid 3,.unit),(cid 99,other)]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (name : String) : Syntax.Expr :=
  ⟨span f a b,.identifier ⟨span f a b,name⟩⟩
private def expectedLambda (parameter key : String) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 17,.lambda (span f 0 3) ⟨span f 3 6,[⟨span f 4 5,.inferred ⟨span f 4 5,parameter⟩⟩]⟩ none
    ⟨span f 6 17,[⟨span f 7 16,.returnStmt (some (ref f 14 15 key))⟩]⟩⟩
private def expectedCall (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 7,.call ⟨span f 0 4,.call (ref f 0 1 "f") ⟨span f 1 4,[ref f 2 3 "x"]⟩⟩
    ⟨span f 4 7,[ref f 5 6 "y"]⟩⟩
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.call callee ⟨a,[argument]⟩⟩ => [s]++spans callee++[a]++spans argument
  | ⟨s,.lambda k ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨b,[⟨r,.returnStmt (some e)⟩]⟩⟩ => [s,k,ps,p,n.span,b,r]++spans e
  | _ => []
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-bounded-callee.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "bounded callee lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / zero diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==ranges) "every actual range"
    return actual
  | _ => throw (IO.userError "bounded callee parser")
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
    (shape : SourceUnaryLambdaShape source name body)
    (ag : ClosedSourceDataExpression argument) (bg : ClosedSourceDataBody body)
    (selection : evaluateClosedSourceExpression? 3 co n e st callee = some (.sourceClosure source owner names captured,st))
    (result : Outcome (fun v final => E co n e st ⟨cs,.call callee ⟨als,[argument]⟩⟩ v final) st)
    (depth : Nat) (bad : Bool) : IO Unit := do
  let call : Syntax.Expr := ⟨cs,.call callee ⟨als,[argument]⟩⟩
  let bound := boundedCalleeLambdaDepthBound 3 argument body
  proof selection; check (bound==depth) "actual selected saved-body / callee maximum plus one"
  match result with
  | .bad impossible =>
    proof impossible; check bad "planned original whole-call exclusion"
    have absent := (boundedCalleeLambda_evaluate_depth_none_iff shape ag bg selection (Nat.le_refl bound)).mpr impossible
    have all := (boundedCalleeLambda_evaluate_depth_none_iff_all_budgets shape ag bg selection).mp absent
    proof absent; proof all
    proof ((boundedCalleeLambda_evaluate_depth_none_iff shape ag bg selection (Nat.le_refl bound)).mp absent)
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
          proof ((boundedCalleeLambda_evaluate_at_depthBound_iff shape ag bg selection enough).mp ran)
          proof ((boundedCalleeLambda_evaluate_at_depthBound_iff shape ag bg selection enough).mpr actualOriginal)
        else throw (IO.userError "unexpected smaller-depth success")
  for extra in [0,3] do
    proof (boundedCalleeLambda_evaluate_depth_stable shape ag bg selection (Nat.le_add_right bound extra)
      (callSpan:=cs) (argumentsSpan:=als))
private def exercise (maker source whole : Syntax.Expr) (sv av core other : V) (tail : Resolved.LocalScope V)
    (callStore : List V) (mc ma : Bool) : IO Unit := do
  let se := sr sv core mc tail
  let me : Resolved.LocalScope V := [(mid 8,core),(mid 8,other),(mid 99,other),(mid 100,core)]
  match hm : maker, hs : source, hw : whole with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred mp⟩]⟩ _ ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩⟩,
    ⟨_,.lambda _ ⟨_,[⟨_,.inferred parameter⟩]⟩ _ body⟩,
    ⟨cs,.call ⟨ics,.call ⟨fs,.identifier f⟩ ⟨ials,[⟨ixs,.identifier ix⟩]⟩⟩ ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
    have makerShape : SourceUnaryLambdaShape maker mp ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ := by rw [hm]; exact .inferred
    have shape : SourceUnaryLambdaShape source parameter body := by rw [hs]; exact .inferred
    if names : f.value="f" ∧ ix.value="x" ∧ mk.value=mp.value then
      let m ← create mo mn me [core,.unit] makerShape
      let t ← create so sn se [other,.unit,core] shape
      match mm : m.val, tt : t.val with
      | (.sourceClosure ms mo mn me,mst),(.sourceClosure ts to tn te,tst) =>
        have mEqual := mm.symm.trans m.property
        have tEqual := tt.symm.trans t.property
        have mf := RuntimeValue.sourceClosure.inj (Prod.mk.inj mEqual).1
        have mshape : SourceUnaryLambdaShape ms mp ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ := mf.1.symm ▸ makerShape
        proof mf; proof (Prod.mk.inj mEqual).2; proof (Prod.mk.inj tEqual).2
        check (mo != to && mo != co && to != co && mst.length != callStore.length && tst.length != callStore.length) "two actual saved owners/creation stores versus caller"
        let closure := RuntimeValue.sourceClosure ts to tn te
        let n := cn ma; let e := cr (.sourceClosure ms mo mn me) closure av other
        let callee : Syntax.Expr := ⟨ics,.call ⟨fs,.identifier f⟩ ⟨ials,[⟨ixs,.identifier ix⟩]⟩⟩
        let fresh := Resolved.freshLocalId mo (mn.map Prod.snd)
        have beta : ClosedSourceBodyEvaluates mo ((mp.value,fresh)::mn) ((fresh,closure)::me) callStore
            ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ closure callStore :=
          .expression (.reference (names.2.2 ▸ LocalNameTable.Lookup.head) .head)
        have betaRun : evaluateClosedSourceBody? 2 mo ((mp.value,fresh)::mn) ((fresh,closure)::me) callStore
            ⟨mbs,[⟨mrs,.returnStmt (some ⟨mks,.identifier mk⟩)⟩]⟩ = some (closure,callStore) := by
          simp [evaluateClosedSourceBody?,evaluateClosedSourceExpression?,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,names.2.2]
        have pick : E co n e callStore ⟨fs,.identifier f⟩ (.sourceClosure ms mo mn me) callStore :=
          .reference (names.1 ▸ LocalNameTable.Lookup.head) .head
        have target : E co n e callStore ⟨ixs,.identifier ix⟩ closure callStore :=
          .reference (names.2.1 ▸ LocalNameTable.Lookup.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
        have originalInner : E co n e callStore callee closure callStore := .call mshape pick target beta
        have directInner : evaluateClosedSourceExpression? 3 co n e callStore callee = some (closure,callStore) := by
          simpa [callee,evaluateClosedSourceExpression?,n,e,cn,cr,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,
            names.1,names.2.1,show cid 1 ≠ cid 2 from by decide,sourceUnaryLambdaShape?_iff.mpr mshape] using betaRun
        have notData : ¬ ClosedSourceDataExpression callee := by intro impossible; dsimp only [callee] at impossible; cases impossible
        proof beta; proof originalInner; proof directInner; proof notData
        for budget in [0,2] do
          check ((evaluateClosedSourceExpression? budget co n e callStore callee).isNone) "independent inner depth-three boundary"
        match irun : evaluateClosedSourceExpression? 3 co n e callStore callee with
        | some (.sourceClosure actualSource actualOwner actualNames actualCaptured,cst) =>
          have equal := (evaluateClosedSourceExpression?_sound irun).deterministic originalInner
          have fields := RuntimeValue.sourceClosure.inj (equal.1.trans (Prod.mk.inj tEqual).1)
          have actualShape : SourceUnaryLambdaShape actualSource parameter body := fields.1.symm ▸ shape
          have selected : evaluateClosedSourceExpression? 3 co n e callStore callee =
              some (.sourceClosure actualSource actualOwner actualNames actualCaptured,callStore) := equal.2 ▸ irun
          have picked : E co n e callStore callee (.sourceClosure actualSource actualOwner actualNames actualCaptured) callStore := equal.1.symm ▸ originalInner
          proof fields; proof equal.2; proof picked; proof selected
          match hb : body with
          | ⟨_,[⟨_,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
            have bg : ClosedSourceDataBody body := by rw [hb]; exact .expression .reference
            match reference co n e callStore xs x with
            | .bad absent =>
              check (ma && x.value=="y") "caller argument missing while selected callee succeeds"
              match reference actualOwner actualNames actualCaptured callStore xs x with
              | .ok _ savedRead => proof savedRead
              | .bad _ => throw (IO.userError "saved y independently exists, but cannot supply caller y")
              have noCall := rejectCall (cs:=cs) (als:=als) actualShape picked (.bad absent)
                (by intro v ev; exact False.elim (absent v callStore ev))
              proof (show ∀ v final, ¬ E co n e callStore whole v final from hw ▸ noCall)
              consume actualShape .reference bg selected (.bad noCall) 4 true
            | .ok argument arg =>
              proof arg
              if hx : x.value="y" then
                if hm : ma=false then
                  have independentArgument : E co n e callStore ⟨xs,.identifier x⟩ av callStore := by
                    apply ClosedSourceExpressionEvaluates.reference (id:=cid 3) _
                      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
                    rw [hx]
                    change LocalNameTable.Lookup (cn ma) "y" (cid 3)
                    rw [hm]; exact .tail (by decide) (.tail (by decide) (.tail (by decide) .head))
                  proof (arg.deterministic independentArgument)
                else throw (IO.userError "missing caller argument cannot succeed")
              else throw (IO.userError "actual fixed caller argument y")
              let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
              let bn := (parameter.value,fresh)::actualNames; let be := (fresh,argument)::actualCaptured
              match reference actualOwner bn be callStore ys key with
              | .bad absent =>
                have noBody : ∀ v final, ¬ ClosedSourceBodyEvaluates actualOwner bn be callStore body v final := by
                  intro v final original; rw [hb] at original; cases original with | expression child => exact absent _ _ child
                have noCall := rejectCall (cs:=cs) (als:=als) actualShape picked (.ok argument arg) (by
                  intro v ev; obtain ⟨same,_⟩ := ev.deterministic arg; cases same; exact noBody)
                proof noBody; check (mc && key.value=="z") "actual selected body fails, no alternate callee fallback"
                proof (show ∀ v final, ¬ E co n e callStore whole v final from hw ▸ noCall)
                consume actualShape .reference bg selected (.bad noCall) 4 true
              | .ok value child =>
                if same : key.value=parameter.value then
                  have freshRead : E actualOwner bn be callStore ⟨ys,.identifier key⟩ argument callStore :=
                    .reference (same ▸ LocalNameTable.Lookup.head) .head
                  proof (child.deterministic freshRead)
                else if hy : key.value="z" then
                  if hp : parameter.value="q" then
                    if hm : mc=false then
                      have savedRead : E actualOwner bn be callStore ⟨ys,.identifier key⟩ sv callStore := by
                        rcases fields with ⟨_,rfl,rfl,rfl⟩
                        apply ClosedSourceExpressionEvaluates.reference (id:=sid 2) _ (Resolved.LocalScope.Lookup.tail (by decide) ?_)
                        · rw [hy]; exact .tail (by simpa only [hp] using (by decide : "q" ≠ "z")) .head
                        · change Resolved.LocalScope.Lookup (sr sv core mc tail) (sid 2) sv
                          rw [hm]; exact .head
                      proof (child.deterministic savedRead)
                    else throw (IO.userError "missing selected saved capture cannot succeed")
                  else throw (IO.userError "actual saved parameter q")
                else throw (IO.userError "actual selected saved free reference z")
                have originalBody : ClosedSourceBodyEvaluates actualOwner bn be callStore body value callStore := by
                  rw [hb]; exact .expression child
                have originalCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape picked arg originalBody
                proof originalBody; proof (show E co n e callStore whole value callStore from hw ▸ originalCall)
                match brun : evaluateClosedSourceBody? 2 actualOwner bn be callStore body with
                | some (bv,bs) =>
                  have actualBody := evaluateClosedSourceBody?_sound brun
                  proof (actualBody.deterministic originalBody)
                  have actualCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape picked arg actualBody
                  have sameStore := (actualBody.deterministic originalBody).2
                  consume actualShape .reference bg selected (.ok bv (sameStore ▸ actualCall)) 4 false
                | none => throw (IO.userError "actual selected saved body must succeed")
          | _ => throw (IO.userError "actual saved body reference")
        | _ => throw (IO.userError "actual inner call must return the independently created target")
      | _,_ => throw (IO.userError "two actual source closure creations")
    else throw (IO.userError "actual f/x and identity maker return")
  | _,_,_ => throw (IO.userError "two saved lambdas and actual f(x)(y)")
end Tests.ParsedBoundedCalleeDepth
open Solcore Solcore.Frontend Tests.ParsedBoundedCalleeDepth in
def Tests.frontendParsedBoundedCalleeDepthTests : IO Unit := do
  let ranges := [(0,17),(0,3),(3,6),(4,5),(4,5),(6,17),(7,16),(14,15),(14,15)]
  let p ← parsed "lam(p){return p;}" (expectedLambda "p" "p") ranges
  let q ← parsed "lam(q){return q;}" (expectedLambda "q" "q") ranges
  let z ← parsed "lam(q){return z;}" (expectedLambda "q" "z") ranges
  let whole ← parsed "f(x)(y)" expectedCall [(0,7),(0,4),(0,1),(0,1),(1,4),(2,3),(2,3),(4,7),(5,6),(5,6)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let other := RuntimeValue.sourceClosure p co [("p",cid 77),("p",cid 88)] [(cid 77,core),(cid 77,.word Core.Word.maximum)]
  let mut count := 0
  for (sv,av) in [(other,RuntimeValue.pair (.word Core.Word.maximum) core),(core,other),
      (RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef .word 900),(RuntimeValue.pair core other,RuntimeValue.bool false)] do
    for (tail,st) in [([],[]),([(sid 8,other),(sid 100,core),(cid 40,other)],
        [other,core,RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef .word 900])] do
      for (target,mc,ma) in [(q,false,false),(z,false,false),(z,true,false),(q,false,true)] do
        exercise p target whole sv av core other tail st mc ma
        count := count+1
  check (count==32) "four higher-order outcomes / four mixed payload pairs / two full contexts"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedBoundedInputsDepthBridge
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedDataBodyDepthBridge
/- Actual parsed bodies retain independent whole AST/ranges and original raw
witnesses before the depth laws. Typed/inferred fresh rows, ordered match choice,
arbitrary mixed payloads and full stores remain literal. Comparison counts are
not source-search depths or Core transition costs; source calls are not covered. -/
set_option autoImplicit false
namespace Tests.ParsedDataBodyDepthBridge
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedBodyDepth",by decide⟩],by decide⟩⟩,303⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=904},700⟩
private def names : LocalNameTable := [("x",sid 7),("y",sid 8),("tag",foreign),("x",sid 99),("y",sid 99)]
private def rows (tag p q : V) (tail : Resolved.LocalScope V) :=
  [(sid 8,q),(sid 7,p),(foreign,tag),(sid 7,.unit),(foreign,.unit)]++tail
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr :=
  ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def ret (f : Syntax.SourceFile) (a b c d e : Nat) (n : String) : Syntax.Block :=
  ⟨span f a e,[⟨span f b (d+1),.returnStmt (some (ref f c d n))⟩]⟩
private def bindingAST (f : Syntax.SourceFile) : Syntax.Block :=
  ⟨span f 0 36,[⟨span f 1 14,.letDecl ⟨span f 5 6,"x"⟩
    (some ⟨span f 7 11,.named ⟨span f 7 11,⟨⟨⟨span f 7 11,"Unit"⟩,[]⟩⟩⟩ none⟩) (some (ref f 12 13 "x"))⟩,
    ⟨span f 14 22,.letDecl ⟨span f 18 19,"x"⟩ none (some (ref f 20 21 "x"))⟩,
    ⟨span f 22 24,.expression (ref f 22 23 "x") true⟩,
    ⟨span f 24 35,.block (ret f 24 25 32 33 35 "x").value⟩]⟩
private def matchAST (fallback : Bool) (f : Syntax.SourceFile) : Syntax.Block :=
  let endByte := if fallback then 49 else 48
  let first : Syntax.MatchCase := ⟨span f 12 29,⟨⟨span f 17 18,.literal ⟨span f 17 18,.decimal "0"⟩⟩,
    ret f 18 19 26 27 29 "x"⟩⟩
  let second : Syntax.MatchCase := ⟨span f 29 46,⟨⟨span f 34 35,.wildcard (span f 34 35)⟩,
    ret f 35 36 43 44 46 "y"⟩⟩
  ⟨span f 0 endByte,[⟨span f 1 (endByte-1),.matchWith ⟨span f 6 11,⟨ref f 7 10 "tag",[]⟩⟩
    ⟨span f 11 (endByte-1),⟨if fallback then [first] else [first,second],
      if fallback then some (ret f 36 37 44 45 47 "y") else none⟩⟩⟩]⟩
private def refSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier ⟨n,_⟩⟩ => [s,n] | _ => []
private def retSpans : Syntax.Block → List Syntax.SourceSpan
  | ⟨b,[⟨s,.returnStmt (some e)⟩]⟩ => [b,s]++refSpans e | _ => []
private def patternSpans : Syntax.Pattern → List Syntax.SourceSpan
  | ⟨s,.literal ⟨t,_⟩⟩ => [s,t] | ⟨s,.wildcard t⟩ => [s,t] | _ => []
private def actualSpans : Syntax.Block → List Syntax.SourceSpan
  | ⟨b,[⟨a,.letDecl ⟨n,_⟩ (some ⟨t,.named ⟨q,⟨⟨⟨i,_⟩,[]⟩⟩⟩ none⟩) (some x)⟩,
      ⟨c,.letDecl ⟨m,_⟩ none (some y)⟩,⟨d,.expression z true⟩,⟨inner,.block rest⟩]⟩ =>
      [b,a,n,t,q,i]++refSpans x++[c,m]++refSpans y++[d]++refSpans z++[inner]++retSpans ⟨inner,rest⟩
  | ⟨b,[⟨s,.matchWith ⟨g,⟨e,[]⟩⟩ ⟨a,⟨cases,fallback⟩⟩⟩]⟩ =>
      [b,s,g]++refSpans e++[a]++cases.flatMap (fun c =>
        [c.span]++patternSpans c.value.pattern++retSpans c.value.body)++fallback.toList.flatMap retSpans
  | _ => []
private def parsed (text : String) (expected : Syntax.SourceFile → Syntax.Block)
    (ranges : List (Nat × Nat)) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-data-body-depth.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "body depth lexer")
  match Syntax.Parser.block .require (Syntax.Parser.State.initial file lexed) with
  | .ok body next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      body.span==Syntax.SourceSpan.fullFile file && body==expected file) "whole handwritten body AST / EOF / diagnostics zero"
    check ((actualSpans body).all (fun s => s.isValidFor file) &&
      (actualSpans body).map (fun s => (s.startByte,s.endByte))==ranges) "every actual node/name/type/pattern/delimiter range"
    return body
  | _ => throw (IO.userError "body depth parser")
private structure EC (t : LocalNameTable) (e : Resolved.LocalScope V) (s : List V) (src : Syntax.Expr) (v : V) : Type where
  gate : ClosedSourceDataExpression src
  original : ClosedSourceExpressionEvaluates owner t e s src v s
private structure BC (t : LocalNameTable) (e : Resolved.LocalScope V) (s : List V) (src : Syntax.Block) (v : V) : Type where
  gate : ClosedSourceDataBody src
  original : ClosedSourceBodyEvaluates owner t e s src v s
private def reference (t : LocalNameTable) (e : Resolved.LocalScope V) (s : List V) (src : Syntax.Expr)
    (spelling : String) (id : Resolved.LocalId) (v : V)
    (named : LocalNameTable.Lookup t spelling id) (found : Resolved.LocalScope.Lookup e id v) : IO (EC t e s src v) := do
  match shape : src with
  | ⟨_,.identifier name⟩ =>
    if h : name.value=spelling then return by rw [shape]; exact ⟨.reference,.reference (h ▸ named) found⟩
    else throw (IO.userError "actual reference spelling")
  | _ => throw (IO.userError "actual reference shape")
private def returned (t : LocalNameTable) (e : Resolved.LocalScope V) (s : List V) (src : Syntax.Block)
    (spelling : String) (id : Resolved.LocalId) (v : V)
    (named : LocalNameTable.Lookup t spelling id) (found : Resolved.LocalScope.Lookup e id v) : IO (BC t e s src v) := do
  match shape : src with
  | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ =>
    let h ← reference t e s child spelling id v named found
    return by rw [shape]; exact ⟨.expression h.gate,.expression h.original⟩
  | _ => throw (IO.userError "actual expression return")
private def bindingWitness (src : Syntax.Block) (tag p q : V) (tail : Resolved.LocalScope V) (store : List V) :
    IO (BC names (rows tag p q tail) store src p) := do
  match shape : src with
  | ⟨bs,[⟨ls,.letDecl ⟨xs,"x"⟩ (some _) (some init)⟩,⟨ls2,.letDecl ⟨xs2,"x"⟩ none (some init2)⟩,
      ⟨ds,.expression discarded true⟩,⟨inner,.block rest⟩]⟩ =>
    let e := rows tag p q tail
    let i := Resolved.freshLocalId owner (names.map Prod.snd)
    let t1 := ("x",i)::names; let e1 := (i,p)::e
    let j := Resolved.freshLocalId owner (t1.map Prod.snd)
    let t2 := ("x",j)::t1; let e2 := (j,p)::e1
    let h1 ← reference names e store init "x" (sid 7) p .head (.tail (by decide) .head)
    let h2 ← reference t1 e1 store init2 "x" i p .head .head
    let hd ← reference t2 e2 store discarded "x" j p .head .head
    let hr ← returned t2 e2 store ⟨inner,rest⟩ "x" j p .head .head
    return by rw [shape]; exact ⟨.binding h1.gate (.binding h2.gate (.discard hd.gate (.block hr.gate))),
      .binding h1.original (.inferred h2.original (.discard hd.original (.block hr.original)))⟩
  | _ => throw (IO.userError "actual typed/inferred fresh shadow/discard/nested block")
private def zero : Core.Word := ⟨0,by decide⟩
private def literal (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p (some zero))) := do
  match shape : p with
  | ⟨_,.literal ⟨_,.decimal "0"⟩⟩ =>
    return by apply PLift.up; rw [shape]; exact .literal ⟨_,rfl,
      .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) (by decide)) .nil)⟩
  | _ => throw (IO.userError "actual original zero pattern")
private structure Tail (e : Resolved.LocalScope V) (s : List V) (v : V) (w : Core.Word)
    (cases : List Syntax.MatchCase) (fallback : Option Syntax.Block) where
  body : Syntax.Block
  cert : BC names e s body v
  branches : ∀ arm ∈ cases, ClosedSourceDataBody arm.value.body
  defaults : ∀ body ∈ fallback.toList, ClosedSourceDataBody body
  choice : RuntimeWordMatchChooses (.word w) cases fallback body 0
private def tailWitness (e : Resolved.LocalScope V) (s : List V) (q : V) (w : Core.Word)
    (cases : List Syntax.MatchCase) (fallback : Option Syntax.Block)
    (found : Resolved.LocalScope.Lookup e (sid 8) q) : IO (Tail e s q w cases fallback) := do
  match shape : (cases,fallback) with
  | ([⟨a,⟨⟨ps,.wildcard marker⟩,body⟩⟩],none) =>
    let h ← returned names e s body "y" (sid 8) q (.tail (by decide) .head) found
    return by cases shape; exact ⟨body,h,by intro arm ha; simp only [List.mem_singleton] at ha; exact ha ▸ h.gate,
      by simp,.wildcard (.wildcard rfl)⟩
  | ([],some body) =>
    let h ← returned names e s body "y" (sid 8) q (.tail (by decide) .head) found
    return by cases shape; exact ⟨body,h,by simp,
      by intro b hb; simp only [Option.toList,List.mem_singleton] at hb; exact hb ▸ h.gate,.fallback⟩
  | _ => throw (IO.userError "actual ordered wildcard/default tail")
private def matchWitness (src : Syntax.Block) (p q : V) (w : Core.Word) (tail : Resolved.LocalScope V) (store : List V) :
    IO (BC names (rows (.word w) p q tail) store src (if w=zero then p else q)) := do
  let e := rows (.word w) p q tail
  match shape : src with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨guard,[]⟩⟩ ⟨_,⟨first::rest,fallback⟩⟩⟩]⟩ =>
    let hg ← reference names e store guard "tag" foreign (.word w)
      (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
    let meaning := (← literal first.value.pattern).down
    let ht ← returned names e store first.value.body "x" (sid 7) p .head (.tail (by decide) .head)
    let hf ← tailWitness e store q w rest fallback .head
    have chosen : RuntimeWordMatchChooses (.word w) (first::rest) fallback
        (if w=zero then first.value.body else hf.body) 1 := by
      by_cases same : w=zero
      · subst w; simp only [↓reduceIte]; exact .hit meaning
      · simp only [same,↓reduceIte]; exact .miss meaning same hf.choice
    proof chosen
    match picked : chooseRuntimeWordMatch? (.word w) (first::rest) fallback with
    | none => False.elim (by have h := chooseRuntimeWordMatch?_iff.mpr chosen; rw [picked] at h; cases h)
    | some (actual,count) =>
      proof ((chooseRuntimeWordMatch?_iff.mp picked).deterministic chosen)
      check (count==1) "one visited comparison remains distinct from whole source depth three"
    return by
      rw [shape]; refine ⟨.wordMatch hg.gate ?_ hf.defaults,?_⟩
      · intro arm ha; rcases List.mem_cons.mp ha with rfl|ha; exact ht.gate; exact hf.branches _ ha
      · by_cases same : w=zero
        · subst w; simp only [↓reduceIte]; exact .wordMatch hg.original (.hit meaning) ht.original
        · simp only [same,↓reduceIte]; exact .wordMatch hg.original (.miss meaning same hf.choice) hf.cert.original
  | _ => throw (IO.userError "actual ordered literal-headed match")
private def exercise {t e s src v} (h : BC t e s src v) (expectedBound : Nat) : IO Unit := do
  proof h.original
  let bound := closedSourceDataBodyDepthBound src
  check (bound==expectedBound) "actual syntax-only body depth"
  proof (h.gate.evaluates_at_depthBound h.original (Nat.le_refl bound))
  have endpoints : ∀ actual final, ClosedSourceBodyEvaluates owner t e s src actual final ↔ actual=v ∧ final=s :=
    fun _ _ => ⟨fun other => other.deterministic h.original,by rintro ⟨rfl,rfl⟩; exact h.original⟩
  proof endpoints
  for budget in [0,bound-1,bound,bound+3] do
    match ran : evaluateClosedSourceBody? budget owner t e s src with
    | none => check (budget<bound) "only below exact selected depth is absent in these fixtures"
    | some (actual,final) =>
      have original := evaluateClosedSourceBody?_sound ran
      have equal := (endpoints actual final).mp original
      proof equal; proof ((endpoints actual final).mpr equal)
      check (bound<=budget) "full actual endpoint and selected-depth boundary"
      if enough : bound≤budget then
        proof ((h.gate.evaluate_at_depthBound_iff enough).mp ran)
        proof ((h.gate.evaluate_at_depthBound_iff enough).mpr original)
        have stable := h.gate.evaluate_depth_stable owner t e s enough
        proof stable
        proof (show evaluateClosedSourceBody? bound owner t e s src = some (actual,final) from stable.symm.trans ran)
  for extra in [0,1,7] do
    proof (h.gate.evaluate_depth_stable owner t e s (Nat.le_add_right bound extra))
    proof (h.gate.evaluates_at_depthBound h.original (Nat.le_add_right bound extra))
end Tests.ParsedDataBodyDepthBridge
open Solcore Solcore.Frontend Tests.ParsedDataBodyDepthBridge in
def Tests.frontendParsedDataBodyDepthBridgeTests : IO Unit := do
  let bound ← parsed "{let x:Unit=x;let x=x;x;{return x;}}" bindingAST
    [(0,36),(1,14),(5,6),(7,11),(7,11),(7,11),(12,13),(12,13),(14,22),(18,19),(20,21),(20,21),
      (22,24),(22,23),(22,23),(24,35),(24,35),(25,34),(32,33),(32,33)]
  let wildcard ← parsed "{match(tag){case 0{return x;}case _{return y;}}}" (matchAST false)
    [(0,48),(1,47),(6,11),(7,10),(7,10),(11,47),(12,29),(17,18),(17,18),(18,29),(19,28),(26,27),(26,27),
      (29,46),(34,35),(34,35),(35,46),(36,45),(43,44),(43,44)]
  let fallback ← parsed "{match(tag){case 0{return x;}default{return y;}}}" (matchAST true)
    [(0,49),(1,48),(6,11),(7,10),(7,10),(11,48),(12,29),(17,18),(17,18),(18,29),(19,28),(26,27),(26,27),
      (36,47),(37,46),(44,45),(44,45)]
  let inert : Syntax.Expr := ⟨bound.span,.tuple ⟨bound.span,[]⟩⟩
  let saved := RuntimeValue.sourceClosure inert foreign.owner [("x",foreign),("x",sid 7)]
    [(foreign,.unit),(foreign,.word Core.Word.maximum)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let mut count := 0
  for p in [saved,RuntimeValue.pair (.word Core.Word.maximum) saved] do
    for tail in [[],[(sid 7,core),(foreign,saved),(sid 100,core),(sid 101,saved)]] do
      for store in [[],[saved,core,RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef (.function .word .word) 900]] do
        let h ← bindingWitness bound (.word Core.Word.maximum) p core tail store
        exercise h 6
        count := count+1
        for src in [wildcard,fallback] do
          for w in [zero,⟨1,by decide⟩] do
            let h ← matchWitness src p core w tail store
            exercise h 3
            count := count+1
  check (count==40) "three spellings / eight mixed contexts / five original success lanes"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedDataCalleeDepthBridge
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedDirectDataLambdaDepthBridge
/- Actual direct calls retain independently handwritten ASTs and every span.
Original creation/argument/fresh-body/call witnesses precede depth laws. The
grouped bare-call control is a different whole AST: depth three, while its
explicitly extracted direct call has depth two. No saved-call bound or Core cost. -/
set_option autoImplicit false
namespace Tests.ParsedDirectDataLambdaDepth
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedDirectDepth",by decide⟩],by decide⟩⟩,304⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=904},700⟩
private def names : LocalNameTable := [("x",foreign),("p",sid 8),("x",sid 99),("p",sid 99)]
private def rows (v : V) (tail : Resolved.LocalScope V) :=
  [(foreign,v),(foreign,.unit),(sid 8,.bool false),(sid 99,.word Core.Word.maximum)]++tail
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr :=
  ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def expected (typed bare grouped : Bool) (key : String) (f : Syntax.SourceFile) : Syntax.Expr :=
  let k := if grouped then 1 else 0
  let t := if typed then 5 else 0
  let b := k+6+t
  let stop := b+(if bare then 9 else 11)
  let c := stop+(if grouped then 1 else 0)
  let parameter : Syntax.LambdaParameter := if typed then
    ⟨span f (k+4) (k+10),.typed none ⟨span f (k+4) (k+5),"p"⟩
      ⟨span f (k+6) (k+10),.named ⟨span f (k+6) (k+10),⟨⟨⟨span f (k+6) (k+10),"Unit"⟩,[]⟩⟩⟩ none⟩⟩
    else ⟨span f (k+4) (k+5),.inferred ⟨span f (k+4) (k+5),"p"⟩⟩
  let body : Syntax.Block := ⟨span f b stop,[⟨span f (b+1) (stop-1),
    .returnStmt (if bare then none else some (ref f (b+8) (b+9) "p"))⟩]⟩
  let source : Syntax.Expr := ⟨span f k stop,.lambda (span f k (k+3))
    ⟨span f (k+3) (k+6+t),[parameter]⟩ none body⟩
  ⟨span f 0 (c+3),.call (if grouped then ⟨span f 0 c,.group source⟩ else source)
    ⟨span f c (c+3),[ref f (c+1) (c+2) key]⟩⟩
private def refSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span] | _ => []
private def typeSpans : Syntax.TypeExpr → List Syntax.SourceSpan
  | ⟨s,.named ⟨q,⟨⟨i,[]⟩⟩⟩ none⟩ => [s,q,i.span] | _ => []
private def parameterSpans : Syntax.LambdaParameter → List Syntax.SourceSpan
  | ⟨s,.inferred n⟩ => [s,n.span]
  | ⟨s,.typed none n t⟩ => [s,n.span]++typeSpans t | _ => []
private def lambdaSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.lambda k ⟨ps,[p]⟩ none ⟨b,[⟨r,.returnStmt child⟩]⟩⟩ =>
    [s,k,ps]++parameterSpans p++[b,r]++child.toList.flatMap refSpans
  | _ => []
private def calleeSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.group child⟩ => [s]++lambdaSpans child | source => lambdaSpans source
private def actualSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.call callee ⟨a,[argument]⟩⟩ => [s]++calleeSpans callee++[a]++refSpans argument | _ => []
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr)
    (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-direct-data-depth.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "direct depth lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole independent AST / EOF / diagnostics zero"
    check ((actualSpans actual).all (fun s => s.isValidFor file) &&
      (actualSpans actual).map (fun s => (s.startByte,s.endByte))==ranges) "every actual expression/name/type/delimiter span"
    return actual
  | _ => throw (IO.userError "direct depth parser")
private structure LC (source : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source name body
private def lambda (source : Syntax.Expr) : IO (LC source) := do
  match h : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred name⟩]⟩ _ body⟩ => return ⟨name,body,by rw [h]; exact .inferred⟩
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none name _⟩]⟩ _ body⟩ => return ⟨name,body,by rw [h]; exact .typed⟩
  | _ => throw (IO.userError "actual direct unary lambda")
private structure CC (e : Resolved.LocalScope V) (st : List V) (callee : Syntax.Expr) where
  source : Syntax.Expr
  cert : LC source
  original : E owner names e st callee (.sourceClosure source owner names e) st
private def calleeWitness (e : Resolved.LocalScope V) (st : List V) (callee : Syntax.Expr) : IO (CC e st callee) := do
  match h : callee with
  | ⟨s,.group inner⟩ =>
    have notDirect : ∀ name body, ¬ SourceUnaryLambdaShape ⟨s,.group inner⟩ name body := by
      intro name body impossible; cases impossible
    proof notDirect
    let c ← lambda inner
    return ⟨inner,c,by rw [h]; exact .group (.creation c.shape)⟩
  | _ =>
    let c ← lambda callee
    return ⟨callee,c,.creation c.shape⟩
private structure BC (e : Resolved.LocalScope V) (st : List V) (name : Syntax.Identifier)
    (argument : V) (body : Syntax.Block) where
  value : V
  gate : ClosedSourceDataBody body
  original : ClosedSourceBodyEvaluates owner
    ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
    ((Resolved.freshLocalId owner (names.map Prod.snd),argument)::e) st body value st
private def bodyWitness (e : Resolved.LocalScope V) (st : List V) (name : Syntax.Identifier)
    (v : V) (body : Syntax.Block) : IO (BC e st name v body) := do
  match h : body with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,by rw [h]; exact .bare,by rw [h]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier key⟩)⟩]⟩ =>
    if same : key.value=name.value then
      return ⟨v,by rw [h]; exact .expression .reference,
        by rw [h]; exact .expression (.reference (same ▸ LocalNameTable.Lookup.head) .head)⟩
    else throw (IO.userError "actual fresh parameter reference")
  | _ => throw (IO.userError "actual return body")
private theorem noArgument {e st callee source argument callSpan argumentsSpan}
    (created : E owner names e st callee (.sourceClosure source owner names e) st)
    (absent : ∀ value final, ¬ E owner names e st argument value final) :
    ∀ value final, ¬ E owner names e st ⟨callSpan,.call callee ⟨argumentsSpan,[argument]⟩⟩ value final := by
  intro value final original
  cases original with
  | creation impossible => cases impossible
  | call _ actualCallee actualArgument _ =>
    obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic created
    cases sameCallee; cases sameStore
    exact absent _ _ actualArgument
private def fullEndpoint {e st src value} (original : E owner names e st src value st) (depth : Nat) : IO Unit := do
  have endpoints : ∀ actual final, E owner names e st src actual final ↔ actual=value ∧ final=st :=
    fun _ _ => ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩
  proof endpoints
  for budget in [0,depth-1,depth,depth+3] do
    match ran : evaluateClosedSourceExpression? budget owner names e st src with
    | none => check (budget<depth) "fixture selected exact depth"
    | some (actual,final) =>
      have equal := (endpoints actual final).mp (evaluateClosedSourceExpression?_sound ran)
      proof equal; proof ((endpoints actual final).mpr equal)
      check (depth<=budget) "complete actual RuntimeValue and store retained"
private def exercise (whole : Syntax.Expr) (v : V) (tail : Resolved.LocalScope V) (st : List V)
    (directDepth wholeDepth : Nat) (failure : Bool) : IO Unit := do
  let e := rows v tail
  match hwhole : whole with
  | ⟨callSpan,.call actualCallee ⟨argumentsSpan,[argument]⟩⟩ =>
    let c ← calleeWitness e st actualCallee
    let b ← bodyWitness e st c.cert.name v c.cert.body
    let direct : Syntax.Expr := ⟨callSpan,.call c.source ⟨argumentsSpan,[argument]⟩⟩
    have created : E owner names e st c.source (.sourceClosure c.source owner names e) st := .creation c.cert.shape
    proof created; proof c.original; proof b.original
    match ha : argument with
    | ⟨_,.identifier key⟩ =>
      have argGate : ClosedSourceDataExpression argument := by rw [ha]; exact .reference
      let bound := directDataLambdaDepthBound argument c.cert.body
      check (bound==directDepth) "actual extracted direct-call bound"
      if missing : key.value="z" then
        check failure "only the planned missing-argument fixture"
        have absent : ∀ value final, ¬ E owner names e st argument value final := by
          intro value final original
          rw [ha] at original
          cases original with
          | reference named _ =>
            have lookup := LocalNameTable.lookup?_iff.mpr named
            rw [missing] at lookup
            cases lookup
          | creation impossible => cases impossible
        have noDirect := noArgument (callSpan:=callSpan) (argumentsSpan:=argumentsSpan) created absent
        have noWhole := noArgument (callSpan:=callSpan) (argumentsSpan:=argumentsSpan) c.original absent
        proof noDirect; proof (show ∀ value final, ¬ E owner names e st whole value final from hwhole ▸ noWhole)
        have atBound := (directDataLambda_evaluate_depth_none_iff c.cert.shape argGate b.gate
          (Nat.le_refl bound) (callSpan:=callSpan) (argumentsSpan:=argumentsSpan)).mpr noDirect
        proof atBound
        have allBudgets := (directDataLambda_evaluate_depth_none_iff_all_budgets c.cert.shape argGate b.gate).mp atBound
        proof allBudgets
        proof ((directDataLambda_evaluate_depth_none_iff c.cert.shape argGate b.gate (Nat.le_refl bound)).mp atBound)
        for extra in [0,1,7] do
          proof (directDataLambda_evaluate_depth_stable c.cert.shape argGate b.gate (Nat.le_add_right bound extra)
            (owner:=owner) (names:=names) (captured:=e) (initialStore:=st)
            (callSpan:=callSpan) (argumentsSpan:=argumentsSpan))
        for budget in [0,bound-1,bound,bound+3] do
          check ((evaluateClosedSourceExpression? budget owner names e st whole).isNone) "actual whole missing argument"
          proof (allBudgets budget)
      else if named : key.value="x" then
        check (!failure) "planned original successful call"
        have arg : E owner names e st argument v st := by rw [ha]; exact .reference (named ▸ LocalNameTable.Lookup.head) .head
        have original : E owner names e st direct b.value st := .call c.cert.shape created arg b.original
        have originalWhole : E owner names e st whole b.value st := by
          rw [hwhole]; exact .call c.cert.shape c.original arg b.original
        proof arg; proof original; proof originalWhole
        fullEndpoint original directDepth
        fullEndpoint originalWhole wholeDepth
        for extra in [0,1,7] do
          have enough := Nat.le_add_right bound extra
          have everyEndpoint : ∀ actual final,
              evaluateClosedSourceExpression? (bound+extra) owner names e st direct = some (actual,final) ↔
                E owner names e st direct actual final := fun _ _ =>
            directDataLambda_evaluate_at_depthBound_iff c.cert.shape argGate b.gate enough
          proof everyEndpoint
          have found := directDataLambda_evaluates_at_depthBound c.cert.shape argGate b.gate original enough
          proof found
          proof ((directDataLambda_evaluate_at_depthBound_iff c.cert.shape argGate b.gate enough).mp found)
          proof ((directDataLambda_evaluate_at_depthBound_iff c.cert.shape argGate b.gate enough).mpr original)
          proof (directDataLambda_evaluate_depth_stable c.cert.shape argGate b.gate enough
            (owner:=owner) (names:=names) (captured:=e) (initialStore:=st)
            (callSpan:=callSpan) (argumentsSpan:=argumentsSpan))
      else throw (IO.userError "actual argument spelling")
    | _ => throw (IO.userError "actual argument reference")
  | _ => throw (IO.userError "actual whole unary call")
end Tests.ParsedDirectDataLambdaDepth
open Solcore Solcore.Frontend Tests.ParsedDirectDataLambdaDepth in
def Tests.frontendParsedDirectDataLambdaDepthTests : IO Unit := do
  let inferred ← parsed "lam(p){return p;}(x)" (expected false false false "x")
    [(0,20),(0,17),(0,3),(3,6),(4,5),(4,5),(6,17),(7,16),(14,15),(14,15),(17,20),(18,19),(18,19)]
  let typed ← parsed "lam(p:Unit){return p;}(x)" (expected true false false "x")
    [(0,25),(0,22),(0,3),(3,11),(4,10),(4,5),(6,10),(6,10),(6,10),(11,22),(12,21),(19,20),(19,20),(22,25),(23,24),(23,24)]
  let bare ← parsed "lam(p){return;}(x)" (expected false true false "x")
    [(0,18),(0,15),(0,3),(3,6),(4,5),(4,5),(6,15),(7,14),(15,18),(16,17),(16,17)]
  let missing ← parsed "lam(p:Unit){return;}(z)" (expected true true false "z")
    [(0,23),(0,20),(0,3),(3,11),(4,10),(4,5),(6,10),(6,10),(6,10),(11,20),(12,19),(20,23),(21,22),(21,22)]
  let grouped ← parsed "(lam(p){return;})(x)" (expected false true true "x")
    [(0,20),(0,17),(1,16),(1,4),(4,7),(5,6),(5,6),(7,16),(8,15),(17,20),(18,19),(18,19)]
  let saved := RuntimeValue.sourceClosure inferred foreign.owner [("p",foreign),("p",sid 8)]
    [(foreign,.unit),(foreign,.word Core.Word.maximum)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let mut count := 0
  for value in [saved,RuntimeValue.pair (.word Core.Word.maximum) core] do
    for tail in [[],[(foreign,core),(sid 8,saved),(sid 100,core),(sid 101,saved)]] do
      for store in [[],[saved,core,RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef (.function .word .word) 900]] do
        for (source,d,w,bad) in [(inferred,3,3,false),(typed,3,3,false),(bare,2,2,false),
            (missing,2,2,true),(grouped,2,3,false)] do
          exercise source value tail store d w bad
          count := count+1
  check (count==40) "five actual spellings / eight mixed duplicate-row full-store contexts"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedSavedDataLambdaDepthBridge
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
end

section
-- leanmerge: from Solcore.Test.FrontendSavedDataLambdaDepthBoundaryProperties
/- Original lexical failures are proved before using saved-body depth decisions.
Caller values do not fill absent saved captures, nor do saved values evaluate
caller arguments. First-match rows and actual mixed stores remain literal. -/
set_option autoImplicit false
namespace Tests.SavedDataLambdaDepthBoundaries
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def unit (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.tuple ⟨s,[]⟩⟩
private def call (s : Syntax.SourceSpan) (callee : Syntax.Identifier) (argument : Syntax.Expr) : Syntax.Expr :=
  ⟨s,.call (ref s callee) ⟨s,[argument]⟩⟩
private def Failed (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope RuntimeValue) (st : List RuntimeValue)
    (s : Syntax.SourceSpan) (callee : Syntax.Identifier) (argument : Syntax.Expr) (body : Syntax.Block) : Prop :=
  evaluateClosedSourceExpression? (savedDataLambdaDepthBound argument body)
    o n e st (call s callee argument) = none ∧
  (∀ budget, evaluateClosedSourceExpression? budget o n e st (call s callee argument) = none) ∧
  ∀ value final, ¬ E o n e st (call s callee argument) value final

variable {source : Syntax.Expr} {parameter callee : Syntax.Identifier} {body : Syntax.Block}
variable {co so : Resolved.DeclarationId} {cn sn : LocalNameTable}
variable {ce se : Resolved.LocalScope RuntimeValue} {fid : Resolved.LocalId}
private theorem reject (s : Syntax.SourceSpan) (st : List RuntimeValue) {argument : Syntax.Expr}
    (shape : SourceUnaryLambdaShape source parameter body)
    (ag : ClosedSourceDataExpression argument) (bg : ClosedSourceDataBody body)
    (named : LocalNameTable.Lookup cn callee.value fid)
    (found : Resolved.LocalScope.Lookup ce fid (.sourceClosure source so sn se))
    (original : ∀ value final, ¬ E co cn ce st (call s callee argument) value final) :
    Failed co cn ce st s callee argument body := by
  have absent := (savedDataLambda_evaluate_depth_none_iff shape ag bg named found
    (Nat.le_refl _) (callSpan:=s) (calleeSpan:=s) (argumentsSpan:=s)).mpr original
  exact ⟨absent,(savedDataLambda_evaluate_depth_none_iff_all_budgets shape ag bg named found).mp absent,original⟩

private theorem fresh_ne {key : String} {id : Resolved.LocalId}
    (named : LocalNameTable.Lookup sn key id) : Resolved.freshLocalId so (sn.map Prod.snd) ≠ id := by
  intro same
  apply Resolved.freshLocalId_not_mem so (sn.map Prod.snd)
  rw [same]
  exact List.mem_map.mpr ⟨(key,id),named.mem,rfl⟩

theorem caller_value_does_not_fill_missing_saved_capture
    (s : Syntax.SourceSpan) (st : List RuntimeValue) (key : Syntax.Identifier)
    (shape : SourceUnaryLambdaShape source parameter ⟨s,[⟨s,.returnStmt (some (ref s key))⟩]⟩)
    (named : LocalNameTable.Lookup cn callee.value fid)
    (found : Resolved.LocalScope.Lookup ce fid (.sourceClosure source so sn se))
    (different : parameter.value ≠ key.value) (id callerId : Resolved.LocalId) (value : RuntimeValue)
    (savedName : LocalNameTable.Lookup sn key.value id)
    (savedMissing : Resolved.LocalScope.lookup? se id = none)
    (callerName : LocalNameTable.Lookup cn key.value callerId)
    (callerValue : Resolved.LocalScope.Lookup ce callerId value) :
    E co cn ce st (ref s key) value st ∧
    Failed co cn ce st s callee (unit s) ⟨s,[⟨s,.returnStmt (some (ref s key))⟩]⟩ := by
  have picked : E co cn ce st (ref s callee) (.sourceClosure source so sn se) st := .reference named found
  have argument : E co cn ce st (unit s) .unit st := .unit
  have caller : E co cn ce st (ref s key) value st := .reference callerName callerValue
  refine ⟨caller,reject s st shape .unit (.expression .reference) named found ?_⟩
  intro actual final original
  cases original with
  | creation impossible => cases impossible
  | call actualShape actualCallee actualArgument actualBody =>
    obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic picked
    cases sameCallee; cases sameStore
    obtain ⟨sameArgument,sameArgumentStore⟩ := actualArgument.deterministic argument
    cases sameArgument; cases sameArgumentStore
    obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
      ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans (sourceUnaryLambdaShape?_iff.mpr shape)))
    cases sameName; cases sameBody
    cases actualBody with
    | expression child =>
      cases child with
      | creation impossible => cases impossible
      | reference actualName actualValue =>
        cases actualName.id_unique (LocalNameTable.Lookup.tail different savedName)
        have lookup := Resolved.LocalScope.lookup?_iff.mpr actualValue
        have missing : Resolved.LocalScope.lookup?
            ((Resolved.freshLocalId so (sn.map Prod.snd),RuntimeValue.unit)::se) id = none := by
          simp only [Resolved.LocalScope.lookup?,if_neg (fresh_ne (so:=so) savedName),savedMissing]
        rw [missing] at lookup
        cases lookup

theorem saved_value_does_not_supply_a_missing_caller_argument
    (s : Syntax.SourceSpan) (st : List RuntimeValue) (key : Syntax.Identifier)
    (shape : SourceUnaryLambdaShape source parameter body) (gate : ClosedSourceDataBody body)
    (named : LocalNameTable.Lookup cn callee.value fid)
    (found : Resolved.LocalScope.Lookup ce fid (.sourceClosure source so sn se))
    (savedId : Resolved.LocalId) (value : RuntimeValue)
    (savedName : LocalNameTable.Lookup sn key.value savedId)
    (savedValue : Resolved.LocalScope.Lookup se savedId value)
    (missing : LocalNameTable.lookup? cn key.value = none) :
    E so sn se st (ref s key) value st ∧ Failed co cn ce st s callee (ref s key) body := by
  have saved : E so sn se st (ref s key) value st := .reference savedName savedValue
  have picked : E co cn ce st (ref s callee) (.sourceClosure source so sn se) st := .reference named found
  have absent : ∀ actual final, ¬ E co cn ce st (ref s key) actual final := by
    intro actual final original
    cases original with
    | creation impossible => cases impossible
    | reference actualName _ =>
      have lookup := LocalNameTable.lookup?_iff.mpr actualName
      rw [missing] at lookup; cases lookup
  refine ⟨saved,reject s st shape .reference gate named found ?_⟩
  intro actual final original
  cases original with
  | creation impossible => cases impossible
  | call _ actualCallee actualArgument _ =>
    obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic picked
    cases sameCallee; cases sameStore
    exact absent _ _ actualArgument

private def bare (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,[⟨s,.returnStmt none⟩]⟩
theorem duplicate_saved_non_bool_guard_never_falls_through
    (s : Syntax.SourceSpan) (st : List RuntimeValue) (key : Syntax.Identifier)
    (shape : SourceUnaryLambdaShape source parameter
      ⟨s,[⟨s,.ifThen (ref s key) (bare s) (some (bare s))⟩]⟩)
    (different : parameter.value ≠ key.value) (id : Resolved.LocalId)
    (bad : RuntimeValue) (notBool : ∀ b, bad ≠ .bool b)
    (savedName : LocalNameTable.Lookup sn key.value id)
    (named : LocalNameTable.Lookup cn callee.value fid)
    (found : Resolved.LocalScope.Lookup ce fid
      (.sourceClosure source so sn ((id,bad)::(id,.bool true)::se))) :
    E so sn ((id,bad)::(id,.bool true)::se) st (ref s key) bad st ∧
    Failed co cn ce st s callee (unit s)
      ⟨s,[⟨s,.ifThen (ref s key) (bare s) (some (bare s))⟩]⟩ := by
  have saved : E so sn ((id,bad)::(id,.bool true)::se) st (ref s key) bad st := .reference savedName .head
  have picked : E co cn ce st (ref s callee)
      (.sourceClosure source so sn ((id,bad)::(id,.bool true)::se)) st := .reference named found
  have argument : E co cn ce st (unit s) .unit st := .unit
  refine ⟨saved,reject s st shape .unit (.conditional .reference .bare .bare) named found ?_⟩
  intro actual final original
  cases original with
  | creation impossible => cases impossible
  | call actualShape actualCallee actualArgument actualBody =>
    obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic picked
    cases sameCallee; cases sameStore
    obtain ⟨sameArgument,sameArgumentStore⟩ := actualArgument.deterministic argument
    cases sameArgument; cases sameArgumentStore
    obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
      ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans (sourceUnaryLambdaShape?_iff.mpr shape)))
    cases sameName; cases sameBody
    have head : E so ((parameter.value,Resolved.freshLocalId so (sn.map Prod.snd))::sn)
        ((Resolved.freshLocalId so (sn.map Prod.snd),RuntimeValue.unit)::(id,bad)::(id,.bool true)::se)
        st (ref s key) bad st :=
      .reference (.tail different savedName) (.tail (fresh_ne (so:=so) savedName) .head)
    cases actualBody with
    | ifTrue tested _ => exact notBool true (head.deterministic tested).1
    | ifFalse tested _ => exact notBool false (head.deterministic tested).1

end Tests.SavedDataLambdaDepthBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendSavedDataLambdaDepthSymbolicProperties
/- Independent original creation, first pickup, caller argument and saved fresh
body witnesses precede depth laws. Creation and invocation stores are separate.
The fixed caller f(x) does not bound arbitrarily nested saved runtime syntax;
all results are whole mixed values/stores, not Core costs or runtime typings. -/
set_option autoImplicit false
namespace Tests.SavedDataLambdaDepthSymbolic
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def nestedStatement (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Nat → Syntax.Statement
  | 0 => ⟨s,.returnStmt (some (ref s name))⟩
  | n+1 => ⟨s,.block [nestedStatement s name n]⟩
private def nested (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) : Syntax.Block :=
  ⟨s,[nestedStatement s name n]⟩
private def lambda (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,match pa with
    | none => .inferred name | some t => .typed none name t⟩]⟩ annotation body⟩
private def call (s : Syntax.SourceSpan) (callee argument : Syntax.Identifier) : Syntax.Expr :=
  ⟨s,.call (ref s callee) ⟨s,[ref s argument]⟩⟩
private theorem shape (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (body : Syntax.Block) :
    SourceUnaryLambdaShape (lambda s name pa annotation body) name body := by
  cases pa with | none => exact .inferred | some t => exact .typed
private theorem nested_original {s name n owner names captured store id value}
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) :
    ClosedSourceBodyEvaluates owner names captured store (nested s name n) value store := by
  induction n with | zero => exact .expression (.reference named found) | succ n ih => exact .block ih
private theorem reference_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceExpression? (budget+1) owner names captured store (ref s name) = some (value,store) := by
  simp [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
private theorem nested_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceBody? budget owner names captured store (nested s name n) =
      if n+2 ≤ budget then some (value,store) else none := by
  induction n generalizing budget with
  | zero =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          cases budget with
          | zero => simp [nested,nestedStatement,evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
          | succ budget =>
              simpa only [nested,nestedStatement,evaluateClosedSourceBody?,Nat.zero_add,Nat.reduceAdd,
                show 2 ≤ budget+1+1 by omega,↓reduceIte] using
                reference_run s name budget owner names captured store id value named found
  | succ n ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          have arithmetic : (n+1+2 ≤ budget+1) ↔ n+2 ≤ budget := by omega
          simpa only [nested,nestedStatement,evaluateClosedSourceBody?,arithmetic] using ih budget
private theorem nested_gate (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) :
    ClosedSourceDataBody (nested s name n) := by
  induction n with | zero => exact .expression .reference | succ n ih => exact .block ih
private theorem nested_depth (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) :
    closedSourceDataBodyDepthBound (nested s name n) = n+2 := by
  induction n with
  | zero => simp [nested,nestedStatement,ref,closedSourceDataBodyDepthBound,closedSourceDataDepthBound]
  | succ n ih => simpa only [nested,nestedStatement,closedSourceDataBodyDepthBound,Nat.add_right_comm] using congrArg (·+1) ih
private theorem sharp_run (s : Syntax.SourceSpan) (parameter callee argument : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (n budget : Nat)
    (callerOwner savedOwner : Resolved.DeclarationId) (callerNames savedNames : LocalNameTable)
    (callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (calleeId argumentId : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup callerNames callee.value calleeId)
    (found : Resolved.LocalScope.Lookup callerCaptured calleeId
      (.sourceClosure (lambda s parameter pa annotation (nested s parameter n)) savedOwner savedNames savedCaptured))
    (argumentNamed : LocalNameTable.Lookup callerNames argument.value argumentId)
    (argumentFound : Resolved.LocalScope.Lookup callerCaptured argumentId value) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured store (call s callee argument) =
      if n+3 ≤ budget then some (value,store) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ budget =>
      cases budget with
      | zero => simp [call,evaluateClosedSourceExpression?]
      | succ budget =>
          have picked := reference_run s callee budget callerOwner callerNames callerCaptured store _ _ named found
          have actualArg := reference_run s argument budget callerOwner callerNames callerCaptured store _ _ argumentNamed argumentFound
          have returned := nested_run s parameter n (budget+1) savedOwner
            ((parameter.value,Resolved.freshLocalId savedOwner (savedNames.map Prod.snd))::savedNames)
            ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd),value)::savedCaptured) store
            (Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)) value .head .head
          have arithmetic : (n+3 ≤ budget+1+1) ↔ n+2 ≤ budget+1 := by omega
          simpa only [call,evaluateClosedSourceExpression?,picked,actualArg,
            sourceUnaryLambdaShape?_iff.mpr (shape s parameter pa annotation (nested s parameter n)),
            arithmetic,bind,Option.bind_some] using returned

/-- Caller argument lookup and saved fresh-body lookup remain separate, as do
creation and invocation stores. An arbitrary saved nest has sharp depth n+3. -/
theorem saved_body_nesting_has_sharp_depth
    (s : Syntax.SourceSpan) (parameter callee argument : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (n extra : Nat)
    (callerOwner savedOwner : Resolved.DeclarationId) (callerNames savedNames : LocalNameTable)
    (callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue)
    (creationStore invocationStore : List RuntimeValue) (calleeId argumentId : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup callerNames callee.value calleeId)
    (found : Resolved.LocalScope.Lookup callerCaptured calleeId
      (.sourceClosure (lambda s parameter pa annotation (nested s parameter n)) savedOwner savedNames savedCaptured))
    (argumentNamed : LocalNameTable.Lookup callerNames argument.value argumentId)
    (argumentFound : Resolved.LocalScope.Lookup callerCaptured argumentId value) :
    let body := nested s parameter n
    let source := lambda s parameter pa annotation body
    let application := call s callee argument
    E savedOwner savedNames savedCaptured creationStore source (.sourceClosure source savedOwner savedNames savedCaptured) creationStore ∧
    E callerOwner callerNames callerCaptured invocationStore (ref s callee)
      (.sourceClosure source savedOwner savedNames savedCaptured) invocationStore ∧
    E callerOwner callerNames callerCaptured invocationStore (ref s argument) value invocationStore ∧
    E callerOwner callerNames callerCaptured invocationStore application value invocationStore ∧
    (∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured invocationStore application =
      if n+3 ≤ budget then some (value,invocationStore) else none) ∧
    savedDataLambdaDepthBound (ref s argument) body = n+3 ∧
    evaluateClosedSourceExpression? (n+3+extra) callerOwner callerNames callerCaptured invocationStore application =
      some (value,invocationStore) ∧
    evaluateClosedSourceExpression? (n+3+extra) callerOwner callerNames callerCaptured invocationStore application =
      evaluateClosedSourceExpression? (savedDataLambdaDepthBound (ref s argument) body)
        callerOwner callerNames callerCaptured invocationStore application ∧
    (∀ actual final, evaluateClosedSourceExpression? (n+3+extra) callerOwner callerNames callerCaptured invocationStore application =
      some (actual,final) ↔ actual=value ∧ final=invocationStore) ∧
    evaluateClosedSourceExpression? (savedDataLambdaDepthBound (ref s argument) body)
      callerOwner callerNames callerCaptured invocationStore application ≠ none ∧
    ¬ (∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured invocationStore application = none) := by
  intro body source application
  have shaped := shape s parameter pa annotation body
  have creation : E savedOwner savedNames savedCaptured creationStore source
      (.sourceClosure source savedOwner savedNames savedCaptured) creationStore := .creation shaped
  have picked : E callerOwner callerNames callerCaptured invocationStore (ref s callee)
      (.sourceClosure source savedOwner savedNames savedCaptured) invocationStore := .reference named found
  have actualArg : E callerOwner callerNames callerCaptured invocationStore (ref s argument) value invocationStore :=
    .reference argumentNamed argumentFound
  have original : E callerOwner callerNames callerCaptured invocationStore application value invocationStore :=
    .call shaped picked actualArg (nested_original .head .head)
  have ran := fun budget => sharp_run s parameter callee argument pa annotation n budget callerOwner savedOwner
    callerNames savedNames callerCaptured savedCaptured invocationStore calleeId argumentId value named found argumentNamed argumentFound
  have ag : ClosedSourceDataExpression (ref s argument) := .reference
  have bg := nested_gate s parameter n
  have bound : savedDataLambdaDepthBound (ref s argument) body = n+3 := by
    simp only [savedDataLambdaDepthBound,ref,closedSourceDataDepthBound,body,nested_depth]; omega
  have enough : savedDataLambdaDepthBound (ref s argument) body ≤ n+3+extra := by omega
  have nonempty : evaluateClosedSourceExpression? (savedDataLambdaDepthBound (ref s argument) body)
      callerOwner callerNames callerCaptured invocationStore application ≠ none := by
    intro absent
    exact ((savedDataLambda_evaluate_depth_none_iff shaped ag bg named found (Nat.le_refl _)).mp absent) _ _ original
  have notAll : ¬ (∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured invocationStore application = none) := by
    intro absent
    exact nonempty ((savedDataLambda_evaluate_depth_none_iff_all_budgets shaped ag bg named found).mpr absent)
  refine ⟨creation,picked,actualArg,original,ran,bound,
    savedDataLambda_evaluates_at_depthBound shaped ag bg named found original enough,
    savedDataLambda_evaluate_depth_stable shaped ag bg named found enough,?_,nonempty,notAll⟩
  intro actual final
  have raw : evaluateClosedSourceExpression? (n+3+extra) callerOwner callerNames callerCaptured invocationStore application =
      some (actual,final) ↔ E callerOwner callerNames callerCaptured invocationStore application actual final :=
    savedDataLambda_evaluate_at_depthBound_iff shaped ag bg named found enough
  exact raw.trans ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩

/-- A fixed f(x) AST defeats every caller-syntax-only candidate bound when the
saved body may vary. Only the saved datum changes with n, not caller syntax. -/
theorem no_caller_syntax_only_bound
    (s : Syntax.SourceSpan) (parameter : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr)
    (callerOwner savedOwner : Resolved.DeclarationId) (savedNames : LocalNameTable)
    (savedCaptured : Resolved.LocalScope RuntimeValue) (creationStore invocationStore : List RuntimeValue)
    (value : RuntimeValue) (candidate : Syntax.Expr → Nat) :
    let callee : Syntax.Identifier := ⟨s,"f"⟩
    let argument : Syntax.Identifier := ⟨s,"x"⟩
    let fid : Resolved.LocalId := ⟨callerOwner,0⟩
    let aid : Resolved.LocalId := ⟨callerOwner,1⟩
    let callerNames := [("f",fid),("x",aid),("f",aid),("x",fid)]
    let application := call s callee argument
    ∃ n,
      let source := lambda s parameter pa annotation (nested s parameter n)
      let saved := RuntimeValue.sourceClosure source savedOwner savedNames savedCaptured
      let captured := [(fid,saved),(fid,.unit),(aid,value),(aid,.bool false)]
      E savedOwner savedNames savedCaptured creationStore source saved creationStore ∧
      E callerOwner callerNames captured invocationStore (ref s callee) saved invocationStore ∧
      E callerOwner callerNames captured invocationStore application value invocationStore ∧
      evaluateClosedSourceExpression? (candidate application) callerOwner callerNames captured invocationStore application = none ∧
      evaluateClosedSourceExpression? (n+3) callerOwner callerNames captured invocationStore application = some (value,invocationStore) := by
  intro callee argument fid aid callerNames application
  refine ⟨candidate application,?_⟩
  intro source saved captured
  have shaped := shape s parameter pa annotation (nested s parameter (candidate application))
  have named : LocalNameTable.Lookup callerNames callee.value fid := .head
  have found : Resolved.LocalScope.Lookup captured fid saved := .head
  have an : LocalNameTable.Lookup callerNames argument.value aid := .tail (by change "f" ≠ "x"; decide) .head
  have af : Resolved.LocalScope.Lookup captured aid value :=
    .tail (by dsimp only [aid,fid]; intro impossible; cases impossible)
      (.tail (by dsimp only [aid,fid]; intro impossible; cases impossible) .head)
  have creation : E savedOwner savedNames savedCaptured creationStore source saved creationStore := .creation shaped
  have picked : E callerOwner callerNames captured invocationStore (ref s callee) saved invocationStore := .reference named found
  have original : E callerOwner callerNames captured invocationStore application value invocationStore :=
    .call shaped picked (.reference an af) (nested_original .head .head)
  have ran := fun budget => sharp_run s parameter callee argument pa annotation (candidate application) budget
    callerOwner savedOwner callerNames savedNames captured savedCaptured invocationStore fid aid value named found an af
  refine ⟨creation,picked,original,?_,?_⟩
  · simpa only [show ¬ candidate application+3 ≤ candidate application by omega,↓reduceIte] using ran (candidate application)
  · simpa only [Nat.le_refl,↓reduceIte] using ran (candidate application+3)

end Tests.SavedDataLambdaDepthSymbolic
end
