import Solcore.Frontend.BoundedCalleeLambdaDepth

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
