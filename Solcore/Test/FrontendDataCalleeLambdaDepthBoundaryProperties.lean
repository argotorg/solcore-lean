import Solcore.Frontend.DataCalleeLambdaDepth

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
