import Solcore.Frontend.DirectDataLambdaDepthDecisionProperties

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
