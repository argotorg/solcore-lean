import Solcore.Frontend.SavedDataLambdaDepth

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
