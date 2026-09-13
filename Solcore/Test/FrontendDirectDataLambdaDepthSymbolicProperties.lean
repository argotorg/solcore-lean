import Solcore.Frontend.DirectDataLambdaDepthDecisionProperties

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
