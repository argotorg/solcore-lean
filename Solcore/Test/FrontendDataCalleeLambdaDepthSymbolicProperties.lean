import Solcore.Frontend.DataCalleeLambdaDepthDecisionProperties

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
