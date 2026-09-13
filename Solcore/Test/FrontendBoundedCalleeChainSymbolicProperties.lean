import Solcore.Frontend.BoundedCalleeLambdaDepthDecisionProperties

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
