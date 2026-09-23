import Solcore.Frontend.BoundedInputsLambdaDepth

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
