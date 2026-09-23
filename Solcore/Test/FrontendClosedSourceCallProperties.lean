import Solcore.Frontend.ClosedSource

/-! Original symbolic call towers are evaluated by closed constructors, not by
assumed callbacks. Every capture, annotation and raw store remains literal.
These are successful derivations, not execution-cost or termination bounds. -/
set_option autoImplicit false
namespace Tests.FrontendClosedSourceCall
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def returned (span : Syntax.SourceSpan) (value : Syntax.Expr) : Syntax.Block :=
  ⟨span,[⟨span,.returnStmt (some value)⟩]⟩
private def lambda (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr :=
  ⟨span,.lambda span ⟨name.span,[⟨name.span,match annotation with
    | none => .inferred name | some type => .typed none name type⟩]⟩ returns body⟩
private theorem shape (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (body : Syntax.Block) :
    SourceUnaryLambdaShape (lambda span name annotation returns body) name body := by
  cases annotation <;> first | exact .inferred | exact .typed
private def app (span : Syntax.SourceSpan) (callee argument : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.call callee ⟨span,[argument]⟩⟩
private def tower (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) : Nat → Syntax.Expr
  | 0 => ref span name
  | n+1 => app span (lambda span name annotation returns
      (returned span (tower span name annotation returns n))) (ref span name)
private theorem towerPath (o : Resolved.DeclarationId) (span : Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr) (n : Nat)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id actual) :
    E o names captured store (tower span name annotation returns n) actual store := by
  induction n generalizing names captured id with
  | zero => exact .reference named found
  | succ n ih =>
      exact .call (shape _ _ _ _ _) (.creation (shape _ _ _ _ _))
        (.reference named found) (.expression (ih _ _ _ .head .head))
private def source (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) : Syntax.Expr :=
  lambda span name annotation returns (returned span (tower span name annotation returns n))
private def call (span : Syntax.SourceSpan) : Syntax.Expr :=
  app span (ref span ⟨span,"f"⟩) (ref span ⟨span,"argument"⟩)
private def callerNames (f x : Resolved.LocalId) (tail : LocalNameTable) : LocalNameTable :=
  ("f",f)::("argument",x)::tail
private def callerValues (f x : Resolved.LocalId) (closure actual : RuntimeValue)
    (tail : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  (f,closure)::(x,actual)::tail
private theorem invoke (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (caller saved : Resolved.DeclarationId)
    (names callerTail : LocalNameTable) (captured callerSuffix : Resolved.LocalScope RuntimeValue)
    (f x : Resolved.LocalId) (different : f≠x) (actual : RuntimeValue) (store : List RuntimeValue) :
    E caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved names captured) actual callerSuffix)
      store (call span) actual store :=
  .call (shape _ _ _ _ _) (.reference .head .head)
    (.reference (.tail (by change "f" ≠ "argument"; decide) .head) (.tail different .head))
    (.expression (towerPath _ _ _ _ _ _ _ _ _ _ _ .head .head))
private theorem freshNe {o : Resolved.DeclarationId} {names : LocalNameTable}
    {name : String} {id : Resolved.LocalId} (named : LocalNameTable.Lookup names name id) :
    Resolved.freshLocalId o (names.map Prod.snd) ≠ id := by
  intro same
  have member : id ∈ names.map Prod.snd := List.mem_map_of_mem named.mem
  exact Resolved.freshLocalId_not_mem o _ (same ▸ member)

theorem arbitrary_original_call_depth_returns_the_actual_value
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id actual) :
    E o names captured store (tower span name annotation returns n) actual store :=
  towerPath _ _ _ _ _ _ _ _ _ _ _ named found

theorem each_nested_callee_captures_every_current_row
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) :
    E o names captured store (source span name annotation returns n)
      (.sourceClosure (source span name annotation returns n) o names captured) store :=
  .creation (shape _ _ _ _ _)

theorem saved_owner_calls_shadow_old_names_and_capture_only_collisions
    (span : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (n : Nat) (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (oldId f x : Resolved.LocalId)
    (different : f≠x) (old collision actual : RuntimeValue) (store : List RuntimeValue) :
    let savedNames := (name.value,oldId)::names
    let rows := (Resolved.freshLocalId saved (savedNames.map Prod.snd),collision)::(oldId,old)::captured
    E caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved savedNames rows)
        actual callerSuffix) store (call span) actual store :=
  invoke _ _ _ _ _ _ _ _ _ _ _ _ _ different _ _

theorem original_open_call_has_the_same_exact_endpoint_without_child_laws
    (span : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (n : Nat) (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (f x : Resolved.LocalId)
    (different : f≠x) (actual result : RuntimeValue) (store final : List RuntimeValue) :
    SourceLambdaEvaluates E (SourceComputationBodyEvaluates E) caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved names captured) actual callerSuffix)
      store (call span) result final ↔ result=actual ∧ final=store := by
  have independent := invoke span name annotation returns n caller saved names callerTail
    captured callerSuffix f x different actual store
  constructor
  · intro evaluated
    exact (closedSourceExpressionEvaluates_call_iff.mpr evaluated).deterministic independent
  · rintro ⟨rfl,rfl⟩
    exact closedSourceExpressionEvaluates_call_iff.mp independent

theorem tower_result_and_store_are_unconditionally_unique
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store final : List RuntimeValue)
    (id : Resolved.LocalId) (actual result : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id actual)
    (other : E o names captured store (tower span name annotation returns n) result final) :
    result=actual ∧ final=store :=
  other.deterministic (towerPath _ _ _ _ _ _ _ _ _ _ _ named found)

theorem a_returned_source_closure_uses_its_own_saved_capture
    (span : Syntax.SourceSpan) (parameter selected : Syntax.Identifier)
    (notParameter : parameter.value≠selected.value) (annotation returns : Option Syntax.TypeExpr)
    (n : Nat) (caller saved : Resolved.DeclarationId) (savedNames callerTail : LocalNameTable)
    (savedValues callerSuffix : Resolved.LocalScope RuntimeValue) (f x selectedId : Resolved.LocalId)
    (different : f≠x) (argument result : RuntimeValue) (store : List RuntimeValue)
    (named : LocalNameTable.Lookup savedNames selected.value selectedId)
    (found : Resolved.LocalScope.Lookup savedValues selectedId result) :
    let original := lambda span parameter annotation returns (returned span (ref span selected))
    E caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure original saved savedNames savedValues) argument callerSuffix) store
      (app span (tower span ⟨span,"f"⟩ annotation returns n) (ref span ⟨span,"argument"⟩)) result store := by
  apply ClosedSourceExpressionEvaluates.call (shape _ _ _ _ _)
  · exact towerPath _ _ _ _ _ _ _ _ _ _ _ .head .head
  · exact .reference (.tail (by change "f" ≠ "argument"; decide) .head) (.tail different .head)
  · exact .expression (.reference (.tail notParameter named) (.tail (freshNe named) found))

end Tests.FrontendClosedSourceCall
