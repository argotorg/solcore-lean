import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluatorCompletenessProperties

/-! Original symbolic call towers are evaluated by closed constructors, not by
assumed callbacks. Every capture, annotation and raw store remains literal.
The thresholds measure search depth, not execution cost or general termination. -/
set_option autoImplicit false
namespace Tests.FrontendClosedSourceCallRunner
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

private theorem towerRun (o : Resolved.DeclarationId) (span : Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr) (n budget : Nat)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id actual) :
    evaluateClosedSourceExpression? budget o names captured store (tower span name annotation returns n) =
      if 2*n+1≤budget then some (actual,store) else none := by
  induction n generalizing budget names captured id with
  | zero =>
      cases budget <;> simp [tower,ref,evaluateClosedSourceExpression?,
        LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
  | succ n ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceExpression?]
      | succ budget =>
          cases budget with
          | zero => simp [tower,app,evaluateClosedSourceExpression?]
          | succ k =>
              let fresh := Resolved.freshLocalId o (names.map Prod.snd)
              have inner := ih k ((name.value,fresh)::names) ((fresh,actual)::captured) fresh .head .head
              cases annotation <;>
                simpa [tower,app,lambda,returned,evaluateClosedSourceExpression?,evaluateClosedSourceBody?,
                  sourceUnaryLambdaShape?,ref,LocalNameTable.lookup?_iff.mpr named,
                  Resolved.LocalScope.lookup?_iff.mpr found,
                  show (2*(n+1)+1≤k+2) ↔ (2*n+1≤k) by omega] using inner

private theorem invokeRun (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n budget : Nat) (caller saved : Resolved.DeclarationId)
    (names callerTail : LocalNameTable) (captured callerSuffix : Resolved.LocalScope RuntimeValue)
    (f x : Resolved.LocalId) (different : f≠x) (actual : RuntimeValue) (store : List RuntimeValue) :
    evaluateClosedSourceExpression? budget caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved names captured) actual callerSuffix)
      store (call span) = if 2*n+3≤budget then some (actual,store) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ budget =>
      cases budget with
      | zero => simp [call,app,evaluateClosedSourceExpression?]
      | succ budget =>
          cases budget with
          | zero =>
              cases annotation <;> simp [call,app,ref,source,lambda,returned,evaluateClosedSourceExpression?,
                evaluateClosedSourceBody?,callerNames,callerValues,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,
                different,sourceUnaryLambdaShape?]
          | succ k =>
              let fresh := Resolved.freshLocalId saved (names.map Prod.snd)
              have inner := towerRun saved span name annotation returns n (k+1)
                ((name.value,fresh)::names) ((fresh,actual)::captured) store fresh actual .head .head
              cases annotation <;>
                simpa [call,app,ref,source,lambda,returned,evaluateClosedSourceExpression?,evaluateClosedSourceBody?,
                  callerNames,callerValues,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,different,
                  sourceUnaryLambdaShape?,show (2*n+3≤k+3) ↔ (2*n+1≤k+1) by omega] using inner

theorem arbitrary_tower_has_exact_depth_threshold
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n budget : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id actual) :
    evaluateClosedSourceExpression? budget o names captured store (tower span name annotation returns n) =
      if 2*n+1≤budget then some (actual,store) else none := towerRun _ _ _ _ _ _ _ _ _ _ _ _ named found

theorem independent_original_tower_is_eventually_found
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id actual) :
    E o names captured store (tower span name annotation returns n) actual store ∧
      ∃ required, ∀ budget, required≤budget →
        evaluateClosedSourceExpression? budget o names captured store (tower span name annotation returns n) = some (actual,store) := by
  have independent := towerPath o span name annotation returns n names captured store id actual named found
  exact ⟨independent,evaluateClosedSourceExpression?_eventually_complete independent⟩

theorem direct_computation_at_the_threshold_supplies_soundness
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id actual) :
    E o names captured store (tower span name annotation returns n) actual store := by
  have computed := towerRun o span name annotation returns n (2*n+1) names captured store id actual named found
  exact evaluateClosedSourceExpression?_sound (by simpa only [Nat.le_refl,↓reduceIte] using computed)

theorem saved_owner_and_capture_only_collision_keep_the_exact_call_threshold
    (span : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (n budget : Nat) (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (oldId f x : Resolved.LocalId)
    (different : f≠x) (old collision actual : RuntimeValue) (store : List RuntimeValue) :
    let savedNames := (name.value,oldId)::names
    let rows := (Resolved.freshLocalId saved (savedNames.map Prod.snd),collision)::(oldId,old)::captured
    E caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved savedNames rows) actual callerSuffix)
      store (call span) actual store ∧
    evaluateClosedSourceExpression? budget caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved savedNames rows) actual callerSuffix)
      store (call span) = if 2*n+3≤budget then some (actual,store) else none :=
  ⟨invoke _ _ _ _ _ _ _ _ _ _ _ _ _ different _ _,
    invokeRun _ _ _ _ _ _ _ _ _ _ _ _ _ _ different _ _⟩

theorem a_returned_higher_order_closure_eventually_uses_its_saved_capture
    (span : Syntax.SourceSpan) (parameter selected : Syntax.Identifier)
    (notParameter : parameter.value≠selected.value) (annotation returns : Option Syntax.TypeExpr)
    (n : Nat) (caller saved : Resolved.DeclarationId) (savedNames callerTail : LocalNameTable)
    (savedValues callerSuffix : Resolved.LocalScope RuntimeValue) (f x selectedId : Resolved.LocalId)
    (different : f≠x) (argument result : RuntimeValue) (store : List RuntimeValue)
    (named : LocalNameTable.Lookup savedNames selected.value selectedId)
    (found : Resolved.LocalScope.Lookup savedValues selectedId result) :
    let original := lambda span parameter annotation returns (returned span (ref span selected))
    let ns := callerNames f x callerTail
    let es := callerValues f x (.sourceClosure original saved savedNames savedValues) argument callerSuffix
    let expression := app span (tower span ⟨span,"f"⟩ annotation returns n) (ref span ⟨span,"argument"⟩)
    E caller ns es store expression result store ∧ ∃ required, ∀ budget, required≤budget →
      evaluateClosedSourceExpression? budget caller ns es store expression = some (result,store) := by
  dsimp only
  have independent : E caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span parameter annotation returns (returned span (ref span selected)))
        saved savedNames savedValues) argument callerSuffix) store
      (app span (tower span ⟨span,"f"⟩ annotation returns n) (ref span ⟨span,"argument"⟩)) result store := by
    apply ClosedSourceExpressionEvaluates.call (shape _ _ _ _ _)
    · exact towerPath _ _ _ _ _ _ _ _ _ _ _ .head .head
    · exact .reference (.tail (by change "f" ≠ "argument"; decide) .head) (.tail different .head)
    · exact .expression (.reference (.tail notParameter named) (.tail (freshNe named) found))
  exact ⟨independent,evaluateClosedSourceExpression?_eventually_complete independent⟩

end Tests.FrontendClosedSourceCallRunner
