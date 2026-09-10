import Solcore.Frontend.SourceLambdaEvaluationProperties
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Resolved.LocalScopeProperties

/-! These independently supplied callbacks only read original local references and
return through explicit blocks. They are not a closed source-language evaluator.
Mixed values, duplicate rows and raw stores need no typing or Core projection. -/
set_option autoImplicit false
namespace Tests.FrontendSourceLambdaEvaluation
open Solcore Solcore.Frontend

private inductive Child (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) :
    List RuntimeValue → Syntax.Expr → RuntimeValue → List RuntimeValue → Prop where
  | reference {store : List RuntimeValue} {span : Syntax.SourceSpan}
      {name : Syntax.Identifier} {id : Resolved.LocalId} {value : RuntimeValue}
      (named : LocalNameTable.Lookup names name.value id)
      (found : Resolved.LocalScope.Lookup captured id value) :
      Child owner names captured store ⟨span,.identifier name⟩ value store
private inductive Body (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) :
    List RuntimeValue → Syntax.Block → RuntimeValue → List RuntimeValue → Prop where
  | returned {store : List RuntimeValue} {span : Syntax.SourceSpan}
      {source : Syntax.Expr} {value : RuntimeValue}
      (evaluated : Child owner names captured store source value store) :
      Body owner names captured store ⟨span,[⟨span,.returnStmt (some source)⟩]⟩ value store
  | block {store : List RuntimeValue} {span : Syntax.SourceSpan}
      {statements : List Syntax.Statement} {value : RuntimeValue}
      (evaluated : Body owner names captured store ⟨span,statements⟩ value store) :
      Body owner names captured store ⟨span,[⟨span,.block statements⟩]⟩ value store
private theorem childDet {o names captured store source value final other otherStore}
    (first : Child o names captured store source value final)
    (second : Child o names captured store source other otherStore) :
    value=other ∧ final=otherStore := by
  cases first with
  | reference named found =>
      cases second with
      | reference otherNamed otherFound =>
          cases named.id_unique otherNamed
          exact ⟨found.value_unique otherFound,rfl⟩
private theorem bodyDet {o names captured store source value final other otherStore}
    (first : Body o names captured store source value final)
    (second : Body o names captured store source other otherStore) :
    value=other ∧ final=otherStore := by
  induction first with
  | returned evaluated => cases second with | returned other => exact childDet evaluated other
  | block evaluated ih => cases second with | block other => exact ih other

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def returned (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Nat → Syntax.Block
  | 0 => ⟨span,[⟨span,.returnStmt (some (reference span name))⟩]⟩
  | n+1 => ⟨span,[⟨span,.block (returned span name n).value⟩]⟩
private theorem returnedPath (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (o : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) (n : Nat) :
    Body o names captured store (returned span name n) value store := by
  induction n with
  | zero => exact .returned (.reference named found)
  | succ n ih => cases n <;> exact .block ih
private def lambda (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr :=
  ⟨span,.lambda span ⟨span,[⟨name.span,match annotation with
    | none => .inferred name | some type => .typed none name type⟩]⟩ returns body⟩
private theorem originalShape (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (body : Syntax.Block) :
    SourceUnaryLambdaShape (lambda span name annotation returns body) name body := by
  cases annotation <;> first | exact .inferred | exact .typed
private def call (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span,.call (reference span ⟨span,"f"⟩) ⟨span,[reference span ⟨span,"argument"⟩]⟩⟩
private def callerNames (f x : Resolved.LocalId) (tail : LocalNameTable) : LocalNameTable :=
  ("f",f)::("argument",x)::tail
private def callerValues (f x : Resolved.LocalId) (closure argument : RuntimeValue)
    (tail : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  (f,closure)::(x,argument)::tail
private theorem invoke (span : Syntax.SourceSpan) (caller saved : Resolved.DeclarationId)
    (names callerTail : LocalNameTable) (captured callerSuffix : Resolved.LocalScope RuntimeValue)
    (f x : Resolved.LocalId) (different : f≠x) (store : List RuntimeValue)
    (source : Syntax.Expr) (name : Syntax.Identifier) (body : Syntax.Block)
    (argument result : RuntimeValue) (shape : SourceUnaryLambdaShape source name body)
    (path : Body saved ((name.value,Resolved.freshLocalId saved (names.map Prod.snd))::names)
      ((Resolved.freshLocalId saved (names.map Prod.snd),argument)::captured) store body result store) :
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure source saved names captured) argument callerSuffix)
      store (call span) result store :=
  .call shape (.reference .head .head)
    (.reference (.tail (by change "f" ≠ "argument"; decide) .head) (.tail different .head)) path
private theorem freshNe {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {spelling : String} {id : Resolved.LocalId} (named : LocalNameTable.Lookup names spelling id) :
    Resolved.freshLocalId owner (names.map Prod.snd) ≠ id := by
  intro equal
  have member : id ∈ names.map Prod.snd := List.mem_map_of_mem named.mem
  exact Resolved.freshLocalId_not_mem owner _ (equal ▸ member)

theorem original_creation_retains_every_row_and_uninterpreted_annotation
    (span : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (body : Syntax.Block) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) :
    sourceUnaryLambdaShape? (lambda span name annotation returns body)=some (name,body) ∧
    SourceLambdaEvaluates Child Body owner names captured store (lambda span name annotation returns body)
      (.sourceClosure (lambda span name annotation returns body) owner names captured) store := by
  have shape := originalShape span name annotation returns body
  exact ⟨sourceUnaryLambdaShape?_iff.mpr shape,.creation shape⟩
theorem creation_iff_preserves_the_whole_original_source_and_actual_store
    (span : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (body : Syntax.Block) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store final : List RuntimeValue) (value : RuntimeValue) :
    SourceLambdaEvaluates Child Body owner names captured store (lambda span name annotation returns body) value final ↔
      value=.sourceClosure (lambda span name annotation returns body) owner names captured ∧ final=store :=
  SourceLambdaEvaluates.creation_iff (originalShape span name annotation returns body)

theorem arbitrary_depth_parameter_shadow_returns_the_actual_mixed_argument
    (span : Syntax.SourceSpan) (parameter : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (n : Nat) (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (f x : Resolved.LocalId) (different : f≠x)
    (store : List RuntimeValue) (argument : RuntimeValue) :
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span parameter annotation returns (returned span parameter n))
        saved names captured) argument callerSuffix) store (call span) argument store :=
  invoke span caller saved names callerTail captured callerSuffix f x different store _ _ _ argument argument
    (originalShape _ _ _ _ _) (returnedPath _ _ _ _ _ _ _ _ .head .head n)

theorem captured_reference_uses_saved_rows_not_the_caller_scope
    (span : Syntax.SourceSpan) (parameter selected : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (notParameter : parameter.value≠selected.value)
    (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (f x id : Resolved.LocalId) (different : f≠x)
    (store : List RuntimeValue) (argument result : RuntimeValue)
    (named : LocalNameTable.Lookup names selected.value id) (found : Resolved.LocalScope.Lookup captured id result) :
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span parameter annotation returns (returned span selected n))
        saved names captured) argument callerSuffix) store (call span) result store :=
  invoke span caller saved names callerTail captured callerSuffix f x different store _ _ _ argument result
    (originalShape _ _ _ _ _) (returnedPath _ _ _ _ _ _ _ _
      (.tail notParameter named) (.tail (freshNe named) found) n)

theorem all_successful_reference_callback_runs_are_value_and_store_deterministic
    {owner names captured store source left leftStore right rightStore}
    (first : SourceLambdaEvaluates Child Body owner names captured store source left leftStore)
    (second : SourceLambdaEvaluates Child Body owner names captured store source right rightStore) :
    left=right ∧ leftStore=rightStore :=
  SourceLambdaEvaluates.deterministic (ChildEval := Child) (BodyEval := Body)
    (fun a b => childDet a b) (fun a b => bodyDet a b) first second

theorem actual_calls_expose_the_saved_scope_and_all_three_store_edges
    {owner names captured store span result final}
    (evaluated : SourceLambdaEvaluates Child Body owner names captured store (call span) result final) :
    ∃ source saved savedNames savedCaptured parameter body calleeStore argument argumentStore,
      SourceUnaryLambdaShape source parameter body ∧
      Child owner names captured store (reference span ⟨span,"f"⟩)
        (.sourceClosure source saved savedNames savedCaptured) calleeStore ∧
      Child owner names captured calleeStore (reference span ⟨span,"argument"⟩) argument argumentStore ∧
      Body saved ((parameter.value,Resolved.freshLocalId saved (savedNames.map Prod.snd))::savedNames)
        ((Resolved.freshLocalId saved (savedNames.map Prod.snd),argument)::savedCaptured)
        argumentStore body result final := SourceLambdaEvaluates.call_iff.mp evaluated

theorem environment_only_fresh_collision_keeps_both_literal_rows_but_selects_argument
    (span : Syntax.SourceSpan) (parameter : Syntax.Identifier) (n : Nat)
    (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (f x : Resolved.LocalId) (different : f≠x)
    (store : List RuntimeValue) (argument old : RuntimeValue) :
    let fresh := Resolved.freshLocalId saved (names.map Prod.snd)
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span parameter none none (returned span parameter n))
        saved names ((fresh,old)::captured)) argument callerSuffix) store (call span) argument store ∧
    Resolved.LocalScope.Lookup ((fresh,argument)::(fresh,old)::captured) fresh argument ∧
    ((fresh,argument)::(fresh,old)::captured).tail=(fresh,old)::captured ∧
    fresh.owner=saved ∧ fresh∉names.map Prod.snd := by
  dsimp only
  exact ⟨arbitrary_depth_parameter_shadow_returns_the_actual_mixed_argument
    span parameter none none n caller saved names callerTail _ callerSuffix f x different store argument,
    .head,rfl,Resolved.freshLocalId_owner _ _,Resolved.freshLocalId_not_mem _ _⟩

theorem first_captured_duplicate_wins_even_under_arbitrary_unselected_suffix
    (span : Syntax.SourceSpan) (n : Nat) (caller saved : Resolved.DeclarationId)
    (names callerTail : LocalNameTable) (captured callerSuffix : Resolved.LocalScope RuntimeValue)
    (f x id : Resolved.LocalId) (different : f≠x) (store : List RuntimeValue)
    (argument first second : RuntimeValue) :
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span ⟨span,"parameter"⟩ none none
        (returned span ⟨span,"saved"⟩ n)) saved (("saved",id)::("saved",x)::names)
        ((id,first)::(id,second)::captured)) argument callerSuffix) store (call span) first store :=
  captured_reference_uses_saved_rows_not_the_caller_scope span _ _ none none n
    (by change "parameter" ≠ "saved"; decide)
    caller saved _ callerTail _ callerSuffix f x id different store argument first .head .head

theorem source_closure_argument_needs_no_core_projection_to_be_returned
    (span : Syntax.SourceSpan) (parameter : Syntax.Identifier) (n : Nat)
    (caller saved actualOwner : Resolved.DeclarationId) (names callerTail actualNames : LocalNameTable)
    (captured callerSuffix actualCaptured : Resolved.LocalScope RuntimeValue)
    (f x : Resolved.LocalId) (different : f≠x) (store : List RuntimeValue) (actualSource : Syntax.Expr) :
    let actual := RuntimeValue.sourceClosure actualSource actualOwner actualNames actualCaptured
    actual.toCore?=none ∧
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span parameter none none (returned span parameter n))
        saved names captured) actual callerSuffix) store (call span) actual store :=
  ⟨by simp [RuntimeValue.toCore?],arbitrary_depth_parameter_shadow_returns_the_actual_mixed_argument
    span parameter none none n caller saved names callerTail captured callerSuffix f x different store _⟩

private def otherOwner (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  {owner with declarationIndex:=owner.declarationIndex+1}
theorem different_caller_owner_and_foreign_high_ids_preserve_actual_core_closure_argument
    (span : Syntax.SourceSpan) (n high : Nat) (saved foreign : Resolved.DeclarationId)
    (foreignOwner : foreign≠saved) (captured callerSuffix : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (a b : Core.Ty) (core : Core.Expr) (actualCaptures : List RuntimeValue) :
    otherOwner saved≠saved ∧
    Resolved.freshLocalId saved [⟨foreign,high⟩,⟨saved,7⟩]=Resolved.freshLocalId saved [⟨saved,7⟩] ∧
    SourceLambdaEvaluates Child Body (otherOwner saved)
      (callerNames ⟨otherOwner saved,0⟩ ⟨otherOwner saved,1⟩ [])
      (callerValues ⟨otherOwner saved,0⟩ ⟨otherOwner saved,1⟩
        (.sourceClosure (lambda span ⟨span,"p"⟩ none none (returned span ⟨span,"p"⟩ n)) saved
          [("foreign",⟨foreign,high⟩),("p",⟨saved,7⟩)] captured)
        (.coreClosure a b core actualCaptures) callerSuffix) store (call span)
      (.coreClosure a b core actualCaptures) store := by
  refine ⟨?_,?_,?_⟩
  · intro equal
    have index := congrArg Resolved.DeclarationId.declarationIndex equal
    simp [otherOwner] at index
  · exact Resolved.freshLocalId_cons_of_ne_owner saved _ ⟨foreign,high⟩ foreignOwner
  · apply arbitrary_depth_parameter_shadow_returns_the_actual_mixed_argument
    intro equal
    have index := congrArg Resolved.LocalId.binderIndex equal
    cases index

end Tests.FrontendSourceLambdaEvaluation
