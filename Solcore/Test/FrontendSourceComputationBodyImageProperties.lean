import Solcore.Frontend.SourceComputationBody
import Solcore.Frontend.SourceLambdaEvaluation
import Solcore.Frontend.LocalReference
import Solcore.Resolved.LocalScope

/-! Independent old/mixed reference callbacks establish the strong all-actual
image contract by first-ID lookup inversion. They do not assume typed rows,
alignment, child determinism, or that actual outputs are already Core images. -/
set_option autoImplicit false
namespace Tests.FrontendSourceComputationBodyImage
open Solcore Solcore.Frontend

private def embedded (environment : Resolved.LocalScope Core.Value) :
    Resolved.LocalScope RuntimeValue :=
  environment.map (fun row => (row.1,RuntimeValue.ofCore row.2))

private inductive OldRef (names : LocalNameTable) (environment : Resolved.LocalScope Core.Value) :
    List Core.Value → Syntax.Expr → Core.Value → List Core.Value → Prop where
  | reference {store : List Core.Value} {span : Syntax.SourceSpan}
      {name : Syntax.Identifier} {id : Resolved.LocalId} {value : Core.Value}
      (named : LocalNameTable.Lookup names name.value id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      OldRef names environment store ⟨span,.identifier name⟩ value store

private inductive ImageRef (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.LocalScope RuntimeValue) :
    List RuntimeValue → Syntax.Expr → RuntimeValue → List RuntimeValue → Prop where
  | reference {store : List RuntimeValue} {span : Syntax.SourceSpan}
      {name : Syntax.Identifier} {id : Resolved.LocalId} {value : RuntimeValue}
      (named : LocalNameTable.Lookup names name.value id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      ImageRef owner names environment store ⟨span,.identifier name⟩ value store

private theorem mapped_lookup_forward {environment : Resolved.LocalScope Core.Value}
    {id : Resolved.LocalId} {value : Core.Value}
    (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup (embedded environment) id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

private theorem mapped_lookup_reflection (environment : Resolved.LocalScope Core.Value)
    {id : Resolved.LocalId} {actual : RuntimeValue}
    (found : Resolved.LocalScope.Lookup (embedded environment) id actual) :
    ∃ value, actual=RuntimeValue.ofCore value ∧ Resolved.LocalScope.Lookup environment id value := by
  induction environment with
  | nil => cases found
  | cons entry rest ih =>
      rcases entry with ⟨candidate,headValue⟩
      cases found with
      | head => exact ⟨headValue,rfl,.head⟩
      | tail different tail =>
          obtain ⟨value,equality,old⟩ := ih tail
          exact ⟨value,equality,.tail different old⟩

private theorem child_forward (owner : Resolved.DeclarationId)
    {names : LocalNameTable} {environment : Resolved.LocalScope Core.Value}
    {store final : List Core.Value} {source : Syntax.Expr} {value : Core.Value}
    (evaluated : OldRef names environment store source value final) :
    ImageRef owner names (embedded environment) (store.map RuntimeValue.ofCore)
      source (RuntimeValue.ofCore value) (final.map RuntimeValue.ofCore) := by
  cases evaluated with
  | reference named found => exact .reference named (mapped_lookup_forward found)

/- The result and final store below are arbitrary mixed data, not assumed images.
Their literal image equalities are obtained by inversion, with no determinism premise. -/
private theorem all_actual_outputs_image_contract (owner : Resolved.DeclarationId)
    {names : LocalNameTable} {environment : Resolved.LocalScope Core.Value}
    {store : List Core.Value} {source : Syntax.Expr}
    {actual : RuntimeValue} {actualFinal : List RuntimeValue} :
    ImageRef owner names (embedded environment) (store.map RuntimeValue.ofCore)
      source actual actualFinal ↔
      ∃ value final, actual=RuntimeValue.ofCore value ∧ actualFinal=final.map RuntimeValue.ofCore ∧
        OldRef names environment store source value final := by
  constructor
  · intro evaluated
    cases evaluated with
    | reference named found =>
        obtain ⟨value,equality,old⟩ := mapped_lookup_reflection environment found
        exact ⟨value,store,equality,rfl,.reference named old⟩
  · rintro ⟨value,final,rfl,rfl,old⟩
    exact child_forward owner old

private def ref (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def spine (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) : Nat → Syntax.Block
  | 0 => ⟨span,[⟨span,.returnStmt (some (ref span name))⟩]⟩
  | n+1 => ⟨span,[⟨name.span,.letDecl name (some annotation) (some (ref span name))⟩,
      ⟨name.span,.letDecl name none (some (ref span name))⟩,
      ⟨span,.expression (ref span name) true⟩,
      ⟨span,.block (spine span name annotation n).value⟩]⟩
private theorem oldPath (o : Resolved.DeclarationId) (span : Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Syntax.TypeExpr) (n : Nat)
    (names : LocalNameTable) (environment : Resolved.LocalScope Core.Value)
    (store : List Core.Value) (id : Resolved.LocalId) (value : Core.Value)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id value) :
    ComputationReturnTreeEvaluates OldRef o names environment store
      (spine span name annotation n) value store := by
  induction n generalizing names environment id with
  | zero => exact .expression (.reference named found)
  | succ n ih =>
      apply ComputationReturnTreeEvaluates.binding (.reference named found)
      apply ComputationReturnTreeEvaluates.inferred (.reference .head .head)
      apply ComputationReturnTreeEvaluates.discard (.reference .head .head)
      cases n <;> exact .block (ih _ _ _ .head .head)
private theorem mixedPath (o : Resolved.DeclarationId) (span : Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Syntax.TypeExpr) (n : Nat)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id value) :
    SourceComputationBodyEvaluates ImageRef o names environment store
      (spine span name annotation n) value store := by
  induction n generalizing names environment id with
  | zero => exact .expression (.reference named found)
  | succ n ih =>
      apply SourceComputationBodyEvaluates.binding (.reference named found)
      apply SourceComputationBodyEvaluates.inferred (.reference .head .head)
      apply SourceComputationBodyEvaluates.discard (.reference .head .head)
      cases n <;> exact .block (ih _ _ _ .head .head)

theorem original_and_mixed_shadow_paths_are_independent
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (tail : Resolved.LocalScope Core.Value) (store : List Core.Value)
    (id : Resolved.LocalId) (value ignored : Core.Value) :
    let names' := (name.value,id)::names
    let environment := (id,value)::(id,ignored)::tail
    ComputationReturnTreeEvaluates OldRef o names' environment store
      (spine span name annotation n) value store ∧
    SourceComputationBodyEvaluates ImageRef o names' (embedded environment)
      (store.map RuntimeValue.ofCore) (spine span name annotation n)
      (RuntimeValue.ofCore value) (store.map RuntimeValue.ofCore) :=
  ⟨oldPath _ _ _ _ _ _ _ _ _ _ .head .head,
    mixedPath _ _ _ _ _ _ _ _ _ _ .head .head⟩

/- Unlike an endpoint-only agreement, this law recovers both images from arbitrary
actual outputs. The independently proved callback contract has no such premises. -/
theorem all_actual_body_outputs_factor_through_the_original_relation
    (o : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.LocalScope Core.Value) (store : List Core.Value)
    (body : Syntax.Block) (actual : RuntimeValue) (actualFinal : List RuntimeValue) :
    SourceComputationBodyEvaluates ImageRef o names (embedded environment)
      (store.map RuntimeValue.ofCore) body actual actualFinal ↔
    ∃ value final, actual=RuntimeValue.ofCore value ∧ actualFinal=final.map RuntimeValue.ofCore ∧
      ComputationReturnTreeEvaluates OldRef o names environment store body value final :=
  sourceComputationBodyEvaluates_ofCore_inputs_iff (all_actual_outputs_image_contract o)

theorem each_literal_old_endpoint_has_exactly_its_original_derivations
    (o : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.LocalScope Core.Value) (store final : List Core.Value)
    (body : Syntax.Block) (value : Core.Value) :
    SourceComputationBodyEvaluates ImageRef o names (embedded environment)
      (store.map RuntimeValue.ofCore) body (RuntimeValue.ofCore value)
      (final.map RuntimeValue.ofCore) ↔
    ComputationReturnTreeEvaluates OldRef o names environment store body value final := by
  constructor
  · intro evaluated
    obtain ⟨oldValue,oldFinal,sameValue,sameFinal,old⟩ :=
      (all_actual_body_outputs_factor_through_the_original_relation o names environment store body _ _).mp evaluated
    have same := RuntimeValue.ofCore_injective sameValue
    subst oldValue
    have sameStores : final=oldFinal :=
      (List.map_inj_right (fun _ _ equal => RuntimeValue.ofCore_injective equal)).mp sameFinal
    subst oldFinal
    exact old
  · intro old
    exact (all_actual_body_outputs_factor_through_the_original_relation o names environment store body _ _).mpr
      ⟨value,final,rfl,rfl,old⟩

/- An opt-in extension may create source closures. Only the one-way body law is
applied to this callback; we do not assert the strong image contract for it. -/
private def Extended (o : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (source : Syntax.Expr) (value : RuntimeValue) (final : List RuntimeValue) : Prop :=
  ImageRef o names environment store source value final ∨
    SourceLambdaEvaluates (fun _ _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ => False)
      o names environment store source value final

theorem source_creating_extension_preserves_every_old_body_derivation
    {o : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.LocalScope Core.Value} {store final : List Core.Value}
    {body : Syntax.Block} {value : Core.Value}
    (old : ComputationReturnTreeEvaluates OldRef o names environment store body value final) :
    SourceComputationBodyEvaluates Extended o names (embedded environment)
      (store.map RuntimeValue.ofCore) body (RuntimeValue.ofCore value) (final.map RuntimeValue.ofCore) :=
  SourceComputationBodyEvaluates.ofCore (fun child => Or.inl (child_forward o child)) old

theorem extension_also_returns_new_source_closures_without_projecting_them
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (names : LocalNameTable)
    (environment : Resolved.LocalScope Core.Value) (store : List Core.Value)
    (source : Syntax.Expr) (name : Syntax.Identifier) (body : Syntax.Block)
    (shape : SourceUnaryLambdaShape source name body) :
    let closure := RuntimeValue.sourceClosure source o names (embedded environment)
    SourceComputationBodyEvaluates Extended o names (embedded environment)
      (store.map RuntimeValue.ofCore) ⟨span,[⟨span,.returnStmt (some source)⟩]⟩
      closure (store.map RuntimeValue.ofCore) ∧ closure.toCore?=none :=
  ⟨.expression (Or.inr (.creation shape)),by simp only [RuntimeValue.toCore?]⟩

end Tests.FrontendSourceComputationBodyImage
