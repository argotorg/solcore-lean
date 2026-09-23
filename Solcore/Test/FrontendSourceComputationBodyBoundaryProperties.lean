import Solcore.Frontend.SourceLambdaEvaluation
import Solcore.Frontend.RuntimeValue
import Solcore.Frontend.Computation
import Solcore.Frontend.SourceComputationBody

/-! A real source-lambda callback can discard a non-Core intermediate value.
These independent boundary witnesses do not define a closed expression evaluator. -/

set_option autoImplicit false

open Solcore

namespace Tests.MixedBodyBoundaries

private def NoOld : Frontend.LocalNameTable → Resolved.Environment → Core.Store →
    Syntax.Expr → Core.Value → Core.Store → Prop := fun _ _ _ _ _ _ => False

private def NoChild : Resolved.DeclarationId → List (String × Resolved.LocalId) →
    List (Resolved.LocalId × Frontend.RuntimeValue) → List Frontend.RuntimeValue →
    Syntax.Expr → Frontend.RuntimeValue → List Frontend.RuntimeValue → Prop :=
  fun _ _ _ _ _ _ _ => False

private def NoBody : Resolved.DeclarationId → List (String × Resolved.LocalId) →
    List (Resolved.LocalId × Frontend.RuntimeValue) → List Frontend.RuntimeValue →
    Syntax.Block → Frontend.RuntimeValue → List Frontend.RuntimeValue → Prop :=
  fun _ _ _ _ _ _ _ => False

private abbrev LambdaChild := Frontend.SourceLambdaEvaluates NoChild NoBody

/-- This is the existing raw lambda judgment, with genuinely empty callbacks. -/
theorem actual_lambda_child_is_deterministic
    {owner names captured store source left leftStore right rightStore}
    (first : LambdaChild owner names captured store source left leftStore)
    (second : LambdaChild owner names captured store source right rightStore) :
    left = right ∧ leftStore = rightStore :=
  Frontend.SourceLambdaEvaluates.deterministic
    (ChildEval := NoChild) (BodyEval := NoBody)
    (fun impossible _ => False.elim impossible)
    (fun impossible _ => False.elim impossible) first second

/-- Agreement checked only at old-image outputs misses every source creation. -/
theorem lambda_child_agrees_with_empty_old_child_on_embedded_outputs
    (owner : Resolved.DeclarationId) (names : Frontend.LocalNameTable)
    (captured : Resolved.Environment) (store finalStore : Core.Store)
    (source : Syntax.Expr) (value : Core.Value) :
    LambdaChild owner names
      (captured.map fun row => (row.1, Frontend.RuntimeValue.ofCore row.2))
      (store.map Frontend.RuntimeValue.ofCore) source
      (Frontend.RuntimeValue.ofCore value) (finalStore.map Frontend.RuntimeValue.ofCore) ↔
      NoOld names captured store source value finalStore := by
  constructor
  · intro evaluated
    generalize embedded : Frontend.RuntimeValue.ofCore value = mixed at evaluated
    generalize finalImage : finalStore.map Frontend.RuntimeValue.ofCore = actualFinal at evaluated
    cases evaluated with
    | creation shape =>
        have projected := Frontend.RuntimeValue.toCore?_ofCore value
        rw [embedded] at projected
        simp only [Frontend.RuntimeValue.toCore?, reduceCtorEq] at projected
    | call shape callee argument body => exact False.elim callee
  · exact False.elim

/-- Creation really occurs from arbitrary old inputs, outside every old value image. -/
theorem actual_source_creation_has_no_old_result_preimage
    (owner : Resolved.DeclarationId) (names : Frontend.LocalNameTable)
    (captured : Resolved.Environment) (store : Core.Store)
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : Frontend.SourceUnaryLambdaShape source name body) :
    ∃ mixed,
      LambdaChild owner names
        (captured.map fun row => (row.1, Frontend.RuntimeValue.ofCore row.2))
        (store.map Frontend.RuntimeValue.ofCore) source mixed
        (store.map Frontend.RuntimeValue.ofCore) ∧
      ∀ old : Core.Value, mixed ≠ Frontend.RuntimeValue.ofCore old := by
  refine ⟨_, .creation shape, ?_⟩
  intro old equality
  have projected := Frontend.RuntimeValue.toCore?_ofCore old
  rw [← equality] at projected
  simp only [Frontend.RuntimeValue.toCore?, reduceCtorEq] at projected

/-- The old relation cannot discard an expression without its old child evidence. -/
theorem empty_old_child_prevents_discard_then_bare
    (owner : Resolved.DeclarationId) (names : Frontend.LocalNameTable)
    (captured : Resolved.Environment) (store finalStore : Core.Store)
    (blockSpan statementSpan returnSpan : Syntax.SourceSpan)
    (source : Syntax.Expr) (value : Core.Value) :
    ¬ Frontend.ComputationReturnTreeEvaluates NoOld owner names captured store
      ⟨blockSpan, [⟨statementSpan, .expression source true⟩, ⟨returnSpan, .returnStmt none⟩]⟩
      value finalStore := by
  intro evaluated
  cases evaluated with
  | discard child tail => exact False.elim child

/-- Discard hides a genuine newly created closure, leaving literal old-image endpoints. -/
theorem discarding_actual_source_creation_returns_embedded_unit
    (owner : Resolved.DeclarationId) (names : Frontend.LocalNameTable)
    (captured : Resolved.Environment) (store : Core.Store)
    (blockSpan statementSpan returnSpan : Syntax.SourceSpan)
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : Frontend.SourceUnaryLambdaShape source name body) :
    Frontend.SourceComputationBodyEvaluates LambdaChild owner names
      (captured.map fun row => (row.1, Frontend.RuntimeValue.ofCore row.2))
      (store.map Frontend.RuntimeValue.ofCore)
      ⟨blockSpan, [⟨statementSpan, .expression source true⟩, ⟨returnSpan, .returnStmt none⟩]⟩
      (Frontend.RuntimeValue.ofCore .unit) (store.map Frontend.RuntimeValue.ofCore) := by
  simpa only [Frontend.RuntimeValue.ofCore] using
    (Frontend.SourceComputationBodyEvaluates.discard
      (Frontend.SourceLambdaEvaluates.creation shape) Frontend.SourceComputationBodyEvaluates.bare)

/-- A uniform exact body image law exposes the strong child condition through return. -/
theorem uniform_actual_body_image_exactness_forces_child_image_exactness
    {OldChild : Frontend.LocalNameTable → Resolved.Environment → Core.Store →
      Syntax.Expr → Core.Value → Core.Store → Prop}
    {MixedChild : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × Frontend.RuntimeValue) → List Frontend.RuntimeValue →
      Syntax.Expr → Frontend.RuntimeValue → List Frontend.RuntimeValue → Prop}
    (owner : Resolved.DeclarationId) (names : Frontend.LocalNameTable)
    (captured : Resolved.Environment) (store : Core.Store)
    (span : Syntax.SourceSpan)
    (bodyExact : ∀ body value finalStore,
      Frontend.SourceComputationBodyEvaluates MixedChild owner names
        (captured.map fun row => (row.1, Frontend.RuntimeValue.ofCore row.2))
        (store.map Frontend.RuntimeValue.ofCore) body value finalStore ↔
      ∃ oldValue oldStore, value = Frontend.RuntimeValue.ofCore oldValue ∧
        finalStore = oldStore.map Frontend.RuntimeValue.ofCore ∧
        Frontend.ComputationReturnTreeEvaluates OldChild owner names captured store
          body oldValue oldStore)
    (source : Syntax.Expr) (value : Frontend.RuntimeValue)
    (finalStore : List Frontend.RuntimeValue) :
    MixedChild owner names
      (captured.map fun row => (row.1, Frontend.RuntimeValue.ofCore row.2))
      (store.map Frontend.RuntimeValue.ofCore) source value finalStore ↔
      ∃ oldValue oldStore, value = Frontend.RuntimeValue.ofCore oldValue ∧
        finalStore = oldStore.map Frontend.RuntimeValue.ofCore ∧
        OldChild names captured store source oldValue oldStore := by
  constructor
  · intro child
    obtain ⟨oldValue, oldStore, resultImage, storeImage, oldBody⟩ :=
      (bodyExact ⟨span, [⟨span, .returnStmt (some source)⟩]⟩ value finalStore).mp
        (.expression child)
    cases oldBody with
    | expression oldChild => exact ⟨oldValue, oldStore, resultImage, storeImage, oldChild⟩
  · rintro ⟨oldValue, oldStore, resultImage, storeImage, oldChild⟩
    have mixedBody :=
      (bodyExact ⟨span, [⟨span, .returnStmt (some source)⟩]⟩ value finalStore).mpr
        ⟨oldValue, oldStore, resultImage, storeImage, .expression oldChild⟩
    cases mixedBody with
    | expression child => exact child

end Tests.MixedBodyBoundaries
