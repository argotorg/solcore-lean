import Solcore.Frontend.SourceComputationBodyEvaluationProperties
import Solcore.Frontend.ComputationReturnTreeEvaluation

/-! One-way child embedding permits extra mixed behavior. Exact reflection needs
all actual mixed child outputs/stores to factor through the old image; endpoint-only
image agreement is insufficient. This is not full enriched-language conservativity. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {OldChild : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr →
  Core.Value → Core.Store → Prop}
variable {MixedChild : Resolved.DeclarationId → LocalNameTable →
  List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
  RuntimeValue → List RuntimeValue → Prop}
variable {owner : Resolved.DeclarationId}

/-- Embed each old body derivation under a one-way child embedding law.
The mixed child may have additional successful behavior outside the old image. -/
theorem SourceComputationBodyEvaluates.ofCore
    (childEmbed : ∀ {table environment initialStore source value finalStore},
      OldChild table environment initialStore source value finalStore →
      MixedChild owner table
        (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
        (initialStore.map RuntimeValue.ofCore) source (RuntimeValue.ofCore value)
        (finalStore.map RuntimeValue.ofCore))
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ComputationReturnTreeEvaluates OldChild owner table environment
      initialStore body value finalStore) :
    SourceComputationBodyEvaluates MixedChild owner table
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) body (RuntimeValue.ofCore value)
      (finalStore.map RuntimeValue.ofCore) := by
  induction evaluation with
  | bare => simp only [RuntimeValue.ofCore]; exact .bare
  | expression child => exact .expression (childEmbed child)
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding (childEmbed initializer) ih
  | inferred initializer _ ih => exact .inferred (childEmbed initializer) ih
  | discard child _ ih => exact .discard (childEmbed child) ih
  | ifTrue child _ ih =>
      exact .ifTrue (by simpa only [RuntimeValue.ofCore] using childEmbed child) ih
  | ifFalse child _ ih =>
      exact .ifFalse (by simpa only [RuntimeValue.ofCore] using childEmbed child) ih
  | wordMatch child choice _ ih =>
      exact .wordMatch (childEmbed child) (runtimeWordMatchChooses_ofCore_iff.mpr choice) ih

private theorem body_reflect
    (childExact : ∀ {table environment initialStore source mixedValue mixedFinal},
      MixedChild owner table
        (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
        (initialStore.map RuntimeValue.ofCore) source mixedValue mixedFinal ↔
      ∃ value finalStore,
        mixedValue = RuntimeValue.ofCore value ∧
        mixedFinal = finalStore.map RuntimeValue.ofCore ∧
        OldChild table environment initialStore source value finalStore)
    {table : LocalNameTable} {mixedEnvironment : List (Resolved.LocalId × RuntimeValue)}
    {mixedInitial mixedFinal : List RuntimeValue} {body : Syntax.Block} {mixedValue : RuntimeValue}
    (evaluation : SourceComputationBodyEvaluates MixedChild owner table mixedEnvironment
      mixedInitial body mixedValue mixedFinal) :
    ∀ (environment : Resolved.Environment) (initialStore : Core.Store),
      mixedEnvironment = environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)) →
      mixedInitial = initialStore.map RuntimeValue.ofCore →
      ∃ value finalStore,
        mixedValue = RuntimeValue.ofCore value ∧
        mixedFinal = finalStore.map RuntimeValue.ofCore ∧
        ComputationReturnTreeEvaluates OldChild owner table environment initialStore body value finalStore := by
  induction evaluation with
  | bare =>
      intro environment initialStore environmentSame storeSame
      exact ⟨.unit, initialStore, by simp only [RuntimeValue.ofCore], storeSame, .bare⟩
  | expression child =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨value, finalStore, valueSame, finalSame, oldChild⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ child)
      exact ⟨value, finalStore, valueSame, finalSame, .expression oldChild⟩
  | block _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨value, finalStore, valueSame, finalSame, oldBody⟩ :=
        ih environment initialStore environmentSame storeSame
      exact ⟨value, finalStore, valueSame, finalSame, .block oldBody⟩
  | binding initializer _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨bound, middleStore, boundSame, middleSame, oldInitializer⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ initializer)
      obtain ⟨value, finalStore, valueSame, finalSame, oldTail⟩ :=
        ih ((_, bound) :: environment) middleStore
          (by rw [environmentSame, boundSame]; rfl) middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .binding oldInitializer oldTail⟩
  | inferred initializer _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨bound, middleStore, boundSame, middleSame, oldInitializer⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ initializer)
      obtain ⟨value, finalStore, valueSame, finalSame, oldTail⟩ :=
        ih ((_, bound) :: environment) middleStore
          (by rw [environmentSame, boundSame]; rfl) middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .inferred oldInitializer oldTail⟩
  | discard child _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨discarded, middleStore, discardedSame, middleSame, oldChild⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ child)
      obtain ⟨value, finalStore, valueSame, finalSame, oldTail⟩ :=
        ih environment middleStore environmentSame middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .discard oldChild oldTail⟩
  | ifTrue child _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨condition, middleStore, conditionSame, middleSame, oldChild⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ child)
      have actualBool : Core.Value.bool true = condition := RuntimeValue.ofCore_injective
        (by simpa only [RuntimeValue.ofCore] using conditionSame)
      cases actualBool
      obtain ⟨value, finalStore, valueSame, finalSame, oldBranch⟩ :=
        ih environment middleStore environmentSame middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .ifTrue oldChild oldBranch⟩
  | ifFalse child _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨condition, middleStore, conditionSame, middleSame, oldChild⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ child)
      have actualBool : Core.Value.bool false = condition := RuntimeValue.ofCore_injective
        (by simpa only [RuntimeValue.ofCore] using conditionSame)
      cases actualBool
      obtain ⟨value, finalStore, valueSame, finalSame, oldBranch⟩ :=
        ih environment middleStore environmentSame middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .ifFalse oldChild oldBranch⟩
  | wordMatch child choice _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨scrutinee, middleStore, scrutineeSame, middleSame, oldChild⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ child)
      have oldChoice := runtimeWordMatchChooses_ofCore_iff.mp (scrutineeSame ▸ choice)
      obtain ⟨value, finalStore, valueSame, finalSame, oldBranch⟩ :=
        ih environment middleStore environmentSame middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .wordMatch oldChild oldChoice oldBranch⟩

/-- Exact image reflection quantifies over every actual mixed result and store.
Its stronger child premise is not generally satisfied by source-creating extensions;
old-image endpoint agreement alone cannot recover discarded intermediate values. -/
theorem sourceComputationBodyEvaluates_ofCore_inputs_iff
    (childExact : ∀ {table environment initialStore source mixedValue mixedFinal},
      MixedChild owner table
        (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
        (initialStore.map RuntimeValue.ofCore) source mixedValue mixedFinal ↔
      ∃ value finalStore,
        mixedValue = RuntimeValue.ofCore value ∧
        mixedFinal = finalStore.map RuntimeValue.ofCore ∧
        OldChild table environment initialStore source value finalStore)
    {table : LocalNameTable} {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {mixedValue : RuntimeValue} {mixedFinal : List RuntimeValue} :
    SourceComputationBodyEvaluates MixedChild owner table
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) body mixedValue mixedFinal ↔
    ∃ value finalStore,
      mixedValue = RuntimeValue.ofCore value ∧
      mixedFinal = finalStore.map RuntimeValue.ofCore ∧
      ComputationReturnTreeEvaluates OldChild owner table environment initialStore body value finalStore := by
  constructor
  · intro evaluated
    exact body_reflect childExact evaluated environment initialStore rfl rfl
  · rintro ⟨value, finalStore, rfl, rfl, oldBody⟩
    exact SourceComputationBodyEvaluates.ofCore
      (fun child => childExact.mpr ⟨_, _, rfl, rfl, child⟩) oldBody

end Solcore.Frontend
