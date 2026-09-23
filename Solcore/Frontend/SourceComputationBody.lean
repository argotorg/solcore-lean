import Solcore.Frontend.RuntimeWordMatch
import Solcore.Resolved.FreshIdentity
import Solcore.Frontend.Computation

/-! Source computation-body evaluation and embedding properties. -/

/-!
## Consolidated module: `Solcore.Frontend.SourceComputationBodyEvaluation`
-/

/-! Nine original raw body forms over mixed values with explicit-owner child
evaluation. Annotations and unselected branches are unchecked; no scope guard,
heap snapshot, closed evaluator, execution cost or failure classification is added. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Original successful body rules with actual mixed stores and ordered rows.
Initializers precede binding; branches use current stores without static guards. -/
inductive SourceComputationBodyEvaluates
    (ChildEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
      RuntimeValue → List RuntimeValue → Prop)
    (owner : Resolved.DeclarationId) :
    List (String × Resolved.LocalId) → List (Resolved.LocalId × RuntimeValue) →
    List RuntimeValue → Syntax.Block → RuntimeValue → List RuntimeValue → Prop where
  | bare {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : List RuntimeValue} :
      SourceComputationBodyEvaluates ChildEval owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store
  | expression {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (child : ChildEval owner table environment initialStore source value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore
  | block {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (child : SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore
  | binding {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {boundValue value : RuntimeValue}
      (initializerEvaluation : ChildEval owner table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : SourceComputationBodyEvaluates ChildEval owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore
  | inferred {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {boundValue value : RuntimeValue}
      (initializerEvaluation : ChildEval owner table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : SourceComputationBodyEvaluates ChildEval owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ value finalStore
  | discard {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {discardedValue value : RuntimeValue}
      (expressionEvaluation : ChildEval owner table environment initialStore expression discardedValue middleStore)
      (tailEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment middleStore
        ⟨blockSpan, rest⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ value finalStore
  | ifTrue {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (conditionEvaluation : ChildEval owner table environment initialStore condition (.bool true) middleStore)
      (branchEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment middleStore thenBody value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (conditionEvaluation : ChildEval owner table environment initialStore condition (.bool false) middleStore)
      (branchEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment middleStore elseBody value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

  | wordMatch {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block} {selected : Syntax.Block}
      {initialStore middleStore finalStore : List RuntimeValue} {scrutineeValue value : RuntimeValue} {tests : Nat}
      (scrutineeEvaluation : ChildEval owner table environment initialStore scrutinee scrutineeValue middleStore)
      (choice : RuntimeWordMatchChooses scrutineeValue cases defaultBody selected tests)
      (branchEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment
        middleStore selected value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩
          ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩ value finalStore

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.SourceComputationBodyEvaluationProperties`
-/

/-! Body value/store determinism requires only the fixed owner's child law.
No cost, checking, typing, image or world assumption is used. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Value/store uniqueness follows solely from the fixed owner's child law;
no typing, child completeness, image or execution-cost premise is required. -/
theorem SourceComputationBodyEvaluates.deterministic
    {ChildEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
      RuntimeValue → List RuntimeValue → Prop}
    {owner : Resolved.DeclarationId}
    (childDeterministic : ∀ {table environment initialStore source left right leftStore rightStore},
      ChildEval owner table environment initialStore source left leftStore →
      ChildEval owner table environment initialStore source right rightStore →
      left = right ∧ leftStore = rightStore)
    {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
    {initialStore : List RuntimeValue} {body : Syntax.Block} {left right : RuntimeValue}
    {leftStore rightStore : List RuntimeValue}
    (first : SourceComputationBodyEvaluates ChildEval owner table environment initialStore body left leftStore)
    (second : SourceComputationBodyEvaluates ChildEval owner table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction first generalizing right rightStore with
  | bare => cases second; exact ⟨rfl, rfl⟩
  | expression child =>
      cases second with
      | expression other => exact childDeterministic child other
  | block _ ih =>
      cases second with
      | block other => exact ih other
  | binding initializer _ ih =>
      cases second with
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := childDeterministic initializer otherInitializer
          exact ih otherTail
  | inferred initializer _ ih =>
      cases second with
      | inferred otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := childDeterministic initializer otherInitializer
          exact ih otherTail
  | discard expression _ ih =>
      cases second with
      | discard otherExpression otherTail =>
          obtain ⟨_, rfl⟩ := childDeterministic expression otherExpression
          exact ih otherTail
  | ifTrue condition _ ih =>
      cases second with
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := childDeterministic condition otherCondition
          exact ih otherBranch
      | ifFalse otherCondition _ => cases (childDeterministic condition otherCondition).1
  | ifFalse condition _ ih =>
      cases second with
      | ifTrue otherCondition _ => cases (childDeterministic condition otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := childDeterministic condition otherCondition
          exact ih otherBranch
  | wordMatch scrutinee choice _ ih =>
      cases second with
      | wordMatch otherScrutinee otherChoice otherBranch =>
          obtain ⟨rfl, rfl⟩ := childDeterministic scrutinee otherScrutinee
          obtain ⟨rfl, rfl⟩ := choice.deterministic otherChoice
          exact ih otherBranch

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.SourceComputationBodyEmbeddingProperties`
-/

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
