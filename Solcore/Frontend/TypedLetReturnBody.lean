import Solcore.Frontend.TerminalReturnTree
import Solcore.Frontend.TypeName
import Solcore.Frontend.LocalTypeInputs
import Solcore.Resolved.FreshIdentity
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.Machine
import Solcore.Core.FuelResumptionProperties

/-! A separate value-free adapter for annotated, initialized, non-shadowing
local declarations followed by an existing terminal return tree. Rejection
is specific to this adapter; no general source binding policy is introduced. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Consume the original prefix in order. Each initializer uses the old scope;
the tail is already lowered under its new binder, so it needs no weakening. -/
def elaborateTypedLetReturnBody? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body with
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ =>
      if name.value ∉ inputs.names.map Prod.fst then do
        let declaredType ← interpretTypeName? types annotation
        let (initializerCore, initializerType) ←
          elaborateLocalExpression? inputs.names inputs.context initializer
        if initializerType = declaredType then do
          let (tailCore, returnType) ← elaborateTypedLetReturnBody? types owner
            (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
          return (.letE initializerCore tailCore, returnType)
        else none
      else none
  | _ => elaborateTerminalReturnTree? inputs.names inputs.context body
termination_by body.value.length

inductive TypedLetReturnBodyHasType (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Ty → Prop where
  | terminal {inputs : LocalTypeInputs} {body : Syntax.Block} {type : Core.Ty}
      (child : TerminalReturnTreeHasType inputs.names inputs.context body type) :
      TypedLetReturnBodyHasType types owner inputs body type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty}
      (meaning : TypeNameDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerTyping : LocalExpressionHasType inputs.names inputs.context initializer declaredType)
      (tailTyping : TypedLetReturnBodyHasType types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ returnType) :
      TypedLetReturnBodyHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ returnType

/-- Independent exact source provenance, with annotation meaning and all three
initializer obligations separate from the elaborated remaining statements. -/
inductive TypedLetReturnBodyElaborates (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Expr → Core.Ty → Prop where
  | terminal {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (child : TerminalReturnTreeElaborates inputs.names inputs.context body core type) :
      TypedLetReturnBodyElaborates types owner inputs body core type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty}
      {initializerResolved : Resolved.Expr} {initializerCore tailCore : Core.Expr}
      (meaning : TypeNameDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (resolution : ResolvesLocalExpression inputs.names initializer initializerResolved)
      (lowered : Resolved.Lowers inputs.ids initializerResolved initializerCore)
      (typing : Resolved.HasType inputs.context initializerResolved declaredType)
      (tailElaboration : TypedLetReturnBodyElaborates types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      TypedLetReturnBodyElaborates types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyElaboration`
-/

/-! Exact whole-source provenance characterizes the total typed-prefix checker.
The initializer keeps the old scope and the remaining source keeps its order. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTypedLetReturnBody?_binding_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ =
        some (core, type)) :
    ∃ declaredType initializerCore tailCore,
      name.value ∉ inputs.names.map Prod.fst ∧
      interpretTypeName? types annotation = some declaredType ∧
      elaborateLocalExpression? inputs.names inputs.context initializer = some (initializerCore, declaredType) ∧
      elaborateTypedLetReturnBody? types owner (inputs.bindFresh owner name.value declaredType)
        ⟨blockSpan, rest⟩ = some (tailCore, type) ∧ core = .letE initializerCore tailCore := by
  rw [elaborateTypedLetReturnBody?] at accepted
  split at accepted
  next unused =>
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨declaredType, meaning, ⟨initializerCore, initializerType⟩, initializerAccepted, remaining⟩ := accepted
    split at remaining
    next sameType =>
      change initializerType = declaredType at sameType
      subst initializerType
      simp only [Option.bind_eq_some_iff] at remaining
      obtain ⟨⟨tailCore, returnType⟩, tailAccepted, result⟩ := remaining
      change some (.letE initializerCore tailCore, returnType) = some (core, type) at result
      simp only [Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨declaredType, initializerCore, tailCore, unused, meaning, initializerAccepted, tailAccepted, rfl⟩
    next different => cases remaining
  next used => cases accepted

theorem TypedLetReturnBodyElaborates.complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnBodyElaborates types owner inputs body core type) :
    elaborateTypedLetReturnBody? types owner inputs body = some (core, type) := by
  induction elaboration with
  | terminal child =>
      have accepted := child.complete
      cases child with
      | single returned => cases returned <;> simpa only [elaborateTypedLetReturnBody?] using accepted
      | conditional => simpa only [elaborateTypedLetReturnBody?] using accepted
  | binding meaning unused resolution lowered typing _ ih =>
      have initializerAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      rw [elaborateTypedLetReturnBody?]
      simp only [if_pos unused, meaning.complete, initializerAccepted, ih, bind,
        Option.bind_some, ite_true, pure, Pure.pure]

theorem elaborateTypedLetReturnBody?_elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type)) :
    TypedLetReturnBodyElaborates types owner inputs body core type := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => exact .terminal (elaborateTerminalReturnTree?_elaborates
          (by simpa only [elaborateTypedLetReturnBody?] using accepted))
      | cons statement rest =>
          cases statement with
          | mk letSpan payload =>
              cases payload <;> try exact .terminal (elaborateTerminalReturnTree?_elaborates
                (by simpa only [elaborateTypedLetReturnBody?] using accepted))
              case letDecl name optionalType optionalInitializer =>
                cases optionalType with
                | none => exact .terminal (elaborateTerminalReturnTree?_elaborates
                    (by simpa only [elaborateTypedLetReturnBody?] using accepted))
                | some annotation =>
                    cases optionalInitializer with
                    | none => exact .terminal (elaborateTerminalReturnTree?_elaborates
                        (by simpa only [elaborateTypedLetReturnBody?] using accepted))
                    | some initializer =>
                        obtain ⟨declaredType, initializerCore, tailCore, unused, meaning,
                          initializerAccepted, tailAccepted, rfl⟩ :=
                          elaborateTypedLetReturnBody?_binding_children accepted
                        obtain ⟨resolved, resolution, lowered, typing⟩ :=
                          elaborateLocalExpression?_sound initializerAccepted
                        exact .binding (interpretTypeName?_sound meaning) unused resolution
                          (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
                          (elaborateTypedLetReturnBody?_elaborates tailAccepted)
termination_by body.value.length

theorem elaborateTypedLetReturnBody?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateTypedLetReturnBody? types owner inputs body = some (core, type) ↔
      TypedLetReturnBodyElaborates types owner inputs body core type :=
  ⟨elaborateTypedLetReturnBody?_elaborates, TypedLetReturnBodyElaborates.complete⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyEvaluation`
-/

/-! Independent operational paths for annotated, initialized let prefixes.
Raw evaluation does not imply whole acceptance or a source shadowing policy.
Fresh IDs are relative to the explicit names, not arbitrary runtime inputs. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive TypedLetReturnBodyEvaluates (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | terminal {table : LocalNameTable} {environment : Resolved.Environment}
      {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
      (child : TerminalReturnTreeEvaluates table environment initialStore body value finalStore) :
      TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : LocalExpressionEvaluates table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : TypedLetReturnBodyEvaluates owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      TypedLetReturnBodyEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore

/-- Both child paths are mandatory even when the new binding is unused.
The original Core let contributes exactly enterLet and bindLet. -/
inductive TypedLetReturnBodyEvaluatesWithCost (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | terminal {table : LocalNameTable} {environment : Resolved.Environment}
      {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
      (child : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost) :
      TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : TypedLetReturnBodyEvaluatesWithCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyEvaluationEmbeddingProperties`
-/

/-! Existing tree paths embed without changing their stores, values or costs.
Neither acceptance nor evaluation of unselected source is required. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeEvaluates.typedLetReturnBody
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnTreeEvaluates table environment initialStore body value finalStore)
    (owner : Resolved.DeclarationId) :
    TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore := .terminal evaluation

theorem TerminalReturnTreeEvaluatesWithCost.typedLetReturnBody
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    (owner : Resolved.DeclarationId) :
    TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost := .terminal evaluation

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyEvaluationProperties`
-/

/-! Raw paths retain their stores and have unique values and costs without
checking. Typed existence uses the actual initial environment and extends it
only with the value obtained by evaluating the original initializer. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyEvaluates.store_eq
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore) :
    finalStore = initialStore := by
  induction evaluation with
  | terminal child => exact child.store_eq
  | binding initializer _ ih => exact ih.trans initializer.store_eq

theorem TypedLetReturnBodyEvaluates.deterministic
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {body : Syntax.Block}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (first : TypedLetReturnBodyEvaluates owner table environment initialStore body left leftStore)
    (second : TypedLetReturnBodyEvaluates owner table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction first generalizing right rightStore with
  | terminal child =>
      cases second with
      | terminal other => exact child.deterministic other
      | binding _ _ => cases child with | single returned => cases returned
  | binding initializer _ ih =>
      cases second with
      | terminal other => cases other with | single returned => cases returned
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := initializer.deterministic otherInitializer
          exact ih otherTail

theorem TypedLetReturnBodyHasType.evaluates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context)) (store : Core.Store) :
    ∃ value, TypedLetReturnBodyEvaluates owner inputs.names environment store body value store ∧
      Core.ValueHasType value type := by
  induction typing generalizing environment with
  | terminal child =>
      obtain ⟨value, evaluation, typed⟩ := child.evaluates sameIds environmentTyped store
      exact ⟨value, .terminal evaluation, typed⟩
  | @binding inputs blockSpan letSpan name annotation initializer rest declaredType returnType
      _ _ initializerTyping _ ih =>
      obtain ⟨boundValue, initializerEvaluation, boundTyped⟩ :=
        initializerTyping.evaluates sameIds environmentTyped store
      have tailIds : Resolved.LocalScope.ids
          ((Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) =
          Resolved.LocalScope.ids (inputs.bindFresh owner name.value declaredType).context := by
        simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons, Prod.fst]
          using congrArg (Resolved.freshLocalId owner inputs.ids :: ·) sameIds
      have tailTyped : Core.EnvironmentHasTypes
          (Resolved.LocalScope.values ((Resolved.freshLocalId owner inputs.ids, boundValue) :: environment))
          (Resolved.LocalScope.values (inputs.bindFresh owner name.value declaredType).context) :=
        .cons boundTyped environmentTyped
      obtain ⟨value, tailEvaluation, valueTyped⟩ := ih tailIds tailTyped
      refine ⟨value, .binding initializerEvaluation ?_, valueTyped⟩
      simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tailEvaluation

theorem TypedLetReturnBodyEvaluates.preserves_type
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {type : Core.Ty}
    {value : Core.Value} {initialStore finalStore : Core.Store}
    (evaluation : TypedLetReturnBodyEvaluates owner inputs.names environment initialStore body value finalStore)
    (typing : TypedLetReturnBodyHasType types owner inputs body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context)) :
    Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨other, evaluated, typed⟩ := typing.evaluates sameIds environmentTyped initialStore
  obtain ⟨rfl, sameStore⟩ := evaluation.deterministic evaluated
  exact ⟨typed, sameStore⟩

theorem TypedLetReturnBodyEvaluatesWithCost.erase
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore := by
  induction evaluation with
  | terminal child => exact .terminal child.erase
  | binding initializer _ ih => exact .binding initializer.erase ih

theorem TypedLetReturnBodyEvaluates.exists_cost
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore) :
    ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost := by
  induction evaluation with
  | terminal child =>
      obtain ⟨cost, costed⟩ := child.exists_cost
      exact ⟨cost, .terminal costed⟩
  | binding initializer _ ih =>
      obtain ⟨_, initializerCost⟩ := initializer.exists_cost
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .binding initializerCost tailCost⟩

theorem typedLetReturnBodyEvaluates_iff_exists_cost
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore ↔
      ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost :=
  ⟨TypedLetReturnBodyEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem TypedLetReturnBodyEvaluatesWithCost.store_eq
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    finalStore = initialStore := evaluation.erase.store_eq

theorem TypedLetReturnBodyEvaluatesWithCost.cost_pos
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    0 < cost := by
  cases evaluation with
  | terminal child => exact child.cost_pos
  | binding _ _ => omega

theorem TypedLetReturnBodyEvaluatesWithCost.deterministic
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {body : Syntax.Block} {left right : Core.Value}
    {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body left leftStore leftCost)
    (second : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction first generalizing right rightStore rightCost with
  | terminal child =>
      cases second with
      | terminal other => exact child.deterministic other
      | binding _ _ => cases child with | single returned => cases returned
  | binding initializer _ ih =>
      cases second with
      | terminal other => cases other with | single returned => cases returned
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := initializer.deterministic otherInitializer
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyProperties`
-/

/-! Independent static typing fixes the exact ordered let prefix and terminal
tree. No runtime environment or inhabitants of the input types are needed. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyElaborates.hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnBodyElaborates types owner inputs body core type) :
    TypedLetReturnBodyHasType types owner inputs body type := by
  induction elaboration with
  | terminal child => exact .terminal child.hasType
  | binding meaning unused resolution _ typing _ ih =>
      exact .binding meaning unused (resolution.reflects_type typing) ih

theorem TypedLetReturnBodyHasType.elaborates_exact
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs body type) :
    ∃ core, TypedLetReturnBodyElaborates types owner inputs body core type := by
  induction typing with
  | terminal child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .terminal elaboration⟩
  | binding meaning unused initializerTyping _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := initializerTyping.resolves
      obtain ⟨initializerCore, lowered, _⟩ := typed.lowers
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .binding meaning unused resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typed tailElaboration⟩

theorem typedLetReturnBodyHasType_iff_elaborates_exact
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    TypedLetReturnBodyHasType types owner inputs body type ↔
      ∃ core, TypedLetReturnBodyElaborates types owner inputs body core type :=
  ⟨TypedLetReturnBodyHasType.elaborates_exact, fun ⟨_, elaboration⟩ => elaboration.hasType⟩

theorem TypedLetReturnBodyHasType.elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs body type) :
    ∃ core, elaborateTypedLetReturnBody? types owner inputs body = some (core, type) := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact ⟨core, elaboration.complete⟩

theorem elaborateTypedLetReturnBody?_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type)) :
    TypedLetReturnBodyHasType types owner inputs body type :=
  (elaborateTypedLetReturnBody?_elaborates accepted).hasType

theorem typedLetReturnBodyHasType_iff_elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    TypedLetReturnBodyHasType types owner inputs body type ↔
      ∃ core, elaborateTypedLetReturnBody? types owner inputs body = some (core, type) :=
  ⟨TypedLetReturnBodyHasType.elaborates, fun ⟨_, accepted⟩ => elaborateTypedLetReturnBody?_sound accepted⟩

theorem elaborateTypedLetReturnBody?_core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values inputs.context) core type := by
  have elaboration := elaborateTypedLetReturnBody?_elaborates accepted
  clear accepted
  induction elaboration with
  | terminal child => exact elaborateTerminalReturnTree?_core_hasType child.complete
  | binding _ _ _ lowered typing _ ih =>
      apply Core.HasType.letE
      · rw [← LocalTypeInputs.context_ids] at lowered
        exact lowered.preserves_type typing
      · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values,
          List.map_cons, Prod.snd] using ih

/-- Exact source provenance fixes both the Core binder structure and its type;
having the same result type does not identify another Core program. -/
theorem TypedLetReturnBodyElaborates.result_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : TypedLetReturnBodyElaborates types owner inputs body leftCore leftType)
    (right : TypedLetReturnBodyElaborates types owner inputs body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem TypedLetReturnBodyHasType.type_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {left right : Core.Ty}
    (first : TypedLetReturnBodyHasType types owner inputs body left)
    (second : TypedLetReturnBodyHasType types owner inputs body right) : left = right := by
  obtain ⟨_, firstElaboration⟩ := first.elaborates_exact
  obtain ⟨_, secondElaboration⟩ := second.elaborates_exact
  exact (firstElaboration.result_unique secondElaboration).2

theorem elaborateTypedLetReturnBody?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} : elaborateTypedLetReturnBody? types owner inputs body = none ↔
      ¬ ∃ type, TypedLetReturnBodyHasType types owner inputs body type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := typing.elaborates
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateTypedLetReturnBody? types owner inputs body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, elaborateTypedLetReturnBody?_sound result⟩)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyEmbeddingProperties`
-/

/-! Existing terminal trees embed with the identical Core and type. Optional
equality is restricted to terminal shapes, since valid let prefixes add success. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeHasType.typedLetReturnBody
    {inputs : LocalTypeInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnTreeHasType inputs.names inputs.context body type)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    TypedLetReturnBodyHasType types owner inputs body type := .terminal typing

theorem TerminalReturnTreeElaborates.typedLetReturnBody
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates inputs.names inputs.context body core type)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    TypedLetReturnBodyElaborates types owner inputs body core type := .terminal elaboration

theorem TerminalReturnTreeElaborates.typedLetReturnBody_complete
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates inputs.names inputs.context body core type)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    elaborateTypedLetReturnBody? types owner inputs body = some (core, type) :=
  (elaboration.typedLetReturnBody types owner).complete

theorem elaborateTypedLetReturnBody?_single
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) :
    elaborateTypedLetReturnBody? types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
      elaborateReturnBody? inputs.names inputs.context
        ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ := by
  simp only [elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?_single]

/-- The recursive tree checker, not this prefix adapter, checks both original
arms. In particular a let inside either arm is not newly accepted. -/
theorem elaborateTypedLetReturnBody?_conditional
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block)
    (blockSpan ifSpan : Syntax.SourceSpan) :
    elaborateTypedLetReturnBody? types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =
      elaborateTerminalReturnTree? inputs.names inputs.context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ := by
  simp only [elaborateTypedLetReturnBody?]

theorem elaborateTypedLetReturnBody?_conditional_singletons
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (condition : Syntax.Expr) (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan) :
    elaborateTypedLetReturnBody? types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ =
      elaborateConditionalReturnBody? inputs.names inputs.context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ := by
  rw [elaborateTypedLetReturnBody?_conditional]
  exact elaborateTerminalReturnTree?_conditional_singletons inputs.names inputs.context condition
    thenReturned elseReturned blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyExecutionProperties`
-/

/-! Actual checked Core follows the original initializer and extended tail.
Aligned IDs suffice for correspondence, not for a runtime typing guarantee.
Exact paths retain arbitrary continuations without running those frames. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTypedLetReturnBody?_evaluates_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    TypedLetReturnBodyEvaluates owner inputs.names environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  have elaboration := elaborateTypedLetReturnBody?_elaborates accepted
  clear accepted
  induction elaboration generalizing environment initialStore finalStore value with
  | terminal child =>
      constructor
      · intro evaluation
        cases evaluation with
        | terminal evaluated => exact (elaborateTerminalReturnTree?_evaluates_iff child.complete sameIds).mp evaluated
        | binding _ _ => cases child with | single returned => cases returned
      · intro evaluated
        exact .terminal ((elaborateTerminalReturnTree?_evaluates_iff child.complete sameIds).mpr evaluated)
  | @binding inputs _ _ name _ _ _ declaredType _ _ _ _ _ _ resolution lowered typing _ ih =>
      have initializerAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      constructor
      · intro evaluation
        cases evaluation with
        | terminal child => cases child with | single returned => cases returned
        | binding initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((elaborateLocalExpression?_evaluates_iff initializerAccepted sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply TypedLetReturnBodyEvaluates.binding
              ((elaborateLocalExpression?_evaluates_iff initializerAccepted sameIds).mpr initializer)
            have tailEvaluation :=
              (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tailEvaluation
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds

theorem TypedLetReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  have elaboration := elaborateTypedLetReturnBody?_elaborates accepted
  clear accepted
  induction elaboration generalizing environment initialStore finalStore value cost continuation with
  | terminal child =>
      cases evaluation with
      | terminal evaluated => exact evaluated.checked_toStepsWithContinuation child.complete sameIds continuation
      | binding _ _ => cases child with | single returned => cases returned
  | @binding inputs _ _ _ _ _ _ _ _ _ _ _ _ _ resolution lowered _ _ ih =>
      cases evaluation with
      | terminal child => cases child with | single returned => cases returned
      | binding initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          have runtimeLowered := lowered
          rw [← LocalTypeInputs.context_ids, ← sameIds] at runtimeLowered
          apply CostStepComposition.letE (initializer.toStepsWithContinuation resolution runtimeLowered _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds

theorem TypedLetReturnBodyEvaluatesWithCost.checked_toSteps
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.checked_toStepsWithContinuation accepted sameIds []

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyOwnerProperties`
-/

/-! Owner-only relabeling preserves exact typed-prefix provenance and every
checker result. Fresh allocation commutes on the complete supplied scope;
no inverse owner map or runtime inhabitants are required. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyElaborates.mapOwner
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnBodyElaborates types owner inputs body core type)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    TypedLetReturnBodyElaborates types (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) body core type := by
  induction elaboration with
  | terminal child =>
      apply TypedLetReturnBodyElaborates.terminal
      simpa only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context] using
        (child.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
  | @binding inputs blockSpan letSpan name annotation initializer rest declaredType returnType
      resolved initializerCore tailCore meaning unused resolution lowered typing _ ih =>
      refine .binding (initializerResolved := resolved.renameIds (ownerLocalIdMap mapping))
        meaning ?_ ?_ ?_ ?_ ?_
      · simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds,
          List.map_map, Function.comp_def] using unused
      · simpa only [LocalTypeInputs.mapIds_names] using (resolution.mapIds (ownerLocalIdMap mapping))
      · simpa only [LocalTypeInputs.mapIds_ids] using
          (Resolved.lowers_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr lowered
      · simpa only [LocalTypeInputs.mapIds_context] using
          (Resolved.typing_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr typing
      · simpa only [LocalTypeInputs.bindFresh_mapOwner inputs owner mapping injective] using ih

theorem TypedLetReturnBodyHasType.mapOwner
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs body type)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    TypedLetReturnBodyHasType types (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) body type := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact (elaboration.mapOwner mapping injective).hasType

/-- Structural recursion also preserves rejection under non-surjective owner
maps. Initializers retain their old scope and tails their freshly extended one. -/
theorem elaborateTypedLetReturnBody?_mapOwner
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateTypedLetReturnBody? types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)) body =
      elaborateTypedLetReturnBody? types owner inputs body := by
  have treeSame := elaborateTerminalReturnTree?_mapIds (ownerLocalIdMap mapping)
    (ownerLocalIdMap_injective mapping injective) inputs.names inputs.context
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateTypedLetReturnBody?, LocalTypeInputs.mapIds_names,
          LocalTypeInputs.mapIds_context, treeSame]
      | cons statement rest =>
          cases statement with
          | mk letSpan payload =>
              cases payload <;> try (solve | simp only [elaborateTypedLetReturnBody?,
                LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context,
                treeSame])
              case letDecl name optionalType optionalInitializer =>
                cases optionalType with
                | none => simp only [elaborateTypedLetReturnBody?, LocalTypeInputs.mapIds_names,
                    LocalTypeInputs.mapIds_context, treeSame]
                | some annotation =>
                    cases optionalInitializer with
                    | none => simp only [elaborateTypedLetReturnBody?, LocalTypeInputs.mapIds_names,
                        LocalTypeInputs.mapIds_context, treeSame]
                    | some initializer =>
                        have tailSame (declaredType : Core.Ty) :=
                          elaborateTypedLetReturnBody?_mapOwner mapping injective types owner
                            (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
                        rw [elaborateTypedLetReturnBody?, elaborateTypedLetReturnBody?]
                        simp only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context]
                        rw [elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
                          (ownerLocalIdMap_injective mapping injective)]
                        simp only [LocalNameTable.mapIds, List.map_map, Function.comp_def,
                          ← LocalTypeInputs.bindFresh_mapOwner inputs owner mapping injective name.value,
                          tailSame]
termination_by body.value.length

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyRunner`
-/

/-! A separate checked body runner uses the actual static projection and the
original ordered values. It does not prepare or extend runtime function entries. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def checkTypedLetReturnBody? (inputs : LocalInputs) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  elaborateTypedLetReturnBody? types owner inputs.toTypeInputs body

def runTypedLetReturnBody? (inputs : LocalInputs) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (fuel : Nat) (body : Syntax.Block)
    (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkTypedLetReturnBody? types owner body
  return (type, Core.runStateful fuel (Core.State.initial core inputs.environment.values store))

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyRunnerEmbeddingProperties`
-/

/-! Old terminal shapes preserve failure and complete machine results at
every fuel. Arbitrary prefixes cannot be identified with the old tree runner. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem runTypedLetReturnBody?_single
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId) (fuel : Nat)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTypedLetReturnBody? types owner fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store =
      inputs.runReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store := by
  simp only [runTypedLetReturnBody?, checkTypedLetReturnBody?, runReturnBody?, checkReturnBody?,
    elaborateTypedLetReturnBody?_single, toTypeInputs_names, toTypeInputs_context]

theorem runTypedLetReturnBody?_conditional
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId) (fuel : Nat)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block)
    (blockSpan ifSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTypedLetReturnBody? types owner fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ store =
      inputs.runTerminalReturnTree? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ store := by
  simp only [runTypedLetReturnBody?, checkTypedLetReturnBody?, runTerminalReturnTree?, checkTerminalReturnTree?,
    elaborateTypedLetReturnBody?_conditional, toTypeInputs_names, toTypeInputs_context]

theorem runTypedLetReturnBody?_conditional_singletons
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId) (fuel : Nat)
    (condition : Syntax.Expr) (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan)
    (store : Core.Store) :
    inputs.runTypedLetReturnBody? types owner fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store =
      inputs.runConditionalReturnBody? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store := by
  simp only [runTypedLetReturnBody?, checkTypedLetReturnBody?, runConditionalReturnBody?, checkConditionalReturnBody?,
    elaborateTypedLetReturnBody?_conditional_singletons, toTypeInputs_names, toTypeInputs_context]

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyRunnerOwnerProperties`
-/

/-! At a fixed store, owner-only relabeling preserves complete optional body
results, including genuine checkpoints. Actual values retain their positions. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkTypedLetReturnBody?_mapOwner (inputs : LocalInputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (body : Syntax.Block) :
    (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).checkTypedLetReturnBody? types (mapping owner) body =
      inputs.checkTypedLetReturnBody? types owner body := by
  simp only [checkTypedLetReturnBody?, toTypeInputs_mapIds,
    elaborateTypedLetReturnBody?_mapOwner mapping injective]

theorem runTypedLetReturnBody?_mapOwner (inputs : LocalInputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).runTypedLetReturnBody? types (mapping owner) fuel body store =
      inputs.runTypedLetReturnBody? types owner fuel body store := by
  simp only [runTypedLetReturnBody?, checkTypedLetReturnBody?_mapOwner inputs mapping injective,
    mapIds_environment, Resolved.LocalScope.values_mapIds]

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyRunnerProperties`
-/

/-! Whole checking and independent costs determine exact fuel thresholds.
Actual typed inputs supply terminating paths without filling in static values. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyEvaluatesWithCost.checked_runStateful_done_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) :
    Core.runStateful fuel (Core.State.initial core environment.values initialStore) = .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_done_iff

theorem TypedLetReturnBodyEvaluatesWithCost.checked_runStateful_outOfFuel_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core environment.values initialStore) =
      .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_outOfFuel_iff

theorem elaborateTypedLetReturnBody?_run_done_iff_cost
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core environment.values initialStore) = .done value finalStore ↔
      ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    have evaluation := (elaborateTypedLetReturnBody?_evaluates_iff accepted sameIds).mpr
      (Core.runStateful_evaluation_sound completed)
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, costed, (costed.checked_runStateful_done_iff accepted sameIds).mp completed⟩
  · rintro ⟨cost, costed, enough⟩
    exact (costed.checked_runStateful_done_iff accepted sameIds).mpr enough

namespace LocalInputs

private theorem aligned (inputs : LocalInputs) : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
  simpa only [toTypeInputs_context] using inputs.sameIds

private theorem actualTypes (inputs : LocalInputs) :
    Core.EnvironmentHasTypes inputs.environment.values inputs.toTypeInputs.context.values := by
  simpa only [toTypeInputs_context] using inputs.environmentTyped

theorem runTypedLetReturnBody?_eq_none_iff
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {body : Syntax.Block} {fuel : Nat} {store : Core.Store} :
    inputs.runTypedLetReturnBody? types owner fuel body store = none ↔
      inputs.checkTypedLetReturnBody? types owner body = none := by
  cases checked : inputs.checkTypedLetReturnBody? types owner body with
  | none => simp [runTypedLetReturnBody?, checked]
  | some pair => rcases pair with ⟨core, type⟩; simp [runTypedLetReturnBody?, checked]

theorem runTypedLetReturnBody?_eq_some_iff
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {body : Syntax.Block} {fuel : Nat} {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.runTypedLetReturnBody? types owner fuel body store = some (type, result) ↔
      ∃ core, inputs.checkTypedLetReturnBody? types owner body = some (core, type) ∧
        Core.runStateful fuel (Core.State.initial core inputs.environment.values store) = result := by
  simp only [runTypedLetReturnBody?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, resultEq⟩
    exact ⟨(core, type), checked, by simp only [resultEq]⟩

theorem runTypedLetReturnBody?_done_iff_typed_cost
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.runTypedLetReturnBody? types owner fuel body initialStore = some (type, .done value finalStore) ↔
      TypedLetReturnBodyHasType types owner inputs.toTypeInputs body type ∧
      ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner inputs.names inputs.environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨core, checked, execution⟩ := runTypedLetReturnBody?_eq_some_iff.mp completed
    refine ⟨elaborateTypedLetReturnBody?_sound checked, ?_⟩
    simpa only [toTypeInputs_names] using
      (elaborateTypedLetReturnBody?_run_done_iff_cost checked (aligned inputs)).mp execution
  · rintro ⟨typing, cost, costed, enough⟩
    obtain ⟨core, checked⟩ := typing.elaborates
    rw [← toTypeInputs_names inputs] at costed
    exact runTypedLetReturnBody?_eq_some_iff.mpr ⟨core, checked,
      (costed.checked_runStateful_done_iff checked (aligned inputs)).mpr enough⟩

/-- Values and exact thresholds come from actual typed inputs. A static type
or a raw path through rejected source is not sufficient for this wrapper. -/
theorem typedLetReturnBody_typed_cost_execution
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs.toTypeInputs body type) (store : Core.Store) :
    ∃ value cost, TypedLetReturnBodyEvaluatesWithCost owner inputs.names inputs.environment
        store body value store cost ∧ Core.ValueHasType value type ∧ ∀ fuel,
      (inputs.runTypedLetReturnBody? types owner fuel body store = some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, inputs.runTypedLetReturnBody? types owner fuel body store =
        some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨core, checked⟩ := typing.elaborates
  obtain ⟨value, evaluated, valueTyped⟩ := typing.evaluates (aligned inputs) (actualTypes inputs) store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  refine ⟨value, cost, by simpa only [toTypeInputs_names] using costed, valueTyped, fun fuel => ?_⟩
  have boundaries := And.intro (costed.checked_runStateful_done_iff checked (aligned inputs) (fuel := fuel))
    (costed.checked_runStateful_outOfFuel_iff checked (aligned inputs) (fuel := fuel))
  simpa only [runTypedLetReturnBody?, checkTypedLetReturnBody?, checked, bind, Option.bind_some, pure,
    Option.some.injEq, Prod.mk.injEq, true_and] using boundaries

theorem runTypedLetReturnBody?_outOfFuel_iff_typed_cost
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {store : Core.Store} {type : Core.Ty} {fuel : Nat} :
    (∃ suspended, inputs.runTypedLetReturnBody? types owner fuel body store = some (type, .outOfFuel suspended)) ↔
      TypedLetReturnBodyHasType types owner inputs.toTypeInputs body type ∧
      ∃ value cost, TypedLetReturnBodyEvaluatesWithCost owner inputs.names inputs.environment
        store body value store cost ∧ fuel < cost := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    obtain ⟨core, checked, _⟩ := runTypedLetReturnBody?_eq_some_iff.mp exhausted
    have typing := elaborateTypedLetReturnBody?_sound checked
    obtain ⟨value, cost, costed, _, boundaries⟩ :=
      typedLetReturnBody_typed_cost_execution (inputs := inputs) typing store
    exact ⟨typing, value, cost, costed, (boundaries fuel).2.mp ⟨suspended, exhausted⟩⟩
  · rintro ⟨typing, value, cost, costed, short⟩
    obtain ⟨core, checked⟩ := typing.elaborates
    rw [← toTypeInputs_names inputs] at costed
    obtain ⟨suspended, exhausted⟩ :=
      (costed.checked_runStateful_outOfFuel_iff checked (aligned inputs)).mpr short
    exact ⟨suspended, runTypedLetReturnBody?_eq_some_iff.mpr ⟨core, checked, exhausted⟩⟩

theorem runTypedLetReturnBody?_never_faults (inputs : LocalInputs) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (body : Syntax.Block) (fuel : Nat) (store : Core.Store)
    (type : Core.Ty) (error : Core.MachineFault) (faultState : Core.State) :
    inputs.runTypedLetReturnBody? types owner fuel body store ≠ some (type, .fault error faultState) := by
  intro fault
  obtain ⟨core, checked, _⟩ := runTypedLetReturnBody?_eq_some_iff.mp fault
  have typing := elaborateTypedLetReturnBody?_sound checked
  obtain ⟨value, cost, _, _, boundaries⟩ :=
    typedLetReturnBody_typed_cost_execution (inputs := inputs) typing store
  by_cases enough : cost ≤ fuel
  · have completed := (boundaries fuel).1.mpr enough
    rw [completed] at fault
    cases fault
  · obtain ⟨suspended, exhausted⟩ := (boundaries fuel).2.mpr (by omega)
    rw [exhausted] at fault
    cases fault

end LocalInputs
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyFuelBoundProperties`
-/

/-! This total budget counts all initializer bounds and the terminal tree's
maximum-arm bound. Neither annotation meaning nor name freshness is a numerical
premise; the bound does not replace whole checking or actual typed values. -/

set_option autoImplicit false

namespace Solcore.Frontend

def typedLetReturnBodyFuelBound (body : Syntax.Block) : Nat :=
  match body with
  | ⟨blockSpan, ⟨_, .letDecl _ (some _) (some initializer)⟩ :: rest⟩ =>
      localExpressionFuelBound initializer + typedLetReturnBodyFuelBound ⟨blockSpan, rest⟩ + 2
  | _ => terminalReturnTreeFuelBound body
termination_by body.value.length

theorem TypedLetReturnBodyEvaluatesWithCost.cost_le_fuelBound
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    cost ≤ typedLetReturnBodyFuelBound body := by
  induction evaluation with
  | terminal child =>
      have bounded := child.cost_le_fuelBound
      cases child with
      | single returned => cases returned <;> simpa only [typedLetReturnBodyFuelBound] using bounded
      | ifTrue _ _ | ifFalse _ _ => simpa only [typedLetReturnBodyFuelBound] using bounded
  | binding initializer _ ih =>
      have initializerBound := initializer.cost_le_fuelBound
      simp only [typedLetReturnBodyFuelBound]
      omega

theorem elaborateTypedLetReturnBody?_run_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context))
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateTypedLetReturnBody?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runTypedLetReturnBody?_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs.toTypeInputs body type)
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runTypedLetReturnBody? types owner fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ :=
    inputs.typedLetReturnBody_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyResumptionProperties`
-/

/-! A genuine exhausted state retains every pending let frame, captured
environment and actual value. Exact residual costs use a closed final path;
arbitrary continuation endpoints are not treated as completed body runs. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyEvaluatesWithCost.checked_residual_of_outOfFuel
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost spent : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty} {checkpoint : Core.State}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.checked_toSteps accepted sameIds).residual_of_outOfFuel exhausted

theorem LocalInputs.runTypedLetReturnBody?_resume
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalInputs}
    {body : Syntax.Block} {spent : Nat} {store : Core.Store} {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : inputs.runTypedLetReturnBody? types owner spent body store = some (type, .outOfFuel checkpoint))
    (additional : Nat) :
    inputs.runTypedLetReturnBody? types owner (spent + additional) body store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, execution⟩ := runTypedLetReturnBody?_eq_some_iff.mp exhausted
  exact runTypedLetReturnBody?_eq_some_iff.mpr ⟨core, checked, (Core.runStateful_resume execution additional).symm⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyStoreProperties`
-/

/-! Replay the original initializer values and exact costs at any store.
Completed observations and exhaustion presence retain their own stores. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyEvaluates.change_store
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore)
    (replacement : Core.Store) :
    TypedLetReturnBodyEvaluates owner table environment replacement body value replacement := by
  induction evaluation with
  | terminal child => exact .terminal (child.change_store replacement)
  | binding initializer _ ih => exact .binding (initializer.change_store replacement) ih

theorem TypedLetReturnBodyEvaluatesWithCost.change_store
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost)
    (replacement : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table environment replacement body value replacement cost := by
  induction evaluation with
  | terminal child => exact .terminal (child.change_store replacement)
  | binding initializer _ ih => exact .binding (initializer.change_store replacement) ih

theorem typedLetReturnBodyEvaluates_store_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore ↔
      finalStore = initialStore ∧
        TypedLetReturnBodyEvaluates owner table environment replacement body value replacement := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

theorem typedLetReturnBodyEvaluatesWithCost_store_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        TypedLetReturnBodyEvaluatesWithCost owner table environment replacement body value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Equal values at the same fuel, each with its own store; not equality of
complete results across stores. Whole checking remains part of each run. -/
theorem LocalInputs.runTypedLetReturnBody?_done_store_iff
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    inputs.runTypedLetReturnBody? types owner fuel body leftStore = some (type, .done value leftStore) ↔
      inputs.runTypedLetReturnBody? types owner fuel body rightStore = some (type, .done value rightStore) := by
  rw [LocalInputs.runTypedLetReturnBody?_done_iff_typed_cost, LocalInputs.runTypedLetReturnBody?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store leftStore, enough⟩

/-- Exhaustion presence agrees, but suspended states retain their distinct
stores and must be resumed separately without dropping pending let frames. -/
theorem LocalInputs.runTypedLetReturnBody?_outOfFuel_store_iff
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store) (type : Core.Ty) :
    (∃ checkpoint, inputs.runTypedLetReturnBody? types owner fuel body leftStore = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, inputs.runTypedLetReturnBody? types owner fuel body rightStore = some (type, .outOfFuel checkpoint) := by
  rw [LocalInputs.runTypedLetReturnBody?_outOfFuel_iff_typed_cost, LocalInputs.runTypedLetReturnBody?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store leftStore, short⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyTypeExtensionProperties`
-/

/-! Preserve annotation meanings without changing source, inputs or exact Core.
One-way extension preserves success; mutual extension also preserves rejection. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyElaborates.extend_types
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnBodyElaborates old owner inputs body core type)
    (extension : TypeNameTable.Extends old new) :
    TypedLetReturnBodyElaborates new owner inputs body core type := by
  induction elaboration with
  | terminal child => exact .terminal child
  | binding meaning unused resolution lowered typing _ ih =>
      exact .binding (meaning.extend_types extension) unused resolution lowered typing ih

theorem TypedLetReturnBodyHasType.extend_types
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType old owner inputs body type)
    (extension : TypeNameTable.Extends old new) :
    TypedLetReturnBodyHasType new owner inputs body type := by
  induction typing with
  | terminal child => exact .terminal child
  | binding meaning unused initializer _ ih =>
      exact .binding (meaning.extend_types extension) unused initializer ih

theorem elaborateTypedLetReturnBody?_some_of_extends
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (extension : TypeNameTable.Extends old new)
    (accepted : elaborateTypedLetReturnBody? old owner inputs body = some (core, type)) :
    elaborateTypedLetReturnBody? new owner inputs body = some (core, type) :=
  ((elaborateTypedLetReturnBody?_elaborates accepted).extend_types extension).complete

/-- Mutual first-match preservation retains the full optional result without
equating tables or requiring unique keys. One-way extension can repair rejection. -/
theorem elaborateTypedLetReturnBody?_eq_of_mutual_extends
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateTypedLetReturnBody? old owner inputs body =
      elaborateTypedLetReturnBody? new owner inputs body := by
  cases oldResult : elaborateTypedLetReturnBody? old owner inputs body with
  | none =>
      cases newResult : elaborateTypedLetReturnBody? new owner inputs body with
      | none => rfl
      | some pair =>
          rcases pair with ⟨core, type⟩
          have preserved := elaborateTypedLetReturnBody?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some pair =>
      rcases pair with ⟨core, type⟩
      exact (elaborateTypedLetReturnBody?_some_of_extends forward oldResult).symm

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnBodyRunnerTypeExtensionProperties`
-/

/-! Meaning extension preserves successful complete body results. Mutual
extension also retains rejection; actual inputs, fuel and store stay fixed. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkTypedLetReturnBody?_some_of_extends {old new : TypeNameTable}
    {inputs : LocalInputs} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {core : Core.Expr} {type : Core.Ty} (extension : TypeNameTable.Extends old new)
    (accepted : inputs.checkTypedLetReturnBody? old owner body = some (core, type)) :
    inputs.checkTypedLetReturnBody? new owner body = some (core, type) :=
  elaborateTypedLetReturnBody?_some_of_extends extension accepted

theorem checkTypedLetReturnBody?_eq_of_mutual_extends (inputs : LocalInputs)
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (body : Syntax.Block) :
    inputs.checkTypedLetReturnBody? old owner body = inputs.checkTypedLetReturnBody? new owner body :=
  elaborateTypedLetReturnBody?_eq_of_mutual_extends forward backward owner inputs.toTypeInputs body

/-- The whole successful pair is retained, even at insufficient fuel with a
genuine suspended state. No separate typing or sufficient-fuel premise is used. -/
theorem runTypedLetReturnBody?_some_of_extends {old new : TypeNameTable}
    {inputs : LocalInputs} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {fuel : Nat} {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult}
    (extension : TypeNameTable.Extends old new)
    (accepted : inputs.runTypedLetReturnBody? old owner fuel body store = some (type, result)) :
    inputs.runTypedLetReturnBody? new owner fuel body store = some (type, result) := by
  cases checked : inputs.checkTypedLetReturnBody? old owner body with
  | none => simp [runTypedLetReturnBody?, checked] at accepted
  | some pair =>
      obtain ⟨core, checkedType⟩ := pair
      have preserved := checkTypedLetReturnBody?_some_of_extends extension checked
      simpa only [runTypedLetReturnBody?, checked, preserved] using accepted

theorem runTypedLetReturnBody?_eq_of_mutual_extends (inputs : LocalInputs)
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    inputs.runTypedLetReturnBody? old owner fuel body store =
      inputs.runTypedLetReturnBody? new owner fuel body store := by
  simp only [runTypedLetReturnBody?, checkTypedLetReturnBody?_eq_of_mutual_extends
    inputs forward backward owner body]

end Solcore.Frontend.LocalInputs
