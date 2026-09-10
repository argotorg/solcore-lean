import Solcore.Frontend.ClosedSourceDataBody
import Solcore.Frontend.ClosedSourceDataExpressionProperties
import Solcore.Frontend.ClosedSourceEvaluationCompatibility
import Solcore.Frontend.SourceComputationBodyEmbeddingProperties
import Solcore.Frontend.ComputationReturnTreeProperties
import Solcore.Frontend.ComputationReturnTreeExecutionProperties
import Solcore.Frontend.LocalExpressionExecutionProperties
import Solcore.Frontend.LocalFragmentProperties
import Solcore.Core.LocalFragmentInsertionProperties

/- Restrict only private child predicates, then reuse the full actual-image body bridge. -/
set_option autoImplicit false
namespace Solcore.Frontend

private def oldChild (names : LocalNameTable) (environment : Resolved.Environment)
    (initialStore : Core.Store) (source : Syntax.Expr) (value : Core.Value) (finalStore : Core.Store) : Prop :=
  ClosedSourceDataExpression source ∧
    LocalExpressionEvaluates names environment initialStore source value finalStore
private def mixedChild (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : List (Resolved.LocalId × RuntimeValue)) (initialStore : List RuntimeValue)
    (source : Syntax.Expr) (value : RuntimeValue) (finalStore : List RuntimeValue) : Prop :=
  ClosedSourceDataExpression source ∧
    ClosedSourceExpressionEvaluates owner names environment initialStore source value finalStore

private theorem selected_property {actual : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
    (choice : RuntimeWordMatchChooses actual cases defaultBody selected tests)
    {P : Syntax.Block → Prop} (branches : ∀ arm ∈ cases, P arm.value.body)
    (fallback : ∀ source ∈ defaultBody.toList, P source) : P selected := by
  induction choice with
  | fallback => exact fallback _ (by simp)
  | wildcard _ => exact branches _ List.mem_cons_self
  | hit _ => exact branches _ List.mem_cons_self
  | miss _ _ _ ih => exact ih (fun arm member => branches arm (List.mem_cons_of_mem _ member)) fallback

private theorem mixed_add {owner names environment initialStore body value finalStore}
    (evaluated : SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates owner names
      environment initialStore body value finalStore) :
    ClosedSourceDataBody body →
      SourceComputationBodyEvaluates mixedChild owner names environment initialStore body value finalStore := by
  induction evaluated with
  | bare => intro _; exact .bare
  | expression child =>
      intro gate; cases gate with
      | expression admitted => exact .expression ⟨admitted, child⟩
  | block _ ih =>
      intro gate; cases gate with
      | block admitted => exact .block (ih admitted)
  | binding initializer _ ih =>
      intro gate; cases gate with
      | binding admitted tail => exact .binding ⟨admitted, initializer⟩ (ih tail)
  | inferred initializer _ ih =>
      intro gate; cases gate with
      | binding admitted tail => exact .inferred ⟨admitted, initializer⟩ (ih tail)
  | discard child _ ih =>
      intro gate; cases gate with
      | discard admitted tail => exact .discard ⟨admitted, child⟩ (ih tail)
  | ifTrue condition _ ih =>
      intro gate; cases gate with
      | conditional admitted yes _ => exact .ifTrue ⟨admitted, condition⟩ (ih yes)
  | ifFalse condition _ ih =>
      intro gate; cases gate with
      | conditional admitted _ no => exact .ifFalse ⟨admitted, condition⟩ (ih no)
  | wordMatch scrutinee choice _ ih =>
      intro gate; cases gate with
      | wordMatch admitted branches fallback =>
          exact .wordMatch ⟨admitted, scrutinee⟩ choice (ih (selected_property choice branches fallback))

private theorem mixed_remove {owner names environment initialStore body value finalStore}
    (evaluated : SourceComputationBodyEvaluates mixedChild owner names environment
      initialStore body value finalStore) :
    SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates owner names environment
      initialStore body value finalStore := by
  induction evaluated with
  | bare => exact .bare
  | expression child => exact .expression child.2
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding initializer.2 ih
  | inferred initializer _ ih => exact .inferred initializer.2 ih
  | discard child _ ih => exact .discard child.2 ih
  | ifTrue condition _ ih => exact .ifTrue condition.2 ih
  | ifFalse condition _ ih => exact .ifFalse condition.2 ih
  | wordMatch scrutinee choice _ ih => exact .wordMatch scrutinee.2 choice ih

private theorem old_add {owner names environment initialStore body value finalStore}
    (evaluated : ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names
      environment initialStore body value finalStore) :
    ClosedSourceDataBody body →
      ComputationReturnTreeEvaluates oldChild owner names environment initialStore body value finalStore := by
  induction evaluated with
  | bare => intro _; exact .bare
  | expression child =>
      intro gate; cases gate with
      | expression admitted => exact .expression ⟨admitted, child⟩
  | block _ ih =>
      intro gate; cases gate with
      | block admitted => exact .block (ih admitted)
  | binding initializer _ ih =>
      intro gate; cases gate with
      | binding admitted tail => exact .binding ⟨admitted, initializer⟩ (ih tail)
  | inferred initializer _ ih =>
      intro gate; cases gate with
      | binding admitted tail => exact .inferred ⟨admitted, initializer⟩ (ih tail)
  | discard child _ ih =>
      intro gate; cases gate with
      | discard admitted tail => exact .discard ⟨admitted, child⟩ (ih tail)
  | ifTrue condition _ ih =>
      intro gate; cases gate with
      | conditional admitted yes _ => exact .ifTrue ⟨admitted, condition⟩ (ih yes)
  | ifFalse condition _ ih =>
      intro gate; cases gate with
      | conditional admitted _ no => exact .ifFalse ⟨admitted, condition⟩ (ih no)
  | wordMatch scrutinee choice _ ih =>
      intro gate; cases gate with
      | wordMatch admitted branches fallback =>
          exact .wordMatch ⟨admitted, scrutinee⟩ choice
            (ih (selected_property (runtimeWordMatchChooses_ofCore_iff.mpr choice) branches fallback))

private theorem old_remove {owner names environment initialStore body value finalStore}
    (evaluated : ComputationReturnTreeEvaluates oldChild owner names environment
      initialStore body value finalStore) :
    ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names environment
      initialStore body value finalStore := by
  induction evaluated with
  | bare => exact .bare
  | expression child => exact .expression child.2
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding initializer.2 ih
  | inferred initializer _ ih => exact .inferred initializer.2 ih
  | discard child _ ih => exact .discard child.2 ih
  | ifTrue condition _ ih => exact .ifTrue condition.2 ih
  | ifFalse condition _ ih => exact .ifFalse condition.2 ih
  | wordMatch scrutinee choice _ ih => exact .wordMatch scrutinee.2 choice ih

private theorem child_exact {owner names environment initialStore source actualValue actualFinal} :
    mixedChild owner names (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
    ∃ value finalStore, actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      oldChild names environment initialStore source value finalStore := by
  constructor
  · rintro ⟨gate, evaluated⟩
    obtain ⟨value, finalStore, same, finalSame, old⟩ := gate.local_evaluates_iff.mp evaluated
    exact ⟨value, finalStore, same, finalSame, gate, old⟩
  · rintro ⟨value, finalStore, same, finalSame, gate, evaluated⟩
    exact ⟨gate, gate.local_evaluates_iff.mpr ⟨value, finalStore, same, finalSame, evaluated⟩⟩

/-- Original gated bodies have exactly the old generic-local actual image. -/
theorem ClosedSourceDataBody.local_evaluates_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataBody body) :
    ClosedSourceBodyEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) body actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names environment
        initialStore body value finalStore := by
  rw [closedSourceBodyEvaluates_iff]
  constructor
  · intro evaluated
    obtain ⟨value, finalStore, same, finalSame, old⟩ :=
      (sourceComputationBodyEvaluates_ofCore_inputs_iff child_exact).mp (mixed_add evaluated fragment)
    exact ⟨value, finalStore, same, finalSame, old_remove old⟩
  · rintro ⟨value, finalStore, same, finalSame, old⟩
    exact mixed_remove ((sourceComputationBodyEvaluates_ofCore_inputs_iff child_exact).mpr
      ⟨value, finalStore, same, finalSame, old_add old fragment⟩)

/-- Whole shared checking and exact ID alignment supply the stronger Core boundary. -/
theorem ClosedSourceDataBody.core_evaluates_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataBody body)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateComputationReturnTree? elaborateLocalExpression?
      types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context) :
    ClosedSourceBodyEvaluates owner inputs.names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) body actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  have elaboration := (elaborateComputationReturnTree?_iff
    (ChildElab := fun names context source core type =>
      elaborateLocalExpression? names context source = some (core, type)) (fun {_ _ _ _ _} => Iff.rfl)).mp accepted
  have correspondence {value finalStore} :
      ComputationReturnTreeEvaluates LocalExpressionEvaluates owner inputs.names environment
        initialStore body value finalStore ↔
      Core.Evaluates environment.values initialStore core value finalStore :=
    ComputationReturnTreeElaborates.evaluates_iff (ChildEval := LocalExpressionEvaluates)
      (F := Core.Expr.LocalFragment)
      elaborateLocalExpression?_localFragment Core.Expr.LocalFragment.weakenAt
      Core.Expr.LocalFragment.evaluates_insert_iff
      (fun checked aligned => elaborateLocalExpression?_evaluates_iff checked aligned) elaboration sameIds
  rw [fragment.local_evaluates_iff]
  constructor
  · rintro ⟨value, finalStore, same, finalSame, evaluated⟩
    exact ⟨value, finalStore, same, finalSame, correspondence.mp evaluated⟩
  · rintro ⟨value, finalStore, same, finalSame, evaluated⟩
    exact ⟨value, finalStore, same, finalSame, correspondence.mpr evaluated⟩

end Solcore.Frontend
