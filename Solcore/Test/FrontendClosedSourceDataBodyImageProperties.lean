import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Frontend.Computation
import Solcore.Frontend.LocalExpressionExecutionProperties
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Core.LocalFragment

/- Original repeated shadowing preserves the pre-binding value and complete raw store. -/
set_option autoImplicit false
namespace Tests.ClosedSourceDataBodyImages
open Solcore Solcore.Frontend

private def statements (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier) :
    List (Option Syntax.TypeExpr) → List Syntax.Statement
  | [] => [⟨spans 1, .returnStmt (some ⟨spans 2, .identifier name⟩)⟩]
  | annotation :: rest =>
      ⟨spans 3, .letDecl name annotation (some ⟨spans 4, .identifier name⟩)⟩ ::
        statements spans name rest

private def source (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotations : List (Option Syntax.TypeExpr)) : Syntax.Block :=
  ⟨spans 0, statements spans name annotations⟩

private theorem mapped_lookup {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

section Family
variable (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
  (annotations : List (Option Syntax.TypeExpr)) (owner : Resolved.DeclarationId)
  (names : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
  (id : Resolved.LocalId) (value : Core.Value)
  (named : LocalNameTable.Lookup names name.value id)
  (found : Resolved.LocalScope.Lookup environment id value)

local notation "original" => source spans name annotations

include named found

/-- Original constructors precede every image law; annotations do not constrain raw success. -/
theorem independent_original_prefixes :
    ClosedSourceDataBody original ∧
    ClosedSourceBodyEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) original (RuntimeValue.ofCore value)
      (store.map RuntimeValue.ofCore) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names environment
      store original value store := by
  induction annotations generalizing names environment id with
  | nil =>
      exact ⟨.expression .reference,
        .expression (.reference named (mapped_lookup found)),
        .expression (.identifier named found)⟩
  | cons annotation rest ih =>
      have tail := ih
        ((name.value, Resolved.freshLocalId owner (names.map Prod.snd)) :: names)
        ((Resolved.freshLocalId owner (names.map Prod.snd), value) :: environment)
        (Resolved.freshLocalId owner (names.map Prod.snd)) .head .head
      refine ⟨.binding .reference tail.1, ?_⟩
      cases annotation with
      | none =>
          exact ⟨.inferred (.reference named (mapped_lookup found))
            (by simpa only [source, List.map_cons] using tail.2.1),
            .inferred (.identifier named found) tail.2.2⟩
      | some annotation =>
          exact ⟨.binding (.reference named (mapped_lookup found))
            (by simpa only [source, List.map_cons] using tail.2.1),
            .binding (.identifier named found) tail.2.2⟩

private theorem old_endpoint {actualValue : Core.Value} {actualFinal : Core.Store}
    (actual : ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names environment
      store original actualValue actualFinal) :
    actualValue = value ∧ actualFinal = store := by
  induction annotations generalizing names environment id store with
  | nil =>
      cases actual with
      | expression child => exact child.deterministic (.identifier named found)
  | cons annotation rest ih =>
      cases annotation with
      | none =>
          cases actual with
          | inferred initializer tail =>
              obtain ⟨rfl, rfl⟩ := initializer.deterministic (.identifier named found)
              exact ih _ _ _ _ .head .head tail
      | some annotation =>
          cases actual with
          | binding initializer tail =>
              obtain ⟨rfl, rfl⟩ := initializer.deterministic (.identifier named found)
              exact ih _ _ _ _ .head .head tail

/-- Every actual raw result agrees with the independent pre-shadowing endpoint. -/
theorem all_actual_local_images {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ClosedSourceBodyEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) original actualValue actualFinal ↔
    actualValue = RuntimeValue.ofCore value ∧ actualFinal = store.map RuntimeValue.ofCore := by
  have paths := independent_original_prefixes spans name annotations owner names environment
    store id value named found
  constructor
  · intro actual
    obtain ⟨result, finalStore, same, finalSame, old⟩ := paths.1.local_evaluates_iff.mp actual
    obtain ⟨rfl, rfl⟩ := old_endpoint spans name annotations owner names environment
      store id value named found old
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact paths.1.local_evaluates_iff.mpr ⟨value, store, rfl, rfl, paths.2.2⟩

end Family

section Checked
variable (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
  (annotations : List (Option Syntax.TypeExpr)) (owner : Resolved.DeclarationId)
  (types : TypeNameTable) (inputs : LocalTypeInputs) (environment : Resolved.Environment)
  (store : Core.Store) (id : Resolved.LocalId) (value : Core.Value)
  (named : LocalNameTable.Lookup inputs.names name.value id)
  (found : Resolved.LocalScope.Lookup environment id value)
  (core : Core.Expr) (type : Core.Ty)

local notation "original" => source spans name annotations

variable (accepted : elaborateComputationReturnTree? elaborateLocalExpression?
    types owner inputs (source spans name annotations) = some (core, type))
  (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)

include spans annotations named found accepted sameIds

/-- The old shared correspondence supplies this endpoint without either new body theorem. -/
theorem independent_checked_core_endpoint :
    Core.Evaluates (Resolved.LocalScope.values environment) store core value store := by
  have originalPaths := independent_original_prefixes spans name annotations owner
    inputs.names environment store id value named found
  have elaboration : ComputationReturnTreeElaborates
      (fun table context child core type =>
        elaborateLocalExpression? table context child = some (core, type))
      types owner inputs original core type :=
    (elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mp accepted
  exact (ComputationReturnTreeElaborates.evaluates_iff
    (ChildEval := LocalExpressionEvaluates)
    (F := Core.Expr.LocalFragment)
    (fun child => elaborateLocalExpression?_localFragment child)
    (fun fragment cutoff => fragment.weakenAt cutoff)
    (fun fragment leading suffix inserted => fragment.evaluates_insert_iff leading suffix inserted)
    (fun child aligned => elaborateLocalExpression?_evaluates_iff child aligned)
    elaboration sameIds).mp originalPaths.2.2

/-- Actual Core image endpoints use whole checking and exact IDs, never runtime typing. -/
theorem all_actual_core_images {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ClosedSourceBodyEvaluates owner inputs.names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) original actualValue actualFinal ↔
    actualValue = RuntimeValue.ofCore value ∧ actualFinal = store.map RuntimeValue.ofCore := by
  have paths := independent_original_prefixes spans name annotations owner inputs.names environment
    store id value named found
  have independent := independent_checked_core_endpoint spans name annotations owner types inputs
    environment store id value named found core type accepted sameIds
  constructor
  · intro actual
    obtain ⟨result, finalStore, same, finalSame, evaluated⟩ :=
      (paths.1.core_evaluates_iff accepted sameIds).mp actual
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated independent
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact (paths.1.core_evaluates_iff accepted sameIds).mpr
      ⟨value, store, rfl, rfl, independent⟩

end Checked
end Tests.ClosedSourceDataBodyImages
