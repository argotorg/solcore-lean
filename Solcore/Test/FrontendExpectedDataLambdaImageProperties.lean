import Solcore.Frontend.Expected
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.ClosedSource
import Solcore.Core.Eval
import Solcore.Resolved.Eval

/- Arbitrarily nested original identity bodies retain spans, captures and raw payloads. -/
set_option autoImplicit false
namespace Tests.ExpectedDataLambdaImages
open Solcore Solcore.Frontend

private def statements (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier) :
    Nat → List Syntax.Statement
  | 0 => [⟨spans 4, .returnStmt (some ⟨spans 5, .identifier name⟩)⟩]
  | n + 1 => [⟨spans (n + 10), .block (statements spans name n)⟩]

private def body (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (depth : Nat) : Syntax.Block := ⟨spans 3, statements spans name depth⟩

private def source (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (depth : Nat) : Syntax.Expr :=
  ⟨spans 0, .lambda (spans 1) ⟨spans 2, [⟨spans 6, .inferred name⟩]⟩
    none (body spans name depth)⟩

private theorem original_body (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (depth : Nat) (blockSpan : Syntax.SourceSpan) (owner : Resolved.DeclarationId)
    (names : LocalNameTable) (captured : List (Resolved.LocalId × RuntimeValue))
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue) :
    ClosedSourceDataBody ⟨blockSpan, statements spans name depth⟩ ∧
    ClosedSourceBodyEvaluates owner ((name.value, id) :: names) ((id, value) :: captured)
      store ⟨blockSpan, statements spans name depth⟩ value store := by
  induction depth generalizing blockSpan with
  | zero => exact ⟨.expression .reference, .expression (.reference .head .head)⟩
  | succ n ih =>
      have child := ih (spans (n + 10))
      exact ⟨.block child.1, .block child.2⟩

private theorem body_checked (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (depth : Nat) (blockSpan : Syntax.SourceSpan) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (type : Core.Ty) :
    ComputationReturnTreeElaborates
      (fun table context child core ty => elaborateLocalExpression? table context child = some (core, ty))
      types owner (inputs.bindFresh owner name.value type)
      ⟨blockSpan, statements spans name depth⟩ (.var 0) type := by
  induction depth generalizing blockSpan with
  | zero =>
      apply ComputationReturnTreeElaborates.expression
      exact elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  | succ n ih => exact .block (ih (spans (n + 10)))

private theorem checked (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (depth : Nat) (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (type : Core.Ty) (wf : type.WellFormed []) :
    elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs
      (source spans name depth) (.function type type) = some (.lambda type type (.var 0)) :=
  (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
    (.lambda (.lambda .inferred .omitted) wf wf
      (body_checked spans name depth (spans 3) types owner inputs type))

private theorem mapped_lookup {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

section Family
variable (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier) (depth : Nat)
  (types : TypeNameTable) (savedOwner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
  (environment : Resolved.Environment) (store : Core.Store) (value : Core.Value)
  (type : Core.Ty) (wf : type.WellFormed [])
  (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)

local notation "original" => source spans name depth
local notation "captures" => List.map (fun row => (Prod.fst row, RuntimeValue.ofCore (Prod.snd row))) environment
local notation "heap" => store.map RuntimeValue.ofCore

include wf in
/-- Source and Core identity endpoints are constructed without a correspondence law. -/
theorem independent_body_and_checker :
    ClosedSourceDataBody (body spans name depth) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? types savedOwner inputs
      original (.function type type) = some (.lambda type type (.var 0)) ∧
    Core.Evaluates (value :: Resolved.LocalScope.values environment) store (.var 0) value store := by
  exact ⟨(original_body spans name depth (spans 3) savedOwner inputs.names captures heap
    (Resolved.freshLocalId savedOwner inputs.ids) (RuntimeValue.ofCore value)).1,
    checked spans name depth types savedOwner inputs type wf, .var rfl⟩

section Invocation
variable (callerOwner : Resolved.DeclarationId) (callerNames : LocalNameTable)
  (callerCaptured : List (Resolved.LocalId × RuntimeValue))
  (calleeName argumentName : Syntax.Identifier) (calleeId argumentId : Resolved.LocalId)
  (calleeNamed : LocalNameTable.Lookup callerNames calleeName.value calleeId)
  (calleeFound : Resolved.LocalScope.Lookup callerCaptured calleeId
    (.sourceClosure (source spans name depth) savedOwner inputs.names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))))
  (argumentNamed : LocalNameTable.Lookup callerNames argumentName.value argumentId)
  (argumentFound : Resolved.LocalScope.Lookup callerCaptured argumentId (RuntimeValue.ofCore value))

include calleeNamed calleeFound argumentNamed argumentFound in
private theorem invocation_source :
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured heap
      ⟨spans 7, .call ⟨spans 8, .identifier calleeName⟩
        ⟨spans 9, [⟨spans 10, .identifier argumentName⟩]⟩⟩ (RuntimeValue.ofCore value) heap :=
  .call .inferred (.reference calleeNamed calleeFound) (.reference argumentNamed argumentFound)
    (original_body spans name depth (spans 3) savedOwner inputs.names captures heap
      (Resolved.freshLocalId savedOwner (inputs.names.map Prod.snd)) (RuntimeValue.ofCore value)).2

include types wf sameIds calleeNamed calleeFound argumentNamed argumentFound in
/-- Arbitrary mixed caller rows invoke the saved identity with its entire store. -/
theorem invocation_original_and_all_actual_images :
    let call : Syntax.Expr := ⟨spans 7, .call ⟨spans 8, .identifier calleeName⟩
      ⟨spans 9, [⟨spans 10, .identifier argumentName⟩]⟩⟩
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured heap call
      (RuntimeValue.ofCore value) heap ∧
    ∀ actual final, ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured heap
      call actual final ↔ actual = RuntimeValue.ofCore value ∧ final = heap := by
  have originalEvaluation := invocation_source spans name depth savedOwner inputs environment store value
    callerOwner callerNames callerCaptured calleeName argumentName calleeId argumentId
    calleeNamed calleeFound argumentNamed argumentFound
  have paths := independent_body_and_checker spans name depth types savedOwner inputs
    environment store value type wf
  refine ⟨originalEvaluation, ?_⟩
  intro actual final
  have image := closedSourceExpectedDataLambda_invocation_core_iff
    (callerOwner := callerOwner) (bodyStore := store)
    (callSpan := spans 7) (argumentsSpan := spans 9)
    (callee := ⟨spans 8, .identifier calleeName⟩) (argument := ⟨spans 10, .identifier argumentName⟩)
    (actualValue := actual) (actualFinal := final) .inferred paths.1 paths.2.1 sameIds
    (.reference calleeNamed calleeFound) (.reference argumentNamed argumentFound)
  constructor
  · intro evaluated
    obtain ⟨result, finalStore, same, sameFinal, core⟩ := image.mp evaluated
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic core paths.2.2
    exact ⟨same, sameFinal⟩
  · rintro ⟨rfl, rfl⟩
    exact image.mpr ⟨value, store, rfl, rfl, paths.2.2⟩

end Invocation

section Application
variable (argumentName : Syntax.Identifier) (argumentId : Resolved.LocalId) (index : Nat)
  (argumentNamed : LocalNameTable.Lookup inputs.names argumentName.value argumentId)
  (argumentFound : Resolved.LocalScope.Lookup environment argumentId value)
  (argumentIndex : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) argumentId index)

include argumentNamed argumentFound in
private theorem application_source :
    ClosedSourceExpressionEvaluates savedOwner inputs.names captures heap
      ⟨spans 7, .call original ⟨spans 9, [⟨spans 10, .identifier argumentName⟩]⟩⟩
      (RuntimeValue.ofCore value) heap :=
  .call .inferred (.creation .inferred) (.reference argumentNamed (mapped_lookup argumentFound))
    (original_body spans name depth (spans 3) savedOwner inputs.names captures heap
      (Resolved.freshLocalId savedOwner (inputs.names.map Prod.snd)) (RuntimeValue.ofCore value)).2

include argumentFound argumentIndex in
private theorem application_core :
    Core.Evaluates (Resolved.LocalScope.values environment) store
      (.apply (.lambda type type (.var 0)) (.var index)) value store :=
  .apply .lambda (.var ((Resolved.LocalScope.lookup_iff_getElem? argumentIndex).mp argumentFound))
    (.var rfl)

include types wf sameIds argumentNamed argumentFound argumentIndex in
/-- Direct original application preserves an opaque reference payload, with no domain typing premise. -/
theorem application_original_and_all_actual_images :
    let call : Syntax.Expr :=
      ⟨spans 7, .call original ⟨spans 9, [⟨spans 10, .identifier argumentName⟩]⟩⟩
    ClosedSourceExpressionEvaluates savedOwner inputs.names captures heap call
      (RuntimeValue.ofCore value) heap ∧
    ∀ actual final, ClosedSourceExpressionEvaluates savedOwner inputs.names captures heap
      call actual final ↔ actual = RuntimeValue.ofCore value ∧ final = heap := by
  have originalEvaluation := application_source spans name depth savedOwner inputs environment store value
    argumentName argumentId argumentNamed argumentFound
  have independent := application_core environment store value type argumentId index argumentFound argumentIndex
  have paths := independent_body_and_checker spans name depth types savedOwner inputs
    environment store value type wf
  refine ⟨originalEvaluation, ?_⟩
  intro actual final
  have image := closedSourceExpectedDataLambda_application_core_iff
    (callSpan := spans 7) (argumentsSpan := spans 9) (initialStore := store)
    (argument := ⟨spans 10, .identifier argumentName⟩) (actualValue := actual) (actualFinal := final)
    .inferred paths.1 paths.2.1 sameIds .reference (.identifier argumentNamed) (.var argumentIndex)
  constructor
  · intro evaluated
    obtain ⟨result, finalStore, same, sameFinal, core⟩ := image.mp evaluated
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic core independent
    exact ⟨same, sameFinal⟩
  · rintro ⟨rfl, rfl⟩
    exact image.mpr ⟨value, store, rfl, rfl, independent⟩

end Application
end Family
end Tests.ExpectedDataLambdaImages
