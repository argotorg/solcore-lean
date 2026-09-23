import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.LocalFunctionApplication

/-! Owner changes relabel identities, not positional Core or runtime values.
Independent entry witnesses retain every header and parameter restriction. -/

set_option autoImplicit false

namespace Tests.FrontendRuntimeOwner

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "runtime-owner.sol"⟩, 9, 1⟩
private def firstOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"RuntimeOwner", by decide⟩], by decide⟩⟩, 0⟩
private def secondOwner : Resolved.DeclarationId := { firstOwner with declarationIndex := 1 }
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Bool"], .bool), (["Value"], type)]
private def params := [parameter "c" "Bool", parameter "x" "Value"]
private def args (argument : TypedRuntimeArgument) := [⟨.bool, .bool true, .bool⟩, argument]
private def inputs (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "c" .bool (.bool true) .bool).bindFresh
    owner "x" argument.type argument.value argument.valueTyped
private def source : Syntax.Expr := ⟨span, .conditional (ref "c") span (ref "x") span (ref "x")⟩
private def core : Core.Expr := .ifE (.var 1) (.var 0) (.var 0)
private def declaration (body : Syntax.Expr := source) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "selected"⟩, none, ⟨span, params⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation "Value"]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some body)⟩]⟩⟩⟩
private def prepared (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) : PreparedRuntimeFunction :=
  ⟨inputs owner argument, core, argument.type⟩
private theorem namesDifferent : "x" ≠ "c" := by decide
private theorem idsDifferent (owner : Resolved.DeclarationId) :
    Resolved.freshLocalId owner [Resolved.freshLocalId owner []] ≠ Resolved.freshLocalId owner [] :=
  Resolved.freshLocalId_cons_fresh_ne owner []
private theorem bound (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) :
    RuntimeParametersBind (types argument.type) owner params (args argument) (inputs owner argument) :=
  .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "x" ∉ ["c"]; simp) .nil)
private theorem preparation (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) :
    RuntimeFunctionPrepares (types argument.type) owner declaration (args argument) (prepared owner argument) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩, bound owner argument,
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.conditional (.identifier (.tail namesDifferent .head)) (.identifier .head) (.identifier .head))
      (.ifE (.var (.tail (idsDifferent owner) .head)) (.var .head) (.var .head))
      (.ifE (.var (.tail (idsDifferent owner) .head)) (.var .head) (.var .head))⟩
private theorem cost (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (types argument.type) owner declaration (args argument)
      store argument.type argument.value store 4 := by
  have condition : LocalExpressionEvaluatesWithCost (inputs owner argument).names
      (inputs owner argument).environment store (ref "c") (.bool true) store 1 :=
    .identifier (.tail namesDifferent .head) (.tail (idsDifferent owner) .head)
  have selected : LocalExpressionEvaluatesWithCost (inputs owner argument).names
      (inputs owner argument).environment store (ref "x") argument.value store 1 :=
    .identifier .head .head
  exact .intro (preparation owner argument) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.ifTrue condition selected))

theorem injective_owner_transport_keeps_independent_parameters_and_exact_preparation
    (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    let mapped := (inputs owner argument).mapIds (ownerLocalIdMap mapping)
      (ownerLocalIdMap_injective mapping injective)
    RuntimeParametersBind (types argument.type) (mapping owner) params (args argument) mapped ∧
    RuntimeFunctionPrepares (types argument.type) (mapping owner) declaration (args argument)
      ⟨mapped, core, argument.type⟩ := by
  intro mapped
  exact ⟨(bound owner argument).map_owner mapping injective,
    (preparation owner argument).mapOwner mapping injective⟩

theorem distinct_owners_change_real_ids_but_preserve_checked_core_and_runtime_values
    (argument : TypedRuntimeArgument) :
    firstOwner ≠ secondOwner ∧
    prepareRuntimeFunction? (types argument.type) firstOwner declaration (args argument) =
      some (prepared firstOwner argument) ∧
    prepareRuntimeFunction? (types argument.type) secondOwner declaration (args argument) =
      some (prepared secondOwner argument) ∧
    (inputs firstOwner argument).ids = [⟨firstOwner, 1⟩, ⟨firstOwner, 0⟩] ∧
    (inputs secondOwner argument).ids = [⟨secondOwner, 1⟩, ⟨secondOwner, 0⟩] ∧
    (inputs firstOwner argument).ids ≠ (inputs secondOwner argument).ids ∧
    (inputs firstOwner argument).environment.values = [argument.value, .bool true] ∧
    (inputs secondOwner argument).environment.values = [argument.value, .bool true] := by
  refine ⟨by decide, (preparation firstOwner argument).complete,
    (preparation secondOwner argument).complete, rfl, rfl, ?_, rfl, rfl⟩
  intro same
  change [(⟨firstOwner, 1⟩ : Resolved.LocalId), ⟨firstOwner, 0⟩] = [⟨secondOwner, 1⟩, ⟨secondOwner, 0⟩] at same
  exact (by decide : firstOwner ≠ secondOwner) (congrArg Resolved.LocalId.owner (List.cons.inj same).1)

theorem every_fuel_preserves_full_results_including_the_same_intermediate_state
    (leftOwner rightOwner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) (store : Core.Store) :
    (∀ fuel, runRuntimeFunction? (types argument.type) leftOwner declaration (args argument) fuel store =
      runRuntimeFunction? (types argument.type) rightOwner declaration (args argument) fuel store) ∧
    runRuntimeFunction? (types argument.type) leftOwner declaration (args argument) 0 store =
      some (argument.type, .outOfFuel (Core.State.initial core [argument.value, .bool true] store)) ∧
    runRuntimeFunction? (types argument.type) rightOwner declaration (args argument) 0 store =
      some (argument.type, .outOfFuel (Core.State.initial core [argument.value, .bool true] store)) ∧
    (∃ suspended,
      runRuntimeFunction? (types argument.type) leftOwner declaration (args argument) 2 store =
        some (argument.type, .outOfFuel suspended) ∧
      runRuntimeFunction? (types argument.type) rightOwner declaration (args argument) 2 store =
        some (argument.type, .outOfFuel suspended)) ∧
    runRuntimeFunction? (types argument.type) rightOwner declaration (args argument) 4 store =
      some (argument.type, .done argument.value store) := by
  have same (fuel : Nat) := runRuntimeFunction?_owner_eq
    (types argument.type) leftOwner rightOwner declaration (args argument) fuel store
  have zero : runRuntimeFunction? (types argument.type) leftOwner declaration (args argument) 0 store =
      some (argument.type, .outOfFuel (Core.State.initial core [argument.value, .bool true] store)) := by
    rw [runRuntimeFunction?, (preparation leftOwner argument).complete]
    rfl
  obtain ⟨suspended, exhausted⟩ := ((cost leftOwner argument store).run_outOfFuel_iff (fuel := 2)).mpr (by decide)
  exact ⟨same, zero, (same 0).symm.trans zero,
    ⟨suspended, exhausted, (same 2).symm.trans exhausted⟩,
    (same 4).symm.trans ((cost leftOwner argument store).run_done_iff.mpr (by decide))⟩

private def missing : Syntax.Expr :=
  ⟨span, .conditional (ref "c") span (ref "x") span (ref "missing")⟩
private theorem missingRejected (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) :
    prepareRuntimeFunction? (types argument.type) owner (declaration missing) (args argument) = none := by
  apply prepareRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨target, accepted⟩
  have sameInputs := accepted.parameters.result_unique (bound owner argument)
  have body := accepted.body
  rw [sameInputs] at body
  cases body with
  | single body =>
      cases body with
      | expression resolution _ _ =>
          cases resolution with
          | conditional _ _ right =>
              cases right with
              | identifier found =>
                  have impossible := LocalNameTable.lookup?_iff.mpr found
                  change none = some _ at impossible
                  cases impossible

theorem skipped_missing_reference_remains_a_whole_entry_failure_after_owner_change
    (leftOwner rightOwner : Resolved.DeclarationId) (argument : TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) :
    ReturnBodyEvaluatesWithCost (inputs leftOwner argument).names (inputs leftOwner argument).environment
      store (declaration missing).value.body argument.value store 4 ∧
    prepareRuntimeFunction? (types argument.type) leftOwner (declaration missing) (args argument) = none ∧
    prepareRuntimeFunction? (types argument.type) rightOwner (declaration missing) (args argument) = none ∧
    runRuntimeFunction? (types argument.type) leftOwner (declaration missing) (args argument) fuel store = none ∧
    runRuntimeFunction? (types argument.type) rightOwner (declaration missing) (args argument) fuel store = none := by
  have rejected := missingRejected leftOwner argument
  have rightRejected : prepareRuntimeFunction? (types argument.type) rightOwner (declaration missing)
      (args argument) = none := by
    have same := prepareRuntimeFunction?_owner_projection_eq
      (types argument.type) leftOwner rightOwner (declaration missing) (args argument)
    rw [rejected] at same
    cases result : prepareRuntimeFunction? (types argument.type) rightOwner (declaration missing) (args argument) with
    | none => rfl
    | some target => simp only [result, Option.map_none, Option.map_some, reduceCtorEq] at same
  have condition : LocalExpressionEvaluatesWithCost (inputs leftOwner argument).names
      (inputs leftOwner argument).environment store (ref "c") (.bool true) store 1 :=
    .identifier (.tail namesDifferent .head) (.tail (idsDifferent leftOwner) .head)
  have selected : LocalExpressionEvaluatesWithCost (inputs leftOwner argument).names
      (inputs leftOwner argument).environment store (ref "x") argument.value store 1 := .identifier .head .head
  exact ⟨.expression (.ifTrue condition selected), rejected, rightRejected,
    by simp only [runRuntimeFunction?, rejected, bind, Option.bind_none],
    by simp only [runRuntimeFunction?, rightRejected, bind, Option.bind_none]⟩

theorem opaque_closures_and_unallocated_cells_are_returned_without_interpretation
    (owner : Resolved.DeclarationId) (location : Core.Location) (store : Core.Store)
    (closure : Core.Value) (closureTyped : Core.ValueHasType closure (.function .bool .bool)) :
    runRuntimeFunction? (types (.function .bool .bool)) owner declaration
      (args ⟨.function .bool .bool, closure, closureTyped⟩) 4 store =
        some (.function .bool .bool, .done closure store) ∧
    runRuntimeFunction? (types (.cell .word)) owner declaration
      (args ⟨.cell .word, .cellRef .word location, .cellRef⟩) 4 store =
        some (.cell .word, .done (.cellRef .word location) store) ∧
    ([] : Core.Store)[location]? = none :=
  ⟨(cost owner ⟨.function .bool .bool, closure, closureTyped⟩ store).run_done_iff.mpr (by decide),
    (cost owner ⟨.cell .word, .cellRef .word location, .cellRef⟩ store).run_done_iff.mpr (by decide), by simp⟩

private def shift (id : Resolved.LocalId) : Resolved.LocalId :=
  { id with binderIndex := id.binderIndex + 10 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  cases left
  cases right
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases owners
  cases indices
  rfl

theorem arbitrary_injective_index_shifts_do_not_commute_with_empty_allocation
    (owner : Resolved.DeclarationId) :
    Function.Injective shift ∧
    shift (Resolved.freshLocalId owner []) = ⟨owner, 10⟩ ∧
    Resolved.freshLocalId owner ([].map shift) = ⟨owner, 0⟩ ∧
    shift (Resolved.freshLocalId owner []) ≠ Resolved.freshLocalId owner ([].map shift) := by
  refine ⟨shiftInjective, rfl, rfl, ?_⟩
  intro same
  have indices := congrArg Resolved.LocalId.binderIndex same
  change 10 = 0 at indices
  cases indices

end Tests.FrontendRuntimeOwner
