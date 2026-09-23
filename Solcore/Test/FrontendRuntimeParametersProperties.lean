import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.LocalFunctionApplication

/-! ADR-0168: independent ordered parameter binding supplies the existing
checked input endpoint. Structural argument typing is not store allocation. -/

set_option autoImplicit false

namespace Tests.FrontendRuntimeParameters

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"RuntimeParameters", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private theorem differentIds : id 1 ≠ id 0 := by decide
private def span : Syntax.SourceSpan := ⟨⟨.main, "runtime-parameters.sol"⟩, 0, 4⟩
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name typeName : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation typeName)⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def types : TypeNameTable :=
  [(["Flag"], .bool), (["Alias"], .bool), (["Word"], .word),
   (["Fn"], .function .bool .bool), (["Cell"], .cell .word)]
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def parameters : List Syntax.FunctionParameter :=
  [parameter "first" "Flag", parameter "second" "Alias"]
private def inputs (first second : Bool) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "first" .bool (.bool first) .bool).bindFresh
    owner "second" .bool (.bool second) .bool
private theorem flagMeaning : TypeNameDenotes types (annotation "Flag") .bool := .named .head
private theorem aliasMeaning : TypeNameDenotes types (annotation "Alias") .bool :=
  .named (.tail (by decide) .head)
private theorem bound (first second : Bool) :
    RuntimeParametersBind types owner parameters [boolArg first, boolArg second] (inputs first second) :=
  .cons flagMeaning.structural (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons aliasMeaning.structural (by change "second" ∉ ["first"]; simp) .nil)

theorem empty_parameters_and_arguments_produce_exactly_empty_inputs
    (suppliedTypes : TypeNameTable) (suppliedOwner : Resolved.DeclarationId) :
    RuntimeParametersBind suppliedTypes suppliedOwner [] [] LocalInputs.empty ∧
    bindRuntimeParameters? suppliedTypes suppliedOwner [] [] = some LocalInputs.empty := ⟨.nil, rfl⟩

theorem either_direction_of_arity_mismatch_has_no_partial_result
    (suppliedTypes : TypeNameTable) (suppliedOwner : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument)
    (mismatched : params.length ≠ args.length) :
    bindRuntimeParameters? suppliedTypes suppliedOwner params args = none ∧
    ¬ ∃ result, RuntimeParametersBind suppliedTypes suppliedOwner params args result := by
  have absent : ¬ ∃ result, RuntimeParametersBind suppliedTypes suppliedOwner params args result := by
    rintro ⟨result, paired⟩
    exact mismatched (RuntimeParametersBind.arity paired)
  exact ⟨bindRuntimeParameters?_eq_none_iff.mpr absent, absent⟩

theorem successful_binding_recovers_exact_paired_rows_and_aligned_projections
    (suppliedTypes : TypeNameTable) (suppliedOwner : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) (result : LocalInputs)
    (accepted : bindRuntimeParameters? suppliedTypes suppliedOwner params args = some result) :
    RuntimeParameterRows suppliedTypes params args result.bindings.reverse ∧
    params.length = args.length ∧ result.bindings.length = args.length ∧
    result.bindings.map (·.type) = args.reverse.map (·.type) ∧
    result.bindings.map (·.value) = args.reverse.map (·.value) ∧
    result.ids = (List.range args.length).reverse.map (fun i => (⟨suppliedOwner, i⟩ : Resolved.LocalId)) ∧
    (result.names.map Prod.fst).Nodup ∧
    Resolved.LocalScope.ids result.environment = Resolved.LocalScope.ids result.context ∧
    Core.EnvironmentHasTypes (Resolved.LocalScope.values result.environment)
      (Resolved.LocalScope.values result.context) := by
  have paired := bindRuntimeParameters?_iff.mp accepted
  exact ⟨RuntimeParametersBind.rows paired, RuntimeParametersBind.arity paired,
    RuntimeParametersBind.bindings_length paired, RuntimeParametersBind.argument_types paired,
    RuntimeParametersBind.argument_values paired, RuntimeParametersBind.generated_ids paired,
    RuntimeParametersBind.names_nodup paired, result.sameIds, result.environmentTyped⟩

theorem same_typed_arguments_keep_their_paired_values_in_reverse_binding_order
    (first second : Bool) :
    RuntimeParametersBind types owner parameters [boolArg first, boolArg second] (inputs first second) ∧
    bindRuntimeParameters? types owner parameters [boolArg first, boolArg second] = some (inputs first second) ∧
    (inputs first second).ids = [id 1, id 0] ∧
    (inputs first second).names = [("second", id 1), ("first", id 0)] ∧
    (inputs first second).context = [(id 1, .bool), (id 0, .bool)] ∧
    (inputs first second).environment = [(id 1, .bool second), (id 0, .bool first)] := by
  exact ⟨bound first second, (bound first second).complete, rfl, rfl, rfl, rfl⟩

private theorem check_first (first second : Bool) :
    (inputs first second).check? (ref "first") = some (.var 1, .bool) :=
  elaborateLocalExpression?_complete (.identifier (.tail (by change "second" ≠ "first"; decide) .head))
    (.var (.tail differentIds .head)) (.var (.tail differentIds .head))
private theorem check_second (first second : Bool) :
    (inputs first second).check? (ref "second") = some (.var 0, .bool) :=
  elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)

theorem exact_lookup_positions_feed_the_existing_checked_runner
    (first second : Bool) (store : Core.Store) :
    LocalNameTable.Lookup (inputs first second).names "first" (id 0) ∧
    Resolved.LocalScope.Lookup (inputs first second).environment (id 0) (.bool first) ∧
    (inputs first second).check? (ref "first") = some (.var 1, .bool) ∧
    (inputs first second).check? (ref "second") = some (.var 0, .bool) ∧
    (inputs first second).run? 1 (ref "first") (.unit :: store) = some (.bool, .done (.bool first) (.unit :: store)) ∧
    (inputs first second).run? 1 (ref "second") (.unit :: store) = some (.bool, .done (.bool second) (.unit :: store)) ∧
    (inputs first second).run? 0 (ref "first") store = some (.bool, .outOfFuel
      (Core.State.initial (.var 1) [.bool second, .bool first] store)) := by
  refine ⟨.tail (by change "second" ≠ "first"; decide) .head, .tail differentIds .head,
    check_first first second, check_second first second, ?_, ?_, ?_⟩
  · rw [LocalInputs.run?, check_first]; rfl
  · rw [LocalInputs.run?, check_second]; rfl
  · rw [LocalInputs.run?, check_first]; rfl

private def rejectedPairs : List (List Syntax.FunctionParameter × List TypedRuntimeArgument) :=
  [([parameter "x" "Flag", parameter "x" "Alias"], [boolArg false, boolArg true]),
   ([parameter "x" "Flag", parameter "y" "Flag", parameter "x" "Alias"],
     [boolArg false, boolArg true, boolArg true]),
   ([parameter "x" "Flag"], [⟨.unit, .unit, .unit⟩]),
   ([parameter "x" "Unknown"], [boolArg false]),
   ([⟨span, .typed (some span) ⟨span, "x"⟩ (annotation "Flag")⟩], [boolArg false]),
   ([⟨span, .error⟩], [boolArg false]),
   ([⟨span, .typed none ⟨span, "x"⟩ ⟨span, .proxy span (annotation "Flag")⟩⟩], [boolArg false])]

theorem duplicates_mismatch_staging_recovery_and_unsupported_annotations_have_no_result
    (pair : List Syntax.FunctionParameter × List TypedRuntimeArgument) (present : pair ∈ rejectedPairs) :
    bindRuntimeParameters? types owner pair.1 pair.2 = none ∧
    ¬ ∃ result, RuntimeParametersBind types owner pair.1 pair.2 result := by
  have absent : ¬ ∃ result, RuntimeParametersBind types owner pair.1 pair.2 result := by
    simp only [rejectedPairs, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rintro ⟨_, bound⟩
      cases bound with
      | cons _ _ tail => cases tail with
        | cons _ unused _ => exact unused (by change "x" ∈ ["x"]; decide)
    · rintro ⟨_, bound⟩
      cases bound with
      | cons _ _ tail => cases tail with
        | cons _ _ tail => cases tail with
          | cons _ unused _ => exact unused (by change "x" ∈ ["y", "x"]; decide)
    · rintro ⟨_, bound⟩
      cases bound with
      | cons meaning _ _ => cases meaning.type_unique flagMeaning.structural
    · rintro ⟨_, bound⟩
      cases bound with
      | cons meaning _ _ => cases meaning with
        | named found =>
          have impossible := TypeNameTable.lookup?_iff.mpr found
          change (none : Option Core.Ty) = some .bool at impossible
          cases impossible
    · rintro ⟨_, bound⟩; cases bound
    · rintro ⟨_, bound⟩; cases bound
    · rintro ⟨_, bound⟩
      cases bound with | cons meaning _ _ => cases meaning
  exact ⟨bindRuntimeParameters?_eq_none_iff.mpr absent, absent⟩

theorem arbitrary_parameter_and_type_ranges_do_not_change_the_supplied_binding
    (outer nameSpan typeSpan qualifiedSpan componentSpan : Syntax.SourceSpan) (value : Bool) :
    let param : Syntax.FunctionParameter := ⟨outer, .typed none ⟨nameSpan, "raw"⟩
      ⟨typeSpan, .named ⟨qualifiedSpan, ⟨⟨⟨componentSpan, "Flag"⟩, []⟩⟩⟩ none⟩⟩
    let result := LocalInputs.empty.bindFresh owner "raw" .bool (.bool value) .bool
    RuntimeParametersBind types owner [param] [boolArg value] result ∧
    bindRuntimeParameters? types owner [param] [boolArg value] = some result := by
  intro param result
  have paired : RuntimeParametersBind types owner [param] [boolArg value] result :=
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil
  exact ⟨paired, paired.complete⟩

private def capturedClosure : Core.Value := .closure .bool .bool (.var 1) [.bool true]
private theorem capturedTyped : Core.ValueHasType capturedClosure (.function .bool .bool) :=
  .closure (.cons .bool .nil) (.var (by rfl))
private def closureArg : TypedRuntimeArgument := ⟨.function .bool .bool, capturedClosure, capturedTyped⟩
private def cellArg (location : Core.Location) : TypedRuntimeArgument :=
  ⟨.cell .word, .cellRef .word location, .cellRef⟩
private def opaqueInputs (location : Core.Location) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "f" (.function .bool .bool) capturedClosure capturedTyped).bindFresh
    owner "p" (.cell .word) (.cellRef .word location) .cellRef
private theorem functionMeaning : TypeNameDenotes types (annotation "Fn") (.function .bool .bool) :=
  .named (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
private theorem cellMeaning : TypeNameDenotes types (annotation "Cell") (.cell .word) :=
  .named (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem opaqueBound (location : Core.Location) :
    RuntimeParametersBind types owner [parameter "f" "Fn", parameter "p" "Cell"]
      [closureArg, cellArg location] (opaqueInputs location) :=
  .cons functionMeaning.structural (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons cellMeaning.structural (by change "p" ∉ ["f"]; simp) .nil)

theorem typed_closures_and_unallocated_references_are_inputs_not_store_allocation
    (location : Core.Location) (store : Core.Store) :
    RuntimeParametersBind types owner [parameter "f" "Fn", parameter "p" "Cell"]
      [closureArg, cellArg location] (opaqueInputs location) ∧
    bindRuntimeParameters? types owner [parameter "f" "Fn", parameter "p" "Cell"]
      [closureArg, cellArg location] = some (opaqueInputs location) ∧
    Core.ValueHasType capturedClosure (.function .bool .bool) ∧
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    ([] : Core.Store)[location]? = none ∧
    (opaqueInputs location).run? 1 (ref "f") store = some (.function .bool .bool, .done capturedClosure store) ∧
    (opaqueInputs location).run? 1 (ref "p") [] = some (.cell .word, .done (.cellRef .word location) []) := by
  have checkedF : (opaqueInputs location).check? (ref "f") = some (.var 1, .function .bool .bool) :=
    elaborateLocalExpression?_complete (.identifier (.tail (by change "p" ≠ "f"; decide) .head))
      (.var (.tail differentIds .head)) (.var (.tail differentIds .head))
  have checkedP : (opaqueInputs location).check? (ref "p") = some (.var 0, .cell .word) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  refine ⟨opaqueBound location, (opaqueBound location).complete, capturedTyped, .cellRef, by simp, ?_, ?_⟩
  · rw [LocalInputs.run?, checkedF]; rfl
  · rw [LocalInputs.run?, checkedP]; rfl

private def lyingClosure : Core.Value := .closure .bool .bool (.word .zero) []
theorem closure_metadata_cannot_replace_structural_argument_typing :
    lyingClosure.type = .function .bool .bool ∧
    ¬ Core.ValueHasType lyingClosure (.function .bool .bool) := by
  refine ⟨rfl, ?_⟩
  intro typed
  cases typed with | closure _ bodyTyped => cases bodyTyped

end Tests.FrontendRuntimeParameters
