import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.RuntimeParametersLayout
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties

/-! Type-only declarations require annotations, not runtime inhabitants.
Actual supplied structural values are used only by the separate binding bridge. -/

set_option autoImplicit false

namespace Tests.FrontendRuntimeParameterDeclarations

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParameterDeclarations", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "parameter-declarations.sol"⟩, 11, 2⟩
private def qualified (name : String) : Syntax.QualifiedName := ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩
private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named (qualified name) none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def types (first middle : Core.Ty) : TypeNameTable := [(["A"], first), (["B"], middle)]
private def parameters := [parameter "first" "A", parameter "middle" "B", parameter "last" "A"]
private def declaredInputs (first middle : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh owner "first" first).bindFresh owner "middle" middle).bindFresh owner "last" first
private theorem declared (first middle : Core.Ty) :
    RuntimeParametersDeclare (types first middle) owner parameters (declaredInputs first middle) :=
  .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "middle" ∉ ["first"]; simp)
      (.cons (.named .head) (by change "last" ∉ ["middle", "first"]; simp) .nil))

theorem arbitrary_types_declare_in_source_order_without_any_runtime_value
    (first middle : Core.Ty) :
    RuntimeParametersDeclare (types first middle) owner parameters (declaredInputs first middle) ∧
    declareRuntimeParameters? (types first middle) owner parameters = some (declaredInputs first middle) ∧
    (declaredInputs first middle).ids = [id 2, id 1, id 0] ∧
    (declaredInputs first middle).names = [("last", id 2), ("middle", id 1), ("first", id 0)] ∧
    (declaredInputs first middle).context = [(id 2, first), (id 1, middle), (id 0, first)] :=
  ⟨declared first middle, (declared first middle).complete, rfl, rfl, rfl⟩

theorem empty_static_preparation_needs_neither_arguments_nor_a_value_environment
    (table : TypeNameTable) (suppliedOwner : Resolved.DeclarationId) :
    RuntimeParametersDeclare table suppliedOwner [] LocalTypeInputs.empty ∧
    declareRuntimeParameters? table suppliedOwner [] = some LocalTypeInputs.empty := ⟨.nil, rfl⟩

private theorem noNamedValue (dataType : Core.DataTypeId) :
    ¬ ∃ value, Core.ValueHasType value (.namedData dataType) [] := by
  rintro ⟨value, typing⟩
  cases typing with
  | constructed found _ =>
      simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem nominal_annotation_success_does_not_assert_runtime_inhabitation
    (dataType : Core.DataTypeId) :
    declareRuntimeParameters? (types (.namedData dataType) .unit) owner parameters =
      some (declaredInputs (.namedData dataType) .unit) ∧
    RuntimeParametersDeclare (types (.namedData dataType) .unit) owner parameters
      (declaredInputs (.namedData dataType) .unit) ∧
    (¬ ∃ value, Core.ValueHasType value (.namedData dataType) []) ∧
    (¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData dataType) := by
  refine ⟨rfl, declared _ _, noNamedValue dataType, ?_⟩
  rintro ⟨argument, sameType⟩
  apply noNamedValue dataType
  exact ⟨argument.value, sameType ▸ argument.valueTyped⟩

private theorem argumentTypes {table : TypeNameTable} {suppliedOwner : Resolved.DeclarationId}
    {params : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument} {inputs : LocalInputs}
    (bound : RuntimeParametersBind table suppliedOwner params arguments inputs) :
    arguments.map (·.type) = inputs.context.values.reverse := by
  have stored : inputs.context.values = arguments.reverse.map (·.type) := by
    simpa only [LocalInputs.context, Resolved.LocalScope.values, List.map_map, Function.comp_def] using
      RuntimeParametersBind.argument_types bound
  simp only [stored, List.map_reverse, List.reverse_reverse]

theorem actual_typed_binding_erases_to_exact_static_declaration
    {table : TypeNameTable} {suppliedOwner : Resolved.DeclarationId}
    {params : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument} {inputs : LocalInputs}
    (bound : RuntimeParametersBind table suppliedOwner params arguments inputs) :
    RuntimeParametersDeclare table suppliedOwner params inputs.toTypeInputs ∧
    declareRuntimeParameters? table suppliedOwner params = some inputs.toTypeInputs ∧
    inputs.toTypeInputs.ids = inputs.ids ∧ inputs.toTypeInputs.names = inputs.names ∧
    inputs.toTypeInputs.context = inputs.context ∧
    arguments.map (·.type) = inputs.toTypeInputs.context.values.reverse := by
  have erased := RuntimeParametersBind.erase_values bound
  exact ⟨erased, erased.complete, inputs.toTypeInputs_ids, inputs.toTypeInputs_names,
    inputs.toTypeInputs_context, by simpa only [LocalInputs.toTypeInputs_context] using argumentTypes bound⟩

theorem matching_supplied_arguments_reconstruct_exact_static_rows_and_their_actual_values
    {table : TypeNameTable} {suppliedOwner : Resolved.DeclarationId}
    {params : List Syntax.FunctionParameter} {static : LocalTypeInputs}
    (meaning : RuntimeParametersDeclare table suppliedOwner params static)
    (arguments : List TypedRuntimeArgument)
    (matching : arguments.map (·.type) = static.context.values.reverse) :
    ∃ inputs, RuntimeParametersBind table suppliedOwner params arguments inputs ∧
      bindRuntimeParameters? table suppliedOwner params arguments = some inputs ∧
      inputs.toTypeInputs = static ∧ inputs.environment.values = arguments.reverse.map (·.value) ∧
      Core.EnvironmentHasTypes inputs.environment.values static.context.values := by
  obtain ⟨inputs, bound, erased⟩ := RuntimeParametersDeclare.bind_typed_arguments meaning arguments matching
  have sameContext : inputs.context = static.context := by
    rw [← LocalInputs.toTypeInputs_context, erased]
  have values : inputs.environment.values = arguments.reverse.map (·.value) := by
    simpa only [LocalInputs.environment, Resolved.LocalScope.values, List.map_map, Function.comp_def] using
      RuntimeParametersBind.argument_values bound
  exact ⟨inputs, bound, bound.complete, erased, values, sameContext ▸ inputs.environmentTyped⟩

theorem wrong_arity_or_ordered_types_cannot_use_static_success_as_runtime_acceptance
    {table : TypeNameTable} {suppliedOwner : Resolved.DeclarationId}
    {params : List Syntax.FunctionParameter} {static : LocalTypeInputs}
    (meaning : RuntimeParametersDeclare table suppliedOwner params static)
    (arguments : List TypedRuntimeArgument)
    (mismatch : arguments.map (·.type) ≠ static.context.values.reverse) :
    declareRuntimeParameters? table suppliedOwner params = some static ∧
    bindRuntimeParameters? table suppliedOwner params arguments = none ∧
    ¬ ∃ inputs, RuntimeParametersBind table suppliedOwner params arguments inputs := by
  have absent : ¬ ∃ inputs, RuntimeParametersBind table suppliedOwner params arguments inputs := by
    rintro ⟨inputs, bound⟩
    have sameContext := congrArg LocalTypeInputs.context
      (meaning.result_unique (RuntimeParametersBind.erase_values bound))
    simp only [LocalInputs.toTypeInputs_context] at sameContext
    apply mismatch
    rw [sameContext]
    exact argumentTypes bound
  exact ⟨meaning.complete, bindRuntimeParameters?_eq_none_iff.mpr absent, absent⟩

private def runtimeInputs : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "first" .bool (.bool false) .bool).bindFresh
    owner "middle" .word (.word Core.Word.zero) .word).bindFresh owner "last" .bool (.bool true) .bool
private def supplied : List TypedRuntimeArgument :=
  [⟨.bool, .bool false, .bool⟩, ⟨.word, .word Core.Word.zero, .word⟩, ⟨.bool, .bool true, .bool⟩]
private theorem runtimeBound : RuntimeParametersBind (types .bool .word) owner parameters supplied runtimeInputs :=
  .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "middle" ∉ ["first"]; simp)
      (.cons (.named .head) (by change "last" ∉ ["middle", "first"]; simp) .nil))

theorem repeated_types_keep_distinct_source_values_when_erased_and_reconstructed :
    RuntimeParametersBind (types .bool .word) owner parameters supplied runtimeInputs ∧
    runtimeInputs.toTypeInputs = declaredInputs .bool .word ∧
    runtimeInputs.environment = [(id 2, .bool true), (id 1, .word Core.Word.zero), (id 0, .bool false)] ∧
    declareRuntimeParameters? (types .bool .word) owner parameters = some runtimeInputs.toTypeInputs ∧
    bindRuntimeParameters? (types .bool .word) owner parameters supplied = some runtimeInputs :=
  ⟨runtimeBound, rfl, rfl, (RuntimeParametersBind.erase_values runtimeBound).complete, runtimeBound.complete⟩

private def rejectedParameters : List (List Syntax.FunctionParameter) :=
  [[parameter "x" "A", parameter "x" "B"],
   [parameter "x" "A", parameter "y" "B", parameter "x" "A"],
   [parameter "x" "Unknown"],
   [⟨span, .typed none ⟨span, "x"⟩ ⟨span, .named (qualified "A") (some ⟨span, ⟨annotation "A", []⟩⟩)⟩⟩],
   [⟨span, .typed (some span) ⟨span, "x"⟩ (annotation "A")⟩],
   [⟨span, .error⟩],
   [⟨span, .typed none ⟨span, "x"⟩ ⟨span, .proxy span (annotation "A")⟩⟩]]

theorem duplicates_unknown_annotations_arguments_staging_and_recovery_are_rejected
    (params : List Syntax.FunctionParameter) (member : params ∈ rejectedParameters) :
    declareRuntimeParameters? (types .bool .word) owner params = none ∧
    ¬ ∃ inputs, RuntimeParametersDeclare (types .bool .word) owner params inputs := by
  have rejected : declareRuntimeParameters? (types .bool .word) owner params = none := by
    simp only [rejectedParameters, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  exact ⟨rejected, declareRuntimeParameters?_eq_none_iff.mp rejected⟩

end Tests.FrontendRuntimeParameterDeclarations
