import Solcore.Frontend.RuntimeParameterDeclarationReferenceProperties
import Solcore.Frontend.RuntimeParameterDeclarationsOwnerProperties
import Solcore.Frontend.RuntimeParameterDeclarationsTypeExtensionProperties
import Solcore.Frontend.RuntimeFunctionParameterReturnProperties
import Solcore.Frontend.RuntimeFunctionPreparationFactorization

/-! Structural annotations keep each original parameter and supplied value whole.
Independent constructor evidence fixes static and runtime bundles before checking. -/
set_option autoImplicit false
namespace Tests.FrontendStructuralParameter
open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "structural-parameter.sol"⟩, 234, 1⟩
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Parameters", by decide⟩], by decide⟩⟩, n⟩
private def named : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def unit : Syntax.TypeExpr := ⟨span, .tuple []⟩
private def single (child : Syntax.TypeExpr) : Syntax.TypeExpr := ⟨span, .tuple [child]⟩
private def shape : Nat → Syntax.TypeExpr
  | 0 => unit
  | n + 1 => ⟨span, .tuple [named, single (shape n)]⟩
private def product (type : Core.Ty) : Nat → Core.Ty
  | 0 => .unit
  | n + 1 => .product type (product type n)
private def packed (value : Core.Value) : Nat → Core.Value
  | 0 => .unit
  | n + 1 => .pair value (packed value n)
private def table (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private theorem meaning (type : Core.Ty) (n : Nat) : StructuralTypeDenotes (table type) (shape n) (product type n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.named .head) (.single ih)
private def parameter (name : String) (annotation : Syntax.TypeExpr) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ annotation⟩
private def parameters (n : Nat) := [parameter "packed" (shape n), parameter "ignored" unit, parameter "leaf" (single named)]
private def static (type : Core.Ty) (n : Nat) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh (owner 0) "packed" (product type n)).bindFresh (owner 0) "ignored" .unit).bindFresh (owner 0) "leaf" type
private theorem declared (type : Core.Ty) (n : Nat) : RuntimeParametersDeclare (table type) (owner 0) (parameters n) (static type n) :=
  .cons (meaning type n) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons .unit (by change "ignored" ∉ ["packed"]; decide)
      (.cons (.single (.named .head)) (by change "leaf" ∉ ["ignored", "packed"]; decide) .nil))
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private theorem packedTyped {type : Core.Ty} (actual : Actual type) (n : Nat) :
    Core.ValueHasType (packed actual.val n) (product type n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair actual.property ih
private def packArgument {type : Core.Ty} (actual : Actual type) (n : Nat) : TypedRuntimeArgument :=
  ⟨product type n, packed actual.val n, packedTyped actual n⟩
private def unitArgument : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
private def leafArgument {type : Core.Ty} (actual : Actual type) : TypedRuntimeArgument := ⟨type, actual.val, actual.property⟩
private def arguments {type : Core.Ty} (actual : Actual type) (n : Nat) := [packArgument actual n, unitArgument, leafArgument actual]
private def runtime {type : Core.Ty} (actual : Actual type) (n : Nat) : LocalInputs :=
  ((LocalInputs.empty.bindFresh (owner 0) "packed" (product type n) (packed actual.val n) (packedTyped actual n)).bindFresh
    (owner 0) "ignored" .unit .unit .unit).bindFresh (owner 0) "leaf" type actual.val actual.property
private theorem bound {type : Core.Ty} (actual : Actual type) (n : Nat) :
    RuntimeParametersBind (table type) (owner 0) (parameters n) (arguments actual n) (runtime actual n) :=
  .cons (meaning type n) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons .unit (by change "ignored" ∉ ["packed"]; decide)
      (.cons (.single (.named .head)) (by change "leaf" ∉ ["ignored", "packed"]; decide) .nil))

theorem arbitrary_structural_depth_declares_three_original_rows (type : Core.Ty) (n : Nat) :
    RuntimeParametersDeclare (table type) (owner 0) (parameters n) (static type n) ∧
    declareRuntimeParameters? (table type) (owner 0) (parameters n) = some (static type n) ∧
    (static type n).bindings = [⟨"leaf", ⟨owner 0, 2⟩, type⟩, ⟨"ignored", ⟨owner 0, 1⟩, .unit⟩,
      ⟨"packed", ⟨owner 0, 0⟩, product type n⟩] ∧
    interpretTypeName? (table type) (shape n) = none :=
  ⟨declared type n, (declared type n).complete, rfl, by cases n <;> rfl⟩

theorem paired_constructor_rows_do_not_flatten_products_or_omit_unit {type : Core.Ty} (actual : Actual type) (n : Nat) :
    RuntimeParameterDeclarationRows (table type) (parameters n) (static type n).bindings.reverse ∧
    RuntimeParameterRows (table type) (parameters n) (arguments actual n) (runtime actual n).bindings.reverse ∧
    bindRuntimeParameters? (table type) (owner 0) (parameters n) (arguments actual n) = some (runtime actual n) ∧
    (runtime actual n).environment = [(⟨owner 0, 2⟩, actual.val), (⟨owner 0, 1⟩, .unit), (⟨owner 0, 0⟩, packed actual.val n)] :=
  ⟨.cons (.typed (meaning type n)) (.cons (.typed .unit) (.cons (.typed (.single (.named .head))) .nil)),
    .cons (.typed (meaning type n)) (.cons (.typed .unit) (.cons (.typed (.single (.named .head))) .nil)),
    (bound actual n).complete, rfl⟩

theorem exact_static_bundles_erase_and_restore_only_supplied_values {type : Core.Ty} (actual : Actual type) (n : Nat) :
    (runtime actual n).toTypeInputs = static type n ∧
    RuntimeParametersDeclare (table type) (owner 0) (parameters n) (runtime actual n).toTypeInputs ∧
    ∃ restored, RuntimeParametersBind (table type) (owner 0) (parameters n) (arguments actual n) restored ∧
      restored.toTypeInputs = static type n ∧ restored = runtime actual n := by
  obtain ⟨restored, binding, erased⟩ := (declared type n).bind_typed_arguments (arguments actual n) rfl
  exact ⟨rfl, (bound actual n).erase_values, restored, binding, erased, binding.result_unique (bound actual n)⟩

theorem every_actual_source_position_keeps_its_exact_structural_meaning {type : Core.Ty}
    (actual : Actual type) (n : Nat) {index : Nat} {parameterSpan : Syntax.SourceSpan}
    {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {argument : TypedRuntimeArgument}
    (parameterAt : (parameters n)[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : (arguments actual n)[index]? = some argument) :
    index < 3 ∧ StructuralTypeDenotes (table type) annotation argument.type ∧
    (runtime actual n).bindings[2 - index]? = some
      ⟨name.value, ⟨owner 0, index⟩, argument.type, argument.value, argument.valueTyped⟩ ∧
    LocalNameTable.Lookup (runtime actual n).names name.value ⟨owner 0, index⟩ ∧
    Resolved.LocalScope.Lookup (runtime actual n).context ⟨owner 0, index⟩ argument.type ∧
    Resolved.LocalScope.Lookup (runtime actual n).environment ⟨owner 0, index⟩ argument.value ∧
    Resolved.LocalScope.IndexOf (runtime actual n).context.ids ⟨owner 0, index⟩ (2 - index) :=
  (bound actual n).position parameterAt argumentAt

theorem static_position_needs_no_value_and_cannot_exchange_equal_outer_types (type : Core.Ty) (n : Nat) :
    StructuralTypeDenotes (table type) (shape n) (product type n) ∧
    Resolved.LocalScope.Lookup (static type n).context ⟨owner 0, 0⟩ (product type n) ∧
    Resolved.LocalScope.IndexOf (static type n).context.ids ⟨owner 0, 0⟩ 2 ∧
    elaborateLocalExpression? (static type n).names (static type n).context
      ⟨span, .identifier ⟨span, "packed"⟩⟩ = some (.var 2, product type n) := by
  obtain ⟨_, actualType, actualMeaning, _, named, found, indexed⟩ := (declared type n).position (index := 0) rfl
  cases actualMeaning.type_unique (meaning type n)
  exact ⟨meaning type n, found, indexed, elaborateLocalExpression?_complete (.identifier named) (.var indexed) (.var found)⟩

private def sparse : LocalInputs := ⟨[⟨"old", ⟨owner 0, 7⟩, .unit, .unit, .unit⟩,
  ⟨"foreign", ⟨owner 1, 999⟩, .unit, .unit, .unit⟩, ⟨"old", ⟨owner 0, 2⟩, .unit, .unit, .unit⟩], by decide⟩
private def extended {type : Core.Ty} (actual : Actual type) (n : Nat) :=
  ((sparse.bindFresh (owner 0) "packed" (product type n) (packed actual.val n) (packedTyped actual n)).bindFresh
    (owner 0) "ignored" .unit .unit .unit).bindFresh (owner 0) "leaf" type actual.val actual.property
private theorem extension {type : Core.Ty} (actual : Actual type) (n : Nat) :
    RuntimeParametersBindFrom (table type) (owner 0) sparse (parameters n) (arguments actual n) (extended actual n) :=
  .cons (meaning type n) (by change "packed" ∉ ["old", "foreign", "old"]; decide)
    (.cons .unit (by change "ignored" ∉ ["packed", "old", "foreign", "old"]; decide)
      (.cons (.single (.named .head)) (by change "leaf" ∉ ["ignored", "packed", "old", "foreign", "old"]; decide) .nil))

theorem sparse_mixed_owners_and_repeated_initial_names_keep_all_rows {type : Core.Ty} (actual : Actual type) (n : Nat) :
    RuntimeParametersBindFrom (table type) (owner 0) sparse (parameters n) (arguments actual n) (extended actual n) ∧
    RuntimeParametersDeclareFrom (table type) (owner 0) sparse.toTypeInputs (parameters n) (extended actual n).toTypeInputs ∧
    (extended actual n).ids = [⟨owner 0, 10⟩, ⟨owner 0, 9⟩, ⟨owner 0, 8⟩] ++ sparse.ids ∧
    (extended actual n).bindings.length = 3 + sparse.bindings.length ∧
    (extended actual n).environment.values = (arguments actual n).reverse.map (·.value) ++ sparse.environment.values :=
  ⟨extension actual n, (extension actual n).erase_values, rfl, (extension actual n).bindings_length,
    (extension actual n).argument_values⟩

theorem semantic_table_extension_keeps_the_exact_static_bundle (type : Core.Ty) (n : Nat)
    (next : TypeNameTable) (preserves : TypeNameTable.Extends (table type) next) :
    RuntimeParametersDeclare next (owner 0) (parameters n) (static type n) ∧
    declareRuntimeParameters? next (owner 0) (parameters n) = some (static type n) :=
  ⟨(declared type n).extend_types preserves,
    declareRuntimeParameters?_some_of_extends preserves (declared type n).complete⟩

theorem owner_relabeling_keeps_structural_types_and_source_order (type : Core.Ty) (n : Nat)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    RuntimeParametersDeclare (table type) (mapping (owner 0)) (parameters n)
      ((static type n).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) :=
  (declared type n).map_owner mapping injective

theorem nominal_packed_and_unused_leaf_types_never_supply_runtime_inhabitants (nominal : Core.DataTypeId) (n : Nat) :
    declareRuntimeParameters? (table (.namedData nominal)) (owner 0) (parameters n) = some (static (.namedData nominal) n) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  refine ⟨(declared _ _).complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩; cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem opaque_cells_and_captured_functions_are_whole_arguments (location : Core.Location) (word : Core.Word) :
    bindRuntimeParameters? (table (.cell .word)) (owner 0) (parameters 1)
      (arguments ⟨.cellRef .word location, .cellRef⟩ 1) = some (runtime ⟨.cellRef .word location, .cellRef⟩ 1) ∧
    bindRuntimeParameters? (table (.function .bool .word)) (owner 0) (parameters 1)
      (arguments ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ 1) =
      some (runtime ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ 1) :=
  ⟨(bound _ _).complete, (bound _ _).complete⟩

private def declaration (n : Nat) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "packed"⟩, none, ⟨span, parameters n⟩, ⟨none, none⟩,
      some ⟨span, ⟨span, [shape n]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some ⟨span, .identifier ⟨span, "packed"⟩⟩)⟩]⟩⟩⟩
private def compiled (type : Core.Ty) (n : Nat) : CompiledRuntimeFunction := ⟨static type n, .var 2, product type n⟩
private theorem compilation (type : Core.Ty) (n : Nat) : RuntimeFunctionCompiles (table type) (owner 0) (declaration n) (compiled type n) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (meaning type n)⟩, declared type n,
    .single (.expression (.identifier (.tail (by change "leaf" ≠ "packed"; decide)
        (.tail (by change "ignored" ≠ "packed"; decide) .head)))
      (.var (.tail (by change (⟨owner 0, 2⟩ : Resolved.LocalId) ≠ ⟨owner 0, 0⟩; decide)
        (.tail (by change (⟨owner 0, 1⟩ : Resolved.LocalId) ≠ ⟨owner 0, 0⟩; decide) .head)))
      (.var (.tail (by change (⟨owner 0, 2⟩ : Resolved.LocalId) ≠ ⟨owner 0, 0⟩; decide)
        (.tail (by change (⟨owner 0, 1⟩ : Resolved.LocalId) ≠ ⟨owner 0, 0⟩; decide) .head))))⟩

theorem parameter_only_record_reconstruction_keeps_the_original_core {type : Core.Ty} (actual : Actual type) (n : Nat) :
    compileRuntimeFunction? (table type) (owner 0) (declaration n) = some (compiled type n) ∧
    ∃ prepared, RuntimeFunctionPrepares (table type) (owner 0) (declaration n) (arguments actual n) prepared ∧
      prepared.toCompiled = compiled type n :=
  ⟨(compilation type n).complete, (compilation type n).prepare_arguments (arguments actual n) rfl⟩

theorem equally_typed_unit_positions_do_not_justify_a_wrong_compiled_variable :
    Core.HasType [.unit, .unit, .unit] (.var 1) .unit ∧
    ¬ RuntimeFunctionCompiles (table .unit) (owner 0) (declaration 0) { compiled .unit 0 with core := .var 1 } := by
  refine ⟨.var rfl, ?_⟩
  intro wrong
  have incompatible := congrArg CompiledRuntimeFunction.core (wrong.result_unique (compilation .unit 0))
  cases incompatible

end Tests.FrontendStructuralParameter
