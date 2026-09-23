import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.TerminalReturnBody

/-! Annotation-only rows fix source positions without supplied values. Sparse
allocation, repeated initial spellings, and saturated indices remain distinct. -/

set_option autoImplicit false

namespace Tests.FrontendParameterDeclarationPosition

open Solcore Solcore.Frontend

private def owner (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"StaticPositions", by decide⟩], by decide⟩⟩, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "static-positions.sol"⟩, 17, 3⟩
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def ref (name : String) (expressionSpan nameSpan : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨expressionSpan, .identifier ⟨nameSpan, name⟩⟩
private def parameters := [parameter "first" "Same", parameter "nominal" "Nominal", parameter "last" "Same"]
private def types (type : Core.Ty) (dataType : Core.DataTypeId) : TypeNameTable :=
  [(["Same"], type), (["Nominal"], .namedData dataType)]
private def inputs (id : Resolved.DeclarationId) (type : Core.Ty) (dataType : Core.DataTypeId) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh id "first" type).bindFresh id "nominal" (.namedData dataType)).bindFresh id "last" type
private theorem sameMeaning (type : Core.Ty) (dataType : Core.DataTypeId) :
    TypeNameDenotes (types type dataType) (annotation "Same") type := .named .head
private theorem nominalMeaning (type : Core.Ty) (dataType : Core.DataTypeId) :
    TypeNameDenotes (types type dataType) (annotation "Nominal") (.namedData dataType) :=
  .named (.tail (by decide) .head)
private theorem declared (id : Resolved.DeclarationId) (type : Core.Ty) (dataType : Core.DataTypeId) :
    RuntimeParametersDeclare (types type dataType) id parameters (inputs id type dataType) :=
  .cons (sameMeaning type dataType).structural (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (nominalMeaning type dataType).structural (by change "nominal" ∉ ["first"]; decide)
      (.cons (sameMeaning type dataType).structural (by change "last" ∉ ["nominal", "first"]; decide) .nil))

theorem independent_static_declaration_retains_source_rows_and_generated_reverse_order
    (id : Resolved.DeclarationId) (type : Core.Ty) (dataType : Core.DataTypeId) :
    RuntimeParametersDeclare (types type dataType) id parameters (inputs id type dataType) ∧
    RuntimeParameterDeclarationRows (types type dataType) parameters (inputs id type dataType).bindings.reverse ∧
    (inputs id type dataType).bindings.length = 3 ∧
    ((inputs id type dataType).names.map Prod.fst).Nodup ∧
    (inputs id type dataType).ids = [⟨id, 2⟩, ⟨id, 1⟩, ⟨id, 0⟩] :=
  ⟨declared id type dataType, (declared id type dataType).rows,
    (declared id type dataType).bindings_length, (declared id type dataType).names_nodup,
    (declared id type dataType).generated_ids⟩

private theorem original_named_annotation {index : Nat} {name : Syntax.Identifier}
    {parameterSpan : Syntax.SourceSpan} {ann : Syntax.TypeExpr} {table : TypeNameTable} {type : Core.Ty}
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name ann⟩)
    (meaning : StructuralTypeDenotes table ann type) : TypeNameDenotes table ann type := by
  have member := List.mem_of_getElem? parameterAt
  simp only [parameters, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same <;> cases same <;> cases meaning with
  | named found => exact .named found

theorem source_lookup_alone_selects_an_annotation_row_and_its_exact_reversed_position
    (id : Resolved.DeclarationId) (type : Core.Ty) (dataType : Core.DataTypeId)
    {index : Nat} {name : Syntax.Identifier} {parameterSpan : Syntax.SourceSpan} {ann : Syntax.TypeExpr}
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name ann⟩) :
    parameters.length = (inputs id type dataType).bindings.reverse.length ∧
    (∃ row, (inputs id type dataType).bindings.reverse[index]? = some row ∧
      RuntimeParameterDeclarationRow (types type dataType) ⟨parameterSpan, .typed none name ann⟩ row) ∧
    index < 3 ∧ ∃ actualType, TypeNameDenotes (types type dataType) ann actualType ∧
      (inputs id type dataType).bindings[2 - index]? = some ⟨name.value, ⟨id, index⟩, actualType⟩ ∧
      LocalNameTable.Lookup (inputs id type dataType).names name.value ⟨id, index⟩ ∧
      Resolved.LocalScope.Lookup (inputs id type dataType).context ⟨id, index⟩ actualType ∧
      Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids (inputs id type dataType).context) ⟨id, index⟩ (2 - index) := by
  obtain ⟨bounded, actualType, meaning, rowAt, named, contextLookup, indexed⟩ :=
    (declared id type dataType).position parameterAt
  exact ⟨(declared id type dataType).rows.arity, (declared id type dataType).rows.row_at parameterAt,
    bounded, actualType, original_named_annotation parameterAt meaning, rowAt, named, contextLookup, indexed⟩

theorem equal_outer_types_do_not_exchange_the_three_checked_positions
    (id : Resolved.DeclarationId) (type : Core.Ty) (dataType : Core.DataTypeId)
    (expressionSpan nameSpan : Syntax.SourceSpan) (definitions : Core.DataEnvironment) :
    ["first", "nominal", "last"].map (fun name => elaborateLocalExpression?
      (inputs id type dataType).names (inputs id type dataType).context (ref name expressionSpan nameSpan)) =
      [some (.var 2, type), some (.var 1, .namedData dataType), some (.var 0, type)] ∧
    Core.HasType [type, .namedData dataType, type] (.var 2) type definitions ∧
    Core.HasType [type, .namedData dataType, type] (.var 0) type definitions := by
  have first := (declared id type dataType).reference_elaborates_at
    (index := 0) rfl (sameMeaning type dataType) expressionSpan nameSpan
  have middle := (declared id type dataType).reference_elaborates_at
    (index := 1) rfl (nominalMeaning type dataType) expressionSpan nameSpan
  have last := (declared id type dataType).reference_elaborates_at
    (index := 2) rfl (sameMeaning type dataType) expressionSpan nameSpan
  exact ⟨by simp only [List.map_cons, List.map_nil, ref, first, middle, last]; rfl, .var rfl, .var rfl⟩

theorem nominal_reference_and_both_return_interfaces_need_no_runtime_value
    (id : Resolved.DeclarationId) (type : Core.Ty) (dataType : Core.DataTypeId)
    (blockSpan returnSpan expressionSpan nameSpan : Syntax.SourceSpan) :
    let body : Syntax.Block := ⟨blockSpan, [⟨returnSpan, .returnStmt (some (ref "nominal" expressionSpan nameSpan))⟩]⟩
    ResolvesLocalExpression (inputs id type dataType).names (ref "nominal" expressionSpan nameSpan) (.var ⟨id, 1⟩) ∧
    ReturnBodyElaborates (inputs id type dataType).names (inputs id type dataType).context body (.var 1) (.namedData dataType) ∧
    TerminalReturnBodyElaborates (inputs id type dataType).names (inputs id type dataType).context body (.var 1) (.namedData dataType) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData dataType) := by
  intro body
  have returned := (declared id type dataType).reference_return_elaborates_at
    (index := 1) rfl (nominalMeaning type dataType) blockSpan returnSpan expressionSpan nameSpan
  refine ⟨(declared id type dataType).reference_resolves_at (index := 1) rfl expressionSpan nameSpan,
    returned, .single returned, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ =>
      simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem owner_transport_changes_the_resolved_identity_but_not_the_checked_position
    (id : Resolved.DeclarationId) (type : Core.Ty) (dataType : Core.DataTypeId)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (expressionSpan nameSpan : Syntax.SourceSpan) :
    let mapped := (inputs id type dataType).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)
    mapped.ids = [⟨mapping id, 2⟩, ⟨mapping id, 1⟩, ⟨mapping id, 0⟩] ∧
    ResolvesLocalExpression mapped.names (ref "first" expressionSpan nameSpan) (.var ⟨mapping id, 0⟩) ∧
    elaborateLocalExpression? mapped.names mapped.context (ref "first" expressionSpan nameSpan) = some (.var 2, type) := by
  intro mapped
  have moved := (declared id type dataType).map_owner mapping injective
  exact ⟨moved.generated_ids, moved.reference_resolves_at (index := 0) rfl expressionSpan nameSpan,
    moved.reference_elaborates_at (index := 0) rfl (sameMeaning type dataType) expressionSpan nameSpan⟩

private def sparse (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"old", ⟨owner 0, 7⟩, type⟩, ⟨"foreign", ⟨owner 1, 999⟩, type⟩, ⟨"older", ⟨owner 0, 2⟩, type⟩],
    by change ([⟨owner 0, 7⟩, ⟨owner 1, 999⟩, ⟨owner 0, 2⟩] : List Resolved.LocalId).Nodup; decide⟩
private def addedParameters := [parameter "newA" "Same", parameter "newB" "Nominal"]
private def extended (type : Core.Ty) (dataType : Core.DataTypeId) : LocalTypeInputs :=
  ((sparse type).bindFresh (owner 0) "newA" type).bindFresh (owner 0) "newB" (.namedData dataType)
private theorem extension (type : Core.Ty) (dataType : Core.DataTypeId) :
    RuntimeParametersDeclareFrom (types type dataType) (owner 0) (sparse type) addedParameters (extended type dataType) :=
  .cons (sameMeaning type dataType).structural (by change "newA" ∉ ["old", "foreign", "older"]; decide)
    (.cons (nominalMeaning type dataType).structural (by change "newB" ∉ ["newA", "old", "foreign", "older"]; decide) .nil)

theorem sparse_mixed_owners_start_at_eight_and_retain_all_initial_rows
    (type : Core.Ty) (dataType : Core.DataTypeId) :
    (Resolved.freshLocalId (owner 0) (sparse type).ids).binderIndex = 8 ∧
    (extended type dataType).ids = [⟨owner 0, 9⟩, ⟨owner 0, 8⟩] ++ (sparse type).ids ∧
    (extended type dataType).bindings.length = 2 + (sparse type).bindings.length ∧
    ((extended type dataType).names.map Prod.fst).Nodup ∧
    ∃ added, (extended type dataType).bindings = added.reverse ++ (sparse type).bindings ∧
      RuntimeParameterDeclarationRows (types type dataType) addedParameters added :=
  ⟨rfl, (extension type dataType).generated_ids, (extension type dataType).bindings_length,
    (extension type dataType).names_nodup (by change (["old", "foreign", "older"] : List String).Nodup; decide),
    (extension type dataType).rows⟩

theorem sparse_allocation_is_neither_table_length_nor_the_other_owners_largest_index (type : Core.Ty) :
    (Resolved.freshLocalId (owner 0) (sparse type).ids).binderIndex ≠ (sparse type).bindings.length ∧
    (Resolved.freshLocalId (owner 0) (sparse type).ids).binderIndex ≠ 1000 := by
  change 8 ≠ 3 ∧ 8 ≠ 1000
  decide

private def repeated (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"old", ⟨owner 0, 7⟩, type⟩, ⟨"old", ⟨owner 0, 2⟩, type⟩],
    by change ([⟨owner 0, 7⟩, ⟨owner 0, 2⟩] : List Resolved.LocalId).Nodup; decide⟩
private theorem repeatedExtension (type : Core.Ty) (dataType : Core.DataTypeId) :
    RuntimeParametersDeclareFrom (types type dataType) (owner 0) (repeated type)
      [parameter "new" "Same"] ((repeated type).bindFresh (owner 0) "new" type) :=
  .cons (sameMeaning type dataType).structural (by change "new" ∉ ["old", "old"]; decide) .nil

theorem a_legal_initial_duplicate_is_not_repaired_by_a_new_distinct_parameter
    (type : Core.Ty) (dataType : Core.DataTypeId) :
    RuntimeParametersDeclareFrom (types type dataType) (owner 0) (repeated type)
      [parameter "new" "Same"] ((repeated type).bindFresh (owner 0) "new" type) ∧
    ¬ (((repeated type).bindFresh (owner 0) "new" type).names.map Prod.fst).Nodup ∧
    ((repeated type).bindFresh (owner 0) "new" type).ids = [⟨owner 0, 8⟩, ⟨owner 0, 7⟩, ⟨owner 0, 2⟩] :=
  ⟨repeatedExtension type dataType, by change ¬ (["new", "old", "old"] : List String).Nodup; decide,
    (repeatedExtension type dataType).generated_ids⟩

theorem an_existing_spelling_is_rejected_even_when_the_initial_ids_are_distinct
    (type : Core.Ty) (dataType : Core.DataTypeId) :
    ¬ ∃ final, RuntimeParametersDeclareFrom (types type dataType) (owner 0) (repeated type)
      [parameter "old" "Same"] final := by
  rintro ⟨final, declaration⟩
  cases declaration with
  | cons _ unused _ => exact unused (by change "old" ∈ ["old", "old"]; simp)

theorem row_annotation_meaning_does_not_supply_allocation_provenance
    (type : Core.Ty) (dataType : Core.DataTypeId) :
    RuntimeParameterDeclarationRows (types type dataType) [parameter "first" "Same"]
      [⟨"first", ⟨owner 0, 100⟩, type⟩] ∧
    ¬ ∃ output : LocalTypeInputs, output.bindings = [⟨"first", ⟨owner 0, 100⟩, type⟩] ∧
      RuntimeParametersDeclare (types type dataType) (owner 0) [parameter "first" "Same"] output := by
  refine ⟨.cons (.typed (sameMeaning type dataType).structural) .nil, ?_⟩
  rintro ⟨output, rows, declaration⟩
  have ids := declaration.generated_ids
  change output.bindings.map (·.id) = [⟨owner 0, 0⟩] at ids
  rw [rows] at ids
  have indices := congrArg (List.map Resolved.LocalId.binderIndex) ids
  change [100] = [0] at indices
  cases indices

theorem same_type_does_not_permit_a_differently_spelled_row
    (type : Core.Ty) (dataType : Core.DataTypeId) :
    ¬ RuntimeParameterDeclarationRow (types type dataType) (parameter "first" "Same")
      ⟨"last", ⟨owner 0, 0⟩, type⟩ := by
  have preservesName : ∀ {binding}, RuntimeParameterDeclarationRow (types type dataType)
      (parameter "first" "Same") binding → binding.name = "first" := by
    intro binding row
    cases row
    rfl
  intro row
  exact (by decide : "last" ≠ "first") (preservesName row)

theorem saturated_reverse_subtraction_does_not_create_an_out_of_range_source_position
    (id : Resolved.DeclarationId) (type : Core.Ty) (dataType : Core.DataTypeId) :
    parameters.length - 1 - 3 = 0 ∧ parameters[3]? = none ∧
    (¬ ∃ parameter, parameters[3]? = some parameter) ∧
    elaborateLocalExpression? (inputs id type dataType).names (inputs id type dataType).context
      (ref "last" span span) = some (.var 0, type) ∧
    ¬ ∃ position, Resolved.LocalScope.IndexOf (inputs id type dataType).ids ⟨id, 3⟩ position := by
  refine ⟨rfl, rfl, by simp [parameters],
    (declared id type dataType).reference_elaborates_at (index := 2) rfl (sameMeaning type dataType) span span, ?_⟩
  rintro ⟨position, found⟩
  have member := List.mem_of_getElem? found.getElem?
  rw [(declared id type dataType).generated_ids] at member
  have indexMember := List.mem_map_of_mem (f := Resolved.LocalId.binderIndex) member
  change 3 ∈ [2, 1, 0] at indexMember
  simp at indexMember

end Tests.FrontendParameterDeclarationPosition
