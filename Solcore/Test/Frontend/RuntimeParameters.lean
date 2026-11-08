import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions
import Solcore.Frontend.Fragments.Internal.ReturnBodies
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.RuntimeParameters
import Solcore.Frontend.Fragments.Internal.Computation
import Solcore.Frontend.Fragments.Internal.RecursiveComputation
import Solcore.Core.Fuel
import Solcore.Syntax.Parser.Internal.ParameterSoundness
import Solcore.Frontend.Fragments.Internal.LocalExpressions
import Solcore.Frontend.Fragments.Internal.Foundations
import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Core.Safety

/-!
# Runtime parameter tests

Runtime parameters: declarations and positions, argument construction, input validation, and unary
function types.
-/

section
-- leanmerge: from Solcore.Test.FrontendParameterCompilationProperties
/-! Exact parameter-return compilation is value-free, but never header-free,
whole-parameter-free, or replaceable by a merely equally typed Core tree. -/

set_option autoImplicit false

namespace Tests.FrontendParameterCompilation

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParameterCompilation", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "parameter-compilation.sol"⟩, 43, 5⟩
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def selected (left right : String) : Syntax.Block :=
  ⟨span, [⟨span, .ifThen (ref "c") (returned left) (some (returned right))⟩]⟩
private def parameters := [parameter "c" "Cond", parameter "t" "Payload", parameter "f" "Payload"]
private def types (payload condition : Core.Ty) : TypeNameTable := [(["Payload"], payload), (["Cond"], condition)]
private def entry (params : List Syntax.FunctionParameter) (result : String) (body : Syntax.Block) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "pick"⟩, none, ⟨span, params⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation result]⟩⟩, none⟩, body⟩⟩
private def declaration (conditional : Bool) : Syntax.FunctionDecl :=
  entry parameters "Payload" (if conditional then selected "t" "f" else returned "t")
private def inputs (id : Resolved.DeclarationId) (payload condition : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh id "c" condition).bindFresh id "t" payload).bindFresh id "f" payload
private def core (conditional : Bool) : Core.Expr := if conditional then .ifE (.var 2) (.var 1) (.var 0) else .var 1
private def compiled (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) : CompiledRuntimeFunction :=
  ⟨inputs id payload .bool, core conditional, payload⟩
private theorem payloadMeaning (payload condition : Core.Ty) :
    TypeNameDenotes (types payload condition) (annotation "Payload") payload := .named .head
private theorem conditionMeaning (payload condition : Core.Ty) :
    TypeNameDenotes (types payload condition) (annotation "Cond") condition := .named (.tail (by decide) .head)
private theorem declared (id : Resolved.DeclarationId) (payload condition : Core.Ty) :
    RuntimeParametersDeclare (types payload condition) id parameters (inputs id payload condition) :=
  .cons (conditionMeaning payload condition).structural (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (payloadMeaning payload condition).structural (by change "t" ∉ ["c"]; decide)
      (.cons (payloadMeaning payload condition).structural (by change "f" ∉ ["t", "c"]; decide) .nil))
private theorem header (payload condition : Core.Ty) (body : Syntax.Block) :
    RuntimeFunctionHeader (types payload condition) (entry parameters "Payload" body).value.signature payload :=
  ⟨rfl, rfl, rfl, rfl, .single (payloadMeaning payload condition).structural⟩
private theorem compilation (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) :
    RuntimeFunctionCompiles (types payload .bool) id (declaration conditional) (compiled id payload conditional) := by
  cases conditional
  · exact runtimeFunction_parameter_compiles (index := 1) (declared id payload .bool)
      rfl (payloadMeaning payload .bool) (header payload .bool _) rfl
  · exact runtimeFunction_conditional_parameters_compiles (conditionIndex := 0) (thenIndex := 1) (elseIndex := 2)
      (declared id payload .bool) rfl rfl rfl (conditionMeaning payload .bool)
      (payloadMeaning payload .bool) (payloadMeaning payload .bool) (header payload .bool _) rfl

theorem both_whole_entries_compile_from_independent_annotations_and_exact_source_positions
    (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) :
    RuntimeParametersDeclare (types payload .bool) id parameters (inputs id payload .bool) ∧
    RuntimeFunctionCompiles (types payload .bool) id (declaration conditional) (compiled id payload conditional) ∧
    compileRuntimeFunction? (types payload .bool) id (declaration conditional) = some (compiled id payload conditional) := by
  refine ⟨declared id payload .bool, compilation id payload conditional, ?_⟩
  cases conditional
  · exact compileRuntimeFunction?_parameter (index := 1) (declared id payload .bool)
      rfl (payloadMeaning payload .bool) (header payload .bool _) rfl
  · exact compileRuntimeFunction?_conditional_parameters (conditionIndex := 0) (thenIndex := 1) (elseIndex := 2)
      (declared id payload .bool) rfl rfl rfl (conditionMeaning payload .bool)
      (payloadMeaning payload .bool) (payloadMeaning payload .bool) (header payload .bool _) rfl

theorem arbitrary_compiled_candidates_recover_exact_inputs_core_and_result_without_extra_header_premises
    (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) (candidate : CompiledRuntimeFunction)
    (provenance : RuntimeFunctionCompiles (types payload .bool) id (declaration conditional) candidate) :
    candidate.inputs = inputs id payload .bool ∧ candidate.core = core conditional ∧ candidate.returnType = payload := by
  refine ⟨provenance.parameters.result_unique (declared id payload .bool), ?_⟩
  cases conditional
  · exact provenance.parameter_return_core (index := 1) rfl (payloadMeaning payload .bool) rfl
  · exact provenance.conditional_parameters_core (conditionIndex := 0) (thenIndex := 1) (elseIndex := 2)
      rfl rfl rfl (conditionMeaning payload .bool) (payloadMeaning payload .bool) (payloadMeaning payload .bool) rfl

theorem same_typed_wrong_variable_and_swapped_branches_are_not_other_compilations
    (id : Resolved.DeclarationId) (payload : Core.Ty) (definitions : Core.DataEnvironment) :
    Core.HasType [payload, payload, .bool] (.var 0) payload definitions ∧
    Core.HasType [payload, payload, .bool] (.ifE (.var 2) (.var 0) (.var 1)) payload definitions ∧
    ¬ RuntimeFunctionCompiles (types payload .bool) id (declaration false) ⟨inputs id payload .bool, .var 0, payload⟩ ∧
    ¬ RuntimeFunctionCompiles (types payload .bool) id (declaration true)
      ⟨inputs id payload .bool, .ifE (.var 2) (.var 0) (.var 1), payload⟩ := by
  refine ⟨.var rfl, .ifE (.var rfl) (.var rfl) (.var rfl), ?_, ?_⟩
  · intro forged
    have exactCore := (forged.parameter_return_core (index := 1) rfl (payloadMeaning payload .bool) rfl).1
    cases exactCore
  · intro forged
    have exactCore := (forged.conditional_parameters_core (conditionIndex := 0) (thenIndex := 1) (elseIndex := 2)
      rfl rfl rfl (conditionMeaning payload .bool) (payloadMeaning payload .bool) (payloadMeaning payload .bool) rfl).1
    cases exactCore

theorem the_two_returned_positions_may_be_the_same_parameter
    (id : Resolved.DeclarationId) (payload : Core.Ty) :
    RuntimeFunctionCompiles (types payload .bool) id (entry parameters "Payload" (selected "t" "t"))
      ⟨inputs id payload .bool, .ifE (.var 2) (.var 1) (.var 1), payload⟩ ∧
    compileRuntimeFunction? (types payload .bool) id (entry parameters "Payload" (selected "t" "t")) =
      some ⟨inputs id payload .bool, .ifE (.var 2) (.var 1) (.var 1), payload⟩ := by
  have accepted := runtimeFunction_conditional_parameters_compiles
    (declaration := entry parameters "Payload" (selected "t" "t"))
    (conditionIndex := 0) (thenIndex := 1) (elseIndex := 1)
    (declared id payload .bool) rfl rfl rfl (conditionMeaning payload .bool)
    (payloadMeaning payload .bool) (payloadMeaning payload .bool) (header payload .bool _) rfl
  exact ⟨accepted, accepted.complete⟩

theorem a_boolean_guard_may_itself_be_returned_by_both_arms (id : Resolved.DeclarationId) :
    RuntimeFunctionCompiles (types .bool .bool) id (entry parameters "Payload" (selected "c" "c"))
      ⟨inputs id .bool .bool, .ifE (.var 2) (.var 2) (.var 2), .bool⟩ ∧
    compileRuntimeFunction? (types .bool .bool) id (entry parameters "Payload" (selected "c" "c")) =
      some ⟨inputs id .bool .bool, .ifE (.var 2) (.var 2) (.var 2), .bool⟩ := by
  have accepted := runtimeFunction_conditional_parameters_compiles
    (declaration := entry parameters "Payload" (selected "c" "c"))
    (conditionIndex := 0) (thenIndex := 0) (elseIndex := 0)
    (declared id .bool .bool) rfl rfl rfl (conditionMeaning .bool .bool)
    (conditionMeaning .bool .bool) (conditionMeaning .bool .bool) (header .bool .bool _) rfl
  exact ⟨accepted, accepted.complete⟩

theorem nominal_parameter_returns_compile_in_both_profiles_without_any_argument_inhabitant
    (id : Resolved.DeclarationId) (dataType : Core.DataTypeId) (conditional : Bool) :
    compileRuntimeFunction? (types (.namedData dataType) .bool) id (declaration conditional) =
      some (compiled id (.namedData dataType) conditional) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData dataType := by
  refine ⟨(compilation id (.namedData dataType) conditional).complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩
  cases same
  cases typed with
  | constructed found _ =>
      simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem valid_parameters_do_not_bypass_the_condition_or_written_else_arm (payload : Core.Ty) :
    RuntimeParametersDeclare (types payload .word) owner parameters (inputs owner payload .word) ∧
    RuntimeParametersDeclare (types payload .bool) owner parameters (inputs owner payload .bool) ∧
    compileRuntimeFunction? (types payload .word) owner (declaration true) = none ∧
    compileRuntimeFunction? (types payload .bool) owner (entry parameters "Payload" (selected "t" "missing")) = none := by
  refine ⟨declared owner payload .word, declared owner payload .bool, ?_, ?_⟩
  · apply compileRuntimeFunction?_eq_none_iff.mpr
    rintro ⟨candidate, accepted⟩
    have sameInputs := accepted.parameters.result_unique (declared owner payload .word)
    have checked := accepted.body.complete
    rw [sameInputs] at checked
    change elaborateTypedLetReturnTree? _ owner (inputs owner payload .word)
      (selected "t" "f") = some (candidate.core, candidate.returnType) at checked
    have conditionAccepted : elaborateLocalExpression? (inputs owner payload .word).names
        (inputs owner payload .word).context (ref "c") = some (.var 2, .word) :=
      (declared owner payload .word).reference_elaborates_at (index := 0) rfl (conditionMeaning payload .word) span span
    simp only [selected, elaborateTypedLetReturnTree?, conditionAccepted, bind, Option.bind_some,
      reduceCtorEq, ↓reduceIte] at checked
  · apply compileRuntimeFunction?_eq_none_iff.mpr
    rintro ⟨candidate, accepted⟩
    have sameInputs := accepted.parameters.result_unique (declared owner payload .bool)
    have checked := accepted.body.complete
    rw [sameInputs] at checked
    simp [elaborateTypedLetReturnTree?, elaborateReturnBody?,
      elaborateLocalExpression?, resolveLocalExpression?, entry, selected, returned, ref, inputs,
      LocalTypeInputs.names, LocalTypeInputs.context, LocalTypeInputs.bindFresh, LocalTypeInputs.empty,
      LocalNameTable.lookup?] at checked

theorem a_selected_valid_parameter_does_not_bypass_the_return_contract_or_other_parameters :
    parameters[1]? = some (parameter "t" "Payload") ∧
    compileRuntimeFunction? (types .word .bool) owner (entry parameters "Cond" (returned "t")) = none ∧
    compileRuntimeFunction? (types .word .bool) owner
      (entry [parameter "c" "Cond", parameter "t" "Payload", parameter "t" "Payload"] "Payload" (returned "t")) = none ∧
    compileRuntimeFunction? (types .word .bool) owner
      (entry [parameter "c" "Cond", parameter "t" "Payload", parameter "unused" "Missing"] "Payload" (returned "t")) = none := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply compileRuntimeFunction?_eq_none_iff.mpr
    rintro ⟨candidate, accepted⟩
    have bodyType := (accepted.parameter_return_core (index := 1) rfl (payloadMeaning .word .bool) rfl).2
    have headerType := accepted.header.type_unique
      ⟨rfl, rfl, rfl, rfl, .single (conditionMeaning .word .bool).structural⟩
    rw [bodyType] at headerType
    cases headerType
  · apply compileRuntimeFunction?_eq_none_iff.mpr
    rintro ⟨candidate, accepted⟩
    cases accepted.parameters with
    | cons _ _ tail => cases tail with
      | cons _ _ tail => cases tail with
        | cons _ unused _ => exact unused (by change "t" ∈ ["t", "c"]; decide)
  · apply compileRuntimeFunction?_eq_none_iff.mpr
    rintro ⟨candidate, accepted⟩
    cases accepted.parameters with
    | cons _ _ tail => cases tail with
      | cons _ _ tail => cases tail with
        | cons meaning _ _ => cases meaning with
          | named found =>
            have impossible := TypeNameTable.lookup?_iff.mpr found
            change (none : Option Core.Ty) = some _ at impossible
            cases impossible

theorem owner_relabeling_preserves_whole_compilation_and_positional_core
    (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    RuntimeFunctionCompiles (types payload .bool) (mapping id) (declaration conditional)
      { compiled id payload conditional with inputs := ((inputs id payload .bool).mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) } ∧
    (compileRuntimeFunction? (types payload .bool) id (declaration conditional)).map
      (fun output => (output.core, output.returnType, output.inputs.context.values)) =
    (compileRuntimeFunction? (types payload .bool) (mapping id) (declaration conditional)).map
      (fun output => (output.core, output.returnType, output.inputs.context.values)) :=
  ⟨(compilation id payload conditional).mapOwner mapping injective,
    compileRuntimeFunction?_owner_projection_eq _ _ _ _⟩

theorem supplied_matching_arguments_restore_preparation_and_every_actual_machine_result
    (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool)
    (arguments : List TypedRuntimeArgument) (matching : arguments.map (·.type) = [.bool, payload, payload])
    (fuel : Nat) (store : Core.Store) :
    (∃ prepared, RuntimeFunctionPrepares (types payload .bool) id (declaration conditional) arguments prepared ∧
      prepared.toCompiled = compiled id payload conditional) ∧
    runRuntimeFunction? (types payload .bool) id (declaration conditional) arguments fuel store =
      some (payload, Core.runStateful fuel (Core.State.initial (core conditional) (arguments.reverse.map (·.value)) store)) :=
  ⟨(compilation id payload conditional).prepare_arguments arguments matching,
    (compilation id payload conditional).run_eq arguments matching fuel store⟩

end Tests.FrontendParameterCompilation
end

section
-- leanmerge: from Solcore.Test.FrontendParameterDeclarationPositionProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeArgumentConstructionEntries
/-! Raw values, original preparation and literal Core paths are retained through
structural construction and the separate, opt-in same-world validation boundary. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeArgumentConstructionEntries
private def check (b : Bool) (label : String) : IO Unit := do unless b do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ConstructedArguments",by decide⟩],by decide⟩⟩,81⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def core : Core.Expr := .apply (.var 1) (.var 0)
private def types (f x : TypedRuntimeArgument) (output : Core.Ty) : TypeNameTable :=
  [(["F"],f.type),(["X"],x.type),(["R"],output)]
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function invoke(f:F,x:X) returns(R){return f(x);}"
  let file : Syntax.SourceFile := ⟨⟨.main,"runtime-argument-construction.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original declaration")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span &&
    source.span.contains source.value.body.span) "complete original header/body spans"
  return source
private def construct (raw : Core.Value) : IO (Σ a : TypedRuntimeArgument, PLift (a.value=raw)) := do
  match built : buildRuntimeArgument? raw with
  | none => throw (IO.userError "raw structural construction")
  | some a =>
      have same := buildRuntimeArgument?_iff.mp built
      have tag : raw.type=a.type := by simpa only [same] using a.valueTyped.type_eq
      have _ := buildRuntimeArgument?_iff.mpr same
      check (decide (a.value=raw ∧ a.type=raw.type)) "exact raw value/type, no repaired payload"
      have _ := tag
      return ⟨a,⟨same⟩⟩
private def meaning (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes table source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : table.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "source annotation")
  | _ => throw (IO.userError "annotation shape")
private def parameters (table : TypeNameTable) (initial : LocalInputs) (ps : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Σ final, PLift (RuntimeParametersBindFrom table owner initial ps args final)) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨initial,⟨by rw [shape,supplied]; exact .nil⟩⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter ranges"
      let m ← meaning table annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let next ← parameters table (initial.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.1,⟨by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused next.2.down⟩⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter shape/arity")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (inputs : LocalTypeInputs) (source : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates inputs.names inputs.context source)) := do
  match shape : source with
  | ⟨_,.identifier name⟩ => match named : inputs.names.lookup? name.value with
    | some id => match typed : inputs.context.lookup? id, indexed : Resolved.LocalScope.index? inputs.context.ids id with
      | some t,some i => return ⟨.var i,t,by
          rw [shape]
          exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
            (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "source name")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call children"
      let f ← child inputs fn; let a ← child inputs arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "call argument")
      | _ => throw (IO.userError "callee")
  | _ => throw (IO.userError "child shape")
termination_by sizeOf source
private def prepare (source : Syntax.FunctionDecl) (f x : TypedRuntimeArgument) (output : Core.Ty) :
    IO (Σ p, PLift (RecursiveComputationFunctionPrepares (types f x output) owner source [f,x] p ∧
      p.core=core ∧ p.returnType=output ∧ p.inputs.environment.values=[x.value,f.value])) := do
  let ps ← parameters (types f x output) .empty source.value.signature.parameters.elements [f,x]
  match bodyShape : source.value.body with
  | ⟨span,[⟨stmtSpan,.returnStmt (some e)⟩]⟩ =>
      check (span.contains stmtSpan && stmtSpan.contains e.span) "original return/body ranges"
      let b ← child ps.1.toTypeInputs e
      if fixed : b.core=core ∧ b.type=output ∧ ps.1.environment.values=[x.value,f.value] then
        check (decide (ps.1.names=[("x",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original reverse-once records"
        match clause : source.value.signature.returnsClause with
        | some ⟨_,⟨_,[annotation]⟩⟩ =>
            let m ← meaning (types f x output) annotation
            if same : m.1=output then
              if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
                let p : PreparedRuntimeFunction := ⟨ps.1,core,output⟩
                have annotationMeaning : StructuralTypeDenotes (types f x output) annotation output := by simpa only [same] using m.2.down
                have h : RuntimeFunctionHeader (types f x output) source.value.signature output :=
                  ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single annotationMeaning⟩
                have body : RecursiveComputationReturnTreeElaborates (types f x output) owner ps.1.toTypeInputs source.value.body core output := by
                  rw [bodyShape]; exact .expression (by simpa only [fixed.1,fixed.2.1] using b.evidence)
                return ⟨p,⟨⟨⟨h,ps.2.down,body⟩,rfl,rfl,fixed.2.2⟩⟩⟩
              else throw (IO.userError "header policy")
            else throw (IO.userError "return annotation")
        | _ => throw (IO.userError "single return type")
      else throw (IO.userError "independent Core/type/actual input order")
  | _ => throw (IO.userError "original return shape")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with
      | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "manual variable")
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured =>
            let r ← path n b (arg.value::captured) arg.final
            return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match found : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual operands")
    | _ => throw (IO.userError "manual grammar")
private def positive (source : Syntax.FunctionDecl) (rf rx : Core.Value) (output : Core.Ty)
    (world : Core.StoreTyping) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let manual ← path 40 core [rx,rf] s
  check (decide (manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "fixed raw Core observations before construction"
  let f ← construct rf; let x ← construct rx; let p ← prepare source f.1 x.1 output
  have envEq : p.1.inputs.environment.values=[rx,rf] := by rw [p.2.down.2.2.2,x.2.down,f.2.down]
  if validated : validateRuntimeInputs world [f.1,x.1] s=true then
    have runtime := validateRuntimeInputs_iff.mp validated
    have finitePath : Core.Steps manual.cost
        (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by
      rw [p.2.down.2.1,envEq]
      exact manual.evidence []
    have safe := ComputationFunctionPrepares.runtime_typed_execution (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost
      RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
      elaborateRecursiveLocalComputation?_iff p.2.down.1 runtime.1 runtime.2 ⟨manual.value, manual.final, Core.steps_from_initial_sound finitePath⟩
    have agreement : ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future manual.final ∧
        Core.RuntimeValueHasType future manual.value output ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner p.1.inputs.names p.1.inputs.environment s source.value.body manual.value manual.final manual.cost ∧
        (∀ k, Core.Steps manual.cost ⟨.eval core [rx,rf],k,s⟩ ⟨.ret manual.value,k,manual.final⟩) ∧
        (∀ fuel, (Core.runStateful fuel (.initial core [rx,rf] s)=.done manual.value manual.final ↔ manual.cost≤fuel) ∧
          ((∃ cp, Core.runStateful fuel (.initial core [rx,rf] s)=.outOfFuel cp) ↔ fuel<manual.cost)) := by
      obtain ⟨future,t,v,n,ext,st,vt,raw,paths,thresholds,_⟩ := safe.2
      have closed : Core.Steps manual.cost (.initial p.1.core p.1.inputs.environment.values s) ⟨.ret manual.value,[],manual.final⟩ := by
        rw [p.2.down.2.1,envEq]; exact manual.evidence []
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique closed
      refine ⟨future,ext,st,by simpa only [p.2.down.2.2.1] using vt,raw,?_,?_⟩
      · simpa only [p.2.down.2.1,envEq] using paths
      · simpa only [p.2.down.2.1,envEq] using thresholds
    if grows : s.length < manual.final.length then
      have extension : ∃ future, Core.WorldExtends world future ∧ world.length < future.length ∧ Core.RuntimeStoreHasTypes future manual.final := by
        obtain ⟨future,ext,st,_,_⟩ := agreement
        exact ⟨future,ext,by simpa only [runtime.2.length_eq,st.length_eq] using grows,st⟩
      have _ := extension
      check (decide (s.length < final.length)) "allocation extends the supplied world and literal store"
    have whole (fuel) : runRecursiveComputationFunction? (types f.1 x.1 output) owner source [f.1,x.1] fuel s =
        some (output,Core.runStateful fuel (.initial core [rx,rf] s)) := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,runs⟩ := safe.2
      simpa only [p.2.down.2.1,p.2.down.2.2.1,envEq] using runs fuel
    have _ := safe.1
    for fuel in List.range (cost+2) do
      have _ := whole fuel
      check (decide (runRecursiveComputationFunction? (types f.1 x.1 output) owner source [f.1,x.1] fuel s=some (output,Core.runStateful fuel (.initial core [rx,rf] s)))) "constructed literal records/full runner"
      match stopped : Core.runStateful fuel (.initial core [rx,rf] s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact source completion threshold"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel stopped
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧
            Core.runStateful 3 cp=Core.runStateful (fuel+3) (.initial core [rx,rf] s))) "every genuine raw checkpoint/full resumption"
      | .fault _ _ => throw (IO.userError "validated constructed input fault")
    match shape : rf with
    | .closure input output body captured =>
        let cp : Core.State := ⟨.ret rx,[.applyClosure input output body captured],s⟩
        have before : Core.Steps 4 (.initial core [rx,rf] s) cp := by
          rw [shape]; exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) .refl)))
        have _ := Core.runStateful_outOfFuel_complete before (Core.advance_next_iff.mpr .invokeClosure)
        let invoked : Core.State := ⟨.eval body (rx::captured),[],s⟩
        check (decide (Core.runStateful 4 (.initial core [rx,rf] s)=.outOfFuel cp ∧
          Core.runStateful 1 cp=.outOfFuel invoked ∧ Core.runStateful (cost-4) cp=.done value final ∧
          Core.runStateful (cost-5) invoked=.done value final)) "literal callee frame, actual argument/captures and body checkpoint"
    | _ => throw (IO.userError "original closure fixture")
  else throw (IO.userError "constructed safe input rejected")
private def rejected (source : Syntax.FunctionDecl) (rf rx : Core.Value) (world : Core.StoreTyping)
    (s : Core.Store) (threshold : Nat) (expected : Core.StatefulRunResult) : IO Unit := do
  let f ← construct rf; let x ← construct rx; let p ← prepare source f.1 x.1 .word
  have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
  check (!validateRuntimeInputs world [f.1,x.1] s) "structural construction is not runtime safety"
  for fuel in List.range (threshold+2) do
    let actual := Core.runStateful fuel (.initial core [rx,rf] s)
    check (decide (runRecursiveComputationFunction? (types f.1 x.1 .word) owner source [f.1,x.1] fuel s=some (.word,actual))) "world rejection preserves source preparation and raw runner"
    if fuel<threshold then
      match actual with
      | .outOfFuel cp => check (decide (Core.runStateful 40 cp=expected ∧ Core.runStateful 3 cp=Core.runStateful (fuel+3) (.initial core [rx,rf] s))) "rejected-input raw resumption"
      | _ => throw (IO.userError "first raw threshold")
    else check (decide (actual=expected)) "rejection does not replace raw success/fault"
private def identity (t : Core.Ty) : Core.Value := .closure t t (.var 0) []
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def writer : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
private def nested (l : Nat) (used : Bool) : Core.Value := .closure .word .word (if used then core else .var 0) [reader l]
private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
end ParsedRuntimeArgumentConstructionEntries
open ParsedRuntimeArgumentConstructionEntries
def frontendParsedRuntimeArgumentConstructionEntryTests : IO Unit := do
  let source ← parsed
  positive source (identity .word) (w 14) .word [] [] [] (w 14) 6
  positive source (identity .bool) (.bool false) .bool [] [] [] (.bool false) 6
  positive source (reader 0) (w 14) .word [.word,.word] [w 23,w 41] [w 23,w 41] (w 23) 8
  positive source (reader 1) (w 14) .word [.word,.word] [w 23,w 41] [w 23,w 41] (w 41) 8
  positive source writer (w 14) .word [.word] [w 23] [w 14] (w 14) 15
  positive source (nested 0 true) (w 14) .word [.word] [w 23] [w 23] (w 23) 13
  positive source allocator (w 14) (.cell .word) [.word] [w 23] [w 23,w 14] (.cellRef .word 1) 8
  let nominal : Core.Ty := .namedData ⟨91⟩
  let sumType := Core.Ty.sum .word nominal
  positive source (identity sumType) (.inLeft nominal (w 14)) sumType [] [] [] (.inLeft nominal (w 14)) 6
  rejected source (reader 0) (w 14) [.word] [] 7 (.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩)
  rejected source (reader 0) (w 14) [.word] [.bool true] 8 (.done (.bool true) [.bool true])
  rejected source writer (w 14) [.word] [.bool true] 15 (.done (w 14) [w 14])
  rejected source (nested 700 false) (w 14) [.word] [w 23] 6 (.done (w 14) [w 23])
  let forged : Core.Value := .closure .word .word (.bool false) []
  for raw in [forged,.closure .word .word (.var 0) [forged],.closure .word .word (.var 1) [],
      .hostFunction .storageRead,.closure .word .word (.var 0) [.hostFunction .storageRead],.constructed ⟨⟨91⟩,0⟩ .unit] do
    check (buildRuntimeArgument? raw |>.isNone) "same tag does not bypass body/capture/nominal evidence"
  check (decide (forged.type=(identity .word).type ∧ Core.runStateful 6 (.initial core [w 14,forged] [])=.done (.bool false) [])) "failed construction does not rewrite raw execution"
  check (decide (Core.runStateful 6 (.initial core [w 14,.closure .word .word (.var 0) [forged]] [])=.done (w 14) [])) "unexecuted invalid captured closure still prevents construction"
  let nf ← construct (identity nominal); let wx ← construct (w 14)
  let table : TypeNameTable := [(["F"],nf.1.type),(["X"],nominal),(["R"],nominal)]
  check (decide ((compileRecursiveComputationFunction? table owner source).map (fun p => (p.core,p.returnType))=some (core,nominal)) &&
    (prepareRecursiveComputationFunction? table owner source [nf.1,wx.1]).isNone &&
    (compileRecursiveComputationFunction? [(["F"],nf.1.type),(["X"],nominal)] owner source).isNone) "nominal construction/value-free typing does not erase actual argument or annotation gates"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeInputValidationEntries
/-! Original preparation and a separate literal Core path precede validation.
The opt-in Bool supplies runtime premises without guarding or rewriting entries. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeInputValidationEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ValidatedEntries",by decide⟩],by decide⟩⟩,74⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩
private def invocation : Core.Expr := .apply (.var 1) (.var 0)
private def tailCore : Core.Expr := .letE (.var 0) (.var 1)
private def core : Core.Expr := .letE invocation tailCore
private def types (f : TypedRuntimeArgument) (output : Core.Ty) : TypeNameTable :=
  [(["F"],f.type),(["X"],.word),(["R"],output)]
private def parsed (annotated : Bool) : IO Syntax.FunctionDecl := do
  let text := "function checked(f:F,x:X) returns(R){let r"++(if annotated then ":R" else "")++"=f(x);r;return r;}"
  let file : Syntax.SourceFile := ⟨⟨.main,"runtime-input-validation.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original declaration")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span &&
    source.span.contains source.value.body.span) "original complete header/body spans"
  return source
private def meaning (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes table source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : table.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
private def parameters (table : TypeNameTable) (initial : LocalInputs) (ps : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Σ final, PLift (RuntimeParametersBindFrom table owner initial ps args final)) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨initial,⟨by rw [shape,supplied]; exact .nil⟩⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter ranges"
      let m ← meaning table annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let next ← parameters table (initial.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.1,⟨by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused next.2.down⟩⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter shape/arity")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (inputs : LocalTypeInputs) (source : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates inputs.names inputs.context source)) := do
  match shape : source with
  | ⟨_,.identifier name⟩ => match named : inputs.names.lookup? name.value with
    | some id => match typed : inputs.context.lookup? id, indexed : Resolved.LocalScope.index? inputs.context.ids id with
      | some t,some i => return ⟨.var i,t,by
          rw [shape]
          exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
            (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "source name")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call children"
      let f ← child inputs fn; let a ← child inputs arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "call argument")
      | _ => throw (IO.userError "callee")
  | _ => throw (IO.userError "child shape")
termination_by sizeOf source
private def body (table : TypeNameTable) (inputs : LocalTypeInputs) (source : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates table owner inputs source)) := do
  check (source.value.all fun s => source.span.contains s.span) "original statement spans"
  match shape : source with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let a ← child inputs e; return ⟨a.core,a.type,by rw [shape]; exact .expression a.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      if unused : name.value ∉ inputs.names.map Prod.fst then
        let a ← child inputs e; let b ← body table (inputs.bindFresh owner name.value a.type) ⟨span,rest⟩
        match annotationAt : annotation with
        | none => return ⟨.letE a.core b.core,b.type,by rw [shape,annotationAt]; exact .inferred a.evidence b.evidence⟩
        | some t =>
            let m ← meaning table t
            if same : m.1=a.type then return ⟨.letE a.core b.core,b.type,by rw [shape,annotationAt]; exact .binding (same ▸ m.2.down) a.evidence b.evidence⟩
            else throw (IO.userError "binding annotation")
      else throw (IO.userError "fresh binding")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ =>
      let a ← child inputs e; let b ← body table inputs ⟨span,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,by rw [shape]; exact .discard a.evidence b.evidence⟩
  | _ => throw (IO.userError "body shape")
termination_by sizeOf source
private def prepare (source : Syntax.FunctionDecl) (f : TypedRuntimeArgument) (output : Core.Ty) :
    IO (Σ p, PLift (RecursiveComputationFunctionPrepares (types f output) owner source [f,x] p ∧
      p.core=core ∧ p.returnType=output)) := do
  let ps ← parameters (types f output) .empty source.value.signature.parameters.elements [f,x]
  let b ← body (types f output) ps.1.toTypeInputs source.value.body
  check (decide (ps.1.environment.values=[x.value,f.value] ∧ ps.1.names=[("x",⟨owner,1⟩),("f",⟨owner,0⟩)])) "actual reverse-once records"
  if fixed : b.core=core ∧ b.type=output then
    match clause : source.value.signature.returnsClause with
    | some ⟨_,⟨_,[annotation]⟩⟩ =>
        let m ← meaning (types f output) annotation
        if same : m.1=output then
          if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
            let p : PreparedRuntimeFunction := ⟨ps.1,core,output⟩
            have annotationMeaning : StructuralTypeDenotes (types f output) annotation output := by
              simpa only [same] using m.2.down
            have h : RuntimeFunctionHeader (types f output) source.value.signature output :=
              ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single annotationMeaning⟩
            return ⟨p,⟨⟨⟨h,ps.2.down,by simpa only [fixed.1,fixed.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
          else throw (IO.userError "header policy")
        else throw (IO.userError "return annotation")
    | _ => throw (IO.userError "single return type")
  else throw (IO.userError "independent literal Core/type")
private structure Path (core : Core.Expr) (env : Core.Environment) (store : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,store⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with
      | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "manual variable")
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured =>
            let r ← path n b (arg.value::captured) arg.final
            return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match found : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core grammar")
private def positive (source : Syntax.FunctionDecl) (f : TypedRuntimeArgument) (output : Core.Ty)
    (world : Core.StoreTyping) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let p ← prepare source f output; let env := p.1.inputs.environment.values
  let manual ← path 40 core env s
  check (decide (manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independently fixed value/store/cost"
  if validated : validateRuntimeInputs world [f,x] s=true then
    have runtime := validateRuntimeInputs_iff.mp validated
    have finitePath : Core.Steps manual.cost
        (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by
      rw [p.2.down.2.1]
      exact manual.evidence []
    have safe := ComputationFunctionPrepares.runtime_typed_execution (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost
      RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
      elaborateRecursiveLocalComputation?_iff p.2.down.1 runtime.1 runtime.2 ⟨manual.value, manual.final, Core.steps_from_initial_sound finitePath⟩
    have agreement : ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future manual.final ∧
        Core.RuntimeValueHasType future manual.value output ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner p.1.inputs.names p.1.inputs.environment s source.value.body manual.value manual.final manual.cost ∧
        (∀ k, Core.Steps manual.cost ⟨.eval core env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩) ∧
        (∀ fuel, (Core.runStateful fuel (.initial core env s)=.done manual.value manual.final ↔ manual.cost≤fuel) ∧
          ((∃ cp, Core.runStateful fuel (.initial core env s)=.outOfFuel cp) ↔ fuel<manual.cost)) := by
      obtain ⟨future,t,v,n,ext,st,vt,raw,paths,thresholds,_⟩ := safe.2
      have closed : Core.Steps manual.cost (.initial p.1.core env s) ⟨.ret manual.value,[],manual.final⟩ := by
        rw [p.2.down.2.1]; exact manual.evidence []
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique closed
      refine ⟨future,ext,st,by simpa only [p.2.down.2.2] using vt,raw,?_,?_⟩
      · simpa only [p.2.down.2.1] using paths
      · simpa only [p.2.down.2.1] using thresholds
    if grows : s.length < manual.final.length then
      have extension : ∃ future, Core.WorldExtends world future ∧ world.length < future.length ∧ Core.RuntimeStoreHasTypes future manual.final := by
        obtain ⟨future,ext,st,_,_⟩ := agreement
        exact ⟨future,ext,by simpa only [runtime.2.length_eq,st.length_eq] using grows,st⟩
      have _ := extension
      check (decide (s.length < final.length)) "allocation extends the validated world and actual store"
    have whole (fuel) : runRecursiveComputationFunction? (types f output) owner source [f,x] fuel s =
        some (output,Core.runStateful fuel (.initial core env s)) := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,runs⟩ := safe.2
      simpa only [p.2.down.2.1,p.2.down.2.2] using runs fuel
    have _ := safe.1
    let call ← path 40 invocation env s
    let first : Core.State := ⟨.ret call.value,[.letBody tailCore env],call.final⟩
    have firstPath : Core.Steps (call.cost+1) (.initial core env s) first := by
      simpa [core,first,Core.State.initial,Nat.add_comm] using Core.Steps.cons Core.Transition.enterLet
        (call.evidence [.letBody tailCore env])
    have _ := Core.runStateful_outOfFuel_complete firstPath (Core.advance_next_iff.mpr .bindLet)
    check (decide (call.cost+6=cost ∧ Core.runStateful (cost-5) (.initial core env s)=.outOfFuel first ∧
      Core.runStateful 5 first=.done value final)) "actual captured values/store and pending named-binding frame"
    for fuel in List.range (cost+2) do
      have _ := whole fuel
      check (decide (runRecursiveComputationFunction? (types f output) owner source [f,x] fuel s=some (output,Core.runStateful fuel (.initial core env s)))) "validation preserves prepared record and full runner"
      match stopped : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact done threshold"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel stopped
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧
            Core.runStateful 3 cp=Core.runStateful (fuel+3) (.initial core env s))) "every genuine checkpoint/full resumption"
      | .fault _ _ => throw (IO.userError "validated input fault")
    let cp : Core.State := ⟨.eval (.var 1) (value::value::env),[],final⟩
    check (decide (Core.runStateful (cost-1) (.initial core env s)=.outOfFuel cp ∧ Core.runStateful 1 cp=.done value final)) "actual named and discard hidden slots"
  else throw (IO.userError "valid input rejected")
private def rejected (source : Syntax.FunctionDecl) (f : TypedRuntimeArgument) (world : Core.StoreTyping)
    (s : Core.Store) (threshold : Nat) (expected : Core.Environment → Core.StatefulRunResult) : IO Unit := do
  let p ← prepare source f .word; let env := p.1.inputs.environment.values
  have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
  have _ := accepted
  check (!validateRuntimeInputs world [f,x] s) "invalid runtime input accepted"
  for fuel in List.range (threshold+2) do
    let actual := Core.runStateful fuel (.initial core env s)
    check (decide (runRecursiveComputationFunction? (types f .word) owner source [f,x] fuel s=some (.word,actual))) "rejection does not guard or repair the unchanged entry"
    if fuel<threshold then
      match actual with
      | .outOfFuel cp => check (decide (Core.runStateful 40 cp=expected env ∧ Core.runStateful 3 cp=Core.runStateful (fuel+3) (.initial core env s))) "rejected raw checkpoint remains resumable"
      | _ => throw (IO.userError "rejected raw first threshold")
    else check (decide (actual=expected env)) "rejection does not replace raw success/fault"
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def identity : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩
private def nested (l : Nat) (used : Bool) : TypedRuntimeArgument :=
  ⟨.function .word .word,.closure .word .word (if used then invocation else .var 0) [(reader l).value],
    .closure (.cons (reader l).valueTyped .nil) (by split; exact .apply (.var rfl) (.var rfl); exact .var rfl)⟩
private def allocator : TypedRuntimeArgument := ⟨.function .word (.cell .word),.closure .word (.cell .word) (.newCell .word (.var 0)) [],.closure .nil (.newCell (.var rfl))⟩
end ParsedRuntimeInputValidationEntries
open ParsedRuntimeInputValidationEntries
def frontendParsedRuntimeInputValidationEntryTests : IO Unit := do
  for annotated in [false,true] do
    let source ← parsed annotated
    positive source identity .word [] [] [] (w 14) 12
    positive source (reader 0) .word [.word] [w 23] [w 23] (w 23) 14
    positive source writer .word [.word] [w 23] [w 14] (w 14) 21
    positive source (nested 0 true) .word [.word] [w 23] [w 23] (w 23) 19
    positive source (nested 0 false) .word [.word] [w 23] [w 23] (w 14) 12
    positive source allocator (.cell .word) [.word] [w 23] [w 23,w 14] (.cellRef .word 1) 14
    rejected source (reader 0) [.word] [] 8 (fun env => .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply,.letBody tailCore env],[]⟩)
    rejected source (reader 0) [.word] [.bool true] 14 (fun _ => .done (.bool true) [.bool true])
    rejected source writer [.word] [.bool true] 21 (fun _ => .done (w 14) [w 14])
    rejected source identity [.word] [.bool true] 12 (fun _ => .done (w 14) [.bool true])
    rejected source (reader 0) [.bool] [.bool true] 14 (fun _ => .done (.bool true) [.bool true])
    rejected source (nested 7 false) [.word] [w 23] 12 (fun _ => .done (w 14) [w 23])
    rejected source (reader 0) [.word] [w 23,w 9] 14 (fun _ => .done (w 23) [w 23,w 9])
    rejected source (reader 0) [.word,.word] [w 23] 14 (fun _ => .done (w 23) [w 23])
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeParameterTypeExtensions
/-! Actual parameter bindings retain complete records across meaning-preserving
tables. Original parsed occurrences and caller values are never reconstructed
from an executable result; erasure alone cannot identify runtime bundles. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeParameterTypeExtensions
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ActualTypes", by decide⟩], by decide⟩⟩, 42⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 99 }
private def base : TypeNameTable := [(["Word"],.word), (["Bool"],.bool), (["Cell"],.cell .word),
  (["Fn"],.function .word .word), (["N"],.namedData ⟨91⟩), (["Pkg","Flag"],.bool),
  (["Pkg.Flag"],.word), (["Word"],.bool)]
private def alternate : TypeNameTable := [(["Pkg.Flag"],.word), (["N"],.namedData ⟨91⟩),
  (["Fn"],.function .word .word), (["Cell"],.cell .word), (["Bool"],.bool), (["Word"],.word),
  (["Pkg","Flag"],.bool), (["N"],.unit), (["Word"],.unit)]
private def extras : TypeNameTable := [(["New"],.bool), (["Word"],.unit)]
private def extended := base ++ extras
private theorem sameLookup (key : List String) : base.lookup? key = alternate.lookup? key := by
  by_cases w : ["Word"] = key; · subst key; rfl
  by_cases b : ["Bool"] = key; · subst key; rfl
  by_cases c : ["Cell"] = key; · subst key; rfl
  by_cases f : ["Fn"] = key; · subst key; rfl
  by_cases n : ["N"] = key; · subst key; rfl
  by_cases q : ["Pkg","Flag"] = key; · subst key; rfl
  by_cases s : ["Pkg.Flag"] = key; · subst key; rfl
  simp [base, alternate, TypeNameTable.lookup?, w, b, c, f, n, q, s]
private theorem fromLookup {left right : TypeNameTable}
    (same : ∀ key, left.lookup? key = right.lookup? key) : TypeNameTable.Extends left right := by
  intro key type found
  exact TypeNameTable.lookup?_iff.mp ((same key).symm.trans (TypeNameTable.lookup?_iff.mpr found))
private theorem forward : TypeNameTable.Extends base alternate := fromLookup sameLookup
private theorem backward : TypeNameTable.Extends alternate base := fromLookup fun key => (sameLookup key).symm
private theorem grows : TypeNameTable.Extends base extended := TypeNameTable.Extends.append_right base extras
private def w (n : Nat) : TypedRuntimeArgument := ⟨.word,.word (Core.Word.ofNatModulo n),.word⟩
private def b (v : Bool) : TypedRuntimeArgument := ⟨.bool,.bool v,.bool⟩
private def u : TypedRuntimeArgument := ⟨.unit,.unit,.unit⟩
private def pair (a z : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.product a.type z.type,.pair a.value z.value,.pair a.valueTyped z.valueTyped⟩
private def rowData (row : TypedLocalBinding) := (row.name,row.id,row.type,row.value)
private theorem rowData_injective : Function.Injective rowData := by
  rintro ⟨an,ai,aType,av,ap⟩ ⟨bn,bi,bType,bv,bp⟩ same
  simp only [rowData, Prod.mk.injEq] at same
  rcases same with ⟨rfl,rfl,rfl,rfl⟩; rfl
private abbrev bindingDecidableEq : DecidableEq TypedLocalBinding := fun a z =>
  decidable_of_iff (rowData a = rowData z) ⟨fun same => rowData_injective same, fun same => congrArg rowData same⟩
attribute [local instance] bindingDecidableEq
private abbrev inputsDecidableEq : DecidableEq LocalInputs := fun a z =>
  decidable_of_iff (a.bindings = z.bindings) ⟨by cases a; cases z; intro same; cases same; rfl,
    fun same => congrArg LocalInputs.bindings same⟩
attribute [local instance] inputsDecidableEq
private def parsed (parameters : String) : IO Syntax.FunctionDecl := do
  let content := "function original" ++ parameters ++ "{return;}"
  let file : Syntax.SourceFile := ⟨⟨.main,"parameter-type-extensions.sol"⟩,content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"original declaration did not parse: {parameters}")
  let params := source.value.signature.parameters
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,content.utf8ByteSize⟩ ∧ params.span =
      ⟨file.id,"function original".utf8ByteSize,"function original".utf8ByteSize + parameters.utf8ByteSize⟩))
    "original whole declaration or exact parameter byte range changed"
  for parameter in params.elements do
    let .typed _ name annotation := parameter.value | throw (IO.userError "parameter lost its original annotation")
    assertTrue (params.span.contains parameter.span && parameter.span.contains name.span &&
      parameter.span.contains annotation.span && decide (name.span.endByte ≤ annotation.span.startByte))
      "original annotation/name ranges or order changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent named meaning absent")
  | ⟨_,.tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ =>
      let inner ← meaning types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.evidence⟩
  | ⟨_,.tuple [left,right]⟩ =>
      let a ← meaning types left; let z ← meaning types right
      return ⟨.product a.type z.type, by rw [atSource]; exact .pair a.evidence z.evidence⟩
  | ⟨span,.tuple (first :: second :: third :: rest)⟩ =>
      let a ← meaning types first; let z ← meaning types ⟨span,.tuple (second :: third :: rest)⟩
      return ⟨.product a.type z.type, by rw [atSource]; exact .many a.evidence z.evidence⟩
  | _ => throw (IO.userError "unsupported independent annotation")
termination_by sizeOf source
private structure Binding (types : TypeNameTable) (initial : LocalInputs)
    (parameters : List Syntax.FunctionParameter) (arguments : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial parameters arguments inputs
private def binding (types : TypeNameTable) (initial : LocalInputs) (parameters : List Syntax.FunctionParameter)
    (arguments : List TypedRuntimeArgument) : IO (Binding types initial parameters arguments) := do
  match atParams : parameters, atArgs : arguments with
  | [],[] => return ⟨initial, by rw [atParams,atArgs]; exact .nil⟩
  | ⟨_,.typed none name annotation⟩ :: rest, argument :: args =>
      let head ← meaning types annotation
      if same : head.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← binding types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest args
          return ⟨tail.inputs, by rw [atParams,atArgs]; exact .cons (same ▸ head.evidence) unused tail.evidence⟩
        else throw (IO.userError "independent duplicate parameter")
      else throw (IO.userError "independent caller type mismatch")
  | _,_ => throw (IO.userError "independent arity or profile mismatch")
private def checkMutual (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO Unit := do
  let params := source.value.signature.parameters.elements
  have _ := bindRuntimeParameters?_eq_of_mutual_extends forward backward owner params args
  have _ := bindRuntimeParameters?_eq_of_mutual_extends backward forward owner params args
  assertTrue (decide (bindRuntimeParameters? base owner params args = bindRuntimeParameters? alternate owner params args))
    "mutual extension changed the full Option, including actual bindings"
private def accepted (text : String) (names : List String) (args : List TypedRuntimeArgument) : IO Unit := do
  let source ← parsed text
  let params := source.value.signature.parameters.elements
  let original ← binding base .empty params args
  let expected := (names.zip args).zipIdx.map fun ((name,arg),index) =>
    (name,(⟨owner,index⟩ : Resolved.LocalId),arg.type,arg.value)
  assertTrue (decide (params.length = names.length ∧ args.length = names.length ∧
    original.inputs.bindings.map rowData = expected.reverse ∧
    original.inputs.environment.values = (args.map (·.value)).reverse)) "source arity, fresh IDs or reverse-once actual rows changed"
  have originalSome := RuntimeParametersBind.complete original.evidence
  have _ := RuntimeParametersBind.extend_types original.evidence grows
  have _ := bindRuntimeParameters?_some_of_extends grows originalSome
  have _ := RuntimeParametersBind.erase_values original.evidence
  assertTrue (decide (bindRuntimeParameters? base owner params args = some original.inputs ∧
    bindRuntimeParameters? extended owner params args = some original.inputs ∧
    bindRuntimeParameters? alternate owner params args = some original.inputs)) "exact complete input record was not retained"
  checkMutual source args
private def rejected (text : String) (args : List TypedRuntimeArgument) : IO Unit := do
  let source ← parsed text
  let params := source.value.signature.parameters.elements
  have _ := bindRuntimeParameters?_eq_none_iff (types := base) (owner := owner) (params := params) (args := args)
  checkMutual source args
  assertTrue (decide (bindRuntimeParameters? base owner params args = none ∧
    bindRuntimeParameters? extended owner params args = none)) "invalid arity, type, spelling or profile acquired a binding"
private def sparse : LocalInputs := ⟨[
  ⟨"old",⟨owner,7⟩,.word,(w 9).value,.word⟩, ⟨"old",⟨owner,2⟩,.bool,.bool false,.bool⟩,
  ⟨"foreign",⟨other,999⟩,.unit,.unit,.unit⟩], by decide⟩
private def retained : IO Unit := do
  let source ← parsed "(p: (Word, Bool, ()), last: ())"
  let params := source.value.signature.parameters.elements
  let args := [pair (w 9) (pair (b true) u),u]
  let original ← binding base sparse params args
  let changed ← binding alternate sparse params args
  have transported := RuntimeParametersBindFrom.extend_types original.evidence forward
  have same := transported.result_unique changed.evidence
  have _ := RuntimeParametersBindFrom.extend_types changed.evidence backward
  assertTrue (decide (original.inputs = changed.inputs ∧ original.inputs.ids =
    [⟨owner,9⟩,⟨owner,8⟩,⟨owner,7⟩,⟨owner,2⟩,⟨other,999⟩] ∧
    original.inputs.names.map Prod.fst = ["last","p","old","old","foreign"] ∧
    original.inputs.environment.values = (args.map (·.value)).reverse ++ sparse.environment.values ∧
    original.inputs.bindings.drop 2 = sparse.bindings)) "arbitrary initial full rows or owner-local sparse allocation changed"
  have _ := same
private def boundaries : IO Unit := do
  let source ← parsed "(x: (Word, New, ()))"
  let params := source.value.signature.parameters.elements
  let args := [pair (w 9) (pair (b true) u)]
  let enabled ← binding extended .empty params args
  have _ := RuntimeParametersBind.complete enabled.evidence
  checkMutual source args
  assertTrue (decide (bindRuntimeParameters? base owner params args = none ∧
    bindRuntimeParameters? extended owner params args = some enabled.inputs ∧ enabled.inputs.ids = [⟨owner,0⟩]))
    "one-way extension did not enable the same original actual argument"
  let changed := (["Word"],Core.Ty.bool) :: base
  have notExtension : ¬ TypeNameTable.Extends base changed := by
    intro extension
    have found : TypeNameTable.Lookup base ["Word"] .word := .head
    have impossible := TypeNameTable.lookup?_iff.mpr (extension found)
    simp [changed, TypeNameTable.lookup?] at impossible
  have _ := notExtension
  let known ← parsed "(x: Word)"
  let p := known.value.signature.parameters.elements
  let first ← binding base .empty p [w 9]
  let second ← binding base .empty p [w 2]
  assertTrue (decide (changed.tail = base ∧ bindRuntimeParameters? changed owner p [w 9] = none ∧
    first.inputs.names = second.inputs.names ∧ first.inputs.context = second.inputs.context ∧
    first.inputs.environment ≠ second.inputs.environment ∧ first.inputs ≠ second.inputs))
    "old rows or erased types incorrectly identified different actual records"
  let nominal ← parsed "(x: ((), N, N))"
  match atParams : nominal.value.signature.parameters.elements with
  | [⟨span,.typed none name annotation⟩] =>
      let head ← meaning base annotation
      if unused : name.value ∉ LocalTypeInputs.empty.names.map Prod.fst then
        let inputs := LocalTypeInputs.empty.bindFresh owner name.value head.type
        have declared : RuntimeParametersDeclare base owner [⟨span,.typed none name annotation⟩] inputs :=
          .cons head.evidence unused .nil
        have _ := declared.extend_types grows
        have originalAccepted : declareRuntimeParameters? base owner nominal.value.signature.parameters.elements = some inputs := by
          rw [atParams]; exact declared.complete
        have _ := originalAccepted
        assertTrue (decide (head.type = .product .unit (.product (.namedData ⟨91⟩) (.namedData ⟨91⟩)) ∧
          (declareRuntimeParameters? base owner nominal.value.signature.parameters.elements).map (fun i => (i.names,i.context)) =
            some (inputs.names,inputs.context)))
          "nominal static declaration required fabricated actual arguments"
      else throw (IO.userError "empty static inputs had a name")
      have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
        rintro ⟨value,typed⟩; cases typed with
        | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
      assertTrue (bindRuntimeParameters? base owner nominal.value.signature.parameters.elements [pair u (pair (w 9) (w 2))]).isNone
        "static nominal meaning fabricated an inhabitant"
  | _ => throw (IO.userError "nominal original parameter shape changed")
end ParsedRuntimeParameterTypeExtensions
open ParsedRuntimeParameterTypeExtensions

def frontendParsedRuntimeParameterTypeExtensionTests : IO Unit := do
  assertTrue (decide (base ≠ alternate ∧ base.lookup? ["Pkg","Flag"] = some .bool ∧
    base.lookup? ["Pkg.Flag"] = some .word)) "dictionary contrast became identical or flattened"
  accepted "()" [] []
  for text in ["(u: ())", "(u: (()))", "(u: ((),))"] do accepted text ["u"] [u]
  for text in ["(x: Word)", "(x: (Word))", "(x: ((Word,),))"] do accepted text ["x"] [w 9]
  for c in [false,true] do
    accepted "(p: (Word, Bool))" ["p"] [pair (w 9) (b c)]
    accepted "(p: (Word, Bool, ()))" ["p"] [pair (w 9) (pair (b c) u)]
    accepted "(p: (Word, Bool, (), Word))" ["p"] [pair (w 9) (pair (b c) (pair u (w 2)))]
    accepted "(p: ((Word, Bool), ()))" ["p"] [pair (pair (w 9) (b c)) u]
    accepted "(u: (), p: (Word, Bool, ()), z: Word)" ["u","p","z"] [u,pair (w 9) (pair (b c) u),w 2]
    accepted "(q: (Pkg /* components */ . Flag, Word))" ["q"] [pair (b c) (w 2)]
  for count in [1,3,8,24] do
    let names := (List.range count).map fun n => s!"a{n}"
    accepted ("(" ++ String.intercalate "," (names.map (· ++ ": Word")) ++ ")") names ((List.range count).map w)
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 999,.cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [(w 7).value],
    .closure (.cons .word .nil) (.var rfl)⟩
  accepted "(c: Cell, f: Fn, p: ((),Cell,Fn))" ["c","f","p"] [cell,closure,pair u (pair cell closure)]
  retained; boundaries
  for (text,args) in [("()",[u]), ("(u: ())",[]), ("(u: ())",[w 9]),
      ("(p: (Word,Bool))",[w 9,b true]), ("(p: (Word,Bool))",[pair (b true) (w 9)]),
      ("(p: (Word,Bool,()))",[pair (pair (w 9) (b true)) u]),
      ("(p: (Word,Bool,()))",[pair (w 9) (pair (b true) (pair u u))]),
      ("(u: (),w: Word)",[w 9,u]), ("(x: Word,x: Word)",[w 9,w 2]),
      ("(x: Word<Bool>)",[w 9]), ("(comptime x: Word)",[w 9]),
      ("(x: mapping(Word => Bool))",[w 9]), ("(x: function(Word) returns(Bool))",[w 9]),
      ("(x: (Word,@Bool))",[pair (w 9) (b true)]),
      ("(x: (Unknown,Word))",[pair (w 9) (w 2)]), ("(x: (Word,Unknown))",[pair (w 9) (w 2)])] do
    rejected text args
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedUnaryFunctionParameters
/-! Exact old static function-annotation rejections become independent declarations.
Original files, owners, tables and source spelling stay fixed. Supplied Unit/Word
still fail binding; actual captured Boolean closures are separate positive inputs. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedUnaryFunctionParameters
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private structure Fixture where
  fileName : String
  owner : Resolved.DeclarationId
  table : TypeNameTable
  text : String
  returnStart : Nat
private def declarations : Fixture := {
  fileName := "parsed-parameter-declarations.sol"
  owner := ⟨⟨.main, ⟨[⟨"Declarations", by decide⟩], by decide⟩⟩, 2⟩
  table := [(["Bool"], .bool), (["Boolean"], .bool), (["Word"], .word), (["Word"], .bool),
    (["Pkg", "Flag"], .bool), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
    (["Pair"], .product .word .bool), (["Choice"], .sum .word .bool)]
  text := "(x: function(Word) returns (Bool))"
  returnStart := 27 }
private def parameters : Fixture := {
  fileName := "structural-parameters.sol"
  owner := ⟨⟨.main, ⟨[⟨"Parameters", by decide⟩], by decide⟩⟩, 34⟩
  table := [(["Word"], .word), (["Word"], .bool), (["Bool"], .bool),
    (["Unit"], .word), (["Pkg", "Flag"], .bool), (["Pkg.Flag"], .word),
    (["Cell"], .cell .word), (["Fn"], .function .word .word), (["N"], .namedData ⟨91⟩)]
  text := "(x: function(Word) returns(Bool))"
  returnStart := 26 }
private def parse {α : Type} (fixture : Fixture) (parser : Syntax.Parser.Parser α)
    (content : String) : IO α := do
  let file : Syntax.SourceFile := ⟨⟨.main, fixture.fileName⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := parser (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original source did not completely parse")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd)
    "original source lost complete diagnostic-free parsing"
  return source
private def range (fixture : Fixture) (start finish : Nat) : Syntax.SourceSpan :=
  ⟨⟨.main, fixture.fileName⟩, start, finish⟩
private def annotationMeaning (fixture : Fixture) (annotation : Syntax.TypeExpr) :
    IO (PLift (StructuralTypeDenotes fixture.table annotation (.function .word .bool))) := do
  match atAnnotation : annotation with
  | ⟨outer, .function keyword ⟨parameterSpan, [parameter]⟩ (some ⟨returnsSpan, [result]⟩)⟩ =>
      match atParameter : parameter, atResult : result with
      | ⟨wordSpan, .named wordName none⟩, ⟨boolSpan, .named boolName none⟩ =>
          assertTrue (decide (outer = range fixture 4 (fixture.text.utf8ByteSize - 1) ∧
            keyword = range fixture 4 12 ∧ parameterSpan = range fixture 12 18 ∧
            wordSpan = range fixture 13 17 ∧ returnsSpan = range fixture fixture.returnStart
              (fixture.returnStart + 6) ∧
            boolSpan = range fixture (fixture.returnStart + 1) (fixture.returnStart + 5) ∧
            qualifiedTypeNameKey wordName = ["Word"] ∧ qualifiedTypeNameKey boolName = ["Bool"]))
            "original keyword, delimiter, child range or name components changed"
          if leaves : fixture.table.lookup? (qualifiedTypeNameKey wordName) = some .word ∧
              fixture.table.lookup? (qualifiedTypeNameKey boolName) = some .bool then
            have first : StructuralTypeDenotes fixture.table parameter .word := by
              rw [atParameter]; exact .named (TypeNameTable.lookup?_iff.mp leaves.1)
            have second : StructuralTypeDenotes fixture.table result .bool := by
              rw [atResult]; exact .named (TypeNameTable.lookup?_iff.mp leaves.2)
            return ⟨by rw [atAnnotation]; exact .functionReturns first (.single second)⟩
          else throw (IO.userError "original first-match leaves changed")
      | _, _ => throw (IO.userError "original named leaves were replaced")
  | _ => throw (IO.userError "original unary/single-return type shape changed")
private def closure (flag : Bool) : TypedRuntimeArgument :=
  ⟨.function .word .bool, .closure .word .bool (.var 1) [.bool flag],
    .closure (.cons .bool .nil) (.var rfl)⟩
private def unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
private def word : TypedRuntimeArgument := ⟨.word, .word (Core.Word.ofNatModulo 9), .word⟩
private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name, row.id, row.type)
private def check (fixture : Fixture) : IO Unit := do
  let source ← parse fixture Syntax.Parser.functionParameters fixture.text
  assertTrue (decide (source.span = range fixture 0 fixture.text.utf8ByteSize))
    "original whole parameter range changed"
  match atParameters : source.elements with
  | [⟨parameterSpan, .typed none name annotation⟩] =>
      let ⟨meaning⟩ ← annotationMeaning fixture annotation
      assertTrue (decide (name.value = "x" ∧ name.span = range fixture 1 2 ∧
        parameterSpan = range fixture 1 (fixture.text.utf8ByteSize - 1)))
        "original parameter spelling or range changed"
      let declared := LocalTypeInputs.empty.bindFresh fixture.owner name.value (.function .word .bool)
      have independent : RuntimeParametersDeclare fixture.table fixture.owner source.elements declared := by
        rw [atParameters]; exact .cons meaning (by simp) .nil
      have accepted := independent.complete
      have _ := declareRuntimeParameters?_iff.mpr independent
      have _ := independent.result_unique (declareRuntimeParameters?_sound accepted)
      have _ := RuntimeParametersDeclare.position independent (index := 0)
        (by rw [atParameters]; rfl)
      let expected := [("x", (⟨fixture.owner, 0⟩ : Resolved.LocalId), Core.Ty.function .word .bool)]
      assertTrue (decide (rows declared = expected ∧
        (declareRuntimeParameters? fixture.table fixture.owner source.elements).map rows = some expected ∧
        declared.context.values = [.function .word .bool] ∧
        declared.ids = [⟨fixture.owner, 0⟩])) "new annotation changed old exact static layout"
      assertTrue (interpretTypeName? fixture.table annotation).isNone
        "named-only interpretation silently acquired function syntax"
      let expression ← parse fixture Syntax.Parser.expression "x"
      match atExpression : expression with
      | ⟨_, .identifier occurrence⟩ =>
          if same : occurrence.value = name.value then
            have typing : LocalExpressionHasType declared.names declared.context expression (.function .word .bool) := by
              rw [atExpression]
              exact .identifier (by rw [same]; exact .head) .head
            have _ := localExpressionHasType_iff_elaborates.mp typing
          else throw (IO.userError "original reference spelling changed")
      | _ => throw (IO.userError "original identifier became another expression")
      assertTrue (decide (elaborateLocalExpression? declared.names declared.context expression =
        some (.var 0, .function .word .bool))) "original x reference changed Core index or type"
      let extra : TypeNameTable := [(["Word"], .unit), (["Fn"], .bool)]
      have extension : TypeNameTable.Extends fixture.table (fixture.table ++ extra) :=
        TypeNameTable.Extends.append_right fixture.table extra
      have _ := independent.extend_types extension
      have _ := declareRuntimeParameters?_some_of_extends extension accepted
      assertTrue (decide ((declareRuntimeParameters? (fixture.table ++ extra) fixture.owner source.elements).map rows =
        some expected)) "later duplicate changed the function domain or static rows"
      for flag in [false, true] do
        let argument := closure flag
        let bound := LocalInputs.empty.bindFresh fixture.owner name.value argument.type argument.value argument.valueTyped
        have binding : RuntimeParametersBind fixture.table fixture.owner source.elements [argument] bound := by
          rw [atParameters]; exact .cons meaning (by simp) .nil
        have erased := binding.erase_values
        have _ := independent.result_unique erased
        have _ := binding.complete
        have _ := RuntimeParametersBind.position binding (index := 0)
          (by rw [atParameters]; rfl) (by rfl)
        have _ := independent.bind_typed_arguments [argument] (by rfl)
        assertTrue (decide (rows bound.toTypeInputs = expected ∧
          bound.environment.values = [.closure .word .bool (.var 1) [.bool flag]] ∧
          (bindRuntimeParameters? fixture.table fixture.owner source.elements [argument]).map
            (fun inputs => (inputs.names, inputs.context, inputs.environment)) =
            some (bound.names, bound.context, bound.environment)))
          "binding lost the actual closure, its captured Boolean or original order"
      for arguments in [[unit], [word], [], [closure false, closure true]] do
        if rejected : bindRuntimeParameters? fixture.table fixture.owner source.elements arguments = none then
          have _ := bindRuntimeParameters?_eq_none_iff.mp rejected
          pure ()
        else throw (IO.userError "new static success bypassed old actual type/arity rejection")
  | _ => throw (IO.userError "original singleton runtime parameter changed")
end ParsedUnaryFunctionParameters

def frontendParsedUnaryFunctionParameterTests : IO Unit := do
  ParsedUnaryFunctionParameters.check ParsedUnaryFunctionParameters.declarations
  ParsedUnaryFunctionParameters.check ParsedUnaryFunctionParameters.parameters

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedUnaryFunctionTypeEffects
/-! Original unary annotations supply no runtime closure. Independently supplied
factory/writer values allocate, capture, write, and return a closure or a triple. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedUnaryFunctionTypeEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"UnaryFunctionTypeEffects",by decide⟩],by decide⟩⟩,123⟩
private def types : TypeNameTable := [(["Word"],.word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def triple : Core.Ty := .product .word (.product .word .word)
private def output (invoke : Bool) : Core.Ty := if invoke then triple else .function .word triple
private def reads : Core.Expr := .pair (.loadCell (.var 3)) (.pair (.loadCell (.var 4)) (.loadCell (.var 1)))
private def factory (l r : Nat) : Core.Value := .closure .word (.function .word triple)
  (.letE (.newCell .word (.var 0)) (.lambda .word triple reads)) [.cellRef .word l,.cellRef .word r]
private def writer (l : Nat) : Core.Value := .closure .word .unit (.storeCell (.var 1) (.var 0)) [.cellRef .word l]
private def resultClosure (l r fresh : Nat) : Core.Value := .closure .word triple reads [.cellRef .word fresh,w 14,.cellRef .word l,.cellRef .word r]
private def lastCore (invoke : Bool) : Core.Expr := if invoke then .apply (.var 2) (.var 3) else .var 2
private def middle (invoke : Bool) : Core.Expr := .letE (.apply (.var 0) (.var 2)) (lastCore invoke)
private def tailCore (invoke : Bool) : Core.Expr := .letE (.var 2) (middle invoke)
private def core (invoke : Bool) : Core.Expr := .letE (.apply (.var 2) (.var 0)) (tailCore invoke)
private def parsed (invoke : Bool) (terminal : Option String := none) : IO Syntax.FunctionDecl := do
  let text := "function route(m:function(Word) returns(function(Word) returns(Word,Word,Word)),w:function(Word),x:Word) returns(" ++ (if invoke then "(Word,Word,Word)" else "function(Word) returns(Word,Word,Word)") ++ "){let f:function(Word) returns(Word,Word,Word)=m(x);let g:function(Word) returns()=w;g(x);return " ++ terminal.getD (if invoke then "f(x)" else "f") ++ ";}"
  let file : Syntax.SourceFile := ⟨⟨.main,"unary-function-type-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original source and range"
  return source
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "original named leaf")
  | ⟨_,.tuple []⟩ => return ⟨.unit,⟨by rw [shape]; exact .unit⟩⟩
  | ⟨_,.tuple [a]⟩ => let x ← meaning a; return ⟨x.1,⟨by rw [shape]; exact .single x.2.down⟩⟩
  | ⟨_,.tuple [a,b]⟩ => let x ← meaning a; let y ← meaning b; return ⟨.product x.1 y.1,⟨by rw [shape]; exact .pair x.2.down y.2.down⟩⟩
  | ⟨span,.tuple (a::b::c::rest)⟩ => let x ← meaning a; let y ← meaning ⟨span,.tuple (b::c::rest)⟩; return ⟨.product x.1 y.1,⟨by rw [shape]; exact .many x.2.down y.2.down⟩⟩
  | ⟨span,.function keyword ⟨ps,[a]⟩ none⟩ =>
      check (span.contains keyword && span.contains ps && ps.contains a.span) "original absent-return function ranges"
      let x ← meaning a; return ⟨.function x.1 .unit,⟨by rw [shape]; exact .functionDefault x.2.down⟩⟩
  | ⟨span,.function keyword ⟨ps,[a]⟩ (some ⟨rs,results⟩)⟩ =>
      check (span.contains keyword && span.contains ps && ps.contains a.span && span.contains rs && results.all (fun r => rs.contains r.span)) "original present return-list range and children"
      let x ← meaning a; let y ← meaning ⟨rs,.tuple results⟩
      return ⟨.function x.1 y.1,⟨by rw [shape]; exact .functionReturns x.2.down y.2.down⟩⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf e
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "actual argument type")
  | _,_ => throw (IO.userError "original arity")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨span,.call f ⟨argsSpan,[a]⟩⟩ =>
      check (span.contains f.span && span.contains argsSpan && argsSpan.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original unary call ranges/order"
      let l ← child i f; let r ← child i a
      match ft : l.type with
      | .function t u => if same : r.type=t then return ⟨.apply l.core r.core,u,by rw [shape]; exact .application (ft ▸ l.evidence) (same ▸ r.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static source child")
termination_by sizeOf e
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; return ⟨r.core,r.type,by rw [shape]; exact .expression r.evidence⟩
  | ⟨span,⟨_,.letDecl name (some annotation) (some e)⟩::rest⟩ =>
      let m ← meaning annotation; let a ← child i e
      if same : m.1=a.type then
        if unused : name.value ∉ i.names.map Prod.fst then
          let r ← body (i.bindFresh owner name.value a.type) ⟨span,rest⟩
          return ⟨.letE a.core r.core,r.type,by rw [shape]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩
        else throw (IO.userError "fresh typed let")
      else throw (IO.userError "typed let annotation")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.core (r.core.weakenAt 0),r.type,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | _ => throw (IO.userError "original body")
termination_by sizeOf b
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (invoke : Bool) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core invoke ∧ p.returnType=output invoke)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=output invoke ∧ b.core=core invoke ∧ b.type=output invoke then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature (output invoke) := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core invoke,output invoke⟩ := ⟨h,ps.declared,by simpa only [erased,same.2.1,same.2.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("x",⟨owner,2⟩),("w",⟨owner,1⟩),("m",⟨owner,0⟩)])) "original declarations and actual reverse once"
          return ⟨⟨ps.actual,core invoke,output invoke⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2.1,same.2.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "independent literal Core and outer single annotation")
  | _ => throw (IO.userError "outer single return policy")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with
      | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "manual variable")
    | .lambda a b c => return ⟨.closure a b c env,s,1,fun _ => by rw [shape]; exact .cons .lambda .refl⟩
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .pair a b =>
        let l ← path n a env s; let r ← path n b env l.final
        return ⟨.pair l.value r.value,r.final,l.cost+r.cost+3,fun k => by rw [shape]; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (Core.Steps.cons .enterPair ((l.evidence _).trans (.cons .enterPairRight ((r.evidence _).trans (.cons .applyPair .refl)))))⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨span,⟨_,.letDecl name (some _) (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .binding a.evidence r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument)
    (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private def verify (invoke : Bool) (l r location : Nat) (s final : Core.Store) (value : Core.Value) (valid : Bool) : IO Unit := do
  let source ← parsed invoke; let rawValues := [factory l r,writer location,w 14]; let cost := if invoke then 48 else 29
  let manual ← path 80 (core invoke) rawValues.reverse s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal calls, captures, store and cost"
  let args ← rawValues.mapM fun value => do
    match built : buildRuntimeArgument? value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=value ∧ a.type=value.type)) "original constructed fields"; return a
    | none => throw (IO.userError "structural construction")
  let p ← prepare source args invoke; let i := p.1.inputs; let env := i.environment.values
  if actualEnv : env=rawValues.reverse then
    have literal (k) : Core.Steps manual.cost ⟨.eval (core invoke) env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actualEnv]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body (core invoke) (output invoke) := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    let raw ← rawBody i.names i.environment s source.value.body
    have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
    have allK (k) : Core.Steps raw.cost ⟨.eval (core invoke) env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original ids k
    have _ := (allK []).final_unique (literal [])
    check (decide (raw.cost=cost ∧ raw.value=value ∧ raw.final=final ∧ validateRuntimeInputs [.word,.word] args s=valid)) "independent source cost and opt-in world boundary"
    have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    have _ := prepareComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args
    have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have whole (fuel) : runRecursiveComputationFunction? types owner source args fuel s=some (output invoke,Core.runStateful fuel (.initial (core invoke) env s)) := by simp only [runRecursiveComputationFunction?,runComputationFunction?,accepted,p.2.down.2.1,p.2.down.2.2,bind,Option.bind_some,pure]; rfl
    for fuel in List.range (cost+2) do
      have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args fuel s
      have _ := whole fuel; have _ := (literal []).runStateful_done_iff (fuel := fuel)
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output invoke,Core.runStateful fuel (.initial (core invoke) env s)))) "same prepared full entry result"
      match stopped : Core.runStateful fuel (.initial (core invoke) env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "fixed completion threshold"
      | .fault _ _ => throw (IO.userError "successful raw path fault")
      | .outOfFuel cp =>
          for extra in [0,1,7,cost] do
            have _ := (literal []).residual_of_outOfFuel stopped; have _ := Core.runStateful_resume stopped extra
            check (decide (fuel<cost ∧ Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (core invoke) env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "every genuine checkpoint and full resume"
    if validated : validateRuntimeInputs [.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have finitePath : Core.Steps manual.cost
          (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by
        rw [p.2.down.2.1]
        exact literal []
      have safe := p.2.down.1.runtime_typed_execution (F := RecursiveLocalComputationFragment) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
        RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaborateRecursiveLocalComputation?_iff runtime.1 runtime.2 ⟨manual.value, manual.final, Core.steps_from_initial_sound finitePath⟩
      have agreement : ∃ future, Core.WorldExtends [.word,.word] future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ Core.RuntimeValueHasType future manual.value (output invoke) ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body manual.value manual.final manual.cost ∧
          ∀ fuel, (Core.runStateful fuel (.initial (core invoke) env s)=.done manual.value manual.final ↔ manual.cost≤fuel) ∧ ((∃ cp, Core.runStateful fuel (.initial (core invoke) env s)=.outOfFuel cp) ↔ fuel<manual.cost) := by
        obtain ⟨future,t,v,n,extension,stored,typed,sourceCost,paths,thresholds,_⟩ := safe.2
        have closed : Core.Steps manual.cost (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by rw [p.2.down.2.1]; exact literal []
        obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique closed
        exact ⟨future,extension,stored,by simpa only [p.2.down.2.2] using typed,sourceCost,by simpa only [p.2.down.2.1] using thresholds⟩
      have _ := agreement
      have reversed := runtimeArguments args.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
      have actual : Core.RuntimeEnvironmentHasTypes [.word,.word] env i.toTypeInputs.context.values := by simpa only [env,i,LocalInputs.environment,LocalInputs.context,LocalInputs.toTypeInputs_context,Resolved.LocalScope.values,List.map_map,Function.comp_def,p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial (core invoke) env s) with
        | .outOfFuel cp =>
            have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 Core.ContinuationHasType.nil stopped
            have future : ∃ savedWorld finalWorld, Core.WorldExtends [.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld finalWorld ∧ Core.RuntimeStoreHasTypes finalWorld manual.final := by
              obtain ⟨savedWorld,ext,storeTyped,resumed⟩ := saved
              obtain ⟨future,growth,finalTyped⟩ := resumed ((literal []).residual_of_outOfFuel stopped).2
              exact ⟨savedWorld,future,ext,storeTyped,growth,finalTyped⟩
            have _ := future
        | _ => throw (IO.userError "genuine typed checkpoint")
    have _ := (literal [.pairApply .unit]).trans (.cons .applyPair .refl)
    check (decide (Core.runStateful cost ⟨.eval (core invoke) env,[.pairApply .unit],s⟩=.outOfFuel ⟨.ret value,[.pairApply .unit],final⟩ ∧ Core.runStateful (cost+1) ⟨.eval (core invoke) env,[.pairApply .unit],s⟩=.done (.pair .unit value) final)) "retained frame is outside original source cost"
    if l=0 && r=1 && location=0 && s==[w 41,w 99] then
      let f := resultClosure 0 1 2; let allocated := s++[w 14]
      let checkpoints : List (Nat × Core.State) := [(12,⟨.ret f,[.letBody (tailCore invoke) env],allocated⟩),(15,⟨.ret (writer 0),[.letBody (middle invoke) (f::env)],allocated⟩),(27,⟨.ret .unit,[.letBody (lastCore invoke) (writer 0::f::env)],final⟩)] ++ if invoke then [(32,⟨.ret (w 14),[.applyClosure .word triple reads [.cellRef .word 2,w 14,.cellRef .word 0,.cellRef .word 1]],final⟩),(47,⟨.ret (.pair (w 99) (w 14)),[.pairApply (w 14)],final⟩)] else []
      for (spent,cp) in checkpoints do
        if genuine : Core.runStateful spent (.initial (core invoke) env s)=.outOfFuel cp then
          have _ := (literal []).residual_of_outOfFuel genuine
          check (decide (Core.runStateful (cost-spent) cp=.done value final)) "literal dynamic captures and pending typed/discard/apply/pair frames"
        else throw (IO.userError "literal checkpoint fields")
  else throw (IO.userError "actual reverse once")
private def fault (missingWriter : Bool) : IO Unit := do
  let source ← parsed true; let r := if missingWriter then 1 else 700; let location := if missingWriter then 700 else 0
  let rawValues := [factory 0 r,writer location,w 14]
  let args ← rawValues.mapM fun v => match buildRuntimeArgument? v with | some a => pure a | none => throw (IO.userError "fault structural construction")
  let p ← prepare source args true; let env := p.1.inputs.environment.values; let f := resultClosure 0 r 2
  let s := [w 41,w 99]; let t := if missingWriter then [w 41,w 99,w 14] else [w 14,w 99,w 14]
  let callEnv := [w 14,.cellRef .word 2,w 14,.cellRef .word 0,.cellRef .word r]
  let frames := if missingWriter then [.storeCellValue (.var 0) [w 14,.cellRef .word 700],.letBody (lastCore true) (writer location::f::env)] else [.loadCellApply,.pairRight (.loadCell (.var 1)) callEnv,.pairApply (w 14)]
  let failed : Core.StatefulRunResult := .fault (.invalidCellLocation 700) ⟨.ret (.cellRef .word 700),frames,t⟩
  let before : Core.State := ⟨.eval (.var (if missingWriter then 1 else 4)) (if missingWriter then [w 14,.cellRef .word 700] else callEnv),frames,t⟩
  let first := if missingWriter then 24 else 41
  check (decide (validateRuntimeInputs [.word,.word] args s=false ∧ Core.runStateful (first-1) (.initial (core true) env s)=.outOfFuel before ∧ Core.runStateful 1 before=failed)) "actual missing reference: precise first fault after earlier effects"
  for fuel in List.range (first+2) do
    let result := Core.runStateful fuel (.initial (core true) env s)
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (triple,result))) "annotation acceptance is not a raw execution guard"
    if fuel<first then match stopped : result with
      | .outOfFuel cp => have _ := Core.runStateful_resume (by simpa only [result] using stopped) first; check (decide (Core.runStateful first cp=failed)) "every pre-fault checkpoint preserves allocation/write"
      | _ => throw (IO.userError "first missing-reference fault")
    else check (decide (result=failed)) "exact fault state and all later fuels"
end ParsedUnaryFunctionTypeEffects
open ParsedUnaryFunctionTypeEffects
def frontendParsedUnaryFunctionTypeEffectTests : IO Unit := do
  verify true 0 1 0 [w 41,w 99] [w 14,w 99,w 14] (.pair (w 14) (.pair (w 99) (w 14))) true
  verify false 0 1 0 [w 41,w 99] [w 14,w 99,w 14] (resultClosure 0 1 2) true
  verify true 1 0 0 [w 41,w 99] [w 14,w 99,w 14] (.pair (w 99) (.pair (w 14) (w 14))) true
  verify true 0 1 1 [w 41,w 99] [w 41,w 14,w 14] (.pair (w 41) (.pair (w 14) (w 14))) true
  verify true 0 1 0 [w 41,.bool true] [w 14,.bool true,w 14] (.pair (w 14) (.pair (.bool true) (w 14))) false
  fault true; fault false
  for callText in ["f()","f(x,x)"] do
    let source ← parsed true (some callText)
    check (decide (compileRecursiveComputationFunction? types owner source=none)) "unary annotations do not broaden original call arity"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedUnaryFunctionTypes
/-! Complete original function annotations are certified independently of the
structural interpreter. Source parameter arity is never inferred from a packed type. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedUnaryFunctionTypes
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def file (content : String) : Syntax.SourceFile := ⟨⟨.main,"structural-type.sol"⟩,content⟩
private def parsed? (content : String) : IO (Option Syntax.TypeExpr) := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "type lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file content) lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      check (decide (source.span=⟨(file content).id,0,content.utf8ByteSize⟩)) "whole original type range"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "type parser invariant")
private def parsed (content : String) : IO Syntax.TypeExpr := do
  let some source ← parsed? content | throw (IO.userError s!"incomplete original type: {content}")
  return source
private structure Certificate (table : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes table source type
private def orderedChildren (outer : Syntax.SourceSpan) (children : List Syntax.TypeExpr) : Bool :=
  children.all (fun child => outer.contains child.span) &&
    (children.zip children.tail).all (fun adjacent => decide (adjacent.1.span.endByte≤adjacent.2.span.startByte))
private def certify (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Certificate table source) := do
  match shape : source with
  | ⟨_,.named name none⟩ =>
      match found : table.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "original named leaf missing")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ =>
      check (source.span.contains child.span) "original singleton type range"
      let inner ← certify table child
      return ⟨inner.type,by rw [shape]; exact .single inner.meaning⟩
  | ⟨_,.tuple [left,right]⟩ =>
      check (orderedChildren source.span [left,right]) "original pair type order"
      let a ← certify table left; let b ← certify table right
      return ⟨.product a.type b.type,by rw [shape]; exact .pair a.meaning b.meaning⟩
  | ⟨span,.tuple (first::second::third::rest)⟩ =>
      check (orderedChildren span (first::second::third::rest)) "all original tuple components"
      let head ← certify table first; let tail ← certify table ⟨span,.tuple (second::third::rest)⟩
      return ⟨.product head.type tail.type,by rw [shape]; exact .many head.meaning tail.meaning⟩
  | ⟨span,.function keyword ⟨parametersSpan,[parameter]⟩ returns⟩ =>
      check (span.contains keyword && span.contains parametersSpan && parametersSpan.contains parameter.span &&
        decide (keyword.endByte-keyword.startByte=8 ∧ keyword.endByte≤parametersSpan.startByte)) "original unary keyword and parameter list"
      let domain ← certify table parameter
      match present : returns with
      | none => return ⟨.function domain.type .unit,by rw [shape,present]; exact .functionDefault domain.meaning⟩
      | some ⟨returnsSpan,results⟩ =>
          check (span.contains returnsSpan && orderedChildren returnsSpan results &&
            decide (parametersSpan.endByte≤returnsSpan.startByte)) "original returns list and every written component"
          let codomain ← certify table ⟨returnsSpan,.tuple results⟩
          return ⟨.function domain.type codomain.type,by rw [shape,present]; exact .functionReturns domain.meaning codomain.meaning⟩
  | _ => throw (IO.userError "outside independent unary structural type profile")
termination_by sizeOf source
private def checked (content : String) (table : TypeNameTable) (expected : Core.Ty) : IO Syntax.TypeExpr := do
  let source ← parsed content
  let independent ← certify table source
  check (decide (independent.type=expected)) "independent original meaning versus literal expected type"
  have accepted := independent.meaning.complete
  have _ := interpretStructuralType?_iff.mpr independent.meaning
  have _ := independent.meaning.type_unique (interpretStructuralType?_sound accepted)
  check (decide (interpretStructuralType? table source=some expected)) "complete structural interpretation"
  check (interpretTypeName? table source).isNone "old named-only interpreter remains unchanged"
  let changed : Syntax.SourceSpan := ⟨⟨.external "unrelated","raw"⟩,92,1⟩
  have _ := interpretStructuralType?_span table source changed
  check (decide (interpretStructuralType? table {source with span:=changed}=some expected)) "outer range is not a semantic validity premise"
  let extras : TypeNameTable := [(["Word"],.unit),(["Unknown"],.bool)]
  have extension := independent.meaning.extend_types (TypeNameTable.Extends.append_right table extras)
  have _ := interpretStructuralType?_some_of_extends (TypeNameTable.Extends.append_right table extras) accepted
  check (decide (interpretStructuralType? (table++extras) source=some expected)) "later duplicates cannot override function children"
  have _ := extension.complete
  return source
-- This is the exact original standalone fixture table, not a new alias scheme.
private def table : TypeNameTable := [(["Word"],.word),(["Bool"],.bool),(["Unit"],.unit),
  (["PairAlias"],.product .word .bool),(["Pkg","Flag"],.bool),(["Pkg.Flag"],.word)]
private def rejected (content : String) (table : TypeNameTable) : IO Unit := do
  let source ← parsed content
  have _ := interpretStructuralType?_eq_none_iff (table := table) (source := source)
  check (interpretStructuralType? table source).isNone "unsupported arity or original child obtained a meaning"
  check (interpretTypeName? table source).isNone "old named-only rejection broadened"
end ParsedUnaryFunctionTypes
open ParsedUnaryFunctionTypes
def frontendParsedUnaryFunctionTypeTests : IO Unit := do
  let migrated ← checked "function(Word) returns(Bool)" table (.function .word .bool)
  check (match migrated.value with
    | .function keyword ⟨parametersSpan,[parameter]⟩ (some ⟨returnsSpan,[result]⟩) =>
        decide (keyword=⟨(file "").id,0,8⟩ ∧ parametersSpan=⟨(file "").id,8,14⟩ ∧
          parameter.span=⟨(file "").id,9,13⟩ ∧ returnsSpan=⟨(file "").id,22,28⟩ ∧ result.span=⟨(file "").id,23,27⟩) &&
          (match parameter.value,result.value with | .named a none,.named b none => decide (qualifiedTypeNameKey a=["Word"] ∧ qualifiedTypeNameKey b=["Bool"]) | _,_ => false)
    | _ => false) "exact old source shape, field spans and original table"
  for (A,B) in [(Core.Ty.word,Core.Ty.bool),(.namedData ⟨83⟩,.cell .word),(.function .unit .bool,.product .bool .unit)] do
    let caller : TypeNameTable := [(["Word"],A),(["Word"],.unit),(["Bool"],B)]
    let absent ← checked "function(Word)" caller (.function A .unit)
    let empty ← checked "function(Word) returns()" caller (.function A .unit)
    let explicitUnit ← checked "function(Word) returns(())" caller (.function A .unit)
    check (match absent.value,empty.value,explicitUnit.value with
      | .function _ _ none,.function _ _ (some ⟨_,[]⟩),.function _ _ (some ⟨_,[⟨_,.tuple []⟩]⟩) => true
      | _,_,_ => false) "equal Unit meanings do not erase original return presence or lists"
    for text in ["function(Word) returns(Bool)","function(Word,) returns(Bool,)","function((Word,)) returns((Bool,),)"] do
      let _ ← checked text caller (.function A B)
    let _ ← checked "function((Word,Bool)) returns(Word)" caller (.function (.product A B) A)
    let _ ← checked "function(()) returns(Bool)" caller (.function .unit B)
    let _ ← checked "function(Word) returns(Bool,Word,())" caller (.function A (.product B (.product A .unit)))
    let _ ← checked "function(Word) returns((Bool,Word),())" caller (.function A (.product (.product B A) .unit))
    let _ ← checked "function(function(Word) returns(Bool)) returns(function(Bool) returns(Word))" caller
      (.function (.function A B) (.function B A))
    for depth in [0,1,3,6] do
      let text := (List.range depth).foldl (fun inner _ => "function(Word) returns("++inner++")") "(Bool,())"
      let expected := (List.range depth).foldl (fun inner _ => Core.Ty.function A inner) (.product B .unit)
      let _ ← checked text caller expected
    for count in [0,1,2,3,7] do
      let results := String.intercalate "," (List.replicate count "Bool")
      let expected := match count with
        | 0 => Core.Ty.unit
        | n+1 => (List.range n).foldl (fun inner _ => Core.Ty.product B inner) B
      let _ ← checked ("function(Word) returns("++results++")") caller (.function A expected)
    for text in ["function(Unknown)","function(Unknown) returns(Bool)","function(Word) returns(Unknown)",
        "function(Word) returns(Bool,Unknown)","function(Word) returns(Unknown,Bool)",
        "function(Word) returns(Bool,function(Unknown) returns(Bool))"] do rejected text caller
    for returns in [""," returns()"," returns(Bool)"," returns(Word,Bool)"] do
      rejected ("function()"++returns) caller
      rejected ("function(Word,Bool)"++returns) caller
      rejected ("function(Word,Bool,Word)"++returns) caller
  let _ ← checked "function(Pkg /* original */ . Flag) returns(PairAlias,())" table
    (.function .bool (.product (.product .word .bool) .unit))
  let _ ← checked "(function(()) returns(),function(Word) returns(Bool))" table
    (.product (.function .unit .unit) (.function .word .bool))
  for text in ["function() returns()","(function() returns(),Word)","(Word,function() returns(Bool),())",
      "function(Word<Bool>) returns(Bool)","function(@Word) returns(Bool)","function(comptime<Word>) returns(Bool)",
      "function(mapping(Word => Bool)) returns(Bool)","function(Word) returns(@Bool)",
      "function(Word) returns(Bool,mapping(Word => Bool))","function(Word) returns(function(Word,Bool))"] do rejected text table
  let unknown ← parsed "function(Word) returns(New)"
  check (interpretStructuralType? table unknown).isNone "unknown return starts rejected"
  let _ ← checked "function(Word) returns(New)" (table++[(["New"],.bool)]) (.function .word .bool)
  let _ ← checked "function(Word) returns(Bool)" ((["Word"],.unit)::table) (.function .unit .bool)
  have sameLookup (key : List String) : table.lookup? key=(table++table).lookup? key := by
    cases result : table.lookup? key with
    | none =>
        symm
        apply TypeNameTable.lookup?_eq_none_iff.mpr
        simpa only [List.map_append, List.mem_append, not_or] using
          And.intro (TypeNameTable.lookup?_eq_none_iff.mp result)
            (TypeNameTable.lookup?_eq_none_iff.mp result)
    | some type =>
        exact (TypeNameTable.lookup?_iff.mpr
          (TypeNameTable.Extends.append_right table table
            (TypeNameTable.lookup?_iff.mp result))).symm
  for text in ["function(Word)","function(Word) returns(Bool)","function(Word) returns(Unknown)","function() returns(Bool)"] do
    let source ← parsed text
    have _ := interpretStructuralType?_congr_lookup table (table++table) sameLookup source
    check (decide (interpretStructuralType? table source=interpretStructuralType? (table++table) source)) "whole Option agreement includes failures"
  for text in ["function(","function(Word) returns(","function(Word,,Bool)","function(Word) returns(Bool,,Word)","function(Word) Word"] do
    check (← parsed? text).isNone "incomplete or malformed original function type"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedParameterCompilation
/-! Whole parsed entries consume all six positional compilation interfaces.
Actual source lookups and shapes fix open Core without argument inhabitants;
equal typing alone cannot certify a different source position or arm order. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owners : List Resolved.DeclarationId :=
  [⟨⟨.main, ⟨[⟨"PositionalCompilation", by decide⟩], by decide⟩⟩, 7⟩,
    ⟨⟨.main, ⟨[⟨"OtherCompilation", by decide⟩], by decide⟩⟩, 53⟩]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Alias"], .namedData ⟨91⟩), (["Flag"], .bool)]
private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name, row.id, row.type)

private structure SelectedParameter (parameters : List Syntax.FunctionParameter) (index : Nat)
    (type : Core.Ty) where
  span : Syntax.SourceSpan
  name : Syntax.Identifier
  annotation : Syntax.TypeExpr
  atPosition : parameters[index]? = some ⟨span, .typed none name annotation⟩
  meaning : TypeNameDenotes types annotation type

private def selected (parameters : List Syntax.FunctionParameter) (index : Nat) (type : Core.Ty) :
    IO (SelectedParameter parameters index type) := do
  match atPosition : parameters[index]? with
  | some ⟨span, .typed none name annotation⟩ =>
      if interpreted : interpretTypeName? types annotation = some type then
        return ⟨span, name, annotation, atPosition, interpretTypeName?_sound interpreted⟩
      else throw (IO.userError "actual parameter annotation did not have the desired meaning")
  | _ => throw (IO.userError "actual source position was not a typed-none parameter")

private def parsed? (content : String) (location : Syntax.Parser.FunctionLocation := .module) :
    IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-positional-compilation.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"lexer invariant: {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")

private def checkResult {owner : Resolved.DeclarationId} {source : Syntax.FunctionDecl}
    {inputs : LocalTypeInputs} {core : Core.Expr} {type : Core.Ty}
    (forward : RuntimeFunctionCompiles types owner source { inputs, core, returnType := type })
    (success : compileRuntimeFunction? types owner source = some { inputs, core, returnType := type })
    (inverse : ∀ compiled, RuntimeFunctionCompiles types owner source compiled →
      compiled.core = core ∧ compiled.returnType = type)
    (parameterTypes : List Core.Ty) (wrongCore : Core.Expr) : IO Unit := do
  match accepted : compileRuntimeFunction? types owner source with
  | none => throw (IO.userError "independently proved whole entry did not compile")
  | some compiled =>
      let provenance := compileRuntimeFunction?_sound accepted
      have _ := inverse compiled provenance
      have _ := forward.result_unique provenance
      have _ : compiled = { inputs, core, returnType := type } :=
        Option.some.inj (accepted.symm.trans success)
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
        rows compiled.inputs = rows inputs ∧ compiled.inputs.context.values = parameterTypes.reverse ∧
        Core.infer? parameterTypes.reverse core = some type)) "exact whole-entry record or open Core type changed"
      if different : wrongCore ≠ core then
        assertTrue (Core.infer? parameterTypes.reverse wrongCore == some type)
          "wrong-position fixture was not independently equally typed"
        have excluded : ¬ RuntimeFunctionCompiles types owner source
            { inputs, core := wrongCore, returnType := type } := by
          intro wrong
          exact different (inverse _ wrong).1
        have _ := excluded
        assertTrue (decide (compiled.core ≠ wrongCore)) "equally typed wrong Core acquired source provenance"

private def single (content : String) (index : Nat) (parameterTypes : List Core.Ty)
    (type : Core.Ty) : IO Unit := do
  let some source ← parsed? content | throw (IO.userError "singleton fixture did not fully parse")
  let parameter ← selected source.value.signature.parameters.elements index type
  match bodyAt : source.value.body with
  | ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, spelling⟩⟩)⟩]⟩ =>
      if sameName : spelling = parameter.name.value then
        have bodyShape : source.value.body = ⟨blockSpan,
            [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, parameter.name.value⟩⟩)⟩]⟩ := by
          simpa only [sameName] using bodyAt
        assertTrue (source.span.contains parameter.span && parameter.span.contains parameter.name.span &&
          blockSpan.contains returnSpan && span.contains nameSpan) "own singleton source positions changed"
        for owner in owners do
          match declaredAt : declareRuntimeParameters? types owner source.value.signature.parameters.elements with
          | none => throw (IO.userError "whole parameter declaration failed")
          | some inputs =>
              let declared := declareRuntimeParameters?_sound declaredAt
              if headerAt : interpretRuntimeFunctionHeader? types source.value.signature = some type then
                let header := interpretRuntimeFunctionHeader?_iff.mp headerAt
                let forward := runtimeFunction_parameter_compiles declared parameter.atPosition parameter.meaning header bodyShape
                let success := compileRuntimeFunction?_parameter declared parameter.atPosition parameter.meaning header bodyShape
                let coreIndex := parameterTypes.length - 1 - index
                let wrongIndex := ((List.range parameterTypes.length).find? fun candidate =>
                  candidate != coreIndex && Core.infer? parameterTypes.reverse (.var candidate) == some type).getD coreIndex
                checkResult forward success (fun _ provenance => provenance.parameter_return_core
                  parameter.atPosition parameter.meaning bodyShape) parameterTypes (.var wrongIndex)
              else throw (IO.userError "whole singleton header failed")
      else throw (IO.userError "singleton reference did not name the selected parameter")
  | _ => throw (IO.userError "singleton fixture lost its exact identifier-return shape")

private def conditional (content : String) (conditionIndex thenIndex elseIndex : Nat)
    (parameterTypes : List Core.Ty) (type : Core.Ty) : IO Unit := do
  let some source ← parsed? content | throw (IO.userError "conditional fixture did not fully parse")
  let parameters := source.value.signature.parameters.elements
  let condition ← selected parameters conditionIndex .bool
  let thenParameter ← selected parameters thenIndex type
  let elseParameter ← selected parameters elseIndex type
  match bodyAt : source.value.body with
  | ⟨blockSpan, [⟨ifSpan, .ifThen ⟨conditionSpan, .identifier ⟨conditionNameSpan, conditionSpelling⟩⟩
      ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenSpelling⟩⟩)⟩]⟩
      (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseSpelling⟩⟩)⟩]⟩)⟩]⟩ =>
      if sameCondition : conditionSpelling = condition.name.value then
        if sameThen : thenSpelling = thenParameter.name.value then
          if sameElse : elseSpelling = elseParameter.name.value then
            have bodyShape : source.value.body = ⟨blockSpan, [⟨ifSpan,
                .ifThen ⟨conditionSpan, .identifier ⟨conditionNameSpan, condition.name.value⟩⟩
                ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt
                  (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenParameter.name.value⟩⟩)⟩]⟩
                (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt
                  (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseParameter.name.value⟩⟩)⟩]⟩)⟩]⟩ := by
              simpa only [sameCondition, sameThen, sameElse] using bodyAt
            assertTrue (source.span.contains condition.span && source.span.contains thenParameter.span &&
              source.span.contains elseParameter.span && conditionSpan.contains conditionNameSpan &&
              thenSpan.contains thenNameSpan && elseSpan.contains elseNameSpan) "own conditional source positions changed"
            for owner in owners do
              match declaredAt : declareRuntimeParameters? types owner parameters with
              | none => throw (IO.userError "whole conditional parameters failed")
              | some inputs =>
                  let declared := declareRuntimeParameters?_sound declaredAt
                  if headerAt : interpretRuntimeFunctionHeader? types source.value.signature = some type then
                    let header := interpretRuntimeFunctionHeader?_iff.mp headerAt
                    let forward := runtimeFunction_conditional_parameters_compiles declared condition.atPosition
                      thenParameter.atPosition elseParameter.atPosition condition.meaning thenParameter.meaning elseParameter.meaning header bodyShape
                    let success := compileRuntimeFunction?_conditional_parameters declared condition.atPosition
                      thenParameter.atPosition elseParameter.atPosition condition.meaning thenParameter.meaning elseParameter.meaning header bodyShape
                    let count := parameterTypes.length
                    checkResult forward success (fun _ provenance => provenance.conditional_parameters_core
                      condition.atPosition thenParameter.atPosition elseParameter.atPosition condition.meaning
                      thenParameter.meaning elseParameter.meaning bodyShape) parameterTypes
                      (.ifE (.var (count - 1 - conditionIndex)) (.var (count - 1 - elseIndex)) (.var (count - 1 - thenIndex)))
                  else throw (IO.userError "whole conditional header failed")
          else throw (IO.userError "else reference changed its source parameter")
        else throw (IO.userError "then reference changed its source parameter")
      else throw (IO.userError "condition reference changed its source parameter")
  | _ => throw (IO.userError "conditional fixture lost its exact terminal shape")

private def parameterText (annotations : List String) : String :=
  String.intercalate ", " (annotations.zipIdx.map fun (annotation, index) => s!"p{index}: {annotation}")
private def conditionalText (annotations : List String) (condition thenIndex elseIndex : Nat)
    (returnAnnotation : String) : String :=
  s!"function select({parameterText annotations}) returns ({returnAnnotation})" ++
    "{if(" ++ s!"p{condition}" ++ "){return " ++ s!"p{thenIndex};" ++ "}else{return " ++ s!"p{elseIndex};" ++ "}}"

private def rejected (content : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let some source ← parsed? content location | throw (IO.userError s!"semantic rejection did not fully parse: {content}")
  for owner in owners do
    match rejectedAt : compileRuntimeFunction? types owner source with
    | some _ => throw (IO.userError "a selected parameter bypassed a whole-entry obligation")
    | none =>
        have _ := compileRuntimeFunction?_eq_none_iff.mp rejectedAt
        pure ()

def frontendParsedParameterCompilationTests : IO Unit := do
  let pool : List (String × Core.Ty) := [("Opaque", .namedData ⟨91⟩), ("Word", .word), ("Bool", .bool),
    ("Unit", .unit), ("Cell", .cell .word), ("Fn", .function .bool .bool)]
  for arity in [1, 2, 4, 6] do
    let parameters := pool.take arity
    for (parameter, index) in parameters.zipIdx do
      single (s!"function pick({parameterText (parameters.map Prod.fst)}) returns ({parameter.1})" ++
        "{return " ++ s!"p{index};" ++ "}") index (parameters.map Prod.snd) parameter.2
  single "function aliases(x: Opaque,y: Alias) returns (Alias){return x;}" 0
    [.namedData ⟨91⟩, .namedData ⟨91⟩] (.namedData ⟨91⟩)
  for arity in [1, 2, 3, 4] do
    for condition in List.range arity do
      for thenIndex in List.range arity do
        for elseIndex in List.range arity do
          conditional (conditionalText (List.replicate arity "Bool") condition thenIndex elseIndex "Flag")
            condition thenIndex elseIndex (List.replicate arity .bool) .bool
  for condition in List.range 4 do
    let annotations := (List.range 4).map fun index => if index == condition then "Flag" else if index % 2 == 0 then "Opaque" else "Alias"
    let parameterTypes := (List.range 4).map fun index => if index == condition then Core.Ty.bool else .namedData ⟨91⟩
    for thenIndex in (List.range 4).filter (· != condition) do
      for elseIndex in (List.range 4).filter (· != condition) do
        conditional (conditionalText annotations condition thenIndex elseIndex "Alias")
          condition thenIndex elseIndex parameterTypes (.namedData ⟨91⟩)
  for (annotation, type) in pool do
    conditional (conditionalText [annotation, "Bool", annotation] 1 0 2 annotation)
      1 0 2 [type, .bool, type] type
  -- Valid ternary-return syntax is outside the exact terminal-if premise, not rejected.
  let some ternary ← parsed? "function ternary(c: Bool,x: Opaque,y: Alias) returns (Opaque){return c ? x : y;}"
    | throw (IO.userError "valid out-of-profile body did not parse")
  for owner in owners do
    let some compiled := compileRuntimeFunction? types owner ternary
      | throw (IO.userError "exact theorem body shape became an unintended compiler restriction")
    assertTrue (decide (compiled.core = .ifE (.var 2) (.var 1) (.var 0) ∧
      compiled.returnType = .namedData ⟨91⟩)) "valid ternary-return compilation changed"
  let some nested ← parsed? "function nested(c: Bool,x: Opaque) returns (Opaque){if(c){if(c){return x;}else{return x;}}else{return x;}}"
    | throw (IO.userError "valid recursive body did not parse")
  for owner in owners do
    assertTrue (decide ((compileRuntimeFunction? types owner nested).map (fun result => (result.core, result.returnType)) =
      some (.ifE (.var 1) (.ifE (.var 1) (.var 0) (.var 0)) (.var 0), .namedData ⟨91⟩)))
      "exact one-level theorem premise became a recursive compiler restriction"
  for content in ["function generic<T>(x: Opaque) returns (Opaque){return x;}",
      "function mismatch(x: Opaque) returns (Word){return x;}", "function absent(x: Opaque){return x;}",
      "function empty(x: Opaque) returns (){return x;}", "function many(x: Opaque) returns (Opaque,Opaque){return x;}",
      "function duplicate(x: Opaque,x: Opaque) returns (Opaque){return x;}",
      "function hidden(x: Opaque,y: Unknown) returns (Opaque){return x;}",
      "function staged(x: Opaque,comptime y: Word) returns (Opaque){return x;}",
      "function missing(x: Opaque) returns (Opaque){return missing;}",
      "function wrong(c: Word,x: Opaque) returns (Opaque){if(c){return x;}else{return x;}}",
      "function wrong(c: Bool,x: Opaque,y: Word) returns (Opaque){if(c){return x;}else{return y;}}",
      "function skipped(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return missing;}}",
      "function noElse(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}}",
      "function extra(x: Opaque) returns (Opaque){return x;return x;}",
      "function extra(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return x;}return x;}",
      "function armExtra(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return x;return x;}}"] do
    rejected content
  rejected "function publicOnly(x: Opaque) public returns (Opaque){return x;}" .contract
  for content in ["function missing(x){return x;}", "function missing(x:){return x;}",
      "function f(x: Word) returns (Word){return x}", "function f(x: Word){return x;} trailing"] do
    assertTrue (← parsed? content).isNone "malformed or partially consumed declaration became whole-entry evidence"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedParameterDeclarations
/-! Complete canonical parameter text is declared without runtime values.
Real supplied arguments are tested separately against the same static rows.
Signature tests exercise only their parameter lists, not whole declarations. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def parsed_variant? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-parameter-declarations.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Declarations", by decide⟩], by decide⟩⟩, 2⟩
private def types_variant : TypeNameTable :=
  [(["Bool"], .bool), (["Boolean"], .bool), (["Word"], .word), (["Word"], .bool),
    (["Pkg", "Flag"], .bool), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
    (["Pair"], .product .word .bool), (["Choice"], .sum .word .bool)]
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def wordArg : TypedRuntimeArgument := ⟨.word, .word Core.Word.zero, .word⟩
private def cellArg : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
private def closureArg : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩

private def checkDeclaration (parameters : List Syntax.FunctionParameter)
    (expectedTypes : List Core.Ty) : IO LocalTypeInputs := do
  let names ← parameters.mapM fun parameter => do
    let .typed none name _ := parameter.value
      | throw (IO.userError "expected runtime-only annotated parameter")
    pure name.value
  assertTrue (decide (names.length = expectedTypes.length)) "invalid expected type count"
  let some inputs := declareRuntimeParameters? types_variant owner parameters
    | throw (IO.userError "type-only declaration failed without supplied values")
  let expected := (names.zip expectedTypes).zipIdx.map fun (entry, index) =>
    (entry.1, (⟨owner, index⟩ : Resolved.LocalId), entry.2)
  assertTrue (decide (rows inputs = expected.reverse)) "static spelling, identity, type, or order changed"
  assertTrue (decide (inputs.context.values = expectedTypes.reverse)) "wrong reversed type context"
  assertTrue (decide (inputs.ids = (List.range names.length).reverse.map
    fun index => (⟨owner, index⟩ : Resolved.LocalId))) "wrong static allocation sequence"
  return inputs

private def declare (content : String) (expectedTypes : List Core.Ty) : IO LocalTypeInputs := do
  let some parameters ← parsed_variant? Syntax.Parser.functionParameters content
    | throw (IO.userError s!"{content}: expected complete parameters")
  checkDeclaration parameters.elements expectedTypes

private def checkExpression (inputs : LocalTypeInputs) (content : String)
    (expectedCore : Core.Expr) (expectedType : Core.Ty) : IO Unit := do
  let some source ← parsed_variant? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete expression")
  assertTrue (decide (elaborateLocalExpression? inputs.names inputs.context source =
    some (expectedCore, expectedType))) s!"{content}: wrong value-free checking result"

private def checkBinding (content : String) (expectedTypes : List Core.Ty)
    (arguments : List TypedRuntimeArgument) : IO Unit := do
  let some parameters ← parsed_variant? Syntax.Parser.functionParameters content
    | throw (IO.userError s!"{content}: expected complete parameters")
  let declared ← checkDeclaration parameters.elements expectedTypes
  let some bound := bindRuntimeParameters? types_variant owner parameters.elements arguments
    | throw (IO.userError s!"{content}: matching actual arguments did not bind")
  assertTrue (decide (rows bound.toTypeInputs = rows declared)) "erasure changed exact static rows"
  assertTrue (decide (bound.names = declared.names)) "erasure changed the name table"
  assertTrue (decide (bound.context = declared.context)) "erasure changed the typing context"
  assertTrue (decide (bound.environment.values = arguments.reverse.map (·.value)))
    "static preparation lost actual argument values or their order"

private def checkProductParameter : IO Unit := do
  let content := "(x: (Word, Bool))"
  let some parameters ← parsed_variant? Syntax.Parser.functionParameters content
    | throw (IO.userError "original product parameter did not fully parse")
  match parametersAt : parameters.elements with
  | [⟨_, .typed none name annotation⟩] =>
      match annotationAt : annotation with
      | ⟨_, .tuple [left, right]⟩ =>
          if meanings : interpretTypeName? types_variant left = some .word ∧ interpretTypeName? types_variant right = some .bool then
            have meaning : StructuralTypeDenotes types_variant annotation (.product .word .bool) := by
              rw [annotationAt]
              exact .pair (interpretTypeName?_sound meanings.1).structural (interpretTypeName?_sound meanings.2).structural
            have independent : RuntimeParametersDeclare types_variant owner parameters.elements
                (LocalTypeInputs.empty.bindFresh owner name.value (.product .word .bool)) := by
              rw [parametersAt]; exact .cons meaning (by simp) .nil
            have _ := independent.complete
            let inputs ← checkDeclaration parameters.elements [.product .word .bool]
            assertTrue (decide (rows inputs = [("x", ⟨owner, 0⟩, .product .word .bool)])) "product parameter was flattened"
            checkExpression inputs "x" (.var 0) (.product .word .bool)
            checkBinding content [.product .word .bool]
              [⟨.product .word .bool, .pair wordArg.value (.bool true), .pair .word .bool⟩]
          else throw (IO.userError "independent original product leaves changed")
      | _ => throw (IO.userError "original structural annotation lost its two children")
  | _ => throw (IO.userError "original source no longer has exactly one parameter")

def frontendParsedParameterDeclarationTests : IO Unit := do
  checkProductParameter
  let empty ← declare "()" []
  assertTrue empty.bindings.isEmpty "empty declaration introduced a binding"
  let opaqueInputs ← declare "(x: Opaque)" [.namedData ⟨91⟩]
  checkExpression opaqueInputs "x" (.var 0) (.namedData ⟨91⟩)
  let composite ← declare "(pair: Pair, choice: Choice)"
    [.product .word .bool, .sum .word .bool]
  checkExpression composite "pair" (.var 1) (.product .word .bool)
  checkExpression composite "choice" (.var 0) (.sum .word .bool)
  let branching ← declare "(c: Pkg /* alias */ . Flag, t: Word, f: Word,)" [.bool, .word, .word]
  checkExpression branching "c ? ~t : f" (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
  for left in [false, true] do
    for right in [false, true] do
      checkBinding "(left: Bool, right: Boolean)" [.bool, .bool] [boolArg left, boolArg right]
  checkBinding "()" [] []
  checkBinding "(c: Bool, w: Word, cell: Cell, fn: Fn)"
    [.bool, .word, .cell .word, .function .bool .bool] [boolArg true, wordArg, cellArg, closureArg]
  let some signature ← parsed_variant? (Syntax.Parser.functionSignature .module)
      "function declared(x: Opaque, y: Word) returns (Opaque)"
    | throw (IO.userError "expected a complete signature")
  let signatureInputs ← checkDeclaration signature.parameters.elements [.namedData ⟨91⟩, .word]
  checkExpression signatureInputs "x" (.var 1) (.namedData ⟨91⟩)
  for (content, expected, arguments) in [
      ("(x: Bool)", [.bool], []), ("()", [], [boolArg false]),
      ("(x: Bool)", [.bool], [boolArg false, boolArg true]),
      ("(x: Bool, y: Word)", [.bool, .word], [wordArg, boolArg true]),
      ("(x: Opaque)", [.namedData ⟨91⟩], []),
      ("(x: Word)", [.word], [boolArg true])] do
    let some parameters ← parsed_variant? Syntax.Parser.functionParameters content
      | throw (IO.userError s!"{content}: mismatch case should parse")
    let _ ← checkDeclaration parameters.elements expected
    assertTrue (bindRuntimeParameters? types_variant owner parameters.elements arguments).isNone
      s!"{content}: static success bypassed runtime arity or ordered type matching"
  for content in ["(x: Bool, x: Bool)", "(x: Bool, y: Word, x: Word)",
      "(x: Unknown)", "(x: bool)", "(x: Bool<Word>)", "(x: @Bool)",
      "(x: mapping(Word => Bool))",
      "(comptime x: Bool)"] do
    let some parameters ← parsed_variant? Syntax.Parser.functionParameters content
      | throw (IO.userError s!"{content}: adapter rejection case should parse")
    assertTrue (declareRuntimeParameters? types_variant owner parameters.elements).isNone
      s!"{content}: unsupported static parameter profile was accepted"
  for content in ["", "(x)", "(x:)", "(x: Bool", "(x: Bool) trailing", "(x: comptime<Bool>)"] do
    assertTrue (← parsed_variant? Syntax.Parser.functionParameters content).isNone
      s!"{content}: accepted malformed, diagnosed, or incompletely consumed parameters"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedParameterPositions
/-! Actual parsed parameter lookups justify reversed Core indices without
runtime arguments. Same-type positions, nominal types, owner composition and
out-of-range subtraction retain their distinct static contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owners_variant : List Resolved.DeclarationId :=
  [⟨⟨.main, ⟨[⟨"StaticPositions", by decide⟩], by decide⟩⟩, 4⟩,
    ⟨⟨.main, ⟨[⟨"OtherPositions", by decide⟩], by decide⟩⟩, 4⟩]
private def shiftOwner (offset : Nat) (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { owner with declarationIndex := owner.declarationIndex + offset }
private theorem shiftInjective (offset : Nat) : Function.Injective (shiftOwner offset) := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; simp_all [shiftOwner]
private def types_variant2 : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private theorem desiredPosition {table : TypeNameTable} {owner : Resolved.DeclarationId}
    {parameters : List Syntax.FunctionParameter} {inputs : LocalTypeInputs}
    (declared : RuntimeParametersDeclare table owner parameters inputs) {index : Nat}
    {parameterSpan : Syntax.SourceSpan} {name : Syntax.Identifier} {annotation : Syntax.TypeExpr}
    {type : Core.Ty} (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes table annotation type) :
    index < parameters.length ∧ inputs.bindings[parameters.length - 1 - index]? =
      some { name := name.value, id := ⟨owner, index⟩, type } ∧
      LocalNameTable.Lookup inputs.names name.value ⟨owner, index⟩ ∧
      Resolved.LocalScope.Lookup inputs.context ⟨owner, index⟩ type ∧
      Resolved.LocalScope.IndexOf inputs.context.ids ⟨owner, index⟩ (parameters.length - 1 - index) := by
  obtain ⟨bounded, actualType, actualMeaning, rowAt, named, typed, indexed⟩ := declared.position parameterAt
  have same := actualMeaning.type_unique meaning.structural
  cases same
  exact ⟨bounded, rowAt, named, typed, indexed⟩

private theorem noOutsideWitness {table : TypeNameTable} {owner : Resolved.DeclarationId}
    {parameters : List Syntax.FunctionParameter} {inputs : LocalTypeInputs}
    (declared : RuntimeParametersDeclare table owner parameters inputs) (index : Nat)
    (outside : parameters.length ≤ index) :
    ¬ ∃ span name annotation, parameters[index]? = some ⟨span, .typed none name annotation⟩ := by
  rintro ⟨span, name, annotation, parameterAt⟩
  exact Nat.not_lt_of_ge outside (declared.position parameterAt).1

private def parsed_variant2? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-static-positions.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def checkOutside {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {inputs : LocalTypeInputs} (declared : RuntimeParametersDeclare types_variant2 owner parameters inputs) : IO Unit := do
  for index in [parameters.length, parameters.length + 1, parameters.length + 17] do
    if outside : parameters.length ≤ index then
      have _ := noOutsideWitness declared index outside
      assertTrue (decide (parameters[index]? = none ∧ parameters.length - 1 - index = 0 ∧
        inputs.context.lookup? ⟨owner, index⟩ = none ∧
        Resolved.LocalScope.index? inputs.ids ⟨owner, index⟩ = none))
        "saturated subtraction fabricated an out-of-range parameter, type lookup, or Core index"
    else throw (IO.userError "outside fixture was in range")

private def checkSelected (source : Syntax.FunctionDecl) (index : Nat) (expectedType : Core.Ty)
    {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    (declared : RuntimeParametersDeclare types_variant2 owner source.value.signature.parameters.elements inputs) : IO Unit := do
  let parameters := source.value.signature.parameters.elements
  let count := parameters.length
  have _ := declared.rows.arity
  have _ := declared.bindings_length
  have _ := declared.names_nodup
  have _ := declared.generated_ids
  assertTrue (decide (inputs.bindings.length = count ∧ (inputs.names.map Prod.fst).Nodup ∧
    inputs.ids = (List.range count).reverse.map (fun index => (⟨owner, index⟩ : Resolved.LocalId))))
    "empty-start layout changed arity, unique spellings, or generated identities"
  match parameterAt : parameters[index]? with
  | some ⟨parameterSpan, .typed none name annotation⟩ =>
      if interpreted : interpretTypeName? types_variant2 annotation = some expectedType then
        let meaning := interpretTypeName?_sound interpreted
        have _ := declared.rows.row_at parameterAt
        have _ := desiredPosition declared parameterAt meaning
        let coreIndex := count - 1 - index
        assertTrue (decide (index < count ∧ inputs.bindings[coreIndex]?.map
          (fun row => (row.name, row.id, row.type)) = some (name.value, ⟨owner, index⟩, expectedType) ∧
          inputs.names.lookup? name.value = some ⟨owner, index⟩ ∧
          inputs.context.lookup? ⟨owner, index⟩ = some expectedType ∧
          Resolved.LocalScope.index? inputs.context.ids ⟨owner, index⟩ = some coreIndex))
          "actual source lookup lost its exact reversed row or first-match position"
        match bodyAt : source.value.body with
        | ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨expressionSpan, .identifier reference⟩)⟩]⟩ =>
            if sameName : reference.value = name.value then
              have _ := declared.reference_resolves_at parameterAt expressionSpan reference.span
              have _ := declared.reference_elaborates_at parameterAt meaning expressionSpan reference.span
              have returned := declared.reference_return_elaborates_at parameterAt meaning
                blockSpan returnSpan expressionSpan reference.span
              have ownReturn : ReturnBodyElaborates inputs.names inputs.context source.value.body
                  (.var coreIndex) expectedType := by
                simpa only [bodyAt, ← sameName] using returned
              have _ := ownReturn.complete
              let expression : Syntax.Expr := ⟨expressionSpan, .identifier reference⟩
              assertTrue (decide (resolveLocalExpression? inputs.names expression = some (.var ⟨owner, index⟩) ∧
                elaborateLocalExpression? inputs.names inputs.context expression = some (.var coreIndex, expectedType) ∧
                elaborateReturnBody? inputs.names inputs.context source.value.body = some (.var coreIndex, expectedType) ∧
                Core.infer? inputs.context.values (.var coreIndex) = some expectedType))
                "own parsed identifier or return did not retain exact positional Core/type"
              assertTrue (source.span.contains parameterSpan && parameterSpan.contains name.span &&
                blockSpan.contains returnSpan && returnSpan.contains expressionSpan && expressionSpan.contains reference.span)
                "source spelling/position witnesses were replaced"
              if 1 < count then
                let wrongIndex := (coreIndex + 1) % count
                assertTrue (decide (wrongIndex ≠ coreIndex ∧
                  Resolved.LocalScope.index? inputs.ids ⟨owner, index⟩ ≠ some wrongIndex ∧
                  elaborateLocalExpression? inputs.names inputs.context expression ≠ some (.var wrongIndex, expectedType)))
                  "same-type or in-range alternative index replaced the actual source position"
            else throw (IO.userError "parsed return named a different source parameter")
        | _ => throw (IO.userError "positive fixture did not retain its own singleton identifier return")
      else throw (IO.userError "actual parameter annotation did not denote the desired type")
  | _ => throw (IO.userError "selected source position lacked its actual typed-none parameter")
  checkOutside declared

private def checkText (content : String) (index : Nat) (parameterTypes : List Core.Ty)
    (expectedType : Core.Ty) : IO Unit := do
  let some source ← parsed_variant2? content | throw (IO.userError "complete positional declaration did not parse")
  for owner in owners_variant do
    match accepted : declareRuntimeParameters? types_variant2 owner source.value.signature.parameters.elements with
    | none => throw (IO.userError "type-only parameter declaration failed")
    | some inputs =>
        let declared := declareRuntimeParameters?_sound accepted
        assertTrue (decide (inputs.context.values = parameterTypes.reverse)) "static type order changed"
        checkSelected source index expectedType declared
        let first := shiftOwner 7
        let second := shiftOwner 11
        let once := declared.map_owner first (shiftInjective 7)
        let twice := once.map_owner second (shiftInjective 11)
        let composed := declared.map_owner (second ∘ first) ((shiftInjective 11).comp (shiftInjective 7))
        checkSelected source index expectedType twice
        checkSelected source index expectedType composed
        let firstInputs := inputs.mapIds (ownerLocalIdMap first) (ownerLocalIdMap_injective first (shiftInjective 7))
        let twiceInputs := firstInputs.mapIds (ownerLocalIdMap second) (ownerLocalIdMap_injective second (shiftInjective 11))
        let composedInputs := inputs.mapIds (ownerLocalIdMap (second ∘ first))
          (ownerLocalIdMap_injective (second ∘ first) ((shiftInjective 11).comp (shiftInjective 7)))
        have _ := inputs.mapIds_comp (ownerLocalIdMap first) (ownerLocalIdMap second)
          (ownerLocalIdMap_injective first (shiftInjective 7)) (ownerLocalIdMap_injective second (shiftInjective 11))
        assertTrue (decide (rows twiceInputs = rows composedInputs ∧ inputs.ids ≠ twiceInputs.ids ∧
          inputs.names.map Prod.fst = twiceInputs.names.map Prod.fst)) "composed owner transport changed spelling/order"
        let some compiled := compileRuntimeFunction? types_variant2 owner source
          | throw (IO.userError "valid own positional return did not compile")
        assertTrue (decide (compiled.core = .var (parameterTypes.length - 1 - index) ∧
          compiled.returnType = expectedType ∧ rows compiled.inputs = rows inputs)) "whole compilation replaced source correspondence"

def frontendParsedParameterPositionTests : IO Unit := do
  let pool : List (String × Core.Ty) := [("Opaque", .namedData ⟨91⟩), ("Word", .word), ("Bool", .bool),
    ("Cell", .cell .word), ("Fn", .function .bool .bool), ("Opaque", .namedData ⟨91⟩), ("Word", .word), ("Unit", .unit)]
  for arity in [1, 2, 3, 5, 8] do
    let selectedTypes := pool.take arity
    let parameters := String.intercalate ", " (selectedTypes.zipIdx.map fun (row, index) => s!"p{index}: {row.1}")
    for (selected, index) in selectedTypes.zipIdx do
      checkText (s!"function pick({parameters}) returns ({selected.1})" ++ " { return " ++ s!"p{index};" ++ " }")
        index (selectedTypes.map Prod.snd) selected.2
  checkText "function same(x: Opaque,y: Opaque) returns (Opaque){return x;}" 0
    [.namedData ⟨91⟩, .namedData ⟨91⟩] (.namedData ⟨91⟩)
  let nominalContext : Core.Context := [.namedData ⟨91⟩, .namedData ⟨91⟩]
  assertTrue (decide (Core.infer? nominalContext (.var 0) = some (.namedData ⟨91⟩) ∧
    Core.infer? nominalContext (.var 1) = some (.namedData ⟨91⟩) ∧ 2 - 1 - 2 = 0))
    "same types or saturated subtraction must not justify a source position"
  let some empty ← parsed_variant2? "function empty(){return;}" | throw (IO.userError "empty declaration did not parse")
  for owner in owners_variant do
    match accepted : declareRuntimeParameters? types_variant2 owner empty.value.signature.parameters.elements with
    | some _inputs => checkOutside (declareRuntimeParameters?_sound accepted)
    | none => throw (IO.userError "empty static parameters rejected")
  for (content, parametersAccepted) in [
      ("function duplicate(x: Word,x: Word){return;}", false),
      ("function duplicate(x: Word,y: Bool,x: Opaque){return;}", false),
      ("function unknown(x: Unknown){return;}", false), ("function staged(comptime x: Word){return;}", false),
      ("function missing(x: Opaque) returns (Opaque){return missing;}", true),
      ("function wrong(x: Opaque) returns (Word){return x;}", true),
      ("function call(f: Fn) returns (Bool){return f();}", true),
      ("function skipped(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return missing;}}", true)] do
    let some source ← parsed_variant2? content | throw (IO.userError "semantic rejection did not fully parse")
    for owner in owners_variant do
      assertTrue ((declareRuntimeParameters? types_variant2 owner source.value.signature.parameters.elements).isSome == parametersAccepted)
        "whole-body rejection was confused with parameter declaration rejection"
      assertTrue (compileRuntimeFunction? types_variant2 owner source).isNone "valid parameter layout certified an invalid whole body/contract"
  for content in ["", "function missing(x){return;}", "function missing(x:){return;}",
      "function f()", "function f(x: Word){return x;} trailing"] do
    assertTrue (← parsed_variant2? content).isNone "missing annotations or incomplete source became static parameter evidence"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeArgumentStatic
/-! Equal typed-argument type lists preserve static preparation, including
rejection. Actual runtime values, suspended states, and costs need not agree. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-argument-static.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  assertTrue lexed.diagnostics.isEmpty s!"{content}: lexer diagnostics"
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      assertTrue (next.atEnd && next.diagnostics.isEmpty) s!"{content}: incomplete or diagnosed declaration"
      return source
  | .reject _ _ => throw (IO.userError s!"{content}: expected a complete declaration")
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner_variant : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Static", by decide⟩], by decide⟩⟩, 0⟩
private def types_variant3 : TypeNameTable :=
  [(["Bool"], .bool), (["Word"], .word), (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def seven : Core.Word := ⟨7, by decide⟩
private def nine : Core.Word := ⟨9, by decide⟩
private def store : Core.Store := [.word nine, .bool true]
private def wordArg_variant (value : Core.Word) : TypedRuntimeArgument := ⟨.word, .word value, .word⟩
private def cellArg_variant (location : Core.Location) : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word location, .cellRef⟩
private def identityClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
private def constantClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.bool false) [], .closure .nil .bool⟩
private def sameStatic : Option PreparedRuntimeFunction → Option PreparedRuntimeFunction → Bool
  | none, none => true
  | some left, some right =>
      decide (left.inputs.ids = right.inputs.ids) && decide (left.inputs.names = right.inputs.names) &&
      decide (left.inputs.context = right.inputs.context) && decide (left.core = right.core) &&
      decide (left.returnType = right.returnType)
  | _, _ => false

private def checkRun (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (prepared : PreparedRuntimeFunction) (value : Core.Value) (cost : Nat) (initialStore : Core.Store) : IO Unit := do
  assertTrue (decide (prepared.inputs.environment.values = arguments.reverse.map (·.value)))
    "new typed argument values did not populate the actual runtime rows"
  assertTrue (decide (runRuntimeFunction? types_variant3 owner_variant source arguments 0 initialStore =
    some (prepared.returnType, .outOfFuel
      (Core.State.initial prepared.core prepared.inputs.environment.values initialStore))))
    "wrong actual zero-fuel environment"
  for fuel in [0, cost - 1] do
    match runRuntimeFunction? types_variant3 owner_variant source arguments fuel initialStore with
    | some (type, .outOfFuel _) =>
        assertTrue (decide (type = prepared.returnType)) "exhaustion changed the static return type"
    | _ => throw (IO.userError "execution did not exhaust below the expected cost")
  for fuel in [cost, cost + 5] do
    assertTrue (decide (runRuntimeFunction? types_variant3 owner_variant source arguments fuel initialStore =
      some (prepared.returnType, .done value initialStore))) "wrong new argument result, cost, or store"

private def checkAccepted (content : String) (left right : List TypedRuntimeArgument)
    (core : Core.Expr) (type : Core.Ty) (leftValue rightValue : Core.Value)
    (leftCost rightCost : Nat) (initialStore : Core.Store := store) : IO Unit := do
  let source ← parsed content
  assertTrue (decide (left.map (·.type) = right.map (·.type))) "fixture must preserve ordered argument types"
  let first := prepareRuntimeFunction? types_variant3 owner_variant source left
  let second := prepareRuntimeFunction? types_variant3 owner_variant source right
  assertTrue (sameStatic first second) s!"{content}: static preparation changed"
  let some first := first | throw (IO.userError s!"{content}: first valid entry rejected")
  let some second := second | throw (IO.userError s!"{content}: second valid entry rejected")
  assertTrue (decide (first.core = core ∧ first.returnType = type)) s!"{content}: unexpected checked Core/type"
  assertTrue (decide (first.inputs.environment.values ≠ second.inputs.environment.values))
    s!"{content}: counterexample must change actual runtime values"
  assertTrue (decide (runRuntimeFunction? types_variant3 owner_variant source left 0 initialStore ≠
    runRuntimeFunction? types_variant3 owner_variant source right 0 initialStore))
    s!"{content}: distinct initial environments must remain distinguishable"
  checkRun source left first leftValue leftCost initialStore
  checkRun source right second rightValue rightCost initialStore

def frontendParsedRuntimeArgumentStaticTests : IO Unit := do
  let left := [boolArg false, wordArg_variant seven, wordArg_variant nine]
  let right := [boolArg true, wordArg_variant seven, wordArg_variant nine]
  let header := "function selected(c: Bool, t: Word, f: Word)"
  checkAccepted (header ++ " returns (Word) { return c ? ~t : f; }") left right
    (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word (.word nine) (.word seven.bitNot) 4 6
  checkAccepted "function logical(c: Bool) returns (Bool) { return c && !c; }"
    [boolArg false] [boolArg true] (.ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false))
    .bool (.bool false) (.bool false) 4 6
  checkAccepted "function first(x: Bool, y: Bool) returns (Bool) { return x; }"
    [boolArg false, boolArg true] [boolArg true, boolArg false] (.var 1) .bool (.bool false) (.bool true) 1 1
  checkAccepted "function cell(x: Cell) returns (Cell) { return x; }"
    [cellArg_variant 40] [cellArg_variant 41] (.var 0) (.cell .word) (.cellRef .word 40) (.cellRef .word 41) 1 1 []
  checkAccepted "function unused(x: Cell) { return; }"
    [cellArg_variant 40] [cellArg_variant 41] .unit .unit .unit .unit 1 1 []
  checkAccepted "function closure(x: Fn) returns (Fn) { return x; }"
    [identityClosure] [constantClosure] (.var 0) (.function .bool .bool)
    identityClosure.value constantClosure.value 1 1
  for content in [
      header ++ " returns (Word) { return c ? t : missing; }",
      header ++ " returns (Word) { return c ? t : c; }",
      header ++ " returns (Bool) { return t; }", header ++ " returns () { return; }",
      "function arity(c: Bool) returns (Bool) { return c; }",
      "function duplicate(c: Bool, t: Word, c: Word) returns (Word) { return t; }",
      "function annotation(c: Word, t: Word, f: Word) returns (Word) { return t; }"] do
    let source ← parsed content
    let first := prepareRuntimeFunction? types_variant3 owner_variant source left
    let second := prepareRuntimeFunction? types_variant3 owner_variant source right
    assertTrue (sameStatic first second) s!"{content}: rejection not preserved"
    assertTrue (first.isNone && second.isNone) s!"{content}: unsupported whole contract accepted"
    for fuel in [0, 4, 6, 20] do
      assertTrue ((runRuntimeFunction? types_variant3 owner_variant source left fuel store).isNone &&
        (runRuntimeFunction? types_variant3 owner_variant source right fuel store).isNone)
        s!"{content}: values bypassed whole preparation"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeParameters
/-! Completely parsed parameter lists feed the actual input builder, and the
returned tables feed existing expression checking and execution. This does not
execute a function declaration or give meaning to its remaining signature. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def parsed_variant3? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-runtime-parameters.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner_variant2 : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Parameters", by decide⟩], by decide⟩⟩, 0⟩
private def types_variant4 : TypeNameTable :=
  [(["Bool"], .bool), (["Boolean"], .bool), (["Word"], .word), (["Pkg", "Flag"], .bool)]
private def boolArgument (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def wordArgument (value : Core.Word) : TypedRuntimeArgument := ⟨.word, .word value, .word⟩
private def store_variant : Core.Store := [.word nine, .bool false]

private def checkOrder (parameters : List Syntax.FunctionParameter)
    (arguments : List TypedRuntimeArgument) (inputs : LocalInputs) : IO Unit := do
  let names : List String ← parameters.mapM fun parameter => do
    let .typed none name _ := parameter.value
      | throw (IO.userError "accepted a non-runtime parameter")
    pure name.value
  assertTrue (decide (names.length = arguments.length)) "accepted mismatched arity"
  let expected : List (String × Resolved.LocalId × Core.Ty × Core.Value) :=
    (names.zip arguments).zipIdx.map fun (entry, index) =>
    (entry.1, (⟨owner_variant2, index⟩ : Resolved.LocalId), entry.2.type, entry.2.value)
  let actual : List (String × Resolved.LocalId × Core.Ty × Core.Value) := inputs.bindings.map fun binding =>
    (binding.name, binding.id, binding.type, binding.value)
  assertTrue (decide (actual = expected.reverse))
    "parameter/argument pairing, generated identity, or reverse storage order changed"

private def prepare (content : String) (arguments : List TypedRuntimeArgument) : IO LocalInputs := do
  let some parameters ← parsed_variant3? Syntax.Parser.functionParameters content
    | throw (IO.userError s!"{content}: expected a complete parameter list")
  let some inputs := bindRuntimeParameters? types_variant4 owner_variant2 parameters.elements arguments
    | throw (IO.userError s!"{content}: valid runtime arguments did not bind")
  checkOrder parameters.elements arguments inputs
  return inputs

private def checkRun_variant (inputs : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let some source ← parsed_variant3? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete local expression")
  let checked := inputs.check? source
  assertTrue (decide (checked = some (expectedCore, type)))
    s!"{content}: wrong checked type or parameter position"
  let some (actualCore, _) := checked
    | throw (IO.userError s!"{content}: checking unexpectedly failed")
  assertTrue (decide (inputs.run? 0 source store_variant =
    some (type, .outOfFuel (Core.State.initial actualCore inputs.environment.values store_variant))))
    s!"{content}: wrong actual initial environment or zero-fuel result"
  for fuel in [0, cost - 1] do
    match inputs.run? fuel source store_variant with
    | some (actualType, .outOfFuel _) =>
        assertTrue (decide (actualType = type)) s!"{content}: exhaustion changed the type"
    | _ => throw (IO.userError s!"{content}: execution did not exhaust below its exact cost")
  for fuel in [cost, cost + 5] do
    assertTrue (decide (inputs.run? fuel source store_variant = some (type, .done value store_variant)))
      s!"{content}: wrong supplied argument, completion boundary, or final store"

def frontendParsedRuntimeParameterTests : IO Unit := do
  let empty ← prepare "()" []
  assertTrue empty.bindings.isEmpty "empty parameters introduced a binding"
  for left in [false, true] do
    for right in [false, true] do
      let inputs ← prepare "(left: Bool, right: Boolean,)" [boolArgument left, boolArgument right]
      checkRun_variant inputs "left" (.var 1) .bool (.bool left) 1
      checkRun_variant inputs "right" (.var 0) .bool (.bool right) 1
      checkRun_variant inputs "left && right" (.ifE (.var 1) (.var 0) (.bool false))
        .bool (.bool (left && right)) 4
      checkRun_variant inputs "left || right" (.ifE (.var 1) (.bool true) (.var 0))
        .bool (.bool (left || right)) 4
  for choice in [false, true] do
    let arguments := [boolArgument choice, wordArgument seven, wordArgument nine]
    let inputs ← prepare "(c: Pkg /* qualified */ . Flag, t: Word, f: Word)" arguments
    checkRun_variant inputs "c ? t : f" (.ifE (.var 2) (.var 1) (.var 0))
      .word (.word (if choice then seven else nine)) 4
    checkRun_variant inputs "t ^ f" (.binary .wordXor (.var 1) (.var 0))
      .word (.word (seven.bitXor nine)) 5
    let some missing ← parsed_variant3? Syntax.Parser.expression "c ? t : missing"
      | throw (IO.userError "missing branch expression did not parse")
    for fuel in [0, 4, 20] do
      assertTrue (inputs.run? fuel missing store_variant).isNone
        "parameter input preparation bypassed whole-expression checking"
  let some signature ← parsed_variant3? (Syntax.Parser.functionSignature .module)
      "function choose(c: Bool, t: Word, f: Word) returns (Word)"
    | throw (IO.userError "complete signature parsing failed")
  let arguments := [boolArgument true, wordArgument seven, wordArgument nine]
  let some signatureInputs := bindRuntimeParameters? types_variant4 owner_variant2 signature.parameters.elements arguments
    | throw (IO.userError "actual signature parameters failed to bind")
  checkOrder signature.parameters.elements arguments signatureInputs
  checkRun_variant signatureInputs "c ? t : f" (.ifE (.var 2) (.var 1) (.var 0)) .word (.word seven) 4
  for (content, arguments) in [
      ("(x: Bool)", []), ("()", [boolArgument false]),
      ("(x: Bool)", [boolArgument false, boolArgument true]),
      ("(x: Bool, y: Bool)", [boolArgument false]),
      ("(x: Bool, x: Bool)", [boolArgument false, boolArgument true]),
      ("(x: Bool, y: Bool, x: Bool)", [boolArgument false, boolArgument true, boolArgument false]),
      ("(x: Word)", [boolArgument true]), ("(x: Bool)", [wordArgument seven]),
      ("(x: Unknown)", [boolArgument true]), ("(x: Bool<Word>)", [boolArgument true]),
      ("(x: @Bool)", [boolArgument true]), ("(comptime x: Bool)", [boolArgument true])] do
    let some parameters ← parsed_variant3? Syntax.Parser.functionParameters content
      | throw (IO.userError s!"{content}: adapter rejection case should parse")
    assertTrue (bindRuntimeParameters? types_variant4 owner_variant2 parameters.elements arguments).isNone
      s!"{content}: unsupported or mismatched arguments were accepted"
  for content in ["", "(x)", "(x:)", "(x: Bool", "(x: Bool) trailing", "(x: comptime<Bool>)"] do
    assertTrue (← parsed_variant3? Syntax.Parser.functionParameters content).isNone
      s!"{content}: accepted malformed, diagnosed, or only partially consumed parameters"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeArgumentConstructionBoundaryProperties
/-! Raw actual values precede construction. Structural acceptance checks actual
bodies/captures but neither adds type well-formedness nor establishes allocation. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeArgumentConstructionBoundary
open Solcore Solcore.Frontend

private def identity (signature : Core.Ty) (captured : Core.Environment) : Core.Value :=
  .closure signature signature (.var 0) captured
private def nested (unused signature : Core.Ty) (suffix : Core.Environment) : Nat → Core.Value → Core.Value
  | 0, value => value
  | n+1, value =>
      let inner := nested unused signature suffix n value
      .pair (.inLeft unused inner) (.inRight unused (identity signature (inner::suffix)))
private theorem environmentTyped {captured : Core.Environment}
    (typed : ∀ value ∈ captured, Core.ValueHasType value value.type) :
    Core.EnvironmentHasTypes captured (captured.map Core.Value.type) := by
  induction captured with
  | nil => exact .nil
  | cons value rest ih => exact .cons (typed value (by simp)) (ih (fun v member => typed v (by simp [member])))
private theorem nestedTyped (unused signature : Core.Ty) (suffix : Core.Environment) (depth : Nat) (value : Core.Value)
    (typed : Core.ValueHasType value value.type) (captured : ∀ v ∈ suffix, Core.ValueHasType v v.type) :
    Core.ValueHasType (nested unused signature suffix depth value) (nested unused signature suffix depth value).type := by
  induction depth with
  | zero => exact typed
  | succ depth ih => exact .pair (.inLeft ih) (.inRight (.closure (.cons ih (environmentTyped captured)) (.var rfl)))
private theorem nestedPayload {unused signature : Core.Ty} {suffix : Core.Environment} {value : Core.Value}
    (depth : Nat) {type : Core.Ty} (typed : Core.ValueHasType (nested unused signature suffix depth value) type) :
    ∃ type, Core.ValueHasType value type := by
  induction depth generalizing type with
  | zero => exact ⟨_,typed⟩
  | succ depth ih => cases typed with | pair left _ => cases left with | inLeft inner => exact ih inner
private theorem capturedLookup {definitions : Core.DataEnvironment} {captured : Core.Environment} {context : Core.Context}
    (typed : Core.EnvironmentHasTypes captured context definitions)
    {index : Nat} {value : Core.Value} (found : captured[index]? = some value) :
    ∃ type, Core.ValueHasType value type definitions := by
  induction typed using Core.EnvironmentHasTypes.rec (motive_1 := fun _ _ _ _ => True) generalizing index with
  | unit | bool | word | integer | pair | inLeft | inRight | closure | cellRef | constructed => trivial
  | nil => simp at found
  | cons head _ _ ih => cases index with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at found; subst value; exact ⟨_,head⟩
    | succ index => exact ih (by simpa using found)
private theorem builds {value : Core.Value} (typed : Core.ValueHasType value value.type) :
    buildRuntimeArgument? value = some ⟨value.type,value,typed⟩ := buildRuntimeArgument?_iff.mpr rfl
private theorem rejects {value : Core.Value} (untyped : ∀ type, ¬ Core.ValueHasType value type) :
    buildRuntimeArgument? value = none := by
  cases checked : buildRuntimeArgument? value with
  | none => rfl
  | some argument =>
      have same := buildRuntimeArgument?_iff.mp checked
      have typed := argument.valueTyped
      rw [same] at typed
      exact False.elim (untyped _ typed)

theorem arbitrary_nested_actual_values_and_captured_suffixes_are_retained
    (unused signature : Core.Ty) (suffix : Core.Environment) (depth : Nat) (value : Core.Value)
    (typed : Core.ValueHasType value value.type) (captured : ∀ v ∈ suffix, Core.ValueHasType v v.type) :
    ∃ argument, buildRuntimeArgument? (nested unused signature suffix depth value) = some argument ∧
      argument.value = nested unused signature suffix depth value ∧ argument.type = (nested unused signature suffix depth value).type :=
  ⟨_,builds (nestedTyped unused signature suffix depth value typed captured),rfl,rfl⟩

theorem no_nested_pair_or_sum_layer_repairs_an_untypable_actual_payload
    (unused signature : Core.Ty) (suffix : Core.Environment) (depth : Nat) (value : Core.Value)
    (untyped : ∀ type, ¬ Core.ValueHasType value type) :
    buildRuntimeArgument? (nested unused signature suffix depth value) = none := by
  apply rejects
  intro type typed
  obtain ⟨type,typed⟩ := nestedPayload depth typed
  exact untyped type typed

theorem unused_invalid_captures_at_arbitrary_positions_are_rejected
    (signature : Core.Ty) (leading suffix : Core.Environment) (bad : Core.Value)
    (untyped : ∀ type, ¬ Core.ValueHasType bad type) :
    buildRuntimeArgument? (identity signature (leading ++ bad::suffix)) = none := by
  apply rejects
  intro type typed
  cases typed with
  | closure captured _ =>
      obtain ⟨type,typed⟩ := capturedLookup captured (show (leading ++ bad::suffix)[leading.length]? = some bad by simp)
      exact untyped type typed

private def forged : Core.Value := .closure .word .word (.bool false) []
private theorem forgedUntyped (type : Core.Ty) : ¬ Core.ValueHasType forged type := by
  intro typed; cases typed with | closure _ body => cases body
theorem unused_bad_closures_and_hosts_are_rejected_at_arbitrary_capture_positions
    (signature : Core.Ty) (leading suffix : Core.Environment) (host : Core.HostFunction) :
    buildRuntimeArgument? (identity signature (leading ++ forged::suffix)) = none ∧
    buildRuntimeArgument? (identity signature (leading ++ .hostFunction host::suffix)) = none := by
  exact ⟨unused_invalid_captures_at_arbitrary_positions_are_rejected signature leading suffix forged forgedUntyped,
    unused_invalid_captures_at_arbitrary_positions_are_rejected signature leading suffix (.hostFunction host)
      (by intro type typed; cases typed)⟩

theorem identical_function_tags_do_not_determine_construction_or_raw_results (word : Core.Word) :
    (identity .word []).type = forged.type ∧
    (buildRuntimeArgument? (identity .word [])).isSome = true ∧ buildRuntimeArgument? forged = none ∧
    Core.runStateful 6 (.initial (.apply (.var 0) (.word word)) [identity .word []] []) = .done (.word word) [] ∧
    Core.runStateful 6 (.initial (.apply (.var 0) (.word word)) [forged] []) = .done (.bool false) [] := by
  refine ⟨rfl,?_,rejects forgedUntyped,rfl,rfl⟩
  simp only [identity]
  rw [builds (.closure .nil (.var rfl))]; rfl

private def unbound : Core.Value := .closure .unit .unit (.var 1) []
theorem an_out_of_range_body_is_rejected_without_repairing_its_raw_fault :
    buildRuntimeArgument? unbound = none ∧
    Core.runStateful 5 (.initial (.apply (.var 0) .unit) [unbound] []) =
      .fault (.unboundVariable 1) ⟨.eval (.var 1) [.unit],[],[]⟩ := by
  refine ⟨rejects ?_,rfl⟩
  intro type typed
  cases typed with | closure captured body => cases captured with | nil => cases body with | var found => cases found

theorem nominal_signatures_are_accepted_without_typing_a_rebuilt_lambda (nominal : Core.DataTypeId) :
    (buildRuntimeArgument? (identity (.namedData nominal) [])).isSome = true ∧
    Core.infer? [] (.lambda (.namedData nominal) (.namedData nominal) (.var 0)) = none := by
  refine ⟨?_,rfl⟩
  simp only [identity]
  rw [builds (.closure .nil (.var rfl))]; rfl

theorem unselected_sum_types_are_not_extra_well_formedness_checks (unused : Core.Ty) :
    (buildRuntimeArgument? (.inLeft unused .unit)).isSome = true ∧
    (buildRuntimeArgument? (.inRight unused .unit)).isSome = true ∧
    (∀ nominal : Core.DataTypeId, Core.infer? [] (.inLeft (.namedData nominal) .unit) = none ∧
      Core.infer? [] (.inRight (.namedData nominal) .unit) = none) := by
  refine ⟨?_,?_,fun _ => ⟨rfl,rfl⟩⟩
  · rw [builds (.inLeft .unit)]; rfl
  · rw [builds (.inRight .unit)]; rfl

theorem structural_cell_construction_does_not_assert_any_allocation
    (element : Core.Ty) (location : Nat) (world : Core.StoreTyping) (store : Core.Store)
    (missing : world[location]? ≠ some element) :
    buildRuntimeArgument? (.cellRef element location) = some ⟨.cell element,.cellRef element location,.cellRef⟩ ∧
    validateRuntimeInputs world [⟨.cell element,.cellRef element location,.cellRef⟩] store = false := by
  refine ⟨builds .cellRef,?_⟩
  cases checked : validateRuntimeInputs world [⟨.cell element,.cellRef element location,.cellRef⟩] store with
  | false => rfl
  | true =>
      have typed := (validateRuntimeInputs_iff.mp checked).1 _ (List.mem_singleton_self _)
      cases typed with | cellRef found => exact False.elim (missing found)

theorem hosts_and_empty_definition_constructors_are_rejected_with_actual_payloads
    (host : Core.HostFunction) (constructor : Core.ConstructorId) (payload : Core.Value) :
    buildRuntimeArgument? (.hostFunction host) = none ∧ buildRuntimeArgument? (.constructed constructor payload) = none := by
  constructor
  · apply rejects; intro type typed; cases typed
  · apply rejects; intro type typed; cases typed with | constructed found _ => cases found

theorem actual_captured_order_not_only_capture_tags_controls_body_typing (word : Core.Word) (b : Bool) :
    (buildRuntimeArgument? (.closure .unit .word (.var 2) [.bool b,.word word])).isSome = true ∧
    buildRuntimeArgument? (.closure .unit .word (.var 2) [.word word,.bool b]) = none ∧
    Core.runStateful 6 (.initial (.apply (.var 0) .unit) [.closure .unit .word (.var 2) [.bool b,.word word]] []) = .done (.word word) [] ∧
    Core.runStateful 6 (.initial (.apply (.var 0) .unit) [.closure .unit .word (.var 2) [.word word,.bool b]] []) = .done (.bool b) [] := by
  refine ⟨?_,rejects ?_,rfl,rfl⟩
  · rw [builds (.closure (.cons .bool (.cons .word .nil)) (.var rfl))]; rfl
  · intro type typed
    cases typed with | closure captured body => cases captured with | cons first tail => cases first with | word =>
      cases tail with | cons second rest => cases second with | bool => cases rest with | nil =>
        cases body with | var found => cases found

private def projected (value : Core.Value) : Option (Core.Value × Core.Ty) :=
  (buildRuntimeArgument? value).map (fun argument => (argument.value,argument.type))
theorem literal_boundary_computations_use_only_the_public_builder :
    projected (nested (.namedData ⟨77⟩) (.namedData ⟨88⟩) [.cellRef .word 700] 2 (.word Core.Word.zero)) =
      some (nested (.namedData ⟨77⟩) (.namedData ⟨88⟩) [.cellRef .word 700] 2 (.word Core.Word.zero),
        (nested (.namedData ⟨77⟩) (.namedData ⟨88⟩) [.cellRef .word 700] 2 (.word Core.Word.zero)).type) ∧
    projected forged = none ∧ projected unbound = none ∧
    projected (identity .unit [.bool true,forged,.unit]) = none ∧
    projected (.hostFunction .storageRead) = none ∧
    projected (identity .unit [.word Core.Word.zero,.hostFunction .storageRead,.bool false]) = none ∧
    projected (.constructed ⟨⟨3⟩,7⟩ .unit) = none ∧
    projected (.cellRef .word 700) = some (.cellRef .word 700,.cell .word) := by
  decide +kernel

end Tests.FrontendRuntimeArgumentConstructionBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeArgumentConstructionProperties
/-! Public construction preserves original records, list order and all existing
entry results. Structural acceptance alone never supplies an allocated world. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeArgumentConstruction
open Solcore Solcore.Frontend

theorem every_existing_record_is_reconstructed (argument : TypedRuntimeArgument) :
    buildRuntimeArgument? argument.value = some argument :=
  buildRuntimeArgument?_iff.mpr rfl

theorem successful_construction_retains_the_literal_value_and_tag
    {value : Core.Value} {argument : TypedRuntimeArgument}
    (built : buildRuntimeArgument? value = some argument) :
    argument.value = value ∧ argument.type = value.type := by
  have same := buildRuntimeArgument?_iff.mp built
  exact ⟨same,by rw [← same]; exact argument.valueTyped.type_eq.symm⟩

theorem every_structurally_typed_original_value_has_its_exact_record
    {value : Core.Value} {type : Core.Ty} (typed : Core.ValueHasType value type) :
    ∃ argument, buildRuntimeArgument? value = some argument ∧
      argument.value = value ∧ argument.type = type :=
  ⟨⟨type,value,typed⟩,buildRuntimeArgument?_iff.mpr rfl,rfl,rfl⟩

theorem absence_is_exactly_the_lack_of_structural_evidence (value : Core.Value) :
    buildRuntimeArgument? value = none ↔ ¬ ∃ type, Core.ValueHasType value type := by
  constructor
  · intro absent ⟨type,typed⟩
    have built := (buildRuntimeArgument?_iff (argument := ⟨type,value,typed⟩)).mpr rfl
    rw [absent] at built
    cases built
  · intro untyped
    cases built : buildRuntimeArgument? value with
    | none => rfl
    | some argument =>
        have same := buildRuntimeArgument?_iff.mp built
        exact False.elim (untyped ⟨argument.type,same ▸ argument.valueTyped⟩)

theorem ordered_list_construction_preserves_every_exact_record
    (values : List Core.Value) (arguments : List TypedRuntimeArgument) :
    values.mapM buildRuntimeArgument? = some arguments ↔
      arguments.map (·.value) = values := by
  induction values generalizing arguments with
  | nil => cases arguments <;> simp
  | cons value rest ih =>
      cases arguments with
      | nil =>
          rw [List.mapM_cons]
          change ((buildRuntimeArgument? value).bind fun head =>
            (rest.mapM buildRuntimeArgument?).bind fun others => some (head :: others)) = some [] ↔ _
          simp only [Option.bind_eq_some_iff,Option.some.injEq,List.cons_ne_nil,
            and_false,exists_false,List.map_nil]
          simp
      | cons argument tail =>
          rw [List.mapM_cons]
          change ((buildRuntimeArgument? value).bind fun head =>
            (rest.mapM buildRuntimeArgument?).bind fun others => some (head :: others)) = some (argument :: tail) ↔ _
          simp only [Option.bind_eq_some_iff,Option.some.injEq,List.map_cons,List.cons.injEq]
          constructor
          · rintro ⟨head,built,found⟩
            rcases found with ⟨others,builtRest,same⟩
            rcases same with ⟨rfl,rfl⟩
            exact ⟨buildRuntimeArgument?_iff.mp built,ih _ |>.mp builtRest⟩
          · rintro ⟨sameHead,sameTail⟩
            exact ⟨argument,buildRuntimeArgument?_iff.mpr sameHead,tail,(ih _).mpr sameTail,rfl,rfl⟩

theorem identical_original_lists_reconstruct_once_without_reordering
    (arguments : List TypedRuntimeArgument) :
    (arguments.map (·.value)).mapM buildRuntimeArgument? = some arguments :=
  (ordered_list_construction_preserves_every_exact_record _ _).mpr rfl

theorem a_list_is_rejected_exactly_when_one_original_value_has_no_structural_type
    (values : List Core.Value) :
    values.mapM buildRuntimeArgument? = none ↔
      ∃ value ∈ values, ¬ ∃ type, Core.ValueHasType value type := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      cases built : buildRuntimeArgument? value with
      | none =>
          simp only [List.mapM_cons,built,bind,Option.bind_none,true_iff]
          exact ⟨value,by simp,(absence_is_exactly_the_lack_of_structural_evidence value).mp built⟩
      | some argument =>
          have same := buildRuntimeArgument?_iff.mp built
          have typed : ∃ type, Core.ValueHasType value type :=
            ⟨argument.type,same ▸ argument.valueTyped⟩
          cases restBuilt : rest.mapM buildRuntimeArgument? with
          | none =>
              simp only [List.mapM_cons,built,restBuilt,bind,Option.bind_some,Option.bind_none,true_iff]
              obtain ⟨item,member,bad⟩ := ih.mp restBuilt
              exact ⟨item,by simp [member],bad⟩
          | some tail =>
              simp only [List.mapM_cons,built,restBuilt,bind,Option.bind_some,pure,reduceCtorEq,false_iff]
              rintro ⟨item,member,bad⟩
              rcases List.mem_cons.mp member with rfl | member
              · exact bad typed
              · have impossible := ih.mpr ⟨item,member,bad⟩
                rw [restBuilt] at impossible
                cases impossible

theorem reconstructed_arguments_leave_existing_preparation_and_full_runner_unchanged
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (source : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    ((arguments.map (·.value)).mapM buildRuntimeArgument?).bind
        (prepareRecursiveComputationFunction? types owner source) =
      prepareRecursiveComputationFunction? types owner source arguments ∧
    ((arguments.map (·.value)).mapM buildRuntimeArgument?).bind
        (fun actual => runRecursiveComputationFunction? types owner source actual fuel store) =
      runRecursiveComputationFunction? types owner source arguments fuel store := by
  rw [identical_original_lists_reconstruct_once_without_reordering]
  exact ⟨rfl,rfl⟩

theorem construction_and_same_world_validation_have_separate_exact_conditions
    (values : List Core.Value) (arguments : List TypedRuntimeArgument)
    (world : Core.StoreTyping) (store : Core.Store) :
    (values.mapM buildRuntimeArgument? = some arguments ∧
      validateRuntimeInputs world arguments store = true) ↔
    arguments.map (·.value) = values ∧
      (∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type) ∧
      Core.StoreHasTypes world store := by
  rw [ordered_list_construction_preserves_every_exact_record,validateRuntimeInputs_iff]

theorem distinct_actual_values_never_collapse_to_the_same_constructed_record
    (first second : TypedRuntimeArgument) (different : first.value ≠ second.value) :
    buildRuntimeArgument? first.value ≠ buildRuntimeArgument? second.value := by
  rw [every_existing_record_is_reconstructed,every_existing_record_is_reconstructed]
  intro equal
  exact different (congrArg TypedRuntimeArgument.value (Option.some.inj equal))

end Tests.FrontendRuntimeArgumentConstruction
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeArgumentStaticProperties
/-! Equal ordered structural types preserve static preparation, not runtime
observations. Independent preparation transport is used before source cost
rules distinguish the selected paths. No cell allocation or call is performed. -/

set_option autoImplicit false

namespace Tests.FrontendRuntimeArgumentStatic

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "argument-static.sol"⟩, 17, 2⟩
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ArgumentStatic", by decide⟩], by decide⟩⟩, 2⟩
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def table (type : Core.Ty) : TypeNameTable :=
  [(["Input"], type), (["Output"], type), (["Word"], .word)]
private def parameter : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, "c"⟩ (annotation "Input")⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def declaration (source : Syntax.Expr) (result : String := "Output") : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "entry"⟩, none, ⟨span, [parameter]⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation result]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some source)⟩]⟩⟩⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def inputs (argument : TypedRuntimeArgument) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "c" argument.type argument.value argument.valueTyped
private def prepared (core : Core.Expr) (argument : TypedRuntimeArgument) : PreparedRuntimeFunction :=
  ⟨inputs argument, core, argument.type⟩
private def static (entry : PreparedRuntimeFunction) :=
  (entry.inputs.ids, entry.inputs.names, entry.inputs.context, entry.core, entry.returnType)
private theorem binding (argument : TypedRuntimeArgument) :
    RuntimeParametersBind (table argument.type) owner [parameter] [argument] (inputs argument) :=
  .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil
private theorem header (type : Core.Ty) (source : Syntax.Expr) :
    RuntimeFunctionHeader (table type) (declaration source).value.signature type :=
  ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩

private theorem transportConcrete {types : TypeNameTable} {decl : Syntax.FunctionDecl} {core : Core.Expr}
    {first second : TypedRuntimeArgument}
    (original : RuntimeFunctionPrepares types owner decl [first] (prepared core first))
    (sameType : first.type = second.type)
    (newBinding : RuntimeParametersBind types owner decl.value.signature.parameters.elements
      [second] (inputs second)) :
    RuntimeFunctionPrepares types owner decl [second] (prepared core second) := by
  obtain ⟨target, transported, _, _, _, coreEq, typeEq⟩ :=
    original.transport_argument_types (rightArguments := [second]) (by simp only [List.map_cons, List.map_nil, sameType])
  have inputsEq := transported.parameters.result_unique newBinding
  rcases target with ⟨targetInputs, targetCore, targetType⟩
  change targetInputs = inputs second at inputsEq
  change targetCore = core at coreEq
  have targetTypeEq : targetType = second.type := typeEq.trans sameType
  cases inputsEq
  cases coreEq
  cases targetTypeEq
  exact transported

private def andNot : Syntax.Expr :=
  ⟨span, .binary (ref "c") ⟨span, .logicalAnd⟩ ⟨span, .unary ⟨span, .logicalNot⟩ (ref "c")⟩⟩
private def andCore : Core.Expr := .ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false)
private theorem falsePrepares : RuntimeFunctionPrepares (table .bool) owner (declaration andNot)
    [boolArg false] (prepared andCore (boolArg false)) :=
  ⟨header .bool andNot, binding (boolArg false),
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.logicalAnd (.identifier .head) (.logicalNot (.identifier .head)))
      (.ifE (.var .head) (.unary (.var .head)) .bool)
      (.ifE (.var .head) (.unary (.var .head)) .bool)⟩
private theorem truePrepares : RuntimeFunctionPrepares (table .bool) owner (declaration andNot)
    [boolArg true] (prepared andCore (boolArg true)) :=
  transportConcrete falsePrepares rfl (binding (boolArg true))
private theorem falseCost (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table .bool) owner (declaration andNot)
      [boolArg false] store .bool (.bool false) store 4 :=
  .intro falsePrepares (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.andFalse (.identifier .head .head)))
private theorem trueCost (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table .bool) owner (declaration andNot)
      [boolArg true] store .bool (.bool false) store 6 := by
  have leaf : LocalExpressionEvaluatesWithCost (inputs (boolArg true)).names
      (inputs (boolArg true)).environment store (ref "c") (.bool true) store 1 :=
    .identifier .head .head
  exact .intro truePrepares (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.andTrue leaf (.logicalNot leaf)))

theorem transported_preparation_preserves_static_but_changes_environment :
    RuntimeFunctionPrepares (table .bool) owner (declaration andNot)
      [boolArg true] (prepared andCore (boolArg true)) ∧
    (prepareRuntimeFunction? (table .bool) owner (declaration andNot) [boolArg false]).map static =
      (prepareRuntimeFunction? (table .bool) owner (declaration andNot) [boolArg true]).map static ∧
    static (prepared andCore (boolArg false)) = static (prepared andCore (boolArg true)) ∧
    (prepared andCore (boolArg false)).inputs.environment ≠ (prepared andCore (boolArg true)).inputs.environment := by
  refine ⟨truePrepares, prepareRuntimeFunction?_static_projection_eq rfl, rfl, ?_⟩
  intro same
  have values := congrArg (List.map Prod.snd) same
  change [Core.Value.bool false] = [.bool true] at values
  cases values

theorem equal_boolean_results_have_different_independent_costs (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table .bool) owner (declaration andNot)
      [boolArg false] store .bool (.bool false) store 4 ∧
    RuntimeFunctionEvaluatesWithCost (table .bool) owner (declaration andNot)
      [boolArg true] store .bool (.bool false) store 6 :=
  ⟨falseCost store, trueCost store⟩

theorem same_fuel_distinguishes_equal_static_boolean_entries (store : Core.Store) :
    runRuntimeFunction? (table .bool) owner (declaration andNot) [boolArg false] 5 store =
      some (.bool, .done (.bool false) store) ∧
    (∃ suspended, runRuntimeFunction? (table .bool) owner (declaration andNot) [boolArg true] 5 store =
      some (.bool, .outOfFuel suspended)) ∧
    runRuntimeFunction? (table .bool) owner (declaration andNot) [boolArg true] 6 store =
      some (.bool, .done (.bool false) store) :=
  ⟨(falseCost store).run_done_iff.mpr (by decide), (trueCost store).run_outOfFuel_iff.mpr (by decide),
    (trueCost store).run_done_iff.mpr (by decide)⟩

private theorem rejectTrue {decl : Syntax.FunctionDecl}
    (rejected : prepareRuntimeFunction? (table .bool) owner decl [boolArg false] = none) :
    prepareRuntimeFunction? (table .bool) owner decl [boolArg true] = none := by
  have same := prepareRuntimeFunction?_static_projection_eq
    (types := table .bool) (owner := owner) (declaration := decl)
    (leftArguments := [boolArg false]) (rightArguments := [boolArg true]) rfl
  rw [rejected] at same
  cases result : prepareRuntimeFunction? (table .bool) owner decl [boolArg true] with
  | none => rfl
  | some target => simp only [result, Option.map_none, Option.map_some, reduceCtorEq] at same

private def missing : Syntax.Expr := ⟨span, .binary (ref "c") ⟨span, .logicalAnd⟩ (ref "missing")⟩
private theorem missingRejected : prepareRuntimeFunction? (table .bool) owner (declaration missing)
    [boolArg false] = none := by
  apply prepareRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨target, preparation⟩
  have sameInputs := preparation.parameters.result_unique (binding (boolArg false))
  have body := preparation.body
  rw [sameInputs] at body
  cases body with
  | single body =>
      cases body with
      | expression resolution _ _ =>
          cases resolution with
          | logicalAnd _ right =>
              cases right with
              | identifier found =>
                  have accepted := LocalNameTable.lookup?_iff.mpr found
                  change none = some _ at accepted
                  cases accepted

theorem skipped_missing_branch_rejects_for_both_argument_values (fuel : Nat) (store : Core.Store) :
    ReturnBodyEvaluatesWithCost (inputs (boolArg false)).names (inputs (boolArg false)).environment
      store (declaration missing).value.body (.bool false) store 4 ∧
    prepareRuntimeFunction? (table .bool) owner (declaration missing) [boolArg false] = none ∧
    prepareRuntimeFunction? (table .bool) owner (declaration missing) [boolArg true] = none ∧
    runRuntimeFunction? (table .bool) owner (declaration missing) [boolArg false] fuel store = none ∧
    runRuntimeFunction? (table .bool) owner (declaration missing) [boolArg true] fuel store = none := by
  have rightRejected := rejectTrue missingRejected
  exact ⟨.expression (.andFalse (.identifier .head .head)), missingRejected, rightRejected,
    by simp only [runRuntimeFunction?, missingRejected, bind, Option.bind_none],
    by simp only [runRuntimeFunction?, rightRejected, bind, Option.bind_none]⟩

private theorem mismatchRejected : prepareRuntimeFunction? (table .bool) owner (declaration (ref "c") "Word")
    [boolArg false] = none := by
  apply prepareRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨target, preparation⟩
  have sameInputs := preparation.parameters.result_unique (binding (boolArg false))
  have body := preparation.body
  rw [sameInputs] at body
  have expectedBody : ReturnBodyElaborates (inputs (boolArg false)).names (inputs (boolArg false)).context
      (declaration (ref "c") "Word").value.body (.var 0) .bool :=
    .expression (.identifier .head) (.var .head) (.var .head)
  have declared : RuntimeFunctionHeader (table .bool) (declaration (ref "c") "Word").value.signature .word :=
    ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) (.tail (by decide) .head)))⟩
  have impossible := ((TypedLetReturnBodyElaborates.returnTree <| .terminal
    (inputs := (inputs (boolArg false)).toTypeInputs) (.single expectedBody)).result_unique body).2.trans
    (declared.type_unique preparation.header).symm
  cases impossible

theorem return_contract_mismatch_rejects_for_both_argument_values (fuel : Nat) (store : Core.Store) :
    (inputs (boolArg false)).checkReturnBody? (declaration (ref "c") "Word").value.body = some (.var 0, .bool) ∧
    prepareRuntimeFunction? (table .bool) owner (declaration (ref "c") "Word") [boolArg false] = none ∧
    prepareRuntimeFunction? (table .bool) owner (declaration (ref "c") "Word") [boolArg true] = none ∧
    runRuntimeFunction? (table .bool) owner (declaration (ref "c") "Word") [boolArg false] fuel store = none ∧
    runRuntimeFunction? (table .bool) owner (declaration (ref "c") "Word") [boolArg true] fuel store = none := by
  have rightRejected := rejectTrue mismatchRejected
  have body : ReturnBodyElaborates (inputs (boolArg false)).names (inputs (boolArg false)).context
      (declaration (ref "c") "Word").value.body (.var 0) .bool :=
    .expression (.identifier .head) (.var .head) (.var .head)
  exact ⟨body.complete,
    mismatchRejected, rightRejected,
    by simp only [runRuntimeFunction?, mismatchRejected, bind, Option.bind_none],
    by simp only [runRuntimeFunction?, rightRejected, bind, Option.bind_none]⟩

private def cellArg (location : Core.Location) : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word location, .cellRef⟩
private theorem cellPrepares (location : Core.Location) : RuntimeFunctionPrepares (table (.cell .word)) owner
    (declaration (ref "c")) [cellArg location] (prepared (.var 0) (cellArg location)) :=
  ⟨header (.cell .word) (ref "c"), binding (cellArg location),
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩

theorem typed_cell_replacement_changes_runtime_value_not_static_output
    (left right : Core.Location) (different : left ≠ right) (store : Core.Store) :
    (prepareRuntimeFunction? (table (.cell .word)) owner (declaration (ref "c")) [cellArg left]).map static =
      (prepareRuntimeFunction? (table (.cell .word)) owner (declaration (ref "c")) [cellArg right]).map static ∧
    runRuntimeFunction? (table (.cell .word)) owner (declaration (ref "c")) [cellArg left] 1 store =
      some (.cell .word, .done (.cellRef .word left) store) ∧
    runRuntimeFunction? (table (.cell .word)) owner (declaration (ref "c")) [cellArg right] 1 store =
      some (.cell .word, .done (.cellRef .word right) store) ∧
    (Core.Value.cellRef .word left) ≠ .cellRef .word right := by
  have transported := transportConcrete (second := cellArg right)
    (cellPrepares left) rfl (binding (cellArg right))
  have leftCost : RuntimeFunctionEvaluatesWithCost (table (.cell .word)) owner (declaration (ref "c"))
      [cellArg left] store (.cell .word) (.cellRef .word left) store 1 :=
    .intro (cellPrepares left) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.identifier .head .head))
  have rightCost : RuntimeFunctionEvaluatesWithCost (table (.cell .word)) owner (declaration (ref "c"))
      [cellArg right] store (.cell .word) (.cellRef .word right) store 1 :=
    .intro transported (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.identifier .head .head))
  exact ⟨prepareRuntimeFunction?_static_projection_eq rfl, leftCost.run_done_iff.mpr (by decide),
    rightCost.run_done_iff.mpr (by decide), by intro same; exact different (Core.Value.cellRef.inj same).2⟩

end Tests.FrontendRuntimeArgumentStatic
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeInputReferenceValidationProperties
/-! The combined public validator consumes existing structural evidence. Actual
nested values and even unused captures matter; unselected tags do not allocate. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeInputReferenceValidation
open Solcore Solcore.Frontend

private def reference (type : Core.Ty) (location : Nat) : TypedRuntimeArgument :=
  ⟨.cell type,.cellRef type location,.cellRef⟩
private theorem structuralEnvironment (args : List TypedRuntimeArgument) :
    Core.EnvironmentHasTypes (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons arg rest ih => exact .cons arg.valueTyped ih
private theorem runtimeEnvironment {world : Core.StoreTyping} {args : List TypedRuntimeArgument}
    (typed : ∀ a ∈ args, Core.RuntimeValueHasType world a.value a.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons arg rest ih => exact .cons (typed arg (by simp)) (ih (fun a member => typed a (by simp [member])))
private def identity (signature : Core.Ty) (captured : List TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.function signature signature,.closure signature signature (.var 0) (captured.map (·.value)),
    .closure (structuralEnvironment captured) (.var rfl)⟩
private def nested (unused signature : Core.Ty) (suffix : List TypedRuntimeArgument) : Nat → TypedRuntimeArgument → TypedRuntimeArgument
  | 0, arg => arg
  | n+1, arg =>
      let inner := nested unused signature suffix n arg
      ⟨.product (.sum inner.type unused) (.function signature signature),
        .pair (.inLeft unused inner.value) (identity signature (inner::suffix)).value,
        .pair (.inLeft inner.valueTyped) (identity signature (inner::suffix)).valueTyped⟩
private theorem identityTyped {world : Core.StoreTyping} {signature : Core.Ty} {captured : List TypedRuntimeArgument}
    (typed : ∀ a ∈ captured, Core.RuntimeValueHasType world a.value a.type) :
    Core.RuntimeValueHasType world (identity signature captured).value (identity signature captured).type :=
  .closure (runtimeEnvironment typed) (.var rfl)
private theorem nestedTyped {world : Core.StoreTyping} {unused signature : Core.Ty} {suffix : List TypedRuntimeArgument}
    {arg : TypedRuntimeArgument} (typed : Core.RuntimeValueHasType world arg.value arg.type)
    (captured : ∀ a ∈ suffix, Core.RuntimeValueHasType world a.value a.type) (depth : Nat) :
    Core.RuntimeValueHasType world (nested unused signature suffix depth arg).value (nested unused signature suffix depth arg).type := by
  induction depth with
  | zero => exact typed
  | succ depth ih =>
      exact .pair (.inLeft ih) (identityTyped (by
        intro a member
        rcases List.mem_cons.mp member with rfl | member
        · exact ih
        · exact captured a member))
private theorem nestedPayload {world : Core.StoreTyping} {unused signature : Core.Ty} {suffix : List TypedRuntimeArgument}
    {arg : TypedRuntimeArgument} (depth : Nat)
    (typed : Core.RuntimeValueHasType world (nested unused signature suffix depth arg).value (nested unused signature suffix depth arg).type) :
    Core.RuntimeValueHasType world arg.value arg.type := by
  induction depth with
  | zero => exact typed
  | succ depth ih => cases typed with | pair selected _ => cases selected with | inLeft inner => exact ih inner
private theorem acceptsSingle {world : Core.StoreTyping} {store : Core.Store} {arg : TypedRuntimeArgument}
    (typed : Core.RuntimeValueHasType world arg.value arg.type) (stored : Core.StoreHasTypes world store) :
    validateRuntimeInputs world [arg] store = true :=
  validateRuntimeInputs_iff.mpr ⟨by simpa using typed,stored⟩
private theorem rejectsSingle {world : Core.StoreTyping} {store : Core.Store} {arg : TypedRuntimeArgument}
    (untyped : ¬ Core.RuntimeValueHasType world arg.value arg.type) :
    validateRuntimeInputs world [arg] store = false := by
  cases checked : validateRuntimeInputs world [arg] store with
  | false => rfl
  | true => exact False.elim (untyped ((validateRuntimeInputs_iff.mp checked).1 arg (by simp)))
private theorem capturedLookup {definitions : Core.DataEnvironment} {world : Core.StoreTyping} {environment : Core.Environment} {context : Core.Context}
    (typed : Core.RuntimeEnvironmentHasTypes world environment context definitions)
    {index : Nat} {value : Core.Value} (found : environment[index]? = some value) :
    ∃ type, Core.RuntimeValueHasType world value type definitions := by
  induction typed using Core.RuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) generalizing index with
  | unit | bool | word | integer | pair | inLeft | inRight | closure | cellRef | constructed => trivial
  | nil => simp at found
  | cons head _ _ ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at found; subst value; exact ⟨_,head⟩
      | succ index => exact ih (by simpa using found)

theorem arbitrary_nested_pairs_sums_and_actual_captured_suffix_validate
    {world : Core.StoreTyping} {store : Core.Store} (unused signature : Core.Ty)
    (arg : TypedRuntimeArgument) (suffix : List TypedRuntimeArgument) (depth : Nat)
    (typed : Core.RuntimeValueHasType world arg.value arg.type)
    (captured : ∀ a ∈ suffix, Core.RuntimeValueHasType world a.value a.type)
    (stored : Core.StoreHasTypes world store) :
    validateRuntimeInputs world [nested unused signature suffix depth arg] store = true ∧
    Core.RuntimeValueHasType world (nested unused signature suffix depth arg).value (nested unused signature suffix depth arg).type ∧
    Core.StoreHasTypes world store := by
  have checked : validateRuntimeInputs world [nested unused signature suffix depth arg] store = true :=
    acceptsSingle (nestedTyped typed captured depth) stored
  exact ⟨checked,(validateRuntimeInputs_iff.mp checked).1 _ (by simp),(validateRuntimeInputs_iff.mp checked).2⟩

theorem all_nested_levels_preserve_an_unallocated_700_rejection
    (world : Core.StoreTyping) (store : Core.Store) (unused signature : Core.Ty)
    (suffix : List TypedRuntimeArgument) (depth : Nat) (short : world.length ≤ 700) :
    Core.ValueHasType (nested unused signature suffix depth (reference .word 700)).value
      (nested unused signature suffix depth (reference .word 700)).type ∧
    validateRuntimeInputs world [nested unused signature suffix depth (reference .word 700)] store = false := by
  refine ⟨(nested unused signature suffix depth (reference .word 700)).valueTyped,rejectsSingle ?_⟩
  intro typed
  have missing := nestedPayload depth typed
  cases missing with
  | cellRef found => have bound := (List.getElem?_eq_some_iff.mp found).1; omega

theorem an_unused_capture_is_checked_before_any_body_execution
    (world : Core.StoreTyping) (store : Core.Store) (signature type : Core.Ty)
    (leading suffix : List TypedRuntimeArgument) (location : Nat) (missing : world[location]? ≠ some type) :
    Core.ValueHasType (identity signature (leading ++ reference type location::suffix)).value (.function signature signature) ∧
    validateRuntimeInputs world [identity signature (leading ++ reference type location::suffix)] store = false := by
  refine ⟨(identity signature (leading ++ reference type location::suffix)).valueTyped,rejectsSingle ?_⟩
  intro typed
  cases typed with
  | closure environment _ =>
      have found : ((leading ++ reference type location::suffix).map (·.value))[leading.length]? = some (.cellRef type location) := by
        simp [reference]
      obtain ⟨_,referenceTyped⟩ := capturedLookup environment found
      cases referenceTyped with | cellRef found => exact missing found

theorem a_nested_unused_closure_capture_is_not_just_an_outer_tag
    (world : Core.StoreTyping) (store : Core.Store) (outer inner type : Core.Ty)
    (suffix : List TypedRuntimeArgument) (location : Nat) (missing : world[location]? ≠ some type) :
    validateRuntimeInputs world
      [identity outer [identity inner (reference type location::suffix)]] store = false := by
  apply rejectsSingle
  intro typed
  cases typed with
  | closure environment _ => cases environment with
    | cons innerTyped _ => cases innerTyped with
      | closure captured _ => cases captured with
        | cons head _ => cases head with | cellRef found => exact missing found

theorem separately_accepted_references_cannot_use_incompatible_actual_worlds (word : Core.Word) (b : Bool) :
    validateRuntimeInputs [.word] [reference .word 0] [.word word] = true ∧
    validateRuntimeInputs [.bool] [reference .bool 0] [.bool b] = true ∧
    ∀ world store, validateRuntimeInputs world [reference .word 0,reference .bool 0] store = false := by
  refine ⟨acceptsSingle (.cellRef rfl) (Core.StoreHasTypes.nil.allocate .word .word),
    acceptsSingle (.cellRef rfl) (Core.StoreHasTypes.nil.allocate .bool .bool),?_⟩
  intro world store
  cases checked : validateRuntimeInputs world [reference .word 0,reference .bool 0] store with
  | false => rfl
  | true =>
      have typed := (validateRuntimeInputs_iff.mp checked).1
      have left := typed (reference .word 0) (by simp)
      have right := typed (reference .bool 0) (by simp)
      cases left with
      | cellRef first => cases right with | cellRef second => rw [first] at second; cases second

private def selected (unused : Core.Ty) : TypedRuntimeArgument := ⟨.sum .unit unused,.inLeft unused .unit,.inLeft .unit⟩
private def selectedRight (unused : Core.Ty) (arg : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.sum unused arg.type,.inRight unused arg.value,.inRight arg.valueTyped⟩
theorem right_selected_sum_preserves_exact_actual_argument_and_store_validation
    (world : Core.StoreTyping) (store : Core.Store) (unused : Core.Ty) (arg : TypedRuntimeArgument) :
    validateRuntimeInputs world [selectedRight unused arg] store = true ↔
      validateRuntimeInputs world [arg] store = true := by
  rw [validateRuntimeInputs_iff,validateRuntimeInputs_iff]
  simp only [List.mem_singleton,forall_eq]
  constructor
  · rintro ⟨typed,stored⟩
    cases typed with | inRight payload => exact ⟨payload,stored⟩
  · rintro ⟨typed,stored⟩
    exact ⟨.inRight typed,stored⟩

theorem nominal_and_function_tags_in_unused_positions_do_not_reject_arguments
    (nominal : Core.DataTypeId) (signature : Core.Ty) :
    validateRuntimeInputs [] [selected (.namedData nominal),selected (.function signature (.namedData nominal)),
      identity (.namedData nominal) [],identity (.function signature (.namedData nominal)) []] [] = true := by
  apply validateRuntimeInputs_iff.mpr
  refine ⟨?_,.nil⟩
  intro arg member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · exact .inLeft .unit
  · exact .inLeft .unit
  · exact .closure .nil (.var rfl)
  · exact .closure .nil (.var rfl)

theorem unselected_nominal_is_an_argument_but_not_a_cell_payload (nominal : Core.DataTypeId) :
    validateRuntimeInputs [] [selected (.namedData nominal)] [] = true ∧
    validateRuntimeInputs [.sum .unit (.namedData nominal)] [] [.inLeft (.namedData nominal) .unit] = false := by
  refine ⟨acceptsSingle (.inLeft .unit) .nil,?_⟩
  cases checked : validateRuntimeInputs [.sum .unit (.namedData nominal)] [] [.inLeft (.namedData nominal) .unit] with
  | false => rfl
  | true =>
      obtain ⟨_,_,payload,_⟩ := (validateRuntimeInputs_iff.mp checked).2.lookup (location := 0) rfl
      cases payload with | sum _ right => cases right

private def forged : Core.Value := .closure .word .word (.bool false) []
theorem a_correct_raw_tag_and_empty_captures_do_not_make_a_typed_argument :
    forged.type = .function .word .word ∧
    (¬ Core.ValueHasType forged (.function .word .word)) ∧
    (¬ ∃ argument : TypedRuntimeArgument, argument.value = forged) ∧
    Core.runStateful 6 (.initial (.apply (.var 0) (.word Core.Word.zero)) [forged] []) = .done (.bool false) [] := by
  have untyped : ¬ Core.ValueHasType forged (.function .word .word) := by
    intro typed
    cases typed with | closure _ body => cases body
  refine ⟨rfl,untyped,?_,rfl⟩
  rintro ⟨argument,same⟩
  have tag := argument.valueTyped.type_eq
  rw [same] at tag
  have typed := argument.valueTyped
  rw [same,← tag] at typed
  exact untyped typed

theorem host_tags_and_unused_host_captures_cannot_bypass_structural_evidence (host : Core.HostFunction) :
    (Core.Value.hostFunction host).type = host.functionType ∧
    (¬ ∃ argument : TypedRuntimeArgument, argument.value = .hostFunction host) ∧
    ¬ ∃ argument : TypedRuntimeArgument,
      argument.value = .closure .unit .unit (.var 0) [.hostFunction host] := by
  refine ⟨rfl,?_,?_⟩
  · rintro ⟨argument,same⟩
    have typed := argument.valueTyped
    rw [same] at typed
    cases typed
  · rintro ⟨argument,same⟩
    have typed := argument.valueTyped
    rw [same] at typed
    have tag := typed.type_eq
    change .function .unit .unit = argument.type at tag
    rw [← tag] at typed
    cases typed with | closure captured _ => cases captured with | cons head _ => cases head

end Tests.FrontendRuntimeInputReferenceValidation
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeInputStoreValidationProperties
/-! Whole-store validation checks every supplied row, independently of which
cells the arguments reference. Arguments and cell payloads have different limits. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeInputStoreValidation
open Solcore Solcore.Frontend

private theorem rejected {world : Core.StoreTyping} {store : Core.Store}
    (arguments : List TypedRuntimeArgument) (invalid : ¬ Core.StoreHasTypes world store) :
    validateRuntimeInputs world arguments store = false := by
  cases checked : validateRuntimeInputs world arguments store with
  | false => rfl
  | true => exact False.elim (invalid (validateRuntimeInputs_iff.mp checked).2)

theorem empty_arguments_still_validate_exactly_the_whole_store
    (world : Core.StoreTyping) (store : Core.Store) :
    validateRuntimeInputs world [] store = true ↔ Core.StoreHasTypes world store := by
  constructor
  · exact fun checked => (validateRuntimeInputs_iff.mp checked).2
  · intro stored; exact validateRuntimeInputs_iff.mpr ⟨by simp, stored⟩

theorem acceptance_checks_every_cell_even_when_unreferenced
    {world : Core.StoreTyping} {arguments : List TypedRuntimeArgument} {store : Core.Store}
    (accepted : validateRuntimeInputs world arguments store = true) :
    world.length = store.length ∧
    ∀ {location type}, world[location]? = some type →
      ∃ value, store.read? location = some value ∧ Core.CellPayload type ∧ Core.ValueHasType value type := by
  have stored := (validateRuntimeInputs_iff.mp accepted).2
  exact ⟨stored.length_eq, stored.lookup⟩

theorem all_original_arguments_survive_an_allowed_extra_cell
    {world : Core.StoreTyping} {arguments : List TypedRuntimeArgument} {store : Core.Store}
    (accepted : validateRuntimeInputs world arguments store = true)
    {type : Core.Ty} {value : Core.Value} (payload : Core.CellPayload type)
    (typed : Core.ValueHasType value type) :
    validateRuntimeInputs (world ++ [type]) arguments (store ++ [value]) = true := by
  obtain ⟨args, stored⟩ := validateRuntimeInputs_iff.mp accepted
  exact validateRuntimeInputs_iff.mpr ⟨fun argument member =>
    (args argument member).weaken ⟨[type], rfl⟩, stored.allocate payload typed⟩

theorem an_unused_wrong_last_cell_rejects_arbitrary_original_arguments
    {world : Core.StoreTyping} {store : Core.Store} (stored : Core.StoreHasTypes world store)
    (arguments : List TypedRuntimeArgument) (b : Bool) :
    validateRuntimeInputs (world ++ [.word]) arguments (store ++ [.bool b]) = false := by
  apply rejected arguments
  intro allCells
  obtain ⟨value, found, _, typed⟩ := allCells.lookup (location := world.length) (elementType := .word) (by simp)
  have same : value = .bool b := by
    simpa only [Core.Store.read?, stored.length_eq, List.getElem?_concat_length, Option.some.injEq] using found.symm
  subst value; cases typed

theorem matching_prefixes_do_not_allow_extra_world_or_store_rows
    {world : Core.StoreTyping} {store : Core.Store} (stored : Core.StoreHasTypes world store)
    (arguments : List TypedRuntimeArgument) (type : Core.Ty) (value : Core.Value) :
    validateRuntimeInputs (world ++ [type]) arguments store = false ∧
    validateRuntimeInputs world arguments (store ++ [value]) = false := by
  constructor
  · apply rejected arguments; intro full
    have mismatch := full.length_eq; simp [stored.length_eq] at mismatch
  · apply rejected arguments; intro full
    have mismatch := full.length_eq; simp [stored.length_eq] at mismatch

private def rowType : Core.Ty := .product (.sum .word .bool) (.sum .unit (.product .word .bool))
private def row (left right : Core.Word) (b : Bool) : Core.Value :=
  .pair (.inLeft .bool (.word left)) (.inRight .unit (.pair (.word right) (.bool b)))
private def rowReference : TypedRuntimeArgument := ⟨.cell rowType,.cellRef rowType 0,.cellRef⟩
private theorem rowTyped (left right : Core.Word) (b : Bool) : Core.ValueHasType (row left right b) rowType :=
  .pair (.inLeft .word) (.inRight (.pair .word .bool))
private theorem rowPayload : Core.CellPayload rowType :=
  .product (.sum .word .bool) (.sum .unit (.product .word .bool))

theorem nested_pairs_and_both_selected_sum_payloads_are_accepted (left right : Core.Word) (b : Bool) :
    validateRuntimeInputs [rowType,.unit] [rowReference] [row left right b,.unit] = true ∧
    Core.StoreHasTypes [rowType,.unit] [row left right b,.unit] ∧
    Core.RuntimeValueHasType [rowType,.unit] rowReference.value rowReference.type := by
  have independentlyStored : Core.StoreHasTypes [rowType,.unit] [row left right b,.unit] :=
    (Core.StoreHasTypes.nil.allocate rowPayload (rowTyped left right b)).allocate .unit .unit
  have checked : validateRuntimeInputs [rowType,.unit] [rowReference] [row left right b,.unit] = true :=
    validateRuntimeInputs_iff.mpr ⟨by intro argument member; simp only [List.mem_singleton] at member; subst argument; exact .cellRef rfl, independentlyStored⟩
  exact ⟨checked,independentlyStored,(validateRuntimeInputs_iff.mp checked).1 rowReference (by simp)⟩

private def leftArgument (unselected : Core.Ty) : TypedRuntimeArgument :=
  ⟨.sum .unit unselected,.inLeft unselected .unit,.inLeft .unit⟩
private def rightArgument (unselected : Core.Ty) : TypedRuntimeArgument :=
  ⟨.sum unselected .unit,.inRight unselected .unit,.inRight .unit⟩

theorem unselected_argument_types_do_not_relax_either_cell_sum_branch (unselected : Core.Ty) :
    validateRuntimeInputs [] [leftArgument unselected,rightArgument unselected] [] = true ∧
    (validateRuntimeInputs [.sum .unit unselected] [] [(leftArgument unselected).value] = true ↔ Core.CellPayload unselected) ∧
    (validateRuntimeInputs [.sum unselected .unit] [] [(rightArgument unselected).value] = true ↔ Core.CellPayload unselected) := by
  refine ⟨validateRuntimeInputs_iff.mpr ⟨?_, .nil⟩, ?_, ?_⟩
  · intro argument member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact .inLeft .unit
    · exact .inRight .unit
  · constructor
    · intro checked
      obtain ⟨_,_,payload,_⟩ := (validateRuntimeInputs_iff.mp checked).2.lookup (location := 0) rfl
      cases payload with | sum _ selected => exact selected
    · intro allowed
      exact validateRuntimeInputs_iff.mpr ⟨by simp,Core.StoreHasTypes.nil.allocate (.sum .unit allowed) (.inLeft .unit)⟩
  · constructor
    · intro checked
      obtain ⟨_,_,payload,_⟩ := (validateRuntimeInputs_iff.mp checked).2.lookup (location := 0) rfl
      cases payload with | sum selected _ => exact selected
    · intro allowed
      exact validateRuntimeInputs_iff.mpr ⟨by simp,Core.StoreHasTypes.nil.allocate (.sum allowed .unit) (.inRight .unit)⟩

theorem function_reference_and_nominal_unselected_types_are_argument_only :
    validateRuntimeInputs [] [leftArgument (.function .unit .unit),rightArgument (.cell .word),
      leftArgument (.namedData ⟨77⟩)] [] = true ∧
    validateRuntimeInputs [.sum .unit (.function .unit .unit)] [] [(leftArgument (.function .unit .unit)).value] = false ∧
    validateRuntimeInputs [.sum (.cell .word) .unit] [] [(rightArgument (.cell .word)).value] = false ∧
    validateRuntimeInputs [.sum .unit (.namedData ⟨77⟩)] [] [(leftArgument (.namedData ⟨77⟩)).value] = false :=
  ⟨by decide +kernel,rfl,rfl,rfl⟩

private def nominal : Core.Ty := .namedData ⟨77⟩
private def identityArgument : TypedRuntimeArgument :=
  ⟨.function nominal nominal,.closure nominal nominal (.var 0) [],.closure .nil (.var rfl)⟩
private def referenceArgument : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 0,.cellRef⟩

theorem actual_function_signatures_and_allocated_references_are_not_cell_payloads (word : Core.Word) :
    validateRuntimeInputs [.word] [identityArgument,referenceArgument] [.word word] = true ∧
    Core.RuntimeValueHasType [.word] identityArgument.value identityArgument.type ∧
    Core.RuntimeValueHasType [.word] referenceArgument.value referenceArgument.type ∧
    validateRuntimeInputs [identityArgument.type] [] [identityArgument.value] = false ∧
    validateRuntimeInputs [referenceArgument.type] [] [referenceArgument.value] = false := by
  have checked : validateRuntimeInputs [.word] [identityArgument,referenceArgument] [.word word] = true :=
    validateRuntimeInputs_iff.mpr ⟨by
      intro argument member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact .closure .nil (.var rfl)
      · exact .cellRef rfl, Core.StoreHasTypes.nil.allocate .word .word⟩
  have arguments := (validateRuntimeInputs_iff.mp checked).1
  exact ⟨checked,arguments identityArgument (by simp),arguments referenceArgument (by simp),rfl,rfl⟩

theorem no_empty_definition_nominal_value_is_fabricated
    (world : Core.StoreTyping) (value : Core.Value) (dataType : Core.DataTypeId) :
    ¬ Core.RuntimeValueHasType world value (.namedData dataType) := by
  intro typed; cases typed with | constructed lookup _ => cases lookup

theorem literal_validation_checks_compute_without_private_helper_access :
    validateRuntimeInputs [rowType,.unit] [rowReference]
      [row (Core.Word.ofNatModulo 17) (Core.Word.ofNatModulo 9) true,.unit] = true ∧
    validateRuntimeInputs [.word] [identityArgument,referenceArgument] [.word (Core.Word.ofNatModulo 17)] = true ∧
    validateRuntimeInputs [.word,.word,.unit] [referenceArgument]
      [.word (Core.Word.ofNatModulo 17),.bool true,.unit] = false ∧
    validateRuntimeInputs [.word,.word] [] [.word (Core.Word.ofNatModulo 17)] = false ∧
    validateRuntimeInputs [.word] [] [.word (Core.Word.ofNatModulo 17),.word (Core.Word.ofNatModulo 9)] = false := by
  decide +kernel

theorem every_host_function_tag_is_function_shaped_but_never_a_stored_payload (f : Core.HostFunction) :
    (Core.Value.hostFunction f).type = .function f.parameterType f.resultType ∧
    validateRuntimeInputs [f.functionType] [] [.hostFunction f] = false ∧
    ∀ type, ¬ Core.ValueHasType (.hostFunction f) type := by
  refine ⟨rfl,rfl,?_⟩
  intro type typed; cases typed

end Tests.FrontendRuntimeInputStoreValidation
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeParameterDeclarations
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
  refine ⟨(declared _ _).complete, declared _ _, noNamedValue dataType, ?_⟩
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
  have absent : ¬ ∃ inputs, RuntimeParametersDeclare (types .bool .word) owner params inputs := by
    simp only [rejectedParameters, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rintro ⟨_, declared⟩
      cases declared with
      | cons _ _ tail => cases tail with
        | cons _ unused _ => exact unused (by change "x" ∈ ["x"]; decide)
    · rintro ⟨_, declared⟩
      cases declared with
      | cons _ _ tail => cases tail with
        | cons _ _ tail => cases tail with
          | cons _ unused _ => exact unused (by change "x" ∈ ["y", "x"]; decide)
    · rintro ⟨_, declared⟩
      cases declared with
      | cons meaning _ _ => cases meaning with
        | named found =>
          have impossible := TypeNameTable.lookup?_iff.mpr found
          change (none : Option Core.Ty) = some _ at impossible
          cases impossible
    · rintro ⟨_, declared⟩
      cases declared with | cons meaning _ _ => cases meaning
    · rintro ⟨_, declared⟩; cases declared
    · rintro ⟨_, declared⟩; cases declared
    · rintro ⟨_, declared⟩
      cases declared with | cons meaning _ _ => cases meaning
  exact ⟨declareRuntimeParameters?_eq_none_iff.mpr absent, absent⟩

end Tests.FrontendRuntimeParameterDeclarations
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeParameterPositionProperties
/-! ADR-0171: actual paired lookups justify reversed positions. Equal argument
types do not identify values, and saturated subtraction is not a bounds proof. -/

set_option autoImplicit false

namespace Tests.FrontendRuntimeParameterPosition

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "parameter-position.sol"⟩, 0, 4⟩
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParameterPosition", by decide⟩], by decide⟩⟩, 0⟩
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def closure : Core.Value := .closure .bool .bool (.var 0) []
private theorem closureTyped : Core.ValueHasType closure (.function .bool .bool) := .closure .nil (.var rfl)
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def cellArg (location : Core.Location) : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word location, .cellRef⟩
private def closureArg : TypedRuntimeArgument := ⟨.function .bool .bool, closure, closureTyped⟩
private def types : TypeNameTable := [(["Flag"], .bool), (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def parameters := [parameter "first" "Flag", parameter "cell" "Cell", parameter "fn" "Fn", parameter "last" "Flag"]
private def arguments (location : Core.Location) := [boolArg false, cellArg location, closureArg, boolArg true]
private def inputs (location : Core.Location) : LocalInputs :=
  (((LocalInputs.empty.bindFresh owner "first" .bool (.bool false) .bool).bindFresh
    owner "cell" (.cell .word) (.cellRef .word location) .cellRef).bindFresh
    owner "fn" (.function .bool .bool) closure closureTyped).bindFresh owner "last" .bool (.bool true) .bool
private theorem bound (location : Core.Location) : RuntimeParametersBind types owner parameters (arguments location) (inputs location) :=
  .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "cell" ∉ ["first"]; simp)
      (.cons (.named (.tail (by decide) (.tail (by decide) .head))) (by change "fn" ∉ ["cell", "first"]; simp)
        (.cons (.named .head) (by change "last" ∉ ["fn", "cell", "first"]; simp) .nil)))

theorem any_actual_source_position_has_its_own_identity_type_value_and_reversed_core
    {suppliedTypes : TypeNameTable} {suppliedOwner : Resolved.DeclarationId}
    {params : List Syntax.FunctionParameter} {args : List TypedRuntimeArgument} {supplied : LocalInputs}
    (binding : RuntimeParametersBind suppliedTypes suppliedOwner params args supplied)
    {index : Nat} {parameterSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {typeAnnotation : Syntax.TypeExpr} {argument : TypedRuntimeArgument}
    (parameterAt : params[index]? = some ⟨parameterSpan, .typed none name typeAnnotation⟩)
    (argumentAt : args[index]? = some argument) (expressionSpan nameSpan : Syntax.SourceSpan)
    (store : Core.Store) :
    let source : Syntax.Expr := ⟨expressionSpan, .identifier ⟨nameSpan, name.value⟩⟩
    index < args.length ∧
    LocalNameTable.Lookup supplied.names name.value ⟨suppliedOwner, index⟩ ∧
    Resolved.LocalScope.Lookup supplied.context ⟨suppliedOwner, index⟩ argument.type ∧
    Resolved.LocalScope.Lookup supplied.environment ⟨suppliedOwner, index⟩ argument.value ∧
    Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids supplied.context)
      ⟨suppliedOwner, index⟩ (args.length - 1 - index) ∧
    supplied.check? source = some (.var (args.length - 1 - index), argument.type) ∧
    LocalExpressionEvaluatesWithCost supplied.names supplied.environment store source argument.value store 1 ∧
    supplied.run? 0 source store = some (argument.type, .outOfFuel
      (Core.State.initial (.var (args.length - 1 - index)) (Resolved.LocalScope.values supplied.environment) store)) ∧
    supplied.run? 1 source store = some (argument.type, .done argument.value store) := by
  intro source
  obtain ⟨bounded, _, _, named, contextLookup, valueLookup, indexed⟩ := binding.position parameterAt argumentAt
  have checked := binding.reference_elaborates_at parameterAt argumentAt expressionSpan nameSpan
  have costed := binding.reference_cost_at parameterAt argumentAt expressionSpan nameSpan store
  refine ⟨bounded, named, contextLookup, valueLookup, indexed, checked, costed, ?_, ?_⟩
  · have path := costed.checked_toSteps checked supplied.sameIds
    cases path with
    | cons transition _ =>
        have advanced := Core.advance_next_iff.mpr transition
        simp only [LocalInputs.run?, LocalInputs.check?, source, checked, bind,
          Option.bind_some, pure, Core.runStateful, advanced]
  · exact LocalInputs.run?_done_iff_typed_cost.mpr
      ⟨.identifier named contextLookup, 1, costed, Nat.le_refl _⟩

theorem singleton_return_of_any_selected_parameter_preserves_exact_core_and_one_step
    {suppliedTypes : TypeNameTable} {suppliedOwner : Resolved.DeclarationId}
    {params : List Syntax.FunctionParameter} {args : List TypedRuntimeArgument} {supplied : LocalInputs}
    (binding : RuntimeParametersBind suppliedTypes suppliedOwner params args supplied)
    {index : Nat} {parameterSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {typeAnnotation : Syntax.TypeExpr} {argument : TypedRuntimeArgument}
    (parameterAt : params[index]? = some ⟨parameterSpan, .typed none name typeAnnotation⟩)
    (argumentAt : args[index]? = some argument)
    (blockSpan returnSpan expressionSpan nameSpan : Syntax.SourceSpan) (store : Core.Store) :
    let body : Syntax.Block := ⟨blockSpan, [⟨returnSpan, .returnStmt
      (some ⟨expressionSpan, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩
    ReturnBodyElaborates supplied.names supplied.context body (.var (args.length - 1 - index)) argument.type ∧
    ReturnBodyEvaluatesWithCost supplied.names supplied.environment store body argument.value store 1 ∧
    supplied.runReturnBody? 1 body store = some (argument.type, .done argument.value store) := by
  intro body
  have elaboration := binding.reference_return_elaborates_at parameterAt argumentAt blockSpan returnSpan expressionSpan nameSpan
  have costed : ReturnBodyEvaluatesWithCost supplied.names supplied.environment store body argument.value store 1 :=
    .expression (binding.reference_cost_at parameterAt argumentAt expressionSpan nameSpan store)
  exact ⟨elaboration, costed, LocalInputs.runReturnBody?_done_iff_typed_cost.mpr
    ⟨elaboration.hasType, 1, costed, Nat.le_refl _⟩⟩

theorem full_entry_keeps_header_binding_exact_body_and_every_fuel_boundary
    {suppliedTypes : TypeNameTable} {suppliedOwner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {args : List TypedRuntimeArgument} {supplied : LocalInputs}
    (binding : RuntimeParametersBind suppliedTypes suppliedOwner
      declaration.value.signature.parameters.elements args supplied)
    {index : Nat} {parameterSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {typeAnnotation : Syntax.TypeExpr} {argument : TypedRuntimeArgument}
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name typeAnnotation⟩)
    (argumentAt : args[index]? = some argument)
    (header : RuntimeFunctionHeader suppliedTypes declaration.value.signature argument.type)
    {blockSpan returnSpan expressionSpan nameSpan : Syntax.SourceSpan}
    (bodyShape : declaration.value.body = ⟨blockSpan, [⟨returnSpan, .returnStmt
      (some ⟨expressionSpan, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩) (store : Core.Store) :
    let prepared : PreparedRuntimeFunction :=
      ⟨supplied, .var (args.length - 1 - index), argument.type⟩
    RuntimeFunctionPrepares suppliedTypes suppliedOwner declaration args prepared ∧
    prepareRuntimeFunction? suppliedTypes suppliedOwner declaration args = some prepared ∧
    RuntimeFunctionEvaluatesWithCost suppliedTypes suppliedOwner declaration args
      store argument.type argument.value store 1 ∧
    ∀ fuel, runRuntimeFunction? suppliedTypes suppliedOwner declaration args fuel store =
      some (argument.type, if fuel = 0 then .outOfFuel
        (Core.State.initial (.var (args.length - 1 - index))
          (Resolved.LocalScope.values supplied.environment) store) else .done argument.value store) := by
  intro prepared
  have preparation := runtimeFunction_parameter_prepares binding parameterAt argumentAt header bodyShape
  exact ⟨preparation, preparation.complete,
    runtimeFunction_parameter_cost binding parameterAt argumentAt header bodyShape store,
    fun fuel => runRuntimeFunction?_parameter binding parameterAt argumentAt header bodyShape fuel store⟩

theorem independent_four_argument_binding_keeps_first_middle_and_last_rows_together (location : Core.Location) :
    RuntimeParametersBind types owner parameters (arguments location) (inputs location) ∧
    (inputs location).ids = [⟨owner, 3⟩, ⟨owner, 2⟩, ⟨owner, 1⟩, ⟨owner, 0⟩] ∧
    (inputs location).environment =
      [(⟨owner, 3⟩, .bool true), (⟨owner, 2⟩, closure), (⟨owner, 1⟩, .cellRef .word location), (⟨owner, 0⟩, .bool false)] :=
  ⟨bound location, rfl, rfl⟩

private theorem selected (location : Core.Location) {index : Nat} {name : String} {typeName : String}
    {argument : TypedRuntimeArgument} (parameterAt : parameters[index]? = some (parameter name typeName))
    (argumentAt : (arguments location)[index]? = some argument) (store : Core.Store) :
    (inputs location).check? (ref name) = some (.var (3 - index), argument.type) ∧
    (inputs location).run? 1 (ref name) store = some (argument.type, .done argument.value store) := by
  have checked := (bound location).reference_elaborates_at parameterAt argumentAt span span
  have costed := (bound location).reference_cost_at parameterAt argumentAt span span store
  have typed := localExpressionHasType_iff_elaborates.mpr ⟨_, checked⟩
  exact ⟨checked, LocalInputs.run?_done_iff_typed_cost.mpr ⟨typed, 1, costed, Nat.le_refl _⟩⟩

theorem all_four_positions_return_their_distinct_values_including_opaque_middle_values
    (location : Core.Location) (store : Core.Store) :
    [ref "first", ref "cell", ref "fn", ref "last"].map (inputs location).check? =
      [some (.var 3, .bool), some (.var 2, .cell .word), some (.var 1, .function .bool .bool), some (.var 0, .bool)] ∧
    [ref "first", ref "cell", ref "fn", ref "last"].map (fun source => (inputs location).run? 1 source store) =
      [some (.bool, .done (.bool false) store), some (.cell .word, .done (.cellRef .word location) store),
       some (.function .bool .bool, .done closure store), some (.bool, .done (.bool true) store)] ∧
    ([] : Core.Store)[location]? = none := by
  have first := selected location (index := 0) (name := "first") (typeName := "Flag") rfl rfl store
  have cell := selected location (index := 1) (name := "cell") (typeName := "Cell") rfl rfl store
  have function := selected location (index := 2) (name := "fn") (typeName := "Fn") rfl rfl store
  have last := selected location (index := 3) (name := "last") (typeName := "Flag") rfl rfl store
  exact ⟨by simp only [List.map_cons, List.map_nil, first.1, cell.1, function.1, last.1]; rfl,
    by simp only [List.map_cons, List.map_nil, first.2, cell.2, function.2, last.2]; rfl, by simp⟩

theorem saturating_subtraction_does_not_supply_an_out_of_range_source_lookup (location : Core.Location) :
    (arguments location).length - 1 - 4 = 0 ∧
    parameters[4]? = none ∧ (arguments location)[4]? = none ∧
    (¬ ∃ name annotation parameterSpan, parameters[4]? = some ⟨parameterSpan, .typed none name annotation⟩) ∧
    (¬ ∃ argument, (arguments location)[4]? = some argument) := by
  exact ⟨rfl, rfl, rfl, by simp [parameters], by simp [arguments]⟩

end Tests.FrontendRuntimeParameterPosition
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeParametersProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendUnaryFunctionTypeProperties
/-! Original unary annotations have independently constructed meanings. Return-list
packing never changes source parameter arity, and meaning does not supply an inhabitant. -/
set_option autoImplicit false
namespace Tests.FrontendUnaryFunctionType
open Solcore Solcore.Frontend
private def span : Syntax.SourceSpan := ⟨⟨.main,"structural-type.sol"⟩,0,1⟩
private def named (s : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr :=
  ⟨s,.named ⟨s,⟨⟨⟨s,name⟩,[]⟩⟩⟩ none⟩
private structure Ranges where
  outer : Syntax.SourceSpan
  keyword : Syntax.SourceSpan
  parameters : Syntax.SourceSpan
  returns : Syntax.SourceSpan
private def original (s : Ranges) (parameter : Syntax.TypeExpr)
    (results : Option (List Syntax.TypeExpr)) : Syntax.TypeExpr :=
  ⟨s.outer,.function s.keyword ⟨s.parameters,[parameter]⟩ (results.map (⟨s.returns,·⟩))⟩
private def product : List Core.Ty → Core.Ty
  | [] => .unit
  | [type] => type
  | first::second::rest => .product first (product (second::rest))
private theorem listMeaning (table : TypeNameTable) (s : Syntax.SourceSpan)
    (entries : List (Syntax.TypeExpr × Core.Ty))
    (means : ∀ entry ∈ entries, StructuralTypeDenotes table entry.1 entry.2) :
    StructuralTypeDenotes table ⟨s,.tuple (entries.map Prod.fst)⟩ (product (entries.map Prod.snd)) := by
  revert means
  induction entries with
  | nil => intro _; exact .unit
  | cons entry rest ih =>
      intro means
      have head := means entry (by simp)
      have tail := ih (fun child member => means child (by simp [member]))
      cases rest with
      | nil => exact .single head
      | cons second remaining =>
          cases remaining with
          | nil => exact .pair head (means second (by simp))
          | cons third remaining => exact .many head tail

theorem absent_empty_and_singleton_returns_keep_the_original_fields
    (s : Ranges) (table : TypeNameTable) (parameter result : Syntax.TypeExpr) (A B : Core.Ty)
    (pa : StructuralTypeDenotes table parameter A) (rb : StructuralTypeDenotes table result B) :
    StructuralTypeDenotes table (original s parameter none) (.function A .unit) ∧
    StructuralTypeDenotes table (original s parameter (some [])) (.function A .unit) ∧
    StructuralTypeDenotes table (original s parameter (some [result])) (.function A B) ∧
    original s parameter none ≠ original s parameter (some []) :=
  ⟨.functionDefault pa,.functionReturns pa .unit,.functionReturns pa (.single rb),by simp [original]⟩

theorem arbitrary_written_return_count_has_one_parameter_and_no_terminal_unit
    (s : Ranges) (table : TypeNameTable) (parameter : Syntax.TypeExpr) (A : Core.Ty)
    (pa : StructuralTypeDenotes table parameter A) (entries : List (Syntax.TypeExpr × Core.Ty))
    (means : ∀ entry ∈ entries, StructuralTypeDenotes table entry.1 entry.2) :
    StructuralTypeDenotes table (original s parameter (some (entries.map Prod.fst)))
      (.function A (product (entries.map Prod.snd))) ∧
    interpretStructuralType? table (original s parameter (some (entries.map Prod.fst))) =
      some (.function A (product (entries.map Prod.snd))) := by
  have independent : StructuralTypeDenotes table (original s parameter (some (entries.map Prod.fst)))
      (.function A (product (entries.map Prod.snd))) := .functionReturns pa (listMeaning table s.returns entries means)
  exact ⟨independent,independent.complete⟩

private def nested (s : Nat → Ranges) (parameter result : Syntax.TypeExpr) : Nat → Syntax.TypeExpr
  | 0 => result
  | n+1 => original (s n) parameter (some [nested s parameter result n])
private def nestedType (A B : Core.Ty) : Nat → Core.Ty
  | 0 => B
  | n+1 => .function A (nestedType A B n)
private theorem nestedMeaning (s : Nat → Ranges) (table : TypeNameTable)
    (parameter result : Syntax.TypeExpr) (A B : Core.Ty)
    (pa : StructuralTypeDenotes table parameter A) (rb : StructuralTypeDenotes table result B) (n : Nat) :
    StructuralTypeDenotes table (nested s parameter result n) (nestedType A B n) := by
  induction n with | zero => exact rb | succ _ ih => exact .functionReturns pa (.single ih)
theorem arbitrary_function_nesting_is_independent_and_unique
    (s : Nat → Ranges) (table : TypeNameTable) (parameter result : Syntax.TypeExpr) (A B : Core.Ty)
    (pa : StructuralTypeDenotes table parameter A) (rb : StructuralTypeDenotes table result B) (n : Nat) :
    StructuralTypeDenotes table (nested s parameter result n) (nestedType A B n) ∧
    interpretStructuralType? table (nested s parameter result n) = some (nestedType A B n) ∧
    ∀ other, StructuralTypeDenotes table (nested s parameter result n) other → other=nestedType A B n := by
  have independent := nestedMeaning s table parameter result A B pa rb n
  exact ⟨independent,independent.complete,fun _ other => other.type_unique independent⟩

theorem explicit_product_parameter_is_not_a_multi_parameter_function
    (s : Ranges) (table : TypeNameTable) (left right : Syntax.TypeExpr) (A B : Core.Ty)
    (la : StructuralTypeDenotes table left A) (rb : StructuralTypeDenotes table right B) :
    StructuralTypeDenotes table (original s ⟨s.parameters,.tuple [left,right]⟩ none)
      (.function (.product A B) .unit) ∧
    StructuralTypeDenotes table (original s ⟨s.parameters,.tuple []⟩ none) (.function .unit .unit) ∧
    interpretStructuralType? table ⟨s.outer,.function s.keyword ⟨s.parameters,[left,right]⟩ none⟩=none ∧
    interpretStructuralType? table ⟨s.outer,.function s.keyword ⟨s.parameters,[]⟩ none⟩=none := by
  refine ⟨.functionDefault (.pair la rb),.functionDefault .unit,?_,?_⟩ <;>
    simp only [interpretStructuralType?]

theorem zero_and_multiple_parameters_cannot_be_rescued_by_any_return_list
    (s : Ranges) (table : TypeNameTable) (left right : Syntax.TypeExpr) (rest : List Syntax.TypeExpr)
    (returns : Option (Syntax.DelimitedList Syntax.TypeExpr)) :
    interpretStructuralType? table ⟨s.outer,.function s.keyword ⟨s.parameters,[]⟩ returns⟩=none ∧
    interpretStructuralType? table ⟨s.outer,.function s.keyword ⟨s.parameters,left::right::rest⟩ returns⟩=none ∧
    (¬ ∃ t, StructuralTypeDenotes table ⟨s.outer,.function s.keyword ⟨s.parameters,[]⟩ returns⟩ t) ∧
    (¬ ∃ t, StructuralTypeDenotes table ⟨s.outer,.function s.keyword ⟨s.parameters,left::right::rest⟩ returns⟩ t) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [interpretStructuralType?]
  · simp only [interpretStructuralType?]
  · rintro ⟨_,h⟩; cases h
  · rintro ⟨_,h⟩; cases h

theorem original_private_unsupported_member_now_has_its_independent_positive
    (table : TypeNameTable) (child : Syntax.TypeExpr) (type : Core.Ty)
    (meaning : StructuralTypeDenotes table child type) (outer : Syntax.SourceSpan) :
    StructuralTypeDenotes table ⟨outer,.function span ⟨span,[child]⟩ (some ⟨span,[child]⟩)⟩ (.function type type) ∧
    interpretStructuralType? table ⟨outer,.function span ⟨span,[child]⟩ (some ⟨span,[child]⟩)⟩=some (.function type type) ∧
    interpretTypeName? table ⟨outer,.function span ⟨span,[child]⟩ (some ⟨span,[child]⟩)⟩=none := by
  have independent : StructuralTypeDenotes table ⟨outer,.function span ⟨span,[child]⟩ (some ⟨span,[child]⟩)⟩
      (.function type type) := .functionReturns meaning (.single meaning)
  exact ⟨independent,independent.complete,rfl⟩

theorem missing_parameter_or_return_children_reject_the_entire_annotation
    (s : Ranges) (table : TypeNameTable) (bad good : Syntax.TypeExpr)
    (missing : ¬ ∃ type, StructuralTypeDenotes table bad type) :
    interpretStructuralType? table (original s bad none)=none ∧
    interpretStructuralType? table (original s bad (some [good]))=none ∧
    interpretStructuralType? table (original s good (some [bad]))=none ∧
    interpretStructuralType? table (original s good (some [good,bad]))=none := by
  have absent := interpretStructuralType?_eq_none_iff.mpr missing
  simp [original,interpretStructuralType?,absent]

theorem nested_success_survives_extensions_without_changing_any_source_range
    (s : Nat → Ranges) (table extras : TypeNameTable) (parameter result : Syntax.TypeExpr) (A B : Core.Ty)
    (pa : StructuralTypeDenotes table parameter A) (rb : StructuralTypeDenotes table result B) (n : Nat)
    (key : List String) (newType : Core.Ty) (fresh : key ∉ table.map Prod.fst) (changed : Syntax.SourceSpan) :
    StructuralTypeDenotes (table++extras) (nested s parameter result n) (nestedType A B n) ∧
    interpretStructuralType? ((key,newType)::table) (nested s parameter result n)=some (nestedType A B n) ∧
    interpretStructuralType? table {nested s parameter result n with span := changed}=some (nestedType A B n) := by
  have independent := nestedMeaning s table parameter result A B pa rb n
  exact ⟨independent.extend_types (TypeNameTable.Extends.append_right table extras),
    interpretStructuralType?_some_of_extends (TypeNameTable.Extends.cons_fresh table key newType fresh) independent.complete,
    (interpretStructuralType?_span table _ changed).trans independent.complete⟩

theorem duplicate_priority_and_lookup_equivalence_apply_inside_function_children
    (s : Ranges) (A B : Core.Ty) (left right : TypeNameTable)
    (same : ∀ key, left.lookup? key=right.lookup? key) (parameter : Syntax.TypeExpr)
    (returns : Option (List Syntax.TypeExpr)) :
    interpretStructuralType? [(["T"],A),(["T"],B)] (original s (named s.parameters "T") (some [named s.returns "T"]))=
      some (.function A A) ∧
    interpretStructuralType? left (original s parameter returns)=interpretStructuralType? right (original s parameter returns) := by
  have leaf (whereAt : Syntax.SourceSpan) : StructuralTypeDenotes [(["T"],A),(["T"],B)] (named whereAt "T") A := .named .head
  exact ⟨(StructuralTypeDenotes.functionReturns (leaf _) (.single (leaf _))).complete,
    interpretStructuralType?_congr_lookup left right same _⟩

theorem nominal_parameter_meaning_needs_no_runtime_inhabitant_or_data_definition
    (s : Ranges) (nominal : Core.DataTypeId) :
    StructuralTypeDenotes [(["N"],.namedData nominal)] (original s (named s.parameters "N") none)
      (.function (.namedData nominal) .unit) ∧
    (¬ ∃ actual, Core.ValueHasType actual (.namedData nominal)) ∧
    interpretTypeName? [(["N"],.namedData nominal)] (original s (named s.parameters "N") none)=none := by
  refine ⟨.functionDefault (.named .head),?_,rfl⟩
  rintro ⟨actual,typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?,Core.DataEnvironment.lookupDataType?] at found
end Tests.FrontendUnaryFunctionType
end
