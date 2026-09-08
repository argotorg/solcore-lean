import Solcore.Frontend.TypedLetReturnTreeEmbeddingProperties
import Solcore.Frontend.RuntimeFunctionParameterCompilationProperties
import Solcore.Frontend.RuntimeFunctionConditionalParameterCompilationProperties
import Solcore.Frontend.RuntimeFunctionCompilationOwnerProperties
import Solcore.Frontend.RuntimeFunctionExecutionFactorization

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
  .cons (conditionMeaning payload condition) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (payloadMeaning payload condition) (by change "t" ∉ ["c"]; decide)
      (.cons (payloadMeaning payload condition) (by change "f" ∉ ["t", "c"]; decide) .nil))
private theorem header (payload condition : Core.Ty) (body : Syntax.Block) :
    RuntimeFunctionHeader (types payload condition) (entry parameters "Payload" body).value.signature payload :=
  ⟨rfl, rfl, rfl, rfl, .single (payloadMeaning payload condition)⟩
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
  refine ⟨rfl, ?_, rfl, rfl⟩
  apply compileRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨candidate, accepted⟩
  have bodyType := (accepted.parameter_return_core (index := 1) rfl (payloadMeaning .word .bool) rfl).2
  have headerType := accepted.header.type_unique
    ⟨rfl, rfl, rfl, rfl, .single (conditionMeaning .word .bool)⟩
  rw [bodyType] at headerType
  cases headerType

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
