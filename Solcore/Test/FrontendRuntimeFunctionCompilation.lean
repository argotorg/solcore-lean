import Solcore.Frontend.RuntimeFunctionCompilationProperties
import Solcore.Frontend.RuntimeFunctionEntryExecutionProperties
import Solcore.Frontend.RuntimeFunctionPreparationFactorization

/-! Compilation evidence types exact open Core without runtime inhabitants.
Supplied argument types and values remain a separate preparation boundary. -/

set_option autoImplicit false

namespace Tests.FrontendRuntimeFunctionCompilation

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"FunctionCompilation", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "function-compilation.sol"⟩, 12, 3⟩
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (value : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt value⟩]⟩
private def declaration (parameters : List Syntax.FunctionParameter) (result : Option Syntax.TypeExpr)
    (body : Syntax.Block) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "entry"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    result.map (fun type => ⟨span, ⟨span, [type]⟩⟩), none⟩, body⟩⟩
private def table (type : Core.Ty) : TypeNameTable := [(["Arg"], type), (["Result"], type), (["Bool"], .bool)]
private def bare := declaration [] none (returned none)
private def bareCompiled : CompiledRuntimeFunction := ⟨.empty, .unit, .unit⟩
private theorem bareCompiles : RuntimeFunctionCompiles [] owner bare bareCompiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .absent⟩, .nil, .single .bare⟩

theorem bare_unit_has_independent_value_free_compilation_and_exact_core_typing :
    RuntimeFunctionCompiles [] owner bare bareCompiled ∧
    compileRuntimeFunction? [] owner bare = some bareCompiled ∧
    Core.HasType [] bareCompiled.core bareCompiled.returnType :=
  ⟨bareCompiles, bareCompiles.complete, bareCompiles.core_hasType⟩

private def identity := declaration [parameter "x" "Arg"] (some (annotation "Result")) (returned (some (ref "x")))
private def identityCompiled (type : Core.Ty) : CompiledRuntimeFunction :=
  ⟨LocalTypeInputs.empty.bindFresh owner "x" type, .var 0, type⟩
private theorem identityCompiles (type : Core.Ty) :
    RuntimeFunctionCompiles (table type) owner identity (identityCompiled type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩

theorem arbitrary_annotation_compiles_to_open_not_closed_core (type : Core.Ty) :
    RuntimeFunctionCompiles (table type) owner identity (identityCompiled type) ∧
    compileRuntimeFunction? (table type) owner identity = some (identityCompiled type) ∧
    (identityCompiled type).inputs.context = [(id 0, type)] ∧
    Core.HasType [type] (.var 0) type ∧
    ¬ Core.HasType [] (.var 0) type := by
  refine ⟨identityCompiles type, (identityCompiles type).complete, rfl,
    (identityCompiles type).core_hasType, ?_⟩
  intro closed
  cases closed with
  | var found => cases found

theorem nominal_compilation_does_not_supply_a_typed_runtime_argument (dataType : Core.DataTypeId) :
    compileRuntimeFunction? (table (.namedData dataType)) owner identity =
      some (identityCompiled (.namedData dataType)) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData dataType := by
  refine ⟨(identityCompiles _).complete, ?_⟩
  rintro ⟨argument, sameType⟩
  rcases argument with ⟨type, value, typed⟩
  cases sameType
  cases typed with
  | constructed found _ =>
      simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def branch : Syntax.Expr := ⟨span, .conditional (ref "c") span (ref "x") span (ref "x")⟩
private def conditional := declaration [parameter "c" "Bool", parameter "x" "Arg"]
  (some (annotation "Result")) (returned (some branch))
private def conditionalCompiled (type : Core.Ty) : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "c" .bool).bindFresh owner "x" type,
    .ifE (.var 1) (.var 0) (.var 0), type⟩
private theorem conditionalCompiles (type : Core.Ty) :
    RuntimeFunctionCompiles (table type) owner conditional (conditionalCompiled type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩,
    .cons (.named (.tail (by decide) (.tail (by decide) .head)))
      (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "x" ∉ ["c"]; simp) .nil),
    .single <| .expression (.conditional (.identifier (.tail (by change "x" ≠ "c"; decide) .head)) (.identifier .head) (.identifier .head))
      (.ifE (.var (.tail (by change id 1 ≠ id 0; decide) .head)) (.var .head) (.var .head))
      (.ifE (.var (.tail (by change id 1 ≠ id 0; decide) .head)) (.var .head) (.var .head))⟩

theorem conditional_compilation_retains_both_branches_and_reversed_parameter_context (type : Core.Ty) :
    RuntimeFunctionCompiles (table type) owner conditional (conditionalCompiled type) ∧
    compileRuntimeFunction? (table type) owner conditional = some (conditionalCompiled type) ∧
    (conditionalCompiled type).inputs.context = [(id 1, type), (id 0, .bool)] ∧
    Core.HasType [type, .bool] (.ifE (.var 1) (.var 0) (.var 0)) type :=
  ⟨conditionalCompiles type, (conditionalCompiles type).complete, rfl, (conditionalCompiles type).core_hasType⟩

theorem an_equally_typed_handmade_core_is_not_the_compiled_expression :
    Core.HasType [.bool] (.bool false) .bool ∧
    (¬ RuntimeFunctionCompiles (table .bool) owner identity { identityCompiled .bool with core := .bool false }) ∧
    compileRuntimeFunction? (table .bool) owner identity ≠
      some { identityCompiled .bool with core := .bool false } := by
  have absent : ¬ RuntimeFunctionCompiles (table .bool) owner identity
      { identityCompiled .bool with core := .bool false } := by
    intro wrong
    have exactCore := (identityCompiles .bool).body.result_unique wrong.body
    cases exactCore.1
  exact ⟨.bool, absent, fun accepted => absent (compileRuntimeFunction?_sound accepted)⟩

theorem independent_compilation_factors_preparation_through_the_exact_argument_guard
    {types : TypeNameTable} {suppliedOwner : Resolved.DeclarationId}
    {source : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types suppliedOwner source compiled)
    (arguments : List TypedRuntimeArgument) :
    (prepareRuntimeFunction? types suppliedOwner source arguments).map PreparedRuntimeFunction.toCompiled =
      (if arguments.map (·.type) = compiled.inputs.context.values.reverse then some compiled else none) ∧
    ((∃ prepared, RuntimeFunctionPrepares types suppliedOwner source arguments prepared ∧
        prepared.toCompiled = compiled) ↔ arguments.map (·.type) = compiled.inputs.context.values.reverse) := by
  have factor := prepareRuntimeFunction?_factorization types suppliedOwner source arguments
  rw [compilation.complete] at factor
  refine ⟨by simpa only [bind, Option.bind_some] using factor, ?_⟩
  exact ⟨fun prepared => (runtimeFunctionPrepares_toCompiled_iff.mp prepared).2,
    fun matching => compilation.prepare_arguments arguments matching⟩

private def boolArg (flag : Bool) : TypedRuntimeArgument := ⟨.bool, .bool flag, .bool⟩
private def wordArg : TypedRuntimeArgument := ⟨.word, .word Core.Word.zero, .word⟩
private def wrongArguments : List (List TypedRuntimeArgument) :=
  [[], [boolArg true], [boolArg true, wordArg, boolArg false], [wordArg, boolArg true]]

theorem missing_extra_and_reordered_types_do_not_bypass_the_runtime_guard
    (arguments : List TypedRuntimeArgument) (member : arguments ∈ wrongArguments)
    (fuel : Nat) (store : Core.Store) :
    compileRuntimeFunction? (table .word) owner conditional = some (conditionalCompiled .word) ∧
    prepareRuntimeFunction? (table .word) owner conditional arguments = none ∧
    runRuntimeFunction? (table .word) owner conditional arguments fuel store = none := by
  have mismatch : arguments.map (·.type) ≠ (conditionalCompiled .word).inputs.context.values.reverse := by
    simp only [wrongArguments, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  have noPreparation : ¬ ∃ prepared, RuntimeFunctionPrepares (table .word) owner conditional arguments prepared := by
    rintro ⟨prepared, preparation⟩
    have erased := preparation.compiles.result_unique (conditionalCompiles .word)
    exact mismatch (runtimeFunctionPrepares_toCompiled_iff.mp ⟨prepared, preparation, erased⟩).2
  have rejected := prepareRuntimeFunction?_eq_none_iff.mpr noPreparation
  exact ⟨(conditionalCompiles .word).complete, rejected,
    by simp only [runRuntimeFunction?, rejected, bind, Option.bind_none]⟩

private def runtimeIdentity (flag : Bool) : PreparedRuntimeFunction :=
  ⟨LocalInputs.empty.bindFresh owner "x" .bool (.bool flag) .bool, .var 0, .bool⟩
private theorem runtimePrepares (flag : Bool) :
    RuntimeFunctionPrepares (table .bool) owner identity [boolArg flag] (runtimeIdentity flag) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩,
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil,
    .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩
private theorem runtimeCost (flag : Bool) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table .bool) owner identity [boolArg flag]
      store .bool (.bool flag) store 1 :=
  .intro (runtimePrepares flag) (.single <| .expression (.identifier .head .head))

theorem different_values_share_the_compiled_result_but_not_the_returned_value (store : Core.Store) :
    compileRuntimeFunction? (table .bool) owner identity = some (identityCompiled .bool) ∧
    (prepareRuntimeFunction? (table .bool) owner identity [boolArg false]).map PreparedRuntimeFunction.toCompiled =
      some (identityCompiled .bool) ∧
    (prepareRuntimeFunction? (table .bool) owner identity [boolArg true]).map PreparedRuntimeFunction.toCompiled =
      some (identityCompiled .bool) ∧
    runRuntimeFunction? (table .bool) owner identity [boolArg false] 1 store = some (.bool, .done (.bool false) store) ∧
    runRuntimeFunction? (table .bool) owner identity [boolArg true] 1 store = some (.bool, .done (.bool true) store) ∧
    runRuntimeFunction? (table .bool) owner identity [boolArg false] 0 store =
      some (.bool, .outOfFuel (Core.State.initial (.var 0) [.bool false] store)) := by
  refine ⟨(identityCompiles .bool).complete, ?_, ?_,
    (runtimeCost false store).run_done_iff.mpr (by decide),
    (runtimeCost true store).run_done_iff.mpr (by decide), ?_⟩
  · rw [(runtimePrepares false).complete]; rfl
  · rw [(runtimePrepares true).complete]; rfl
  · rw [runRuntimeFunction?, (runtimePrepares false).complete]; rfl

private def publicBare : Syntax.FunctionDecl :=
  ⟨span, ⟨{ bare.value.signature with modifiers := ⟨some span, none⟩ }, bare.value.body⟩⟩
private def emptyBody := declaration [] none ⟨span, []⟩

theorem whole_header_and_body_restrictions_apply_without_any_runtime_arguments :
    (¬ ∃ compiled, RuntimeFunctionCompiles [] owner publicBare compiled) ∧
    compileRuntimeFunction? [] owner publicBare = none ∧
    (¬ ∃ compiled, RuntimeFunctionCompiles [] owner emptyBody compiled) ∧
    compileRuntimeFunction? [] owner emptyBody = none := by
  have headerAbsent : ¬ ∃ compiled, RuntimeFunctionCompiles [] owner publicBare compiled := by
    rintro ⟨compiled, evidence⟩
    cases evidence.header.noPublic
  have bodyAbsent : ¬ ∃ compiled, RuntimeFunctionCompiles [] owner emptyBody compiled := by
    rintro ⟨compiled, evidence⟩
    cases evidence.body with
    | single body => cases body
    | conditional body => cases body
  exact ⟨headerAbsent, compileRuntimeFunction?_eq_none_iff.mpr headerAbsent,
    bodyAbsent, compileRuntimeFunction?_eq_none_iff.mpr bodyAbsent⟩

end Tests.FrontendRuntimeFunctionCompilation
