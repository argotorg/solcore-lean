import Solcore.Frontend.RuntimeApplicationFunction
import Solcore.Frontend.LocalApplication
import Solcore.Frontend.LocalFunctionApplication

/-! Original three-parameter declarations retain independent static and actual
provenance. Swapping equally typed arguments changes values, not acceptance. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeApplicationFunction
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ApplicationEntry", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "application-entry.sol"⟩, 248, 7⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Fn"], .function type type), (["Payload"], type), (["Flag"], .bool)]
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def call : Syntax.Expr := ⟨span, .call (ref "f") ⟨span, [ref "x"]⟩⟩
private def body : Syntax.Block := ⟨span, [⟨span, .returnStmt (some call)⟩]⟩
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (named type)⟩
private def parameters := [parameter "f" "Fn", parameter "x" "Payload", parameter "y" "Payload"]
private def entry (result : String := "Payload") (exposed : Bool := false) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "invoke"⟩, none, ⟨span, parameters⟩, ⟨if exposed then some span else none, none⟩,
    some ⟨span, ⟨span, [named result]⟩⟩, none⟩, body⟩⟩
private def initial (type : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh owner "f" (.function type type)).bindFresh owner "x" type).bindFresh owner "y" type
private def core : Core.Expr := .apply (.var 2) (.var 1)
private def compiled (type : Core.Ty) : CompiledRuntimeFunction := ⟨initial type, core, type⟩
private theorem header (type : Core.Ty) : RuntimeFunctionHeader (types type) (entry "Payload").value.signature type :=
  ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
private theorem declared (type : Core.Ty) : RuntimeParametersDeclare (types type) owner parameters (initial type) :=
  .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "x" ∉ ["f"]; decide)
      (.cons (.named (.tail (by decide) .head)) (by change "y" ∉ ["x", "f"]; decide) .nil))
private theorem child (type : Core.Ty) : LocalFunctionApplicationElaborates (initial type).names (initial type).context call core type :=
  .call (parameterType := type)
    (.identifier (.tail (by change "y" ≠ "f"; decide) (.tail (by change "x" ≠ "f"; decide) .head)))
    (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)))
    (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)))
    (.identifier (.tail (by change "y" ≠ "x"; decide) .head))
    (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head))
    (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head))
private theorem compilation (type : Core.Ty) : RuntimeApplicationFunctionCompiles (types type) owner (entry "Payload") (compiled type) :=
  ⟨header type, declared type, .application (child type)⟩
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def identity (type : Core.Ty) : Core.Value := .closure type type (.var 0) []
private theorem identityTyped (type : Core.Ty) : Core.ValueHasType (identity type) (.function type type) := .closure .nil (.var rfl)
private def arguments {type : Core.Ty} (x y : Actual type) : List TypedRuntimeArgument :=
  [⟨.function type type, identity type, identityTyped type⟩, ⟨type, x.val, x.property⟩, ⟨type, y.val, y.property⟩]
private def inputs {type : Core.Ty} (x y : Actual type) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "f" (.function type type) (identity type) (identityTyped type)).bindFresh owner "x" type x.val x.property).bindFresh owner "y" type y.val y.property
private def prepared {type : Core.Ty} (x y : Actual type) : PreparedRuntimeFunction := ⟨inputs x y, core, type⟩
private theorem bound {type : Core.Ty} (x y : Actual type) : RuntimeParametersBind (types type) owner parameters (arguments x y) (inputs x y) :=
  .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "x" ∉ ["f"]; decide)
      (.cons (.named (.tail (by decide) .head)) (by change "y" ∉ ["x", "f"]; decide) .nil))
private theorem preparation {type : Core.Ty} (x y : Actual type) :
    RuntimeApplicationFunctionPrepares (types type) owner (entry "Payload") (arguments x y) (prepared x y) :=
  ⟨header type, bound x y, .application (child type)⟩
private theorem path {type : Core.Ty} (x y : Actual type) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 6 ⟨.eval core (inputs x y).environment.values, k, store⟩ ⟨.ret x.val, k, store⟩ :=
  .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (.cons (.var rfl) .refl)))))
private theorem cost {type : Core.Ty} (x y : Actual type) (store : Core.Store) :
    LocalFunctionApplicationEvaluatesWithCost (inputs x y).names (inputs x y).environment store call x.val store 6 := by
  apply LocalFunctionApplicationEvaluatesWithCost.call (parameterType := type) (resultType := type)
    (body := .var 0) (captured := []) (argumentValue := x.val) (functionCost := 1) (argumentCost := 1) (bodyCost := 1)
  · exact .identifier (.tail (by change "y" ≠ "f"; decide) (.tail (by change "x" ≠ "f"; decide) .head))
      (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head))
  · exact .identifier (.tail (by change "y" ≠ "x"; decide) .head) (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head)
  · exact .cons (.var rfl) .refl
private theorem entryChild {type : Core.Ty} (x y : Actual type) (fuel : Nat) (store : Core.Store) :
    runRuntimeApplicationFunction? (types type) owner (entry "Payload") (arguments x y) fuel store =
      (inputs x y).runApplication? fuel call store :=
  (preparation x y).run_eq_body fuel store |>.trans ((inputs x y).runApplicationReturnBody?_return fuel span span call store)

theorem arbitrary_types_compile_without_runtime_inhabitants (type : Core.Ty) :
    RuntimeApplicationFunctionCompiles (types type) owner (entry "Payload") (compiled type) ∧
    compileRuntimeApplicationFunction? (types type) owner (entry "Payload") = some (compiled type) ∧
    Core.HasType (initial type).context.values core type :=
  ⟨compileRuntimeApplicationFunction?_sound (compilation type).complete,
    compileRuntimeApplicationFunction?_iff.mpr (compilation type), (compilation type).core_hasType⟩

theorem actual_preparation_keeps_the_complete_original_record {type : Core.Ty} (x y : Actual type)
    {other : PreparedRuntimeFunction}
    (candidate : RuntimeApplicationFunctionPrepares (types type) owner (entry "Payload") (arguments x y) other) :
    other = prepared x y ∧ prepareRuntimeApplicationFunction? (types type) owner (entry "Payload") (arguments x y) = some (prepared x y) ∧
    Core.HasType (inputs x y).context.values core type ∧ (inputs x y).environment.values = [y.val, x.val, identity type] :=
  ⟨candidate.result_unique (prepareRuntimeApplicationFunction?_sound (preparation x y).complete),
    prepareRuntimeApplicationFunction?_iff.mpr (preparation x y), (preparation x y).core_hasType, rfl⟩

theorem erasure_and_reconstruction_need_the_same_ordered_type_guard {type : Core.Ty} (x y : Actual type) :
    RuntimeApplicationFunctionCompiles (types type) owner (entry "Payload") (prepared x y).toCompiled ∧
    (∃ p, RuntimeApplicationFunctionPrepares (types type) owner (entry "Payload") (arguments x y) p ∧ p.toCompiled = compiled type) ∧
    (arguments x y).map (·.type) = (initial type).context.values.reverse := by
  have recovered := (compilation type).prepare_arguments (arguments x y) rfl
  have guard := runtimeApplicationFunctionPrepares_toCompiled_iff.mp recovered
  exact ⟨(preparation x y).compiles, runtimeApplicationFunctionPrepares_toCompiled_iff.mpr guard, guard.2⟩

theorem full_option_factorization_retains_the_argument_guard (type : Core.Ty) (args : List TypedRuntimeArgument) :
    (prepareRuntimeApplicationFunction? (types type) owner (entry "Payload") args).map PreparedRuntimeFunction.toCompiled =
      if args.map (·.type) = [.function type type, type, type] then some (compiled type) else none := by
  have layout : (compiled type).inputs.context.values.reverse = [.function type type, type, type] := rfl
  simpa only [(compilation type).complete, bind, Option.bind_some, layout] using
    prepareRuntimeApplicationFunction?_factorization (types type) owner (entry "Payload") args

theorem exact_compiled_and_prepared_paths_preserve_all_machine_results {type : Core.Ty}
    (x y : Actual type) (fuel : Nat) (store : Core.Store) :
    runRuntimeApplicationFunction? (types type) owner (entry "Payload") (arguments x y) fuel store =
      some (type, Core.runStateful fuel (.initial core [y.val, x.val, identity type] store)) ∧
    (runRuntimeApplicationFunction? (types type) owner (entry "Payload") (arguments x y) fuel store = some (type, .done x.val store) ↔ 6 ≤ fuel) ∧
    ((∃ cp, runRuntimeApplicationFunction? (types type) owner (entry "Payload") (arguments x y) fuel store = some (type, .outOfFuel cp)) ↔ fuel < 6) := by
  refine ⟨(compilation type).run_eq (arguments x y) rfl fuel store, ?_, ?_⟩
  · rw [entryChild]
    exact LocalInputs.runApplication?_done_iff_of_cost (inputs := inputs x y) (child type).hasType (cost x y store)
  · rw [entryChild]
    exact LocalInputs.runApplication?_outOfFuel_iff_of_cost (inputs := inputs x y) (child type).hasType (cost x y store)

theorem independent_closed_path_reflects_through_present_result_factorization {type : Core.Ty}
    (x y : Actual type) (store : Core.Store) :
    Core.Steps 6 (.initial core (inputs x y).environment.values store) (.final x.val store) ∧
    ∃ p, RuntimeApplicationFunctionPrepares (types type) owner (entry "Payload") (arguments x y) p ∧ p.returnType = type ∧
      Core.runStateful 6 (.initial p.core p.inputs.environment.values store) = .done x.val store := by
  have actual := path x y store []
  have present := runRuntimeApplicationFunction?_eq_some_iff.mpr
    ⟨prepared x y, preparation x y, rfl, actual.runStateful_done_iff.mpr (Nat.le_refl 6)⟩
  exact ⟨actual, runRuntimeApplicationFunction?_eq_some_iff.mp present⟩

private def checkpoint {type : Core.Ty} (x y : Actual type) (store : Core.Store) : Core.State :=
  ⟨.eval (.var 1) (inputs x y).environment.values, [.applyClosure type type (.var 0) []], store⟩
theorem whole_body_and_child_share_the_genuine_checkpoint_and_full_resumption {type : Core.Ty}
    (x y : Actual type) (store : Core.Store) (additional : Nat) :
    runRuntimeApplicationFunction? (types type) owner (entry "Payload") (arguments x y) 3 store = some (type, .outOfFuel (checkpoint x y store)) ∧
    (inputs x y).runApplicationReturnBody? 3 body store = some (type, .outOfFuel (checkpoint x y store)) ∧
    (inputs x y).runApplication? 3 call store = some (type, .outOfFuel (checkpoint x y store)) ∧
    Core.Steps 3 (checkpoint x y store) (.final x.val store) ∧
    runRuntimeApplicationFunction? (types type) owner (entry "Payload") (arguments x y) (3 + additional) store =
      some (type, Core.runStateful additional (checkpoint x y store)) := by
  have stopped : (inputs x y).runApplication? 3 call store = some (type, .outOfFuel (checkpoint x y store)) :=
    LocalInputs.runApplication?_eq_some_iff.mpr ⟨core, (child type).complete, rfl⟩
  exact ⟨(entryChild x y 3 store).trans stopped,
    ((inputs x y).runApplicationReturnBody?_return 3 span span call store).trans stopped, stopped,
    (LocalInputs.runApplication?_residual_of_outOfFuel (cost x y store) stopped).2,
    (entryChild x y _ store).trans (LocalInputs.runApplication?_resume stopped additional)⟩

private def word (n : Nat) : Actual .word := ⟨.word (Core.Word.ofNatModulo n), .word⟩
theorem equally_typed_argument_swap_changes_values_and_results_not_acceptance (store : Core.Store) :
    (arguments (word 9) (word 14)).map (·.type) = (arguments (word 14) (word 9)).map (·.type) ∧
    (prepared (word 9) (word 14)).toCompiled = (prepared (word 14) (word 9)).toCompiled ∧
    (prepared (word 9) (word 14)).inputs.environment.values ≠ (prepared (word 14) (word 9)).inputs.environment.values ∧
    prepareRuntimeApplicationFunction? (types .word) owner (entry "Payload") (arguments (word 9) (word 14)) = some (prepared (word 9) (word 14)) ∧
    prepareRuntimeApplicationFunction? (types .word) owner (entry "Payload") (arguments (word 14) (word 9)) = some (prepared (word 14) (word 9)) ∧
    runRuntimeApplicationFunction? (types .word) owner (entry "Payload") (arguments (word 9) (word 14)) 6 store = some (.word, .done (word 9).val store) ∧
    runRuntimeApplicationFunction? (types .word) owner (entry "Payload") (arguments (word 14) (word 9)) 6 store = some (.word, .done (word 14).val store) ∧
    (word 9).val ≠ (word 14).val := by
  have different : (word 9).val ≠ (word 14).val := by
    intro same
    have numbers := congrArg Fin.val (Core.Value.word.inj same)
    change 9 = 14 at numbers
    cases numbers
  refine ⟨rfl, rfl, ?_, (preparation _ _).complete, (preparation _ _).complete,
    ((exact_compiled_and_prepared_paths_preserve_all_machine_results _ _ 6 store).2.1).mpr (Nat.le_refl 6),
    ((exact_compiled_and_prepared_paths_preserve_all_machine_results _ _ 6 store).2.1).mpr (Nat.le_refl 6), different⟩
  intro same
  exact different (List.cons.inj same).1.symm

theorem another_same_typed_open_core_has_no_original_compilation_provenance (type : Core.Ty) :
    Core.HasType (initial type).context.values (.apply (.var 2) (.var 0)) type ∧
    ¬ RuntimeApplicationFunctionCompiles (types type) owner (entry "Payload") { compiled type with core := .apply (.var 2) (.var 0) } := by
  refine ⟨.apply (.var rfl) (.var rfl), ?_⟩
  intro forged
  have impossible := congrArg CompiledRuntimeFunction.core (forged.result_unique (compilation type))
  cases impossible

private theorem rejectedArguments (args : List TypedRuntimeArgument) (wrong : args.map (·.type) ≠ [.function .word .word, .word, .word]) :
    prepareRuntimeApplicationFunction? (types .word) owner (entry "Payload") args = none := by
  apply prepareRuntimeApplicationFunction?_eq_none_iff.mpr
  rintro ⟨p, proof⟩
  have erased := proof.compiles.result_unique (compilation .word)
  exact wrong (runtimeApplicationFunctionPrepares_toCompiled_iff.mp ⟨p, proof, erased⟩).2
theorem wrong_arity_or_ordered_types_reject_even_with_an_accepted_local_body (fuel : Nat) (store : Core.Store) :
    (inputs (word 9) (word 14)).checkApplicationReturnBody? body = some (core, .word) ∧
    runRuntimeApplicationFunction? (types .word) owner (entry "Payload") [] fuel store = none ∧
    runRuntimeApplicationFunction? (types .word) owner (entry "Payload")
      [⟨.word, (word 9).val, .word⟩, ⟨.function .word .word, identity .word, identityTyped .word⟩, ⟨.word, (word 14).val, .word⟩] fuel store = none :=
  ⟨(preparation (word 9) (word 14)).body.complete,
    (runRuntimeApplicationFunction?_eq_none_iff fuel store).mpr (rejectedArguments [] (by decide)),
    (runRuntimeApplicationFunction?_eq_none_iff fuel store).mpr (rejectedArguments _ (by decide))⟩

theorem whole_header_and_declared_return_contract_are_not_local_call_typing :
    compileRuntimeApplicationFunction? (types .word) owner (entry "Payload" true) = none ∧
    compileRuntimeApplicationFunction? (types .word) owner (entry "Flag") = none ∧
    (¬ ∃ c, RuntimeApplicationFunctionCompiles (types .word) owner (entry "Payload" true) c) := by
  have hidden : compileRuntimeApplicationFunction? (types .word) owner (entry "Payload" true) = none := rfl
  refine ⟨hidden, compileRuntimeApplicationFunction?_eq_none_iff.mpr ?_, compileRuntimeApplicationFunction?_eq_none_iff.mp hidden⟩
  rintro ⟨c, proof⟩
  have same := proof.parameters.result_unique (declared .word)
  have actualBody := proof.body
  rw [same] at actualBody
  have flagHeader : RuntimeFunctionHeader (types .word) (entry "Flag").value.signature .bool :=
    ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) (.tail (by decide) .head)))⟩
  have impossible := ((compilation .word).body.result_unique actualBody).2.trans (flagHeader.type_unique proof.header).symm
  cases impossible

theorem nominal_static_parameters_do_not_supply_nominal_actual_arguments (nominal : Core.DataTypeId) :
    compileRuntimeApplicationFunction? (types (.namedData nominal)) owner (entry "Payload") = some (compiled (.namedData nominal)) ∧
    Core.ValueHasType (identity (.namedData nominal)) (.function (.namedData nominal) (.namedData nominal)) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(compilation _).complete, identityTyped _, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem the_same_actual_word_bundle_transports_runtime_world_safety
    (fuel : Nat) (error : Core.MachineFault) (fault : Core.State) :
    runRuntimeApplicationFunction? (types .word) owner (entry "Payload") (arguments (word 9) (word 14)) fuel [] ≠
      some (.word, .fault error fault) ∧
    runRuntimeApplicationFunction? (types .word) owner (entry "Payload") (arguments (word 9) (word 14)) 6 [] =
      some (.word, .done (word 9).val []) ∧
    ∃ world, Core.WorldExtends [] world ∧ Core.StoreHasTypes world [] ∧
      Core.RuntimeValueHasType world (word 9).val .word := by
  have environmentTyped : Core.RuntimeEnvironmentHasTypes []
      (inputs (word 9) (word 14)).environment.values (inputs (word 9) (word 14)).context.values :=
    .cons .word (.cons .word (.cons (.closure .nil (.var rfl)) .nil))
  have storeTyped : Core.StoreHasTypes [] [] := .nil
  have done : (inputs (word 9) (word 14)).runApplication? 6 call [] = some (.word, .done (word 9).val []) :=
    (LocalInputs.runApplication?_done_iff_of_cost (inputs := inputs (word 9) (word 14))
      (child .word).hasType (cost (word 9) (word 14) [])).mpr (Nat.le_refl 6)
  refine ⟨?_, (entryChild (word 9) (word 14) 6 []).trans done,
    (LocalInputs.runApplication?_runtime_done_sound environmentTyped storeTyped done).2⟩
  rw [entryChild]
  exact LocalInputs.runApplication?_runtime_never_faults environmentTyped storeTyped call fuel .word error fault

end Tests.FrontendRuntimeApplicationFunction
