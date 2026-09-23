import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Frontend.LocalComputation
import Solcore.Frontend.RuntimeApplicationFunction
import Solcore.Core.FuelResumptionProperties
import Solcore.Core.Safety

/-! Exact original declarations and actual three-argument records. An equally
typed swap changes the answer, while a hidden discard slot changes no source ID. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeComputationFunction
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ComputationEntry", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "computation-entry.sol"⟩, 252, 9⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Fn"], .function type type), (["Payload"], type), (["Flag"], .bool)]
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def call : Syntax.Expr := ⟨span, .call (ref "f") ⟨span, [ref "x"]⟩⟩
private def returned (expr : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some expr)⟩]⟩
private def body : Syntax.Block := ⟨span, [⟨span, .letDecl ⟨span, "r"⟩ none (some call)⟩,
  ⟨span, .expression (ref "r") true⟩, ⟨span, .returnStmt (some (ref "r"))⟩]⟩
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (named type)⟩
private def parameters := [parameter "f" "Fn", parameter "x" "Payload", parameter "y" "Payload"]
private def entry (result : String := "Payload") (exposed : Bool := false) (original : Syntax.Block := body) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "mixed"⟩, none, ⟨span, parameters⟩, ⟨if exposed then some span else none, none⟩,
    some ⟨span, ⟨span, [named result]⟩⟩, none⟩, original⟩⟩
private def initial (type : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh owner "f" (.function type type)).bindFresh owner "x" type).bindFresh owner "y" type
private def leafCore : Core.Expr := .apply (.var 2) (.var 1)
private def core : Core.Expr := .letE leafCore (.letE (.var 0) (.var 1))
private def compiled (type : Core.Ty) : CompiledRuntimeFunction := ⟨initial type, core, type⟩
private theorem header (type : Core.Ty) : RuntimeFunctionHeader (types type) (entry "Payload").value.signature type :=
  ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
private theorem declared (type : Core.Ty) : RuntimeParametersDeclare (types type) owner parameters (initial type) :=
  .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "x" ∉ ["f"]; decide)
      (.cons (.named (.tail (by decide) .head)) (by change "y" ∉ ["x", "f"]; decide) .nil))
private theorem child (type : Core.Ty) : LocalFunctionApplicationElaborates (initial type).names (initial type).context call leafCore type :=
  .call (parameterType := type)
    (.identifier (.tail (by change "y" ≠ "f"; decide) (.tail (by change "x" ≠ "f"; decide) .head)))
    (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)))
    (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)))
    (.identifier (.tail (by change "y" ≠ "x"; decide) .head))
    (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head))
    (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head))
private theorem bodyElab (type : Core.Ty) : LocalComputationReturnTreeElaborates (types type) owner (initial type) body core type := by
  have shift : (Core.Expr.var 0).weakenAt 0 = .var 1 := by simp [Core.Expr.weakenAt]
  simp only [body, core, ← shift]
  refine .inferred (by change "r" ∉ ["y", "x", "f"]; decide) (.application (child type)) ?_
  exact .discard (.pure (.identifier .head) (.var .head) (.var .head))
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem compilation (type : Core.Ty) : RuntimeComputationFunctionCompiles (types type) owner (entry "Payload") (compiled type) :=
  ⟨header type, declared type, bodyElab type⟩
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
    RuntimeComputationFunctionPrepares (types type) owner (entry "Payload") (arguments x y) (prepared x y) :=
  ⟨header type, bound x y, bodyElab type⟩
private theorem path {type : Core.Ty} (x y : Actual type) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 12 ⟨.eval core (inputs x y).environment.values, k, store⟩ ⟨.ret x.val, k, store⟩ :=
  .cons .enterLet (.cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl)
    (.cons .invokeClosure (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl)
      (.cons .bindLet (.cons (.var rfl) .refl)))))))))))
private theorem leafCost {type : Core.Ty} (x y : Actual type) (store : Core.Store) :
    LocalComputationEvaluatesWithCost (inputs x y).names (inputs x y).environment store call x.val store 6 := by
  apply LocalComputationEvaluatesWithCost.application
  apply LocalFunctionApplicationEvaluatesWithCost.call (parameterType := type) (resultType := type)
    (body := .var 0) (captured := []) (argumentValue := x.val) (functionCost := 1) (argumentCost := 1) (bodyCost := 1)
  · exact .identifier (.tail (by change "y" ≠ "f"; decide) (.tail (by change "x" ≠ "f"; decide) .head))
      (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head))
  · exact .identifier (.tail (by change "y" ≠ "x"; decide) .head) (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head)
  · exact .cons (.var rfl) .refl
private theorem counted {type : Core.Ty} (x y : Actual type) (store : Core.Store) :
    LocalComputationReturnTreeEvaluatesWithCost owner (inputs x y).names (inputs x y).environment store body x.val store 12 :=
  .inferred (initializerCost := 6) (tailCost := 4) (leafCost x y store)
    (.discard (.pure (.identifier .head .head)) (.expression (.pure (.identifier .head .head))))

theorem exact_original_static_and_actual_records_support_both_some_iffs (type : Core.Ty) :
    compileRuntimeComputationFunction? (types type) owner (entry "Payload") = some (compiled type) ∧
    RuntimeComputationFunctionCompiles (types type) owner (entry "Payload") (compiled type) ∧
    ∀ x y : Actual type, prepareRuntimeComputationFunction? (types type) owner (entry "Payload") (arguments x y) = some (prepared x y) ∧
      RuntimeComputationFunctionPrepares (types type) owner (entry "Payload") (arguments x y) (prepared x y) :=
  ⟨compileRuntimeComputationFunction?_iff.mpr (compilation type),
    compileRuntimeComputationFunction?_iff.mp (compileRuntimeComputationFunction?_iff.mpr (compilation type)),
    fun x y => ⟨prepareRuntimeComputationFunction?_iff.mpr (preparation x y),
      prepareRuntimeComputationFunction?_iff.mp (prepareRuntimeComputationFunction?_iff.mpr (preparation x y))⟩⟩

theorem full_option_projection_keeps_arity_and_original_type_order (type : Core.Ty) (args : List TypedRuntimeArgument) :
    (prepareRuntimeComputationFunction? (types type) owner (entry "Payload") args).map PreparedRuntimeFunction.toCompiled =
      if args.map (·.type) = [.function type type, type, type] then some (compiled type) else none := by
  have accepted := compileRuntimeComputationFunction?_iff.mpr (compilation type)
  simpa only [accepted, bind, Option.bind_some,
    show (compiled type).inputs.context.values.reverse = [.function type type, type, type] from rfl] using
    prepareRuntimeComputationFunction?_factorization (types type) owner (entry "Payload") args

private theorem runEq {type : Core.Ty} (x y : Actual type) (fuel : Nat) (store : Core.Store) :
    runRuntimeComputationFunction? (types type) owner (entry "Payload") (arguments x y) fuel store =
      some (type, Core.runStateful fuel (.initial core (inputs x y).environment.values store)) := by
  have values : (arguments x y).reverse.map (·.value) = (inputs x y).environment.values := rfl
  simpa only [compileRuntimeComputationFunction?_iff.mpr (compilation type), bind, Option.bind_some, values,
    show (arguments x y).map (·.type) = (compiled type).inputs.context.values.reverse from rfl, ↓reduceIte,
    show (compiled type).core = core from rfl, show (compiled type).returnType = type from rfl] using
    runRuntimeComputationFunction?_factorization (types type) owner (entry "Payload") (arguments x y) fuel store

theorem independent_body_cost_and_all_fuel_entry_outcomes {type : Core.Ty} (x y : Actual type)
    (store : Core.Store) (fuel : Nat) :
    LocalComputationReturnTreeEvaluatesWithCost owner (inputs x y).names (inputs x y).environment store body x.val store 12 ∧
    (∀ k, Core.Steps 12 ⟨.eval core (inputs x y).environment.values, k, store⟩ ⟨.ret x.val, k, store⟩) ∧
    (runRuntimeComputationFunction? (types type) owner (entry "Payload") (arguments x y) fuel store = some (type, .done x.val store) ↔ 12 ≤ fuel) ∧
    runRuntimeComputationFunction? (types type) owner (entry "Payload") (arguments x y) fuel store =
      some (type, Core.runStateful fuel (.initial core ((arguments x y).reverse.map (·.value)) store)) := by
  refine ⟨counted x y store, path x y store, ?_, runEq x y fuel store⟩
  rw [runEq, Option.some.injEq, Prod.mk.injEq]; simp only [true_and]
  exact (path x y store []).runStateful_done_iff

private def checkpoint {type : Core.Ty} (x y : Actual type) (store : Core.Store) : Core.State :=
  ⟨.ret x.val, [.letBody (.var 1) (x.val :: (inputs x y).environment.values)], store⟩
theorem genuine_checkpoint_keeps_the_same_actual_values_and_all_resumed_results {type : Core.Ty}
    (x y : Actual type) (store : Core.Store) (additional : Nat) :
    runRuntimeComputationFunction? (types type) owner (entry "Payload") (arguments x y) 10 store = some (type, .outOfFuel (checkpoint x y store)) ∧
    Core.Steps 2 (checkpoint x y store) (.final x.val store) ∧
    runRuntimeComputationFunction? (types type) owner (entry "Payload") (arguments x y) (10 + additional) store =
      some (type, Core.runStateful additional (checkpoint x y store)) := by
  have stopped : Core.runStateful 10 (.initial core (inputs x y).environment.values store) = .outOfFuel (checkpoint x y store) := rfl
  refine ⟨(runEq x y 10 store).trans (congrArg (fun result => some (type, result)) stopped),
    ((path x y store []).residual_of_outOfFuel stopped).2, ?_⟩
  rw [runEq, Core.runStateful_resume stopped additional]

private def word (n : Nat) : Actual .word := ⟨.word (Core.Word.ofNatModulo n), .word⟩
theorem same_typed_swap_preserves_compilation_but_changes_the_actual_answer (store : Core.Store) :
    (arguments (word 9) (word 14)).map (·.type) = (arguments (word 14) (word 9)).map (·.type) ∧
    (prepared (word 9) (word 14)).toCompiled = (prepared (word 14) (word 9)).toCompiled ∧
    prepareRuntimeComputationFunction? (types .word) owner (entry "Payload") (arguments (word 9) (word 14)) = some (prepared (word 9) (word 14)) ∧
    prepareRuntimeComputationFunction? (types .word) owner (entry "Payload") (arguments (word 14) (word 9)) = some (prepared (word 14) (word 9)) ∧
    runRuntimeComputationFunction? (types .word) owner (entry "Payload") (arguments (word 9) (word 14)) 12 store = some (.word, .done (word 9).val store) ∧
    runRuntimeComputationFunction? (types .word) owner (entry "Payload") (arguments (word 14) (word 9)) 12 store = some (.word, .done (word 14).val store) ∧
    (word 9).val ≠ (word 14).val := by
  refine ⟨rfl, rfl, prepareRuntimeComputationFunction?_iff.mpr (preparation _ _), prepareRuntimeComputationFunction?_iff.mpr (preparation _ _),
    ((independent_body_cost_and_all_fuel_entry_outcomes _ _ store 12).2.2.1).mpr (Nat.le_refl 12),
    ((independent_body_cost_and_all_fuel_entry_outcomes _ _ store 12).2.2.1).mpr (Nat.le_refl 12), ?_⟩
  intro same; have numbers := congrArg Fin.val (Core.Value.word.inj same); change 9 = 14 at numbers; cases numbers

theorem a_same_typed_data_record_does_not_prove_original_compilation (type : Core.Ty) :
    Core.HasType (initial type).context.values (.letE leafCore (.letE (.var 0) (.var 2))) type ∧
    (¬ RuntimeComputationFunctionCompiles (types type) owner (entry "Payload")
      { compiled type with core := .letE leafCore (.letE (.var 0) (.var 2)) }) ∧
    ¬ LocalComputationReturnTreeElaborates (types type) owner (initial type) body
      (.letE leafCore (.letE (.var 0) (.var 2))) type := by
  have rejected : ¬ RuntimeComputationFunctionCompiles (types type) owner (entry "Payload")
      { compiled type with core := .letE leafCore (.letE (.var 0) (.var 2)) } := by
    intro forged
    have equal := Option.some.inj ((compileRuntimeComputationFunction?_iff.mpr forged).symm.trans
      (compileRuntimeComputationFunction?_iff.mpr (compilation type)))
    have impossible := congrArg CompiledRuntimeFunction.core equal
    cases impossible
  exact ⟨.letE (.apply (.var rfl) (.var rfl)) (.letE (.var rfl) (.var rfl)), rejected,
    fun forgedBody => rejected ⟨header type, declared type, forgedBody⟩⟩

theorem nominal_compilation_does_not_invent_runtime_arguments (nominal : Core.DataTypeId) :
    compileRuntimeComputationFunction? (types (.namedData nominal)) owner (entry "Payload") = some (compiled (.namedData nominal)) ∧
    Core.ValueHasType (identity (.namedData nominal)) (.function (.namedData nominal) (.namedData nominal)) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨compileRuntimeComputationFunction?_iff.mpr (compilation _), identityTyped _, ?_⟩
  rintro ⟨value, typed⟩; cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem body_success_does_not_remove_the_whole_header_or_return_gate :
    elaborateLocalComputationReturnTree? (types .word) owner (initial .word) body = some (core, .word) ∧
    compileRuntimeComputationFunction? (types .word) owner (entry "Payload" true) = none ∧
    compileRuntimeComputationFunction? (types .word) owner (entry "Flag") = none := by
  refine ⟨elaborateLocalComputationReturnTree?_iff.mpr (bodyElab .word), rfl, ?_⟩
  cases accepted : compileRuntimeComputationFunction? (types .word) owner (entry "Flag") with
  | none => rfl
  | some c =>
      have proof := compileRuntimeComputationFunction?_iff.mp accepted
      have originalBody := proof.body
      rw [proof.parameters.result_unique (declared .word)] at originalBody
      have same := Option.some.inj ((elaborateLocalComputationReturnTree?_iff.mpr (bodyElab .word)).symm.trans
        (elaborateLocalComputationReturnTree?_iff.mpr originalBody))
      have flagHeader : RuntimeFunctionHeader (types .word) (entry "Flag").value.signature .bool :=
        ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) (.tail (by decide) .head)))⟩
      have impossible := (congrArg Prod.snd same).trans (flagHeader.type_unique proof.header).symm
      cases impossible

theorem full_factorization_rejects_bad_arity_and_order_not_equally_typed_swaps (fuel : Nat) (store : Core.Store) :
    runRuntimeComputationFunction? (types .word) owner (entry "Payload") [] fuel store = none ∧
    runRuntimeComputationFunction? (types .word) owner (entry "Payload")
      [⟨.word, (word 9).val, .word⟩, ⟨.function .word .word, identity .word, identityTyped .word⟩,
       ⟨.word, (word 14).val, .word⟩] fuel store = none := by
  constructor <;> rw [runRuntimeComputationFunction?_factorization, compileRuntimeComputationFunction?_iff.mpr (compilation .word)]
  · rfl
  · rfl

theorem independently_accepted_old_bodies_embed_without_full_option_equality (type : Core.Ty) :
    RuntimeFunctionCompiles (types type) owner (entry "Payload" false (returned (ref "x"))) ⟨initial type, .var 1, type⟩ ∧
    RuntimeApplicationFunctionCompiles (types type) owner (entry "Payload" false (returned call)) ⟨initial type, leafCore, type⟩ ∧
    compileRuntimeComputationFunction? (types type) owner (entry "Payload" false (returned (ref "x"))) = some ⟨initial type, .var 1, type⟩ ∧
    compileRuntimeComputationFunction? (types type) owner (entry "Payload" false (returned call)) = some ⟨initial type, leafCore, type⟩ := by
  have pureOld : RuntimeFunctionCompiles (types type) owner (entry "Payload" false (returned (ref "x"))) ⟨initial type, .var 1, type⟩ :=
    ⟨header type, declared type, .single (.expression (.identifier (.tail (by change "y" ≠ "x"; decide) .head))
      (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head))
      (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head)))⟩
  have appOld : RuntimeApplicationFunctionCompiles (types type) owner (entry "Payload" false (returned call)) ⟨initial type, leafCore, type⟩ :=
    ⟨header type, declared type, .application (child type)⟩
  refine ⟨pureOld, appOld, compileRuntimeComputationFunction?_iff.mpr
    ⟨pureOld.header, pureOld.parameters, pureOld.body.toLocalComputationReturnTree⟩, compileRuntimeComputationFunction?_iff.mpr ?_⟩
  refine ⟨appOld.header, appOld.parameters, ?_⟩
  cases appOld.body with
  | application original => exact .expression (.application original)

theorem this_same_actual_bundle_and_empty_store_supply_runtime_world_safety
    (fuel : Nat) (error : Core.MachineFault) (fault : Core.State) :
    Core.RuntimeEnvironmentHasTypes [] (inputs (word 9) (word 14)).environment.values (initial .word).context.values ∧
    Core.StoreHasTypes [] [] ∧ Core.StateHasType (.initial core (inputs (word 9) (word 14)).environment.values []) .word ∧
    Core.StateHasType (checkpoint (word 9) (word 14) []) .word ∧
    runRuntimeComputationFunction? (types .word) owner (entry "Payload") (arguments (word 9) (word 14)) fuel [] ≠
      some (.word, .fault error fault) := by
  have envTyped : Core.RuntimeEnvironmentHasTypes []
      (inputs (word 9) (word 14)).environment.values (initial .word).context.values :=
    .cons .word (.cons .word (.cons (.closure .nil (.var rfl)) .nil))
  have stateTyped : Core.StateHasType (.initial core (inputs (word 9) (word 14)).environment.values []) .word :=
    .eval .nil envTyped (bodyElab .word).core_hasType .nil
  have stopped : Core.runStateful 10 (.initial core (inputs (word 9) (word 14)).environment.values []) =
      .outOfFuel (checkpoint (word 9) (word 14) []) := rfl
  refine ⟨envTyped, .nil, stateTyped, (Core.runStateful_outOfFuel_sound stopped).1.preserve_state_type stateTyped, ?_⟩
  rw [runEq]; intro equal
  exact Core.well_typed_runStateful_never_faults stateTyped (Prod.mk.inj (Option.some.inj equal)).2

end Tests.FrontendRuntimeComputationFunction
