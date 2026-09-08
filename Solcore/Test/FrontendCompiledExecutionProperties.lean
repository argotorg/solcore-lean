import Solcore.Frontend.RuntimeFunctionExecutionFactorization
import Solcore.Frontend.RuntimeFunctionEntryExecutionProperties
import Solcore.Frontend.RuntimeFunctionCompiledExecutionProperties

/-! Independently compiled entries execute the actual supplied typed values.
Full machine states, ordered arguments, whole contracts, and cost boundaries
remain distinct from mere hand-built compiled data. -/

set_option autoImplicit false

namespace Tests.FrontendCompiledExecution

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"CompiledExecution", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compiled-execution.sol"⟩, 9, 2⟩
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def declaration (parameters : List Syntax.FunctionParameter) (source : Syntax.Expr) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "entry"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation "Output"]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some source)⟩]⟩⟩⟩
private def table (input output : Core.Ty) : TypeNameTable := [(["Input"], input), (["Output"], output)]
private def argument (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    TypedRuntimeArgument := ⟨type, value, typed⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := argument .bool (.bool value) .bool
private def wordArg (value : Core.Word) : TypedRuntimeArgument := argument .word (.word value) .word
private theorem header (input output : Core.Ty) (parameters : List Syntax.FunctionParameter) (source : Syntax.Expr) :
    RuntimeFunctionHeader (table input output) (declaration parameters source).value.signature output :=
  ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
private def identity := declaration [parameter "x" "Input"] (ref "x")
private def identityCompiled (type : Core.Ty) : CompiledRuntimeFunction :=
  ⟨LocalTypeInputs.empty.bindFresh owner "x" type, .var 0, type⟩
private theorem identityCompiles (type : Core.Ty) :
    RuntimeFunctionCompiles (table type type) owner identity (identityCompiled type) :=
  ⟨header type type _ _, .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩

theorem arbitrary_typed_identity_preserves_full_results_and_zero_state
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) (store : Core.Store) :
    RuntimeFunctionCompiles (table type type) owner identity (identityCompiled type) ∧
    (∀ fuel, runRuntimeFunction? (table type type) owner identity [argument type value typed] fuel store =
      some (type, Core.runStateful fuel (Core.State.initial (.var 0) [value] store))) ∧
    runRuntimeFunction? (table type type) owner identity [argument type value typed] 0 store =
      some (type, .outOfFuel (Core.State.initial (.var 0) [value] store)) ∧
    runRuntimeFunction? (table type type) owner identity [argument type value typed] 1 store =
      some (type, .done value store) :=
  ⟨identityCompiles type, fun fuel => (identityCompiles type).run_eq _ rfl fuel store,
    (identityCompiles type).run_eq _ rfl 0 store, (identityCompiles type).run_eq _ rfl 1 store⟩

private def pairParameters := [parameter "l" "Input", parameter "r" "Input"]
private def pairInputs (type : Core.Ty) : LocalTypeInputs :=
  (LocalTypeInputs.empty.bindFresh owner "l" type).bindFresh owner "r" type
private theorem pairDeclares (input output : Core.Ty) :
    RuntimeParametersDeclare (table input output) owner pairParameters (pairInputs input) :=
  .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private def selected (left : Bool) := declaration pairParameters (ref (if left then "l" else "r"))
private def selectedCompiled (type : Core.Ty) (left : Bool) : CompiledRuntimeFunction :=
  ⟨pairInputs type, .var (if left then 1 else 0), type⟩
private theorem selectedCompiles (type : Core.Ty) (left : Bool) :
    RuntimeFunctionCompiles (table type type) owner (selected left) (selectedCompiled type left) := by
  refine ⟨header type type _ _, pairDeclares type type, ?_⟩
  cases left
  · exact .single <| .expression (.identifier .head) (.var .head) (.var .head)
  · exact .single <| .expression (.identifier (.tail names_ne .head))
      (.var (.tail ids_ne .head)) (.var (.tail ids_ne .head))

theorem equally_typed_distinct_values_remain_in_their_source_positions
    (type : Core.Ty) (left right : Core.Value) (leftTyped : Core.ValueHasType left type)
    (rightTyped : Core.ValueHasType right type) (different : left ≠ right) (store : Core.Store) :
    (∀ selection fuel, runRuntimeFunction? (table type type) owner (selected selection)
      [argument type left leftTyped, argument type right rightTyped] fuel store =
        some (type, Core.runStateful fuel
          (Core.State.initial (.var (if selection then 1 else 0)) [right, left] store))) ∧
    runRuntimeFunction? (table type type) owner (selected true)
      [argument type left leftTyped, argument type right rightTyped] 1 store ≠
    runRuntimeFunction? (table type type) owner (selected false)
      [argument type left leftTyped, argument type right rightTyped] 1 store := by
  refine ⟨fun selection fuel => (selectedCompiles type selection).run_eq _ rfl fuel store, ?_⟩
  rw [(selectedCompiles type true).run_eq _ rfl, (selectedCompiles type false).run_eq _ rfl]
  change some (type, Core.StatefulRunResult.done left store) ≠ some (type, .done right store)
  exact fun same => different (Core.StatefulRunResult.done.inj (Prod.mk.inj (Option.some.inj same)).2).1

theorem boolean_and_word_pairs_do_not_alias_source_positions
    (left right : Core.Word) (different : left ≠ right) (store : Core.Store) :
    (runRuntimeFunction? (table .bool .bool) owner (selected true) [boolArg true, boolArg false] 1 store ≠
      runRuntimeFunction? (table .bool .bool) owner (selected false) [boolArg true, boolArg false] 1 store) ∧
    (runRuntimeFunction? (table .word .word) owner (selected true) [wordArg left, wordArg right] 1 store ≠
      runRuntimeFunction? (table .word .word) owner (selected false) [wordArg left, wordArg right] 1 store) :=
  ⟨(equally_typed_distinct_values_remain_in_their_source_positions .bool (.bool true) (.bool false)
      .bool .bool (by intro same; cases same) store).2,
    (equally_typed_distinct_values_remain_in_their_source_positions .word (.word left) (.word right)
      .word .word (fun same => different (Core.Value.word.inj same)) store).2⟩

private def greater : Syntax.Expr := ⟨span, .binary (ref "l") ⟨span, .greater⟩ (ref "r")⟩
private def greaterCompiled : CompiledRuntimeFunction := ⟨pairInputs .word, .binary .wordGt (.var 1) (.var 0), .bool⟩
private theorem greaterCompiles : RuntimeFunctionCompiles (table .word .bool) owner
    (declaration pairParameters greater) greaterCompiled :=
  ⟨header .word .bool _ _, pairDeclares .word .bool,
    .single <| .expression (.greater (.identifier (.tail names_ne .head)) (.identifier .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))⟩

theorem compiled_comparison_exposes_ordered_intermediate_state
    (left right : Core.Word) (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? (table .word .bool) owner (declaration pairParameters greater)
      [wordArg left, wordArg right] fuel store = some (.bool, Core.runStateful fuel
        (Core.State.initial greaterCompiled.core [.word right, .word left] store)) ∧
    runRuntimeFunction? (table .word .bool) owner (declaration pairParameters greater)
      [wordArg left, wordArg right] 4 store = some (.bool, .outOfFuel
        ⟨.ret (.word right), [.binaryApply .wordGt (.word left)], store⟩) ∧
    (∃ compiled, RuntimeFunctionCompiles (table .word .bool) owner (declaration pairParameters greater) compiled ∧
      [Core.Ty.word, .word] = compiled.inputs.context.values.reverse ∧ .bool = compiled.returnType ∧
      Core.runStateful 5 (Core.State.initial compiled.core [.word right, .word left] store) =
        .done (.bool (decide (left > right))) store) := by
  refine ⟨greaterCompiles.run_eq _ rfl fuel store, greaterCompiles.run_eq _ rfl 4 store, ?_⟩
  exact runRuntimeFunction?_eq_some_compiled_iff.mp
    (greaterCompiles.run_eq [wordArg left, wordArg right] rfl 5 store)

private def mixed := declaration [parameter "l" "Input", parameter "r" "Output"] (ref "r")
private def mixedCompiled : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .bool, .var 0, .bool⟩
private theorem mixedCompiles : RuntimeFunctionCompiles (table .word .bool) owner mixed mixedCompiled :=
  ⟨header .word .bool _ _, .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "r" ∉ ["l"]; simp) .nil),
    .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩
private def wrongArguments : List (List TypedRuntimeArgument) :=
  [[], [wordArg .zero], [wordArg .zero, boolArg true, wordArg .zero], [boolArg true, wordArg .zero]]

theorem arity_and_type_order_reject_before_any_machine_execution
    (arguments : List TypedRuntimeArgument) (member : arguments ∈ wrongArguments) (fuel : Nat) (store : Core.Store) :
    compileRuntimeFunction? (table .word .bool) owner mixed = some mixedCompiled ∧
    runRuntimeFunction? (table .word .bool) owner mixed arguments fuel store = none := by
  have mismatch : arguments.map (·.type) ≠ mixedCompiled.inputs.context.values.reverse := by
    simp only [wrongArguments, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  refine ⟨mixedCompiles.complete, ?_⟩
  rw [runRuntimeFunction?_factorization, mixedCompiles.complete]
  simp only [bind, Option.bind_some, if_neg mismatch]

private def forged : CompiledRuntimeFunction := { identityCompiled .bool with core := .bool false }

theorem well_typed_forged_data_does_not_license_execution (store : Core.Store) :
    Core.HasType [.bool] forged.core .bool ∧
    (¬ RuntimeFunctionCompiles (table .bool .bool) owner identity forged) ∧
    runRuntimeFunction? (table .bool .bool) owner identity [boolArg true] 1 store =
      some (.bool, .done (.bool true) store) ∧
    Core.runStateful 1 (Core.State.initial forged.core [.bool true] store) = .done (.bool false) store := by
  refine ⟨.bool, ?_, (identityCompiles .bool).run_eq _ rfl 1 store, rfl⟩
  intro claimed
  have same := congrArg CompiledRuntimeFunction.core ((identityCompiles .bool).result_unique claimed)
  cases same

private def emptyBody : Syntax.FunctionDecl :=
  ⟨span, ⟨identity.value.signature, ⟨span, []⟩⟩⟩

theorem independent_body_failure_blocks_every_supplied_argument_list
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    (¬ ∃ compiled, RuntimeFunctionCompiles (table .bool .bool) owner emptyBody compiled) ∧
    runRuntimeFunction? (table .bool .bool) owner emptyBody arguments fuel store = none := by
  have absent : ¬ ∃ compiled, RuntimeFunctionCompiles (table .bool .bool) owner emptyBody compiled := by
    rintro ⟨compiled, evidence⟩
    cases evidence.body with
    | single body => cases body
    | conditional body => cases body
  refine ⟨absent, ?_⟩
  rw [runRuntimeFunction?_factorization, compileRuntimeFunction?_eq_none_iff.mpr absent]
  rfl

theorem actual_typed_identity_arguments_license_compiled_safety
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (fuel : Nat) (store : Core.Store) (error : Core.MachineFault) (faultState : Core.State) :
    (∃ result cost, RuntimeFunctionEvaluatesWithCost (table type type) owner identity
        [argument type value typed] store type result store cost ∧ Core.ValueHasType result type ∧
      ∀ budget, (Core.runStateful budget (Core.State.initial (.var 0) [value] store) =
        .done result store ↔ cost ≤ budget) ∧
        ((∃ suspended, Core.runStateful budget (Core.State.initial (.var 0) [value] store) =
          .outOfFuel suspended) ↔ budget < cost)) ∧
    Core.runStateful fuel (Core.State.initial (.var 0) [value] store) ≠ .fault error faultState :=
  ⟨(identityCompiles type).typed_compiled_execution [argument type value typed] rfl store,
    (identityCompiles type).compiled_never_faults [argument type value typed] rfl fuel store error faultState⟩

private def shortSource : Syntax.Expr := ⟨span, .binary (ref "x") ⟨span, .logicalAnd⟩
  ⟨span, .unary ⟨span, .logicalNot⟩ ⟨span, .unary ⟨span, .logicalNot⟩ (ref "x")⟩⟩⟩
private def shortDeclaration := declaration [parameter "x" "Input"] shortSource
private def shortCompiled : CompiledRuntimeFunction :=
  { identityCompiled .bool with core := .ifE (.var 0) (.unary .boolNot (.unary .boolNot (.var 0))) (.bool false) }
private theorem shortCompiles : RuntimeFunctionCompiles (table .bool .bool) owner shortDeclaration shortCompiled :=
  ⟨header .bool .bool _ _, (identityCompiles .bool).parameters,
    .single <| .expression (.logicalAnd (.identifier .head) (.logicalNot (.logicalNot (.identifier .head))))
      (.ifE (.var .head) (.unary (.unary (.var .head))) .bool)
      (.ifE (.var .head) (.unary (.unary (.var .head))) .bool)⟩
private def shortPrepared (choice : Bool) : PreparedRuntimeFunction :=
  ⟨LocalInputs.empty.bindFresh owner "x" .bool (.bool choice) .bool, shortCompiled.core, .bool⟩
private theorem shortPrepares (choice : Bool) : RuntimeFunctionPrepares (table .bool .bool) owner
    shortDeclaration [boolArg choice] (shortPrepared choice) :=
  ⟨shortCompiles.header, .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil,
    shortCompiles.body⟩
private theorem shortCost (choice : Bool) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table .bool .bool) owner shortDeclaration [boolArg choice]
      store .bool (.bool choice) store (if choice then 8 else 4) := by
  cases choice
  · exact .intro (shortPrepares false) (.single <| .expression (.andFalse (.identifier .head .head)))
  · have leaf : LocalExpressionEvaluatesWithCost (shortPrepared true).inputs.names
        (shortPrepared true).inputs.environment store (ref "x") (.bool true) store 1 := .identifier .head .head
    exact .intro (shortPrepares true) (.single <| .expression (.andTrue leaf (.logicalNot (.logicalNot leaf))))

theorem equal_argument_types_do_not_equalize_costs_states_or_results (store : Core.Store) :
    [boolArg false].map (·.type) = [boolArg true].map (·.type) ∧
    (∀ choice, RuntimeFunctionEvaluatesWithCost (table .bool .bool) owner shortDeclaration [boolArg choice]
        store .bool (.bool choice) store (if choice then 8 else 4) ∧
      [boolArg choice].map (·.type) = shortCompiled.inputs.context.values.reverse ∧
      Core.Steps (if choice then 8 else 4) (Core.State.initial shortCompiled.core [.bool choice] store)
        (Core.State.final (.bool choice) store) ∧ ∀ fuel,
      (Core.runStateful fuel (Core.State.initial shortCompiled.core [.bool choice] store) =
        .done (.bool choice) store ↔ (if choice then 8 else 4) ≤ fuel) ∧
      ((∃ suspended, Core.runStateful fuel (Core.State.initial shortCompiled.core [.bool choice] store) =
        .outOfFuel suspended) ↔ fuel < (if choice then 8 else 4))) ∧
    runRuntimeFunction? (table .bool .bool) owner shortDeclaration [boolArg false] 5 store =
      some (.bool, .done (.bool false) store) ∧
    (∃ suspended, runRuntimeFunction? (table .bool .bool) owner shortDeclaration [boolArg true] 5 store =
      some (.bool, .outOfFuel suspended)) ∧
    runRuntimeFunction? (table .bool .bool) owner shortDeclaration [boolArg true] 8 store =
      some (.bool, .done (.bool true) store) := by
  refine ⟨rfl, ?_, (shortCost false store).run_done_iff.mpr (by decide),
    (shortCost true store).run_outOfFuel_iff.mpr (by decide), (shortCost true store).run_done_iff.mpr (by decide)⟩
  intro choice
  exact ⟨shortCost choice store, ((shortCost choice store).compiled_contract shortCompiles).1,
    (shortCost choice store).compiled_toSteps shortCompiles, fun _ =>
    ⟨(shortCost choice store).compiled_run_done_iff shortCompiles,
      (shortCost choice store).compiled_run_outOfFuel_iff shortCompiles⟩⟩

end Tests.FrontendCompiledExecution
