import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.RuntimeFunction
import Solcore.Core.ModularArithmetic
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.RuntimeApplicationFunction
import Solcore.Frontend.LocalApplication
import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Frontend.LocalComputation
import Solcore.Core.ExactFuelProperties
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.Safety
import Solcore.Frontend.TypedLetReturnBody

/-!
# Runtime function tests

Runtime functions: compilation, entries, the evaluator, applications, checkpoints, and compiled
execution and observations.
-/

section
-- leanmerge: from Solcore.Test.FrontendCompiledExecutionProperties
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
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩

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
  · exact TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)
  · exact TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier (.tail names_ne .head))
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
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.greater (.identifier (.tail names_ne .head)) (.identifier .head))
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
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩
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
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.logicalAnd (.identifier .head) (.logicalNot (.logicalNot (.identifier .head))))
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
  · exact .intro (shortPrepares false) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.andFalse (.identifier .head .head)))
  · have leaf : LocalExpressionEvaluatesWithCost (shortPrepared true).inputs.names
        (shortPrepared true).inputs.environment store (ref "x") (.bool true) store 1 := .identifier .head .head
    exact .intro (shortPrepares true) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.andTrue leaf (.logicalNot (.logicalNot leaf))))

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
end

section
-- leanmerge: from Solcore.Test.FrontendCompiledObservationProperties
/-! Independent compilation removes names, aliases, owners, ranges, and groups
from observations, but not ordered parameter types, actual values, or Core cost. -/

set_option autoImplicit false

namespace Tests.FrontendCompiledObservation

open Solcore Solcore.Frontend

private def owner (variant : Bool) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"Observation", by decide⟩], by decide⟩⟩, if variant then 19 else 0⟩
private def span (variant : Bool) : Syntax.SourceSpan :=
  ⟨⟨.main, if variant then "renamed.sol" else "original.sol"⟩, if variant then 30 else 0, 2⟩
private def name (variant : Bool) := if variant then "renamed" else "x"
private def typeName (variant : Bool) := if variant then "AmountAlias" else "Word"
private def table (variant : Bool) : TypeNameTable := [([typeName variant], .word)]
private def annotation (variant : Bool) (spelling : String) : Syntax.TypeExpr :=
  ⟨span variant, .named ⟨span variant, ⟨⟨⟨span variant, spelling⟩, []⟩⟩⟩ none⟩
private def parameter (variant : Bool) (spelling type : String) : Syntax.FunctionParameter :=
  ⟨span variant, .typed none ⟨span variant, spelling⟩ (annotation variant type)⟩
private def reference (variant : Bool) : Syntax.Expr := ⟨span variant, .identifier ⟨span variant, name variant⟩⟩
private def zero (variant : Bool) : Syntax.Expr := ⟨span variant, .literal ⟨span variant, .decimal "0"⟩⟩
private theorem zeroMeaning (variant : Bool) : WordLiteralDenotes ⟨span variant, .decimal "0"⟩ Core.Word.zero :=
  .decimal (by decide) (.cons (digit := 0) (.decimal (by decide) rfl) .nil)
private def added (variant : Bool) : Syntax.Expr :=
  ⟨span variant, .binary (reference variant) ⟨span variant, .add⟩ (zero variant)⟩
private def composite (variant : Bool) : Syntax.Expr :=
  ⟨span variant, .conditional ⟨span variant, .binary (added variant) ⟨span variant, .greater⟩ (zero variant)⟩
    (span variant) (reference variant) (span variant) (reference variant)⟩
private def source (variant : Bool) : Syntax.Expr :=
  if variant then ⟨span variant, .group ⟨span variant, .group (composite variant)⟩⟩ else composite variant
private def declaration (variant : Bool) (parameters : List Syntax.FunctionParameter) (body : Syntax.Expr) : Syntax.FunctionDecl :=
  ⟨span variant, ⟨⟨span variant, ⟨span variant, if variant then "otherFunction" else "function"⟩,
    none, ⟨span variant, parameters⟩, ⟨none, none⟩,
    some ⟨span variant, ⟨span variant, [annotation variant (typeName variant)]⟩⟩, none⟩,
    ⟨span variant, [⟨span variant, .returnStmt (some body)⟩]⟩⟩⟩
private def parameters (variant : Bool) := [parameter variant (name variant) (typeName variant)]
private def entry (variant : Bool) := declaration variant (parameters variant) (source variant)
private def staticInputs (variant : Bool) := LocalTypeInputs.empty.bindFresh (owner variant) (name variant) .word
private def core : Core.Expr := .ifE (.binary .wordGt (.binary .wordAdd (.var 0) (.word .zero)) (.word .zero)) (.var 0) (.var 0)
private def compiled (variant : Bool) : CompiledRuntimeFunction := ⟨staticInputs variant, core, .word⟩
private theorem header (variant : Bool) (parameters : List Syntax.FunctionParameter) (body : Syntax.Expr) :
    RuntimeFunctionHeader (table variant) (declaration variant parameters body).value.signature .word :=
  ⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩
private theorem declared (variant : Bool) : RuntimeParametersDeclare (table variant) (owner variant)
    (parameters variant) (staticInputs variant) :=
  .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil
private theorem compilation (variant : Bool) : RuntimeFunctionCompiles (table variant) (owner variant) (entry variant) (compiled variant) := by
  have base : ResolvesLocalExpression (staticInputs variant).names (composite variant)
      (.ifE (.binary .wordGt (.binary .wordAdd (.var ⟨owner variant, 0⟩) (.word .zero)) (.word .zero))
        (.var ⟨owner variant, 0⟩) (.var ⟨owner variant, 0⟩)) :=
    .conditional (.greater (.add (.identifier .head) (.wordLiteral (zeroMeaning variant)))
      (.wordLiteral (zeroMeaning variant))) (.identifier .head) (.identifier .head)
  refine ⟨header variant _ _, declared variant, TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression ?_
    (.ifE (.binary (.binary (.var .head) .word) .word) (.var .head) (.var .head))
    (.ifE (.binary (.binary (.var .head) .word) .word) (.var .head) (.var .head))⟩
  cases variant
  · exact base
  · exact .group (.group base)
private def argument (value : Core.Word) : TypedRuntimeArgument := ⟨.word, .word value, .word⟩

theorem renamed_aliased_grouped_owners_compile_independently :
    RuntimeFunctionCompiles (table false) (owner false) (entry false) (compiled false) ∧
    RuntimeFunctionCompiles (table true) (owner true) (entry true) (compiled true) ∧
    (compiled false).inputs.context.values = (compiled true).inputs.context.values ∧
    (compiled false).core = (compiled true).core ∧
    (compiled false).returnType = (compiled true).returnType ∧
    (compiled false).inputs.names ≠ (compiled true).inputs.names := by
  refine ⟨compilation false, compilation true, rfl, rfl,
    (compilation false).returnType_eq_of_same_core (compilation true) rfl rfl, ?_⟩
  intro same
  have spellings := congrArg (List.map Prod.fst) same
  change ["x"] = ["renamed"] at spellings
  exact (by decide : ["x"] ≠ ["renamed"]) spellings

theorem arbitrary_arguments_share_all_fuel_results_and_exact_costs
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (initialStore finalStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) :
    runRuntimeFunction? (table false) (owner false) (entry false) arguments fuel initialStore =
      runRuntimeFunction? (table true) (owner true) (entry true) arguments fuel initialStore ∧
    (RuntimeFunctionEvaluatesWithCost (table false) (owner false) (entry false) arguments
        initialStore type value finalStore cost ↔
      RuntimeFunctionEvaluatesWithCost (table true) (owner true) (entry true) arguments
        initialStore type value finalStore cost) :=
  ⟨(compilation false).run_eq_of_same_core (compilation true) rfl rfl arguments fuel initialStore,
    (compilation false).cost_iff_of_same_core (compilation true) rfl rfl⟩

private def prepared (value : Core.Word) : PreparedRuntimeFunction :=
  ⟨LocalInputs.empty.bindFresh (owner false) (name false) .word (.word value) .word, core, .word⟩
private theorem prepares (value : Core.Word) : RuntimeFunctionPrepares (table false) (owner false)
    (entry false) [argument value] (prepared value) :=
  ⟨(compilation false).header, .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil,
    (compilation false).body⟩
private theorem originalCost (value : Core.Word) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table false) (owner false) (entry false) [argument value]
      store .word (.word value) store 12 := by
  have leaf : LocalExpressionEvaluatesWithCost (prepared value).inputs.names (prepared value).inputs.environment
      store (reference false) (.word value) store 1 := .identifier .head .head
  have literal : LocalExpressionEvaluatesWithCost (prepared value).inputs.names (prepared value).inputs.environment
      store (zero false) (.word .zero) store 1 := .wordLiteral (zeroMeaning false)
  have sum : LocalExpressionEvaluatesWithCost (prepared value).inputs.names (prepared value).inputs.environment
      store (added false) (.word value) store 5 := by
    simpa [added] using
      (LocalExpressionEvaluatesWithCost.add (span := span false) (operatorSpan := span false)
        (leftValue := value) (rightValue := Core.Word.zero) (leftCost := 1) (rightCost := 1) leaf literal)
  have comparison : LocalExpressionEvaluatesWithCost (prepared value).inputs.names (prepared value).inputs.environment
      store ⟨span false, .binary (added false) ⟨span false, .greater⟩ (zero false)⟩
      (.bool (decide (value > Core.Word.zero))) store 9 :=
    .greater (leftValue := value) (rightValue := Core.Word.zero) (leftCost := 5) (rightCost := 1) sum literal
  apply RuntimeFunctionEvaluatesWithCost.intro (prepares value)
  apply TypedLetReturnBodyEvaluatesWithCost.returnTree
  apply TypedLetReturnBodyEvaluatesWithCost.terminal
  apply TerminalReturnTreeEvaluatesWithCost.single
  apply ReturnBodyEvaluatesWithCost.expression
  by_cases positive : value > Core.Word.zero
  · exact .ifTrue (by simpa only [positive, decide_true] using comparison) leaf
  · exact .ifFalse (by simpa only [positive, decide_false] using comparison) leaf

theorem composite_cost_transports_across_spelling_and_groups (value : Core.Word) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table false) (owner false) (entry false) [argument value]
      store .word (.word value) store 12 ∧
    RuntimeFunctionEvaluatesWithCost (table true) (owner true) (entry true) [argument value]
      store .word (.word value) store 12 ∧ ∀ fuel,
    (runRuntimeFunction? (table true) (owner true) (entry true) [argument value] fuel store =
      some (.word, .done (.word value) store) ↔ 12 ≤ fuel) ∧
    ((∃ suspended, runRuntimeFunction? (table true) (owner true) (entry true) [argument value] fuel store =
      some (.word, .outOfFuel suspended)) ↔ fuel < 12) := by
  have transported := ((compilation false).cost_iff_of_same_core (compilation true) rfl rfl).mp (originalCost value store)
  exact ⟨originalCost value store, transported, fun _ => ⟨transported.run_done_iff, transported.run_outOfFuel_iff⟩⟩

private theorem mismatch_rejects {types : TypeNameTable} {id : Resolved.DeclarationId}
    {decl : Syntax.FunctionDecl} {output : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types id decl output) (args : List TypedRuntimeArgument)
    (mismatch : args.map (·.type) ≠ output.inputs.context.values.reverse) (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? types id decl args fuel store = none := by
  rw [runRuntimeFunction?_factorization, compilation.complete]
  simp only [bind, Option.bind_some, if_neg mismatch]

private def guardTable : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def guardEntry (swapped : Bool) := declaration false
  [parameter false "a" (if swapped then "Bool" else "Word"),
   parameter false "b" (if swapped then "Word" else "Bool")] (zero false)
private def guardCompiled (swapped : Bool) : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh (owner false) "a" (if swapped then .bool else .word)).bindFresh
    (owner false) "b" (if swapped then .word else .bool), .word .zero, .word⟩
private theorem guardCompilation (swapped : Bool) :
    RuntimeFunctionCompiles guardTable (owner false) (guardEntry swapped) (guardCompiled swapped) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, ?_,
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.wordLiteral (zeroMeaning false)) .word .word⟩
  cases swapped
  · exact .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named (.tail (by decide) .head)) (by change "b" ∉ ["a"]; decide) .nil)
  · exact .cons (.named (.tail (by decide) .head)) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "b" ∉ ["a"]; decide) .nil)
private def emptyEntry := declaration false [] (zero false)
private def emptyCompiled : CompiledRuntimeFunction := ⟨LocalTypeInputs.empty, .word .zero, .word⟩
private theorem emptyCompilation : RuntimeFunctionCompiles guardTable (owner false) emptyEntry emptyCompiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, .nil,
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.wordLiteral (zeroMeaning false)) .word .word⟩
private def guardedArguments (value : Core.Word) : List TypedRuntimeArgument :=
  [argument value, ⟨.bool, .bool false, .bool⟩]

theorem identical_core_does_not_remove_ordered_context_and_arity_guards
    (value : Core.Word) (store : Core.Store) :
    (guardCompiled false).core = (guardCompiled true).core ∧
    (guardCompiled false).core = emptyCompiled.core ∧
    (guardCompiled false).inputs.context.values ≠ (guardCompiled true).inputs.context.values ∧
    (guardCompiled false).inputs.context.values ≠ emptyCompiled.inputs.context.values ∧
    runRuntimeFunction? guardTable (owner false) (guardEntry false) (guardedArguments value) 1 store =
      some (.word, .done (.word .zero) store) ∧
    runRuntimeFunction? guardTable (owner false) emptyEntry [] 1 store = some (.word, .done (.word .zero) store) ∧
    ∀ fuel, runRuntimeFunction? guardTable (owner false) (guardEntry true) (guardedArguments value) fuel store = none ∧
      runRuntimeFunction? guardTable (owner false) emptyEntry (guardedArguments value) fuel store = none := by
  refine ⟨rfl, rfl, by decide, by decide,
    (guardCompilation false).run_eq (guardedArguments value) rfl 1 store,
    emptyCompilation.run_eq [] rfl 1 store, ?_⟩
  intro fuel
  exact ⟨mismatch_rejects (guardCompilation true) (guardedArguments value)
      (by change [Core.Ty.word, .bool] ≠ [.bool, .word]; decide) fuel store,
    mismatch_rejects emptyCompilation (guardedArguments value)
      (by change [Core.Ty.word, .bool] ≠ []; decide) fuel store⟩

private def simpleEntry (addition : Bool) :=
  declaration false (parameters false) (if addition then added false else reference false)
private def simpleCompiled (addition : Bool) : CompiledRuntimeFunction :=
  ⟨staticInputs false, if addition then .binary .wordAdd (.var 0) (.word .zero) else .var 0, .word⟩
private theorem simpleCompilation (addition : Bool) : RuntimeFunctionCompiles (table false) (owner false)
    (simpleEntry addition) (simpleCompiled addition) := by
  refine ⟨header false _ _, declared false, ?_⟩
  cases addition
  · exact TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)
  · exact TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.add (.identifier .head) (.wordLiteral (zeroMeaning false)))
      (.binary (.var .head) .word) (.binary (.var .head) .word)

theorem equal_eventual_values_do_not_preserve_exact_core_or_fuel
    (value : Core.Word) (store : Core.Store) :
    (simpleCompiled false).inputs.context.values = (simpleCompiled true).inputs.context.values ∧
    (simpleCompiled false).core ≠ (simpleCompiled true).core ∧
    runRuntimeFunction? (table false) (owner false) (simpleEntry false) [argument value] 1 store =
      some (.word, .done (.word value) store) ∧
    runRuntimeFunction? (table false) (owner false) (simpleEntry true) [argument value] 4 store =
      some (.word, .outOfFuel ⟨.ret (.word .zero), [.binaryApply .wordAdd (.word value)], store⟩) ∧
    runRuntimeFunction? (table false) (owner false) (simpleEntry true) [argument value] 5 store =
      some (.word, .done (.word value) store) := by
  refine ⟨rfl, (by intro same; cases same), (simpleCompilation false).run_eq _ rfl 1 store,
    (simpleCompilation true).run_eq _ rfl 4 store, ?_⟩
  have result := (simpleCompilation true).run_eq [argument value] rfl 5 store
  change runRuntimeFunction? _ _ _ _ _ _ = some (.word, .done (.word (value.add Core.Word.zero)) store) at result
  simpa only [Core.Word.add_zero] using result

theorem equal_argument_types_do_not_replace_shared_values
    (left right : Core.Word) (different : left ≠ right) (store : Core.Store) :
    [argument left].map (·.type) = [argument right].map (·.type) ∧
    runRuntimeFunction? (table false) (owner false) (simpleEntry false) [argument left] 1 store ≠
      runRuntimeFunction? (table false) (owner false) (simpleEntry false) [argument right] 1 store := by
  refine ⟨rfl, ?_⟩
  rw [(simpleCompilation false).run_eq [argument left] rfl 1 store,
    (simpleCompilation false).run_eq [argument right] rfl 1 store]
  change some (Core.Ty.word, Core.StatefulRunResult.done (.word left) store) ≠
    some (.word, .done (.word right) store)
  intro same
  exact different (Core.Value.word.inj (Core.StatefulRunResult.done.inj (Prod.mk.inj (Option.some.inj same)).2).1)

end Tests.FrontendCompiledObservation
end

section
-- leanmerge: from Solcore.Test.FrontendParsedCompiledObservations
/-! Independently parsed declarations share observations through their actual
ordered type contexts and exact Core trees, not their names or eventual values.
Every expected execution uses the supplied values and an unchanged Core machine. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? (path content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, path⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{path}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{path}: parser invariant {reprStr error}")

private def leftOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ObservationLeft", by decide⟩], by decide⟩⟩, 1⟩
private def rightOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ObservationRight", by decide⟩], by decide⟩⟩, 9⟩
private def leftTypes : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def rightTypes : TypeNameTable :=
  [(["Truth"], .bool), (["Number"], .word), (["Proc"], .function .bool .bool), (["Ref"], .cell .word)]
private def word (value : Nat) := Core.Word.ofNatModulo value
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word value), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def cellArg (address : Nat) : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word address, .cellRef⟩
private def closureArg : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
private def store : Core.Store := [.word (word 91), .bool false]

private structure CompiledCase where
  types : TypeNameTable
  owner : Resolved.DeclarationId
  declaration : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction

private def compileCase (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (path content : String) : IO CompiledCase := do
  let some declaration ← parsed? path content | throw (IO.userError s!"{content}: incomplete declaration")
  let some compiled := compileRuntimeFunction? types owner declaration
    | throw (IO.userError s!"{content}: compilation failed")
  assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some compiled.returnType))
    s!"{content}: actual compiled Core failed typing"
  return ⟨types, owner, declaration, compiled⟩

private def runCase (entry : CompiledCase) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (initialStore : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) :=
  runRuntimeFunction? entry.types entry.owner entry.declaration arguments fuel initialStore

private def pair (leftSource rightSource : String) (parameterTypes : List Core.Ty)
    (expectedCore : Core.Expr) (expectedType : Core.Ty) : IO (CompiledCase × CompiledCase) := do
  let left ← compileCase leftTypes leftOwner "observations-left.sol" leftSource
  let right ← compileCase rightTypes rightOwner "observations-right.sol" ("\n/* renamed */\n" ++ rightSource)
  assertTrue (decide (left.compiled.inputs.context.values = right.compiled.inputs.context.values ∧
    left.compiled.core = right.compiled.core)) "independent compilations do not meet observation premises"
  assertTrue (decide (left.compiled.returnType = right.compiled.returnType))
    "independently inferred return types differ"
  assertTrue (decide (left.compiled.core = expectedCore ∧ left.compiled.returnType = expectedType ∧
    left.compiled.inputs.context.values = parameterTypes.reverse)) "wrong expected exact compiled output"
  assertTrue (decide (left.owner ≠ right.owner ∧ left.declaration.span ≠ right.declaration.span ∧
    left.declaration.value.signature.name.value ≠ right.declaration.value.signature.name.value))
    "renaming/range fixtures accidentally coincide"
  unless parameterTypes.isEmpty do
    assertTrue (decide (left.compiled.inputs.names ≠ right.compiled.inputs.names ∧
      left.compiled.inputs.context.ids ≠ right.compiled.inputs.context.ids))
      "identity-bearing tables should not be equal"
  return (left, right)

private def compareFuels (left right : CompiledCase) (arguments : List TypedRuntimeArgument)
    (limit : Nat) (initialStore : Core.Store) : IO Unit := do
  for fuel in List.range limit do
    let expected := if arguments.map (·.type) = left.compiled.inputs.context.values.reverse then
      some (left.compiled.returnType, Core.runStateful fuel
        (Core.State.initial left.compiled.core (arguments.reverse.map (·.value)) initialStore))
      else none
    assertTrue (decide (runCase left arguments fuel initialStore = expected ∧
      runCase right arguments fuel initialStore = expected))
      s!"same compiled observation changed at fuel {fuel}"

private def completedPair (left right : CompiledCase) (arguments : List TypedRuntimeArgument)
    (value : Core.Value) (cost : Nat) (initialStore : Core.Store := store) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) = left.compiled.inputs.context.values.reverse))
    "completion fixture failed the argument guard"
  compareFuels left right arguments (cost + 3) initialStore
  for entry in [left, right] do
    assertTrue (decide (runCase entry arguments 0 initialStore = some (entry.compiled.returnType,
      .outOfFuel (Core.State.initial entry.compiled.core (arguments.reverse.map (·.value)) initialStore))))
      "wrong exact initial state"
    assertTrue (match runCase entry arguments (cost - 1) initialStore with
      | some (_, .outOfFuel _) => true | _ => false) "completed below the expected cost"
    for fuel in [cost, cost + 2] do
      assertTrue (decide (runCase entry arguments fuel initialStore =
        some (entry.compiled.returnType, .done value initialStore))) "wrong result or completion boundary"

private def rejectedPair (left right : CompiledCase) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ left.compiled.inputs.context.values.reverse))
    "rejection fixture passed the argument guard"
  compareFuels left right arguments 20 store

/-- All 29 ordered pairs are compiled twice with different spellings and
owners; unequal source-position values expose subtraction/order mistakes. -/
private def compositePairs : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let leftParameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    let rightParameters := String.intercalate ", " (indices.map fun index => s!"q{index}: Number")
    for first in indices do
      for second in indices do
        let leftVar := Core.Expr.var (arity - 1 - first)
        let rightVar := Core.Expr.var (arity - 1 - second)
        let core := Core.Expr.ifE (.binary .wordGt (.binary .wordMul leftVar rightVar) rightVar)
          (.binary .wordSub leftVar rightVar) leftVar
        let (left, right) ← pair
          (s!"function original({leftParameters}) returns (Word)"
            ++ " { return " ++ s!"p{first} * p{second} > p{second} ? p{first} - p{second} : p{first};" ++ " }")
          (s!"function renamed({rightParameters}) returns (Number)"
            ++ " { return " ++ s!"(((q{first}) * (q{second})) > (q{second})) ? ((q{first}) - (q{second})) : ((q{first}));" ++ " }")
          (List.replicate arity .word) core .word
        for nonzero in [false, true] do
          let valueAt := fun index => if nonzero then 7 + 3 * index else 0
          let arguments := indices.map fun index => wordArg (valueAt index)
          let leftWord := word (valueAt first)
          let rightWord := word (valueAt second)
          let selected := decide (leftWord.mul rightWord > rightWord)
          completedPair left right arguments
            (.word (if selected then leftWord.sub rightWord else leftWord)) (if selected then 16 else 12)
        for arguments in [[], [boolArg false], indices.map (fun _ => boolArg true),
            (indices.map fun index => wordArg index) ++ [wordArg 0]] do
          rejectedPair left right arguments

private def necessaryPremises : IO Unit := do
  let left ← compileCase leftTypes leftOwner "unused-left.sol"
    "function unused(a: Word, b: Bool) { return; }"
  let right ← compileCase rightTypes rightOwner "unused-right.sol"
    "function reordered(u: Truth, v: Number) { return; }"
  let fewer ← compileCase rightTypes rightOwner "fewer.sol" "function fewer(u: Number) { return; }"
  assertTrue (decide (left.compiled.core = right.compiled.core ∧ left.compiled.core = fewer.compiled.core ∧
    left.compiled.returnType = right.compiled.returnType ∧ left.compiled.returnType = fewer.compiled.returnType ∧
    left.compiled.inputs.context.values ≠ right.compiled.inputs.context.values ∧
    left.compiled.inputs.context.values ≠ fewer.compiled.inputs.context.values)) "missing context counterexample"
  for fuel in List.range 10 do
    assertTrue (decide (runCase right [wordArg 7, boolArg false] fuel store = none ∧
      runCase fewer [wordArg 7, boolArg false] fuel store = none ∧
      runCase left [wordArg 7] fuel store = none)) "wrong type order or arity was accepted"
  assertTrue (decide (runCase left [wordArg 7, boolArg false] 1 store = some (.unit, .done .unit store) ∧
    runCase fewer [wordArg 7] 1 store = some (.unit, .done .unit store) ∧
    runCase right [boolArg false, wordArg 7] 1 store = some (.unit, .done .unit store)))
    "same Core did not retain its distinct argument guard"
  let direct ← compileCase leftTypes leftOwner "direct.sol"
    "function direct(a: Word) returns (Word) { return a; }"
  let added ← compileCase rightTypes rightOwner "added.sol"
    "function added(u: Number) returns (Number) { return u + 0; }"
  assertTrue (decide (direct.compiled.inputs.context.values = added.compiled.inputs.context.values ∧
    direct.compiled.returnType = added.compiled.returnType ∧ direct.compiled.core ≠ added.compiled.core))
    "algebraic equality was mistaken for exact Core equality"
  assertTrue (decide (runCase direct [wordArg 7] 5 store = some (.word, .done (.word (word 7)) store) ∧
    runCase added [wordArg 7] 5 store = some (.word, .done (.word (word 7)) store) ∧
    runCase direct [wordArg 7] 1 store = some (.word, .done (.word (word 7)) store) ∧
    runCase added [wordArg 7] 4 store = some (.word, .outOfFuel
      ⟨.ret (.word .zero), [.binaryApply .wordAdd (.word (word 7))], store⟩) ∧
    runCase direct [wordArg 7] 0 store ≠ runCase added [wordArg 7] 0 store))
    "equal eventual values erased the exact cost or suspended-state difference"
  assertTrue (decide (([wordArg 7].map (·.type)) = [wordArg 9].map (·.type) ∧
    runCase direct [wordArg 7] 0 store ≠ runCase direct [wordArg 9] 0 store ∧
    runCase direct [wordArg 7] 1 store ≠ runCase direct [wordArg 9] 1 store))
    "equal argument types erased actual values"

def frontendParsedCompiledObservationTests : IO Unit := do
  compositePairs
  for index in List.range 3 do
    let leftName := ["a", "b", "c"][index]!
    let rightName := ["x", "y", "z"][index]!
    let (left, right) ← pair
      ("function select(a: Bool, b: Bool, c: Bool) returns (Bool) { return " ++ leftName ++ "; }")
      ("function choose(x: Truth, y: Truth, z: Truth) returns (Truth) { return ((" ++ rightName ++ ")); }")
      [.bool, .bool, .bool] (.var (2 - index)) .bool
    for a in [false, true] do
      for b in [false, true] do
        for c in [false, true] do
          completedPair left right [boolArg a, boolArg b, boolArg c] (.bool ([a, b, c][index]!)) 1
    for arguments in [[], [boolArg false], [boolArg true, wordArg 7, boolArg false]] do
      rejectedPair left right arguments
  let (shortLeft, shortRight) ← pair
    "function short(c: Bool) returns (Bool) { return c && !c; }"
    "function renamedShort(flag: Truth) returns (Truth) { return (flag) && (!(flag)); }"
    [.bool] (.ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false)) .bool
  for choice in [false, true] do
    completedPair shortLeft shortRight [boolArg choice] (.bool false) (if choice then 6 else 4)
  assertTrue (decide (runCase shortLeft [boolArg false] 5 store = some (.bool, .done (.bool false) store)))
    "short-circuit false path did not finish"
  assertTrue (match runCase shortRight [boolArg true] 5 store with
    | some (.bool, .outOfFuel _) => true | _ => false) "different actual values erased selected-path cost"
  for (leftType, rightType, type, arguments) in
      [("Cell", "Ref", Core.Ty.cell .word, [cellArg 40, cellArg 91]),
       ("Fn", "Proc", Core.Ty.function .bool .bool, [closureArg])] do
    let (left, right) ← pair
      (s!"function identity(a: {leftType}) returns ({leftType})" ++ " { return a; }")
      (s!"function renamedIdentity(value: {rightType}) returns ({rightType})" ++ " { return (((value))); }")
      [type] (.var 0) type
    for argument in arguments do
      completedPair left right [argument] argument.value 1 []
    for wrong in [[], [boolArg false], arguments ++ arguments] do
      rejectedPair left right wrong
  necessaryPremises
  for content in ["", "function incomplete()", "function f() { return;", "function f() { return; } trailing"] do
    assertTrue (← parsed? "incomplete-observation.sol" content).isNone "incomplete input entered observation tests"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedFunctionCheckpointWorlds
/-! Original preparation, literal source costs and separate Core paths precede
function checkpoint safety. Actual aliased captures share one supplied world.
The typed caller itself allocates/writes and returns a different result type. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedFunctionCheckpointWorlds
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"FunctionCheckpointWorlds",by decide⟩],by decide⟩⟩,142⟩
private def types : TypeNameTable := [(["Word"],.word),(["Word"],.bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def fBody : Core.Expr := .letE (.newCell .word (.var 0)) (.binary .wordAdd (.loadCell (.var 2)) (.word (Core.Word.ofNatModulo 1)))
private def allocator (l m : Nat) : Core.Value := .closure .word .word fBody [.cellRef .word l,reader m]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def second : Core.Expr := .letE (.apply (.var 4) (.var 1)) (.var 0)
private def first : Core.Expr := .letE (.apply (.var 2) (.var 0)) second
private def core : Core.Expr := .letE (.apply (.var 2) (.var 0)) first
private def caller : Core.Expr := .letE (.storeCell (.var 1) (.word (Core.Word.ofNatModulo 7))) (.loadCell (.var 1))
private def pending : List Core.Frame := [.newCellApply .word,.letBody caller [.cellRef .word 0],.pairApply (.bool true)]
private theorem pendingTyped : Core.ContinuationHasType [.word,.word] pending .word (.product .bool .word) :=
  .cons .newCellApply (.cons (.letBody (.cons (.cellRef rfl) .nil)
    (.letE (.storeCell (.var rfl) .word) (.loadCell (.var rfl)))) (.cons (.pairApply .bool) .nil))
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function checkpoint(f:function(Word) returns(Word),g:function(Word) returns(Word),x:Word) returns(Word){let x:Word=f(x);g(x);let x=f(x);return x;}"
  let file : Syntax.SourceFile := ⟨⟨.main,"function-checkpoint-worlds.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original source and range"
  return source
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "original named leaf")
  | ⟨_,.tuple [a]⟩ => let x ← meaning a; return ⟨x.1,⟨by rw [shape]; exact .single x.2.down⟩⟩
  | ⟨_,.function _ ⟨_,[a]⟩ (some ⟨span,results⟩)⟩ => let x ← meaning a; let y ← meaning ⟨span,.tuple results⟩; return ⟨.function x.1 y.1,⟨by rw [shape]; exact .functionReturns x.2.down y.2.down⟩⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf e
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
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.core (r.core.weakenAt 0),r.type,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.head?=some ⟨owner,i.bindings.length⟩ ∧ i.names.lookup? "x"=some ⟨owner,if i.bindings.length=3 then 2 else 3⟩)) "fresh3/4 retains original x2/3; discard creates no source ID"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | _ => throw (IO.userError "original body")
termination_by sizeOf b
private def bind (i : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Σ o, PLift (RuntimeParametersBindFrom types owner i ps args o)) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨i,⟨by rw [shape,supplied]; exact .nil⟩⟩
  | ⟨_,.typed none name annotation⟩::rest,arg::tail =>
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ i.names.map Prod.fst then
          let r ← bind (i.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨r.1,⟨by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused r.2.down⟩⟩
        else throw (IO.userError "duplicate actual binding")
      else throw (IO.userError "ordered actual type")
  | _,_ => throw (IO.userError "actual arity")
private structure Preparation (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RecursiveComputationFunctionPrepares types owner source args ⟨inputs,core,.word⟩
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Preparation source args) := do
  let rows ← bind .empty source.value.signature.parameters.elements args; let b ← body rows.1.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core ∧ b.type=.word then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have _ := rows.2.down.erase_values
          return ⟨rows.1,⟨h,rows.2.down,by simpa only [same.2.1,same.2.2] using b.evidence⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core and original return annotation")
  | _ => throw (IO.userError "outer return")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .word w => return ⟨.word w,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell found) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.word word) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l, written : s.write? l (.word word) with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons .word (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual caller missing write")
      | _ => throw (IO.userError "manual caller reference")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match found : s.read? l, written : s.write? l v with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual missing write")
      | _,_ => throw (IO.userError "manual write reference")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩ | none => throw (IO.userError "manual binary payload")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
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
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence⟩
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private def arguments (f g : Core.Value) : IO (List TypedRuntimeArgument) :=
  [f,g,w 14].mapM fun v => do
    match built : buildRuntimeArgument? v with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=v ∧ a.type=v.type)) "literal supplied values and captures"; return a
    | none => throw (IO.userError "structural actual argument")
private theorem storeWorld {world : Core.StoreTyping} {store : Core.Store}
    (typed : Core.RuntimeStoreHasTypes world store) : world=store.map Core.Value.type :=
  typed.world_eq
private def verify (l m a r : Nat) : IO Unit := do
  let f := allocator l m; let g := writer m; let s := [w 41,w 99]; let env : Core.Environment := [w 14,g,f]
  let allocated := s++[w 14]; let written := if m=0 then [w a,w 99,w 14] else [w 41,w a,w 14]
  let bodyStore := written++[w a]; let callerStore := bodyStore++[w r]; let finalStore := w 7::callerStore.tail
  let source ← parsed; let args ← arguments f g; let p ← prepare source args
  let manual ← path 80 core env s; let extra ← path 30 caller [.cellRef .word 4,.cellRef .word 0] callerStore
  let raw ← rawBody p.inputs.names p.inputs.environment s source.value.body
  if fixed : p.inputs.environment.values=env ∧ manual.value=w r ∧ manual.final=bodyStore ∧ manual.cost=56 ∧
      raw.value=w r ∧ raw.final=bodyStore ∧ raw.cost=56 ∧ extra.value=w r ∧ extra.final=finalStore ∧ extra.cost=10 then
    have ⟨ev,mv,ms,mc,rv,rs,rc,xv,xs,xc⟩ := fixed
    have literal (k) : Core.Steps 56 ⟨.eval core env,k,s⟩ ⟨.ret (w r),k,bodyStore⟩ := by simpa only [mv,ms,mc] using manual.evidence k
    have counted : RecursiveComputationReturnTreeEvaluatesWithCost owner p.inputs.names p.inputs.environment s source.value.body (w r) bodyStore 56 := by simpa only [rv,rs,rc] using raw.evidence
    have sourcePath (k) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using counted) p.evidence.body (by simpa only [LocalInputs.toTypeInputs_context] using p.inputs.sameIds) k
    have aligned (k) : Core.Steps 56 ⟨.eval core p.inputs.environment.values,k,s⟩ ⟨.ret (w r),k,bodyStore⟩ := by rw [ev]; exact literal k
    have _ := (sourcePath []).final_unique (aligned [])
    have finishing : Core.Steps 13 ⟨.ret (w r),pending,bodyStore⟩ (.final (.pair (.bool true) (w r)) finalStore) := by
      have path : Core.Steps 10 ⟨.eval caller [.cellRef .word 4,.cellRef .word 0],[.pairApply (.bool true)],callerStore⟩ ⟨.ret (w r),[.pairApply (.bool true)],finalStore⟩ := by simpa only [xv,xs,xc] using extra.evidence [.pairApply (.bool true)]
      have length : bodyStore.length=4 := by simp [bodyStore,written]; split <;> rfl
      have staged : Core.Steps 11 ⟨.eval caller [.cellRef .word bodyStore.length,.cellRef .word 0],[.pairApply (.bool true)],callerStore⟩ (.final (.pair (.bool true) (w r)) finalStore) := by simpa only [length,Core.State.final,Nat.reduceAdd] using path.trans (.cons .applyPair .refl)
      exact .cons .applyNewCell (.cons .bindLet staged)
    let start : Core.State := ⟨.eval core env,pending,s⟩
    have whole : Core.Steps 69 start (.final (.pair (.bool true) (w r)) finalStore) := (literal pending).trans finishing
    if validated : validateRuntimeInputs [.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have safe := p.evidence.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType runtime.1 runtime.2 pendingTyped
      have exactSafe : Core.StateHasType start (.product .bool .word) ∧
          (∀ fuel error state, Core.runStateful fuel start≠.fault error state) ∧
          ∀ {fuel cp}, Core.runStateful fuel start=.outOfFuel cp → Core.StateHasType cp (.product .bool .word) ∧
            ∀ more error state, Core.runStateful more cp≠.fault error state := by simpa only [ev] using safe
      for fuel in List.range 71 do
        check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "original prepared runner remains separate from typed caller"
        match exhausted : Core.runStateful fuel start with
        | .done v t => check (decide (69≤fuel ∧ v=.pair (.bool true) (w r) ∧ t=finalStore)) "caller returns Bool times Word after its own effects"
        | .fault error state => False.elim (exactSafe.2.1 fuel error state exhausted)
        | .outOfFuel cp =>
            have _ := exactSafe.2.2 exhausted
            have saved := p.evidence.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType runtime.1 runtime.2 pendingTyped (by simpa only [ev] using exhausted)
            have terminal : ∃ savedWorld future, Core.WorldExtends [.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧
                Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future finalStore ∧ future[0]?=some .word := by
              obtain ⟨savedWorld,ext,stored,further⟩ := saved
              obtain ⟨future,growth,typed⟩ := further (whole.residual_of_outOfFuel exhausted).2
              exact ⟨savedWorld,future,ext,stored,growth,typed,(ext.trans growth).lookup rfl⟩
            have _ := terminal
            check (decide (fuel<69 ∧ Core.runStateful (69-fuel) cp=.done (.pair (.bool true) (w r)) finalStore)) "all genuine saved states complete from actual stored state"
            for more in [0,1,13,69] do
              have _ := Core.runStateful_resume exhausted more
              check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) start)) "full resumption, not re-preparation"
              match again : Core.runStateful more cp with
              | .outOfFuel next =>
                  have chain : ∃ savedWorld future, Core.WorldExtends [.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future next.store := by
                    obtain ⟨savedWorld,ext,stored,further⟩ := saved
                    obtain ⟨future,growth,typed⟩ := further (Core.runStateful_outOfFuel_sound again).1
                    exact ⟨savedWorld,future,ext,stored,growth,typed⟩
                  have _ := chain
              | .done _ _ => pure ()
              | .fault error state => False.elim ((exactSafe.2.2 exhausted).2 more error state again)
      let xenv := w a::env; let hidden := w a::xenv
      let cpA : Core.State := ⟨.ret (.cellRef .word 2),.letBody (.binary .wordAdd (.loadCell (.var 2)) (.word (Core.Word.ofNatModulo 1))) [w 14,.cellRef .word l,reader m]::.letBody first env::pending,allocated⟩
      let cpW : Core.State := ⟨.ret .unit,.letBody (.loadCell (.var 2)) [w a,.cellRef .word m]::.letBody second xenv::pending,written⟩
      let cpB : Core.State := ⟨.ret (.cellRef .word 3),.letBody (.binary .wordAdd (.loadCell (.var 2)) (.word (Core.Word.ofNatModulo 1))) [w a,.cellRef .word l,reader m]::.letBody (.var 0) hidden::pending,bodyStore⟩
      let cpC : Core.State := ⟨.ret (.cellRef .word 4),[.letBody caller [.cellRef .word 0],.pairApply (.bool true)],callerStore⟩
      let cpD : Core.State := ⟨.ret .unit,[.letBody (.loadCell (.var 1)) [.cellRef .word 4,.cellRef .word 0],.pairApply (.bool true)],finalStore⟩
      for (spent,cp) in [(10,cpA),(31,cpW),(46,cpB),(56,⟨.ret (w r),pending,bodyStore⟩),(57,cpC),(64,cpD)] do
        if exhausted : Core.runStateful spent start=.outOfFuel cp then
          have actualWorld : Core.WorldExtends [.word,.word] (cp.store.map Core.Value.type) ∧ Core.RuntimeStoreHasTypes (cp.store.map Core.Value.type) cp.store := by
            obtain ⟨world,ext,typed,_⟩ := p.evidence.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType runtime.1 runtime.2 pendingTyped (by simpa only [ev] using exhausted)
            simpa only [storeWorld typed] using And.intro ext typed
          have _ := actualWorld
          check (decide (Core.runStateful (69-spent) cp=.done (.pair (.bool true) (w r)) finalStore)) "literal original captures, discard slot and caller frames"
        else throw (IO.userError "literal checkpoint")
      if links : Core.runStateful 10 start=.outOfFuel cpA ∧ Core.runStateful 21 cpA=.outOfFuel cpW ∧ Core.runStateful 15 cpW=.outOfFuel cpB ∧ Core.runStateful 11 cpB=.outOfFuel cpC ∧ Core.runStateful 7 cpC=.outOfFuel cpD then
        have worlds : Core.WorldExtends [.word,.word] [.word,.word,.word] ∧ Core.RuntimeStoreHasTypes [.word,.word,.word] cpA.store ∧ Core.RuntimeStoreHasTypes [.word,.word,.word] cpW.store ∧
            Core.RuntimeStoreHasTypes [.word,.word,.word,.word] cpB.store ∧ Core.WorldExtends [.word,.word,.word] [.word,.word,.word,.word,.word] ∧ Core.RuntimeStoreHasTypes [.word,.word,.word,.word,.word] cpC.store ∧ Core.RuntimeStoreHasTypes [.word,.word,.word,.word,.word] cpD.store := by
          obtain ⟨world,ext,stored,further⟩ := p.evidence.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType runtime.1 runtime.2 pendingTyped (by simpa only [ev] using links.1)
          have initialWorld : world=[.word,.word,.word] := storeWorld stored
          subst world
          have aw := (Core.runStateful_outOfFuel_sound links.2.1).1
          have ab := aw.trans (Core.runStateful_outOfFuel_sound links.2.2.1).1
          have ac := ab.trans (Core.runStateful_outOfFuel_sound links.2.2.2.1).1
          have ad := ac.trans (Core.runStateful_outOfFuel_sound links.2.2.2.2).1
          obtain ⟨_,_,tw⟩ := further aw; obtain ⟨_,_,tb⟩ := further ab; obtain ⟨future,growth,tc⟩ := further ac; obtain ⟨_,_,td⟩ := further ad
          rw [storeWorld tc] at growth
          rw [storeWorld stored] at stored; rw [storeWorld tw] at tw; rw [storeWorld tb] at tb; rw [storeWorld tc] at tc; rw [storeWorld td] at td
          by_cases same : m=0
          all_goals simp [cpW,cpB,cpC,cpD,finalStore,callerStore,bodyStore,written,same,w,Core.Value.type] at tw tb tc td growth ⊢
          all_goals exact ⟨ext,stored,tw,tb,growth,tc,td⟩
        have _ := worlds
      else throw (IO.userError "independent further paths 21/15/11/7")
    else throw (IO.userError "actual argument/capture/store common world")
  else throw (IO.userError "independent original raw56/Core56/caller10 expectations")
end ParsedFunctionCheckpointWorlds
open ParsedFunctionCheckpointWorlds in
def frontendParsedFunctionCheckpointWorldTests : IO Unit := do
  for (l,m,a,r) in [(0,0,42,43),(1,0,100,100),(1,1,100,101)] do verify l m a r
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeApplicationCompilation
/-! Value-free original declarations establish their own compilation evidence.
Only the separate Unit/Word smoke supplies actual arguments; nominal types do not. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeApplicationCompilation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"CompileApplication", by decide⟩], by decide⟩⟩, n⟩
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def standard := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def parsed (text : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "compile-application.sol"⟩, text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing failed")
  let .ok source next := Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError s!"original declaration did not parse: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) s!"original full declaration range changed: {text}"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "original annotation missing")
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [original]; exact .unit⟩
  | ⟨_, .tuple [single]⟩ =>
      let m ← meaning types single
      return ⟨m.type, by rw [original]; exact .single m.evidence⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let a ← meaning types left; let b ← meaning types right
      return ⟨.product a.type b.type, by rw [original]; exact .pair a.evidence b.evidence⟩
  | _ => throw (IO.userError "outside independent annotation fixture")
termination_by sizeOf source
private structure Declared (types : TypeNameTable) (o : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types o initial params inputs
private def declare (types : TypeNameTable) (o : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (params : List Syntax.FunctionParameter) : IO (Declared types o initial params) := do
  match original : params with
  | [] => return ⟨initial, by rw [original]; exact .nil⟩
  | ⟨s, .typed none name annotation⟩ :: rest =>
      check (s.contains name.span && s.contains annotation.span) "original parameter fields changed"
      let m ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declare types o (initial.bindFresh o name.value m.type) rest
        return ⟨tail.inputs, by rw [original]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate original parameter")
  | _ => throw (IO.userError "outside declaration fixture")
private structure Header (types : TypeNameTable) (signature : Syntax.FunctionSignature) where
  type : Core.Ty
  evidence : RuntimeFunctionHeader types signature type
private def header (types : TypeNameTable) (signature : Syntax.FunctionSignature) : IO (Header types signature) := do
  if policy : signature.genericParameters = none ∧ signature.whereClause = none ∧
      signature.modifiers.publicMarker = none ∧ signature.modifiers.payableMarker = none then
    match clause : signature.returnsClause with
    | none => return ⟨.unit, ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, by rw [clause]; exact .absent⟩⟩
    | some ⟨_, ⟨_, [annotation]⟩⟩ =>
        let m ← meaning types annotation
        return ⟨m.type, ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, by rw [clause]; exact .single m.evidence⟩⟩
    | _ => throw (IO.userError "not absent or exactly one return annotation")
  else throw (IO.userError "unsupported original header")
private structure Reference (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.context.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def reference (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Reference s source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "original context row missing")
      | none => throw (IO.userError "original name missing")
  | _ => throw (IO.userError "not original identifier")
private structure Body (s : LocalTypeInputs) (body : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalApplicationReturnBodyElaborates s.names s.context body core type
private def body (s : LocalTypeInputs) (body : Syntax.Block) : IO (Body s body) := do
  match original : body with
  | ⟨bs, [⟨rs, .returnStmt (some ⟨span, .call callee ⟨argsSpan, [argument]⟩⟩)⟩]⟩ =>
      check (bs.contains rs && rs.contains span && span.contains callee.span && span.contains argsSpan &&
        argsSpan.contains argument.span && decide (callee.span.endByte ≤ argsSpan.startByte)) "original body/call spans changed"
      let f ← reference s callee; let a ← reference s argument
      match shape : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core, output, by
            rw [original]; exact .application (.call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing))⟩
          else throw (IO.userError "original argument type differs")
      | _ => throw (IO.userError "original callee is not Function")
  | _ => throw (IO.userError "not original singleton application return")
private def table (input output : Core.Ty) : TypeNameTable :=
  [(["F"], .function input output), (["mod", "F"], .function input output), (["A"], input), (["R"], output), (["Unit"], .unit)]
private def fields (c : CompiledRuntimeFunction) := (c.inputs.names, c.inputs.context, c.core, c.returnType)
private structure Ready (types : TypeNameTable) (o : Resolved.DeclarationId) where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  evidence : RuntimeApplicationFunctionCompiles types o source compiled
private def positive (input output : Core.Ty) (o : Resolved.DeclarationId) (text : String) : IO (Ready (table input output) o) := do
  let types := table input output; let source ← parsed text
  let ps ← declare types o .empty source.value.signature.parameters.elements
  let h ← header types source.value.signature; let b ← body ps.inputs source.value.body
  if expected : h.type = output ∧ b.type = output ∧ b.core = target then
    let compiled : CompiledRuntimeFunction := ⟨ps.inputs, target, output⟩
    have compilation : RuntimeApplicationFunctionCompiles types o source compiled :=
      ⟨by simpa only [compiled, expected.1] using h.evidence, ps.evidence,
        by simpa only [compiled, expected.2.1, expected.2.2] using b.evidence⟩
    let expectedInputs := (LocalTypeInputs.empty.bindFresh o "f" (.function input output)).bindFresh o "x" input
    let expectedRecord : CompiledRuntimeFunction := ⟨expectedInputs, target, output⟩
    check (decide (fields compiled = fields expectedRecord ∧
      (compileRuntimeApplicationFunction? types o source).map fields = some (fields expectedRecord) ∧
      compileRuntimeFunction? types o source = none)) "independent original static record/Core/type differs"
    have accepted := compilation.complete
    have _ := compileRuntimeApplicationFunction?_iff.mpr compilation
    have _ := compilation.result_unique (compileRuntimeApplicationFunction?_sound accepted)
    have _ := (compileRuntimeApplicationFunction?_iff.mp accepted).core_hasType
    let wrongCore : Core.Expr := .letE .unit (.apply (.var 2) (.var 1))
    have _ : Core.HasType expectedInputs.context.values wrongCore output := .letE .unit (.apply (.var rfl) (.var rfl))
    have exactSource : ¬ RuntimeApplicationFunctionCompiles types o source ⟨expectedInputs, wrongCore, output⟩ := by
      intro other
      have impossible := congrArg CompiledRuntimeFunction.core (compilation.result_unique other)
      cases impossible
    have _ := exactSource
    return ⟨source, compiled, compilation⟩
  else throw (IO.userError "independent body does not match declared result")
private def actualSmoke (argument : TypedRuntimeArgument) (o : Resolved.DeclarationId) : IO Unit := do
  let ready ← positive argument.type argument.type o standard
  let types := table argument.type argument.type
  let f : TypedRuntimeArgument := ⟨.function argument.type argument.type,
    .closure argument.type argument.type (.var 0) [], .closure .nil (.var rfl)⟩
  let args := [f, argument]
  if aligned : args.map (·.type) = ready.compiled.inputs.context.values.reverse then
    have _ := ready.evidence.prepare_arguments args aligned
    have _ := runtimeApplicationFunctionPrepares_toCompiled_iff.mpr ⟨ready.evidence, aligned⟩
    match accepted : prepareRuntimeApplicationFunction? types o ready.source args with
    | none => throw (IO.userError "matching real arguments did not prepare")
    | some prepared =>
        have preparation := prepareRuntimeApplicationFunction?_sound accepted
        have erased := preparation.compiles.result_unique ready.evidence
        have _ := runtimeApplicationFunctionPrepares_toCompiled_iff.mp ⟨prepared, preparation, erased⟩
        have _ := preparation.result_unique (prepareRuntimeApplicationFunction?_iff.mp preparation.complete)
        have _ := preparation.core_hasType
        check (decide (fields prepared.toCompiled = fields ready.compiled ∧ prepared.core = target ∧
          prepared.returnType = argument.type ∧ prepared.inputs.environment.values = [argument.value, f.value] ∧
          prepared.inputs.bindings.map (fun b => (b.name, b.id, b.type, b.value)) =
            [("x", ⟨o, 1⟩, argument.type, argument.value), ("f", ⟨o, 0⟩, f.type, f.value)])) "actual complete record/order changed"
        have manual (store k) : Core.Steps 6 ⟨.eval target (args.reverse.map (·.value)), k, store⟩ ⟨.ret argument.value, k, store⟩ :=
          .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (.cons (.var rfl) .refl)))))
        for store in [[], [.bool true]] do
          for fuel in List.range 9 do
            have _ := ready.evidence.run_eq args aligned fuel store
            have _ := preparation.run_eq_body fuel store
            have _ := (manual store []).runStateful_done_iff (fuel := fuel)
            check (decide (runRuntimeApplicationFunction? types o ready.source args fuel store =
              some (argument.type, Core.runStateful fuel (.initial target [argument.value, f.value] store)))) "compiled execution changed actual values/store"
            match result : runRuntimeApplicationFunction? types o ready.source args fuel store with
            | some (_, .done v t) =>
                have _ := runRuntimeApplicationFunction?_eq_some_iff.mp result
                check (decide (6 ≤ fuel ∧ v = argument.value ∧ t = store)) "actual identity smoke differs"
            | some (_, .outOfFuel _) => check (decide (fuel < 6)) "actual smoke cost differs"
            | _ => throw (IO.userError "actual identity failed")
    for supplied in [args, [], [argument], args.reverse, args ++ [argument]] do
      have _ := prepareRuntimeApplicationFunction?_factorization types o ready.source supplied
      let projected := (prepareRuntimeApplicationFunction? types o ready.source supplied).map (fun p => fields p.toCompiled)
      check (decide (projected = if supplied.map (·.type) = args.map (·.type) then some (fields ready.compiled) else none)) "full Option or ordered type guard differs"
      have _ := prepareRuntimeApplicationFunction?_eq_none_iff (types := types) (owner := o) (declaration := ready.source) (arguments := supplied)
      have _ := runRuntimeApplicationFunction?_eq_none_iff (types := types) (owner := o) (declaration := ready.source) (arguments := supplied) 0 []
  else throw (IO.userError "original argument type ordering changed")
private def rejected (o : Resolved.DeclarationId) (text : String) (localSuccess : Bool)
    (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let types := table .word .word; let source ← parsed text location
  if localSuccess then
    let originalCaller := (LocalTypeInputs.empty.bindFresh o "f" (.function .word .word)).bindFresh o "x" .word
    let localBody ← body originalCaller source.value.body
    check (decide (localBody.core = target ∧ localBody.type = .word ∧ elaborateLocalApplicationReturnBody?
      originalCaller.names originalCaller.context source.value.body = some (target, .word))) "original body-only success was lost"
  if absent : compileRuntimeApplicationFunction? types o source = none then
    have _ := compileRuntimeApplicationFunction?_eq_none_iff.mp absent
    check ((compileRuntimeApplicationFunction? types o source).isNone) "whole rejection changed"
  else throw (IO.userError "invalid whole contract compiled")
end ParsedRuntimeApplicationCompilation
open ParsedRuntimeApplicationCompilation
def frontendParsedRuntimeApplicationCompilationTests : IO Unit := do
  let types : List Core.Ty := [.unit, .bool, .word, .cell .word, .product .word .unit,
    .namedData ⟨77⟩, .function (.namedData ⟨9⟩) (.namedData ⟨9⟩)]
  for o in [owner 0, owner 41] do
    for input in types do
      for output in types do
        let _ ← positive input output o standard
        let _ ← positive input output o "function invoke(f:mod.F,x:(A)) returns((R)){return f(x);}"
      let _ ← positive input .unit o "function invoke(f:F,x:A){return f(x);}"
      let _ ← positive input .unit o "function invoke(f:F,x:A) returns(()){return f(x);}"
    let _ ← positive (.product (.namedData ⟨1⟩) .unit) (.product (.namedData ⟨2⟩) .word) o
      "function invoke(f:F,x:A) returns(R){return f(x);}"
    let _ ← positive (.product .unit .unit) (.product .unit .unit) o
      "function invoke(f:F,x:((),())) returns(((),())){return f(x);}"
    let _ ← positive .unit .unit o "function invoke(f:F,x:()) returns(()){return f(x);}"
    actualSmoke ⟨.unit, .unit, .unit⟩ o
    actualSmoke ⟨.word, .word (Core.Word.ofNatModulo 14), .word⟩ o
    rejected o "function invoke(f:F,x:A) public returns(R){return f(x);}" true .contract
    rejected o "function invoke(f:F,x:A) payable returns(R){return f(x);}" true .contract
    for text in ["function invoke<T>(f:F,x:A) returns(R){return f(x);}",
        "function invoke(f:F,x:A) returns(R) where A: Eq {return f(x);}",
        "function invoke(f:F,x:A){return f(x);}", "function invoke(f:F,x:A) returns(Unit){return f(x);}",
        "function invoke(f:F,x:A) returns(){return f(x);}", "function invoke(f:F,x:A) returns(R,R){return f(x);}",
        "function invoke(f:F,x:A) returns(Missing){return f(x);}",
        "function invoke(comptime f:F,x:A) returns(R){return f(x);}",
        "function invoke(f:F,f:A) returns(R){return f(x);}", "function invoke(f:F,x:Missing) returns(R){return f(x);}"] do
      rejected o text true
    for text in ["function invoke(f:F,x:A) returns(R){return x;}",
        "function invoke(f:F,x:A) returns(R){return;}", "function invoke(f:F,x:A) returns(R){}",
        "function invoke(f:F,x:A) returns(R){return f(f(x));}",
        "function invoke(f:F,x:A) returns(R){return f(x);return x;}",
        "function invoke(f:F,x:A) returns(R){{return f(x);}}"] do rejected o text false
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeComputationCompilation
/-! Whole original declarations have independent annotation, parameter and body
certificates. The nominal matrix supplies no values; only two actual smokes run. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeComputationCompilation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"CompileMixed", by decide⟩], by decide⟩⟩, n⟩
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def text (body : String) := "function example(f:F,g:G,x:A) returns(R){" ++ body ++ "}"
private def parsed (text : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"compile-mixed.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing")
  let .ok source next := Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError s!"original declaration parse: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "whole original span"
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span &&
    decide (source.value.signature.span.endByte ≤ source.value.body.span.startByte)) "original header before body"
  return source
private structure Meaning (ts : TypeNameTable) (s : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes ts s type
private def meaning (ts : TypeNameTable) (s : Syntax.TypeExpr) : IO (Meaning ts s) := do
  match shape : s with
  | ⟨_,.named name none⟩ =>
      match found : ts.lookup? (qualifiedTypeNameKey name) with
      | some t => return ⟨t,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | _ => throw (IO.userError "missing annotation")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [a]⟩ => let m ← meaning ts a; return ⟨m.type,by rw [shape]; exact .single m.evidence⟩
  | ⟨_,.tuple [a,b]⟩ =>
      let x ← meaning ts a; let y ← meaning ts b
      return ⟨.product x.type y.type,by rw [shape]; exact .pair x.evidence y.evidence⟩
  | _ => throw (IO.userError "outside annotation fixture")
termination_by sizeOf s
private structure Declared (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (ps : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom ts o i ps inputs
private def declare (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (ps : List Syntax.FunctionParameter) : IO (Declared ts o i ps) := do
  match shape : ps with
  | [] => return ⟨i,by rw [shape]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest =>
      check (span.contains name.span && span.contains annotation.span && decide (name.span.endByte ≤ annotation.span.startByte)) "parameter original order"
      let m ← meaning ts annotation
      if unused : name.value ∉ i.names.map Prod.fst then
        let tail ← declare ts o (i.bindFresh o name.value m.type) rest
        return ⟨tail.inputs,by rw [shape]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate parameter")
  | _ => throw (IO.userError "non-runtime parameter")
private structure Header (ts : TypeNameTable) (s : Syntax.FunctionSignature) where
  type : Core.Ty
  evidence : RuntimeFunctionHeader ts s type
private def header (ts : TypeNameTable) (s : Syntax.FunctionSignature) : IO (Header ts s) := do
  if policy : s.genericParameters = none ∧ s.whereClause = none ∧ s.modifiers.publicMarker = none ∧ s.modifiers.payableMarker = none then
    match shape : s.returnsClause with
    | none => return ⟨.unit,⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [shape]; exact .absent⟩⟩
    | some ⟨_,⟨_,[a]⟩⟩ =>
        let m ← meaning ts a
        return ⟨m.type,⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [shape]; exact .single m.evidence⟩⟩
    | _ => throw (IO.userError "return annotation shape")
  else throw (IO.userError "whole header policy")
private structure Atom (i : LocalTypeInputs) (s : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression i.names s resolved
  lowered : Resolved.Lowers i.context.ids resolved core
  typing : Resolved.HasType i.context resolved type
private def atom (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Atom i s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some id =>
          match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
          | some t,some n => return ⟨.var id,.var n,t,by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original row")
      | _ => throw (IO.userError "original name")
  | _ => throw (IO.userError "not fixture atom")
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalComputationElaborates i.names i.context s core type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte ≤ argsSpan.startByte)) "call spans/order"
      let f ← atom i fn; let a ← atom i arg
      match ft : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,by
            rw [shape]; exact .application (.call f.resolution f.lowered (ft ▸ f.typing) a.resolution a.lowered (same ▸ a.typing))⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | _ => let a ← atom i s; return ⟨a.core,a.type,.pure a.resolution a.lowered a.typing⟩
private structure Body (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (b : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalComputationReturnTreeElaborates ts o i b core type
private def body (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (b : Syntax.Block) : IO (Body ts o i b) := do
  for s in b.value do check (b.span.contains s.span) "original statement span"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,.unit,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨rs,.returnStmt (some s)⟩]⟩ =>
      check (rs.contains s.span) "return span"; let c ← child i s
      return ⟨c.core,c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨_,[⟨inner,.block statements⟩]⟩ =>
      let c ← body ts o i ⟨inner,statements⟩; return ⟨c.core,c.type,by rw [shape]; exact .block c.evidence⟩
  | ⟨bs,⟨ls,.letDecl name annotation (some init)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains init.span && decide (name.span.endByte ≤ init.span.startByte)) "binding spans/order"
      if unused : name.value ∉ i.names.map Prod.fst then
        let c ← child i init; let tail ← body ts o (i.bindFresh o name.value c.type) ⟨bs,rest⟩
        match ann : annotation with
        | none => return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .inferred unused c.evidence tail.evidence⟩
        | some a =>
            check (ls.contains a.span && decide (a.span.endByte ≤ init.span.startByte)) "annotation before initializer"
            let m ← meaning ts a
            if same : m.type = c.type then return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .binding (same ▸ m.evidence) unused c.evidence tail.evidence⟩
            else throw (IO.userError "initializer annotation mismatch")
      else throw (IO.userError "shadowing")
  | ⟨bs,⟨_,.expression s true⟩::rest⟩ =>
      let c ← child i s; let tail ← body ts o i ⟨bs,rest⟩
      return ⟨.letE c.core (tail.core.weakenAt 0),tail.type,by rw [shape]; exact .discard c.evidence tail.evidence⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let c ← child i guard; let a ← body ts o i yes; let d ← body ts o i no
      if ct : c.type = .bool then
        if same : d.type = a.type then return ⟨.ifE c.core a.core d.core,a.type,by rw [shape]; exact .conditional (ct ▸ c.evidence) a.evidence (same ▸ d.evidence)⟩
        else throw (IO.userError "arm types")
      else throw (IO.userError "guard type")
  | _ => throw (IO.userError "outside body fixture")
termination_by sizeOf b
private def table (a b r : Core.Ty) : TypeNameTable := [(["F"],.function a b),(["F"],.bool),
  (["G"],.function a .bool),(["A"],a),(["B"],b),(["R"],r),(["Unit"],.unit),(["mod","F"],.function a b)]
private def fields (c : CompiledRuntimeFunction) := (c.inputs.names,c.inputs.context,c.core,c.returnType)
private structure Ready (ts : TypeNameTable) (o : Resolved.DeclarationId) where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  evidence : RuntimeComputationFunctionCompiles ts o source compiled
private def positive (a b r : Core.Ty) (o : Resolved.DeclarationId) (sourceText : String)
    (expectedCore : Core.Expr) (oldProfile : Nat := 0) : IO (Ready (table a b r) o) := do
  let ts := table a b r; let s ← parsed sourceText
  let ps ← declare ts o .empty s.value.signature.parameters.elements; let h ← header ts s.value.signature
  let c ← body ts o ps.inputs s.value.body
  if exactResult : h.type = r ∧ c.type = r ∧ c.core = expectedCore then
    let compiled : CompiledRuntimeFunction := ⟨ps.inputs,expectedCore,r⟩
    have e : RuntimeComputationFunctionCompiles ts o s compiled := ⟨by simpa only [compiled,exactResult.1] using h.evidence,
      ps.evidence,by simpa only [compiled,exactResult.2.1,exactResult.2.2] using c.evidence⟩
    let expectedInputs := ((LocalTypeInputs.empty.bindFresh o "f" (.function a b)).bindFresh o "g" (.function a .bool)).bindFresh o "x" a
    let expected : CompiledRuntimeFunction := ⟨expectedInputs,expectedCore,r⟩
    have accepted := compileRuntimeComputationFunction?_iff.mpr e
    have _ := (compileRuntimeComputationFunction?_iff.mp accepted).body.core_hasType
    check (decide (fields compiled = fields expected ∧ (compileRuntimeComputationFunction? ts o s).map fields = some (fields expected))) "independent full record/Core/return"
    check (decide ((compileRuntimeFunction? ts o s).map fields = (if oldProfile = 1 then some (fields expected) else none)) &&
      decide ((compileRuntimeApplicationFunction? ts o s).map fields = (if oldProfile = 2 then some (fields expected) else none))) "old success embedding or narrower boundary"
    let wrong : CompiledRuntimeFunction := ⟨ps.inputs,.letE .unit (expectedCore.weakenAt 0),r⟩
    have _ : Core.HasType ps.inputs.context.values wrong.core r := .letE .unit
      (by simpa only [Core.Context.insertAt] using e.body.core_hasType.weakenAt (inserted := .unit) 0)
    if different : (compileRuntimeComputationFunction? ts o s).map fields ≠ some (fields wrong) then
      have _ : ¬ RuntimeComputationFunctionCompiles ts o s wrong := by
        intro other; rw [compileRuntimeComputationFunction?_iff.mpr other] at different; exact different rfl
      pure ()
    else throw (IO.userError "same-typed wrong Core acquired exact provenance")
    return ⟨s,compiled,e⟩
  else throw (IO.userError "independent body/declared return differs")
private structure Bound (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom ts o i ps args inputs
private def bindActual (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Bound ts o i ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨i,by rw [shape,supplied]; exact .nil⟩
  | ⟨_,.typed none name annotation⟩::rest,arg::tail =>
      let m ← meaning ts annotation
      if same : m.type = arg.type then
        if unused : name.value ∉ i.names.map Prod.fst then
          let b ← bindActual ts o (i.bindFresh o name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨b.inputs,by rw [shape,supplied]; exact .cons (same ▸ m.evidence) unused b.evidence⟩
        else throw (IO.userError "actual duplicate")
      else throw (IO.userError "actual type")
  | _,_ => throw (IO.userError "actual arity")
private def smoke (x : TypedRuntimeArgument) (o : Resolved.DeclarationId) : IO Unit := do
  let core : Core.Expr := .letE (call 2 0) (.var 0)
  let ready ← positive x.type x.type x.type o (text "let r=f(x);return r;") core
  let ts := table x.type x.type x.type
  let f : TypedRuntimeArgument := ⟨.function x.type x.type,.closure x.type x.type (.var 0) [.unit],.closure (.cons .unit .nil) (.var rfl)⟩
  let g : TypedRuntimeArgument := ⟨.function x.type .bool,.closure x.type .bool (.bool true) [],.closure .nil .bool⟩
  let args := [f,g,x]; let actual ← bindActual ts o .empty ready.source.value.signature.parameters.elements args
  let c ← body ts o actual.inputs.toTypeInputs ready.source.value.body
  if exactResult : c.core = core ∧ c.type = x.type ∧ ready.compiled.returnType = x.type then
    let prepared : PreparedRuntimeFunction := ⟨actual.inputs,core,x.type⟩
    have e : RuntimeComputationFunctionPrepares ts o ready.source args prepared :=
      ⟨by simpa only [prepared,exactResult.2.2] using ready.evidence.header,actual.evidence,
      by simpa only [prepared,exactResult.1,exactResult.2.1] using c.evidence⟩
    have accepted := prepareRuntimeComputationFunction?_iff.mpr e
    have _ := prepareRuntimeComputationFunction?_iff.mp accepted
    check (decide (fields prepared.toCompiled = fields ready.compiled ∧ prepared.inputs.environment.values = [x.value,g.value,f.value] ∧
      prepared.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)) =
        [("x",⟨o,2⟩,x.type,x.value),("g",⟨o,1⟩,g.type,g.value),("f",⟨o,0⟩,f.type,f.value)])) "actual original rows/reverse once/no let locals"
    have manual (store k) : Core.Steps 9 ⟨.eval core [x.value,g.value,f.value],k,store⟩ ⟨.ret x.value,k,store⟩ :=
      .cons .enterLet (.cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl)
        (.cons .invokeClosure (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))))))
    for store in [[],[.bool false]] do
      for fuel in List.range 11 do
        have _ := (manual store []).runStateful_done_iff (fuel := fuel)
        have _ := runRuntimeComputationFunction?_factorization ts o ready.source args fuel store
        check (decide (runRuntimeComputationFunction? ts o ready.source args fuel store =
          some (x.type,Core.runStateful fuel (.initial core [x.value,g.value,f.value] store)))) "full actual execution"
      check (decide (runRuntimeComputationFunction? ts o ready.source args 9 store = some (x.type,.done x.value store))) "literal actual value/cost/store"
      match runRuntimeComputationFunction? ts o ready.source args 8 store with
      | some (_, .outOfFuel checkpoint) =>
          check (decide (Core.runStateful 1 checkpoint = .done x.value store)) "genuine spent8 remaining1"
      | _ => throw (IO.userError "expected actual checkpoint before final variable")
    for supplied in [args,[],[f,x],args.reverse,args++[x]] do
      have _ := prepareRuntimeComputationFunction?_factorization ts o ready.source supplied
      check (decide ((prepareRuntimeComputationFunction? ts o ready.source supplied).map (fun p => fields p.toCompiled) =
        if supplied.map (·.type) = args.map (·.type) then some (fields ready.compiled) else none)) "full Option/type/arity guard"
  else throw (IO.userError "actual body differs")
private def rejected (sourceText : String) (localSuccess : Bool) (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let ts := table .word .word .word; let o := owner 4; let s ← parsed sourceText location
  if localSuccess then
    let fixed := ((LocalTypeInputs.empty.bindFresh o "f" (.function .word .word)).bindFresh o "g" (.function .word .bool)).bindFresh o "x" .word
    let c ← body ts o fixed s.value.body
    check (decide (c.core = .letE (call 2 0) (.var 0) ∧ c.type = .word ∧
      elaborateLocalComputationReturnTree? ts o fixed s.value.body = some (c.core,c.type))) "body-only success under separate valid caller"
  check ((compileRuntimeComputationFunction? ts o s).isNone) "invalid whole declaration compiled"
end ParsedRuntimeComputationCompilation
open ParsedRuntimeComputationCompilation
def frontendParsedRuntimeComputationCompilationTests : IO Unit := do
  let types : List Core.Ty := [.unit,.bool,.word,.cell .word,.product .word .unit,.namedData ⟨77⟩,.function (.namedData ⟨9⟩) (.namedData ⟨9⟩)]
  for o in [owner 0,owner 41] do
    for a in types do
      for b in types do
        for (bodyText,core) in [("let r=f(x);return r;",.letE (call 2 0) (.var 0)),
            ("let r:B=f(x);return r;",.letE (call 2 0) (.var 0)),
            ("f(x);return f(x);",.letE (call 2 0) (call 3 1)),
            ("if(g(x)){{let r=f(x);return r;}}else{return f(x);}",.ifE (call 1 0) (.letE (call 2 0) (.var 0)) (call 2 0))] do
          let _ ← positive a b b o (text bodyText) core
        let _ ← positive a (.function a b) b o (text "let h=f(x);return h(x);") (.letE (call 2 0) (call 0 1))
        let _ ← positive a b a o (text "return x;") (.var 0) 1
        let _ ← positive a b b o (text "return f(x);") (call 2 0) 2
      let _ ← positive a .unit .unit o "function example(f:mod.F,g:G,x:(A)) returns(()){let r:B=f(x);{return r;}}" (.letE (call 2 0) (.var 0))
    let _ ← positive (.product .unit .unit) (.product .unit .unit) (.product .unit .unit) o
      "function example(f:F,g:G,x:((),())) returns(((),())){let r:((),())=f(x);return r;}" (.letE (call 2 0) (.var 0))
    smoke ⟨.unit,.unit,.unit⟩ o; smoke ⟨.word,.word (Core.Word.ofNatModulo 17),.word⟩ o
  let suffix := "{let r=f(x);return r;}"
  for head in ["function example<T>(f:F,g:G,x:A) returns(R)","function example(f:F,g:G,x:A) returns(R) where A: Eq",
      "function example(f:F,g:G,x:A)","function example(f:F,g:G,x:A) returns(Unit)",
      "function example(f:F,g:G,x:A) returns()","function example(f:F,g:G,x:A) returns(R,R)",
      "function example(f:F,g:G,x:A) returns(Missing)","function example(comptime f:F,g:G,x:A) returns(R)",
      "function example(f:F,g:G,x:Missing) returns(R)","function example(f:F,g:G,f:A) returns(R)"] do rejected (head++suffix) true
  for marker in ["public","payable"] do rejected ("function example(f:F,g:G,x:A) "++marker++" returns(R)"++suffix) true .contract
  for b in ["let x=f(x);return x;","let r;return x;","let r=f(f(x));return r;","let r=f(x);return f(r,x);",
      "if(g(x)){return f(x);}else{return Missing;}","{let r=f(x);}return r;","return f(x);return x;"] do rejected (text b) false
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeApplicationFunctionProperties
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
    ∃ world, Core.WorldExtends [] world ∧ Core.RuntimeStoreHasTypes world [] ∧
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
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeComputationFunctionProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeFunctionCompilation
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
  ⟨⟨rfl, rfl, rfl, rfl, .absent⟩, .nil, TypedLetReturnBodyElaborates.returnTree <| .terminal (.single .bare)⟩

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
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩

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
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.conditional (.identifier (.tail (by change "x" ≠ "c"; decide) .head)) (.identifier .head) (.identifier .head))
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
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩
private theorem runtimeCost (flag : Bool) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table .bool) owner identity [boolArg flag]
      store .bool (.bool flag) store 1 :=
  .intro (runtimePrepares flag) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.identifier .head .head))

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
  exact ⟨headerAbsent, compileRuntimeFunction?_eq_none_iff.mpr headerAbsent,
    bodyAbsent, compileRuntimeFunction?_eq_none_iff.mpr bodyAbsent⟩

end Tests.FrontendRuntimeFunctionCompilation
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeFunctionEntryProperties
/-! ADR-0170: independent entry preparation checks the complete declared
contract and retains exact Core. Returning a value is not a source call. -/

set_option autoImplicit false

namespace Tests.FrontendRuntimeFunctionEntry

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "runtime-entry.sol"⟩, 0, 4⟩
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"RuntimeEntry", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private theorem differentIds : id 1 ≠ id 0 := by decide
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation "Arg")⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (source : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt source⟩]⟩
private def declaration (params : List Syntax.FunctionParameter) (result : Option Syntax.TypeExpr)
    (body : Syntax.Block) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "caller_named"⟩, none, ⟨span, params⟩, ⟨none, none⟩,
    result.map (fun type => ⟨span, ⟨span, [type]⟩⟩), none⟩, body⟩⟩
private def table (type : Core.Ty) : TypeNameTable := [(["Arg"], type), (["Result"], type)]
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def bare := declaration [] none (returned none)
private def barePrepared : PreparedRuntimeFunction := ⟨LocalInputs.empty, .unit, .unit⟩
private theorem barePrepares : RuntimeFunctionPrepares [] owner bare [] barePrepared :=
  ⟨⟨rfl, rfl, rfl, rfl, .absent⟩, .nil, TypedLetReturnBodyElaborates.returnTree <| .terminal (.single .bare)⟩

theorem absent_return_contract_prepares_bare_unit_and_has_exact_one_step (store : Core.Store) :
    RuntimeFunctionPrepares [] owner bare [] barePrepared ∧
    prepareRuntimeFunction? [] owner bare [] = some barePrepared ∧
    RuntimeFunctionEvaluatesWithCost [] owner bare [] store .unit .unit store 1 ∧
    runRuntimeFunction? [] owner bare [] 0 store = some (.unit, .outOfFuel (Core.State.initial .unit [] store)) ∧
    runRuntimeFunction? [] owner bare [] 1 store = some (.unit, .done .unit store) := by
  refine ⟨barePrepares, barePrepares.complete, .intro barePrepares (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal (.single .bare)), ?_, ?_⟩
  · rw [runRuntimeFunction?, barePrepares.complete]; rfl
  · rw [runRuntimeFunction?, barePrepares.complete]; rfl

private def identity := declaration [parameter "x"] (some (annotation "Result")) (returned (some (ref "x")))
private def identityPrepared (argument : TypedRuntimeArgument) : PreparedRuntimeFunction :=
  ⟨LocalInputs.empty.bindFresh owner "x" argument.type argument.value argument.valueTyped, .var 0, argument.type⟩
private theorem identityPrepares (argument : TypedRuntimeArgument) :
    RuntimeFunctionPrepares (table argument.type) owner identity [argument] (identityPrepared argument) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩,
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil,
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩

theorem explicit_aliases_return_arbitrary_structurally_typed_values_without_added_cost
    (argument : TypedRuntimeArgument) (store : Core.Store) (fuel : Nat) :
    RuntimeFunctionPrepares (table argument.type) owner identity [argument] (identityPrepared argument) ∧
    prepareRuntimeFunction? (table argument.type) owner identity [argument] = some (identityPrepared argument) ∧
    RuntimeFunctionEvaluatesWithCost (table argument.type) owner identity [argument]
      store argument.type argument.value store 1 ∧
    (runRuntimeFunction? (table argument.type) owner identity [argument] fuel store =
      some (argument.type, .done argument.value store) ↔ 1 ≤ fuel) := by
  have evaluated : RuntimeFunctionEvaluatesWithCost (table argument.type) owner identity [argument]
      store argument.type argument.value store 1 :=
    .intro (identityPrepares argument) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.identifier .head .head))
  refine ⟨identityPrepares argument, (identityPrepares argument).complete, evaluated, ?_⟩
  rw [runRuntimeFunction?_done_iff_cost]
  constructor
  · rintro ⟨cost, other, enough⟩
    exact (other.deterministic evaluated).2.2.2 ▸ enough
  · intro enough
    exact ⟨1, evaluated, enough⟩

theorem identity_entry_exhaustion_is_present_and_retains_its_exact_initial_state
    (argument : TypedRuntimeArgument) (store : Core.Store) (fuel : Nat) :
    runRuntimeFunction? (table argument.type) owner identity [argument] 0 store =
      some (argument.type, .outOfFuel (Core.State.initial (.var 0) [argument.value] store)) ∧
    ((∃ suspended, runRuntimeFunction? (table argument.type) owner identity [argument] fuel store =
      some (argument.type, .outOfFuel suspended)) ↔ fuel < 1) ∧
    RuntimeFunctionHasType (table argument.type) owner identity [argument] argument.type := by
  have evaluated : RuntimeFunctionEvaluatesWithCost (table argument.type) owner identity [argument]
      store argument.type argument.value store 1 :=
    .intro (identityPrepares argument) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.identifier .head .head))
  exact ⟨by rw [runRuntimeFunction?, (identityPrepares argument).complete]; rfl,
    evaluated.run_outOfFuel_iff, evaluated.hasType⟩

private def pairInputs (first second : Bool) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "first" .bool (.bool first) .bool).bindFresh
    owner "second" .bool (.bool second) .bool
private def pairDeclaration := declaration [parameter "first", parameter "second"]
  (some (annotation "Result")) (returned (some (ref "first")))
private def pairPrepared (first second : Bool) : PreparedRuntimeFunction := ⟨pairInputs first second, .var 1, .bool⟩
private theorem pairPrepares (first second : Bool) : RuntimeFunctionPrepares (table .bool) owner pairDeclaration
    [boolArg first, boolArg second] (pairPrepared first second) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩,
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons (.named .head) (by change "second" ∉ ["first"]; simp) .nil),
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier (.tail (by change "second" ≠ "first"; decide) .head))
      (.var (.tail differentIds .head)) (.var (.tail differentIds .head))⟩

theorem same_typed_source_order_arguments_select_their_exact_core_position
    (first second : Bool) (store : Core.Store) :
    RuntimeFunctionPrepares (table .bool) owner pairDeclaration [boolArg first, boolArg second] (pairPrepared first second) ∧
    (pairPrepared first second).inputs.names = [("second", id 1), ("first", id 0)] ∧
    (pairPrepared first second).inputs.environment = [(id 1, .bool second), (id 0, .bool first)] ∧
    runRuntimeFunction? (table .bool) owner pairDeclaration [boolArg first, boolArg second] 1 (.unit :: store) =
      some (.bool, .done (.bool first) (.unit :: store)) := by
  refine ⟨pairPrepares first second, rfl, rfl, ?_⟩
  rw [runRuntimeFunction?, (pairPrepares first second).complete]
  rfl

theorem equal_core_type_does_not_allow_substitution_of_a_different_prepared_expression
    (first second : Bool) :
    Core.HasType [.bool, .bool] (.bool first) .bool ∧
    ¬ RuntimeFunctionPrepares (table .bool) owner pairDeclaration [boolArg first, boolArg second]
      { pairPrepared first second with core := .bool first } := by
  refine ⟨.bool, ?_⟩
  intro wrong
  have same := (pairPrepares first second).body.result_unique wrong.body
  cases same.1

private def zeroSource : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def mismatched := declaration [] (some (annotation "Result")) (returned (some zeroSource))
theorem successful_word_body_does_not_satisfy_a_boolean_return_contract (fuel : Nat) (store : Core.Store) :
    LocalInputs.empty.checkReturnBody? mismatched.value.body = some (.word .zero, .word) ∧
    (¬ ∃ prepared, RuntimeFunctionPrepares (table .bool) owner mismatched [] prepared) ∧
    prepareRuntimeFunction? (table .bool) owner mismatched [] = none ∧
    runRuntimeFunction? (table .bool) owner mismatched [] fuel store = none := by
  have noPreparation : ¬ ∃ prepared, RuntimeFunctionPrepares (table .bool) owner mismatched [] prepared := by
    rintro ⟨prepared, derived⟩
    have header : RuntimeFunctionHeader (table .bool) mismatched.value.signature .bool :=
      ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
    have body : ReturnBodyElaborates prepared.inputs.names prepared.inputs.context mismatched.value.body (.word .zero) .word :=
      .expression (.wordLiteral zeroMeaning) .word .word
    have impossible := (header.type_unique derived.header).trans
      ((TypedLetReturnBodyElaborates.returnTree <| .terminal
        (inputs := prepared.inputs.toTypeInputs) (.single (by
          simpa only [LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context] using body))).result_unique derived.body).2.symm
    cases impossible
  have rejected := prepareRuntimeFunction?_eq_none_iff.mpr noPreparation
  exact ⟨(ReturnBodyElaborates.expression (.wordLiteral zeroMeaning) .word .word).complete,
    noPreparation, rejected, by simp only [runRuntimeFunction?, rejected, bind, Option.bind_none]⟩

private def badHeaders : List Syntax.FunctionSignature :=
  [{ bare.value.signature with genericParameters := some ⟨span, ⟨⟨span, "T"⟩, []⟩⟩ },
   { bare.value.signature with whereClause := some ⟨span,
       ⟨⟨span, annotation "Arg", ⟨span, "Trait"⟩, none⟩, []⟩⟩ },
   { bare.value.signature with modifiers := ⟨some span, none⟩ },
   { bare.value.signature with modifiers := ⟨none, some span⟩ },
   { bare.value.signature with returnsClause := some ⟨span, ⟨span, []⟩⟩ },
   { bare.value.signature with returnsClause := some ⟨span, ⟨span, [annotation "Arg", annotation "Arg"]⟩⟩ }]

theorem every_excluded_header_shape_prevents_entry_before_body_execution
    (types : TypeNameTable) (header : Syntax.FunctionSignature) (present : header ∈ badHeaders)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    let decl : Syntax.FunctionDecl := ⟨span, ⟨header, returned none⟩⟩
    (¬ ∃ type, RuntimeFunctionHeader types header type) ∧
    (¬ ∃ prepared, RuntimeFunctionPrepares types owner decl arguments prepared) ∧
    prepareRuntimeFunction? types owner decl arguments = none ∧
    runRuntimeFunction? types owner decl arguments fuel store = none := by
  intro decl
  have rejectedHeader : interpretRuntimeFunctionHeader? types header = none := by
    simp only [badHeaders, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have absent := interpretRuntimeFunctionHeader?_eq_none_iff.mp rejectedHeader
  have noPreparation : ¬ ∃ prepared, RuntimeFunctionPrepares types owner decl arguments prepared := by
    rintro ⟨prepared, derived⟩
    exact absent ⟨prepared.returnType, derived.header⟩
  have rejected := prepareRuntimeFunction?_eq_none_iff.mpr noPreparation
  exact ⟨absent, noPreparation, rejected, by simp only [runRuntimeFunction?, rejected, bind, Option.bind_none]⟩

private def missingSource : Syntax.Expr := ⟨span, .conditional (ref "x") span (ref "x") span (ref "missing")⟩
private def missingDecl := declaration [parameter "x"] (some (annotation "Result")) (returned (some missingSource))
theorem raw_skipped_missing_evaluation_is_not_a_whole_entry_contract (fuel : Nat) (store : Core.Store) :
    ReturnBodyEvaluates (identityPrepared (boolArg true)).inputs.names
      (identityPrepared (boolArg true)).inputs.environment store missingDecl.value.body (.bool true) store ∧
    (identityPrepared (boolArg true)).inputs.checkReturnBody? missingDecl.value.body = none ∧
    (¬ ∃ type, RuntimeFunctionHasType (table .bool) owner missingDecl [boolArg true] type) ∧
    (¬ ∃ type value finalStore cost, RuntimeFunctionEvaluatesWithCost (table .bool) owner missingDecl [boolArg true]
      store type value finalStore cost) ∧
    prepareRuntimeFunction? (table .bool) owner missingDecl [boolArg true] = none ∧
    runRuntimeFunction? (table .bool) owner missingDecl [boolArg true] fuel store = none := by
  have bodyRejected : (identityPrepared (boolArg true)).inputs.checkReturnBody? missingDecl.value.body = none := by
    simp [LocalInputs.checkReturnBody?, elaborateReturnBody?, missingDecl, declaration, returned,
      elaborateLocalExpression?, resolveLocalExpression?, missingSource, ref, identityPrepared,
      LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  have noPreparation : ¬ ∃ prepared, RuntimeFunctionPrepares (table .bool) owner missingDecl [boolArg true] prepared := by
    rintro ⟨prepared, derived⟩
    have sameInputs := RuntimeParametersBindFrom.result_unique (identityPrepares (boolArg true)).parameters derived.parameters
    have accepted := derived.body.complete
    rw [← sameInputs] at accepted
    rw [show missingDecl.value.body = ⟨span, [⟨span, .returnStmt (some missingSource)⟩]⟩ from rfl,
      elaborateTypedLetReturnTree?_single] at accepted
    change (identityPrepared (boolArg true)).inputs.checkReturnBody? missingDecl.value.body = some _ at accepted
    rw [bodyRejected] at accepted
    cases accepted
  have rejected := prepareRuntimeFunction?_eq_none_iff.mpr noPreparation
  have noContract : ¬ ∃ type, RuntimeFunctionHasType (table .bool) owner missingDecl [boolArg true] type := by
    rintro ⟨type, typing⟩
    obtain ⟨prepared, preparation, _⟩ := runtimeFunctionHasType_iff_prepares.mp typing
    exact noPreparation ⟨prepared, preparation⟩
  refine ⟨.expression (.ifTrue (.identifier .head .head) (.identifier .head .head)), bodyRejected, noContract, ?_, rejected,
    by simp only [runRuntimeFunction?, rejected, bind, Option.bind_none]⟩
  rintro ⟨type, value, finalStore, cost, evaluation⟩
  exact noContract ⟨type, evaluation.hasType⟩

private def closure : Core.Value := .closure .bool .bool (.var 0) []
private def closureArg : TypedRuntimeArgument := ⟨.function .bool .bool, closure, .closure .nil (.var rfl)⟩
private def cellArg (location : Core.Location) : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word location, .cellRef⟩
theorem aliases_return_closures_and_unallocated_references_without_calling_or_allocating
    (location : Core.Location) (store : Core.Store) :
    runRuntimeFunction? (table closureArg.type) owner identity [closureArg] 1 (.unit :: store) =
      some (.function .bool .bool, .done closure (.unit :: store)) ∧
    runRuntimeFunction? (table (cellArg location).type) owner identity [cellArg location] 1 [] =
      some (.cell .word, .done (.cellRef .word location) []) ∧
    ([] : Core.Store)[location]? = none :=
  ⟨((explicit_aliases_return_arbitrary_structurally_typed_values_without_added_cost closureArg (.unit :: store) 1).2.2.2).mpr (Nat.le_refl _),
    ((explicit_aliases_return_arbitrary_structurally_typed_values_without_added_cost (cellArg location) [] 1).2.2.2).mpr (Nat.le_refl _), by simp⟩

end Tests.FrontendRuntimeFunctionEntry
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeFunctionEvaluatorProperties
/-! Original declarations and actual arguments, independently justified before
the direct triple is reflected back into the established machine contracts. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeFunctionEvaluator
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"DirectEntry", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "direct-entry.sol"⟩, 225, 9⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Flag"], .bool)]
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def bind (name : String) (value : Syntax.Expr) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some (named "Payload")) (some value)⟩ :: tail.value⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private def guardCore : Core.Expr := .binary .wordEq (.word .zero) (.word .zero)
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => branch guard (bind name (ref previous) (tree rest name)) (bind name (ref previous) (returned name))
private def core : Nat → Core.Expr
  | 0 => .var 0
  | depth + 1 => .ifE guardCore (.letE (.var 0) (core depth)) (.letE (.var 0) (.var 0))
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (named type)⟩
private def parameters := [parameter "flag" "Flag", parameter "seed" "Payload"]
private def entry (body : Syntax.Block) (result : String := "Payload") (exposed : Bool := false) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "tree"⟩, none, ⟨span, parameters⟩, ⟨if exposed then some span else none, none⟩, some ⟨span, ⟨span, [named result]⟩⟩, none⟩, body⟩⟩
private def initial (type : Core.Ty) : LocalTypeInputs := (LocalTypeInputs.empty.bindFresh owner "flag" .bool).bindFresh owner "seed" type
private def compiled (names : List String) (type : Core.Ty) : CompiledRuntimeFunction := ⟨initial type, core names.length, type⟩
private theorem treeElab (names : List String) (previous : String) (type : Core.Ty)
    (inputs : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ inputs.names.map Prod.fst)
    (resolution : ResolvesLocalExpression inputs.names (ref previous) resolved)
    (lowered : Resolved.Lowers inputs.ids resolved (.var 0)) (typing : Resolved.HasType inputs.context resolved type) :
    TypedLetReturnTreeElaborates (types type) owner inputs (tree names previous) (core names.length) type := by
  induction names generalizing previous inputs resolved with
  | nil => exact .single (.expression resolution (by simpa only [List.length_nil, core, LocalTypeInputs.context_ids] using lowered) typing)
  | cons name rest ih =>
    have parts := List.nodup_cons.mp distinct
    have eta : ⟨span, (tree rest name).value⟩ = tree rest name := by cases rest <;> rfl
    refine .conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (.binary .word .word) (.binary .word .word) ?_ ?_
    · apply TypedLetReturnTreeElaborates.binding (name := ⟨span, name⟩)
        (show TypeNameDenotes (types type) (named "Payload") type from .named .head).structural (fresh name (by simp)) resolution lowered typing
      rw [eta]
      apply ih name (inputs.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
    · exact .binding (.named .head) (fresh name (by simp)) resolution lowered typing
        (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem header (type : Core.Ty) (body : Syntax.Block) : RuntimeFunctionHeader (types type) (entry body).value.signature type :=
  ⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩
private theorem declared (type : Core.Ty) : RuntimeParametersDeclare (types type) owner parameters (initial type) :=
  .cons (.named (.tail (by decide) .head)) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named .head) (by change "seed" ∉ ["flag"]; decide) .nil)
private theorem compilation (names : List String) (type : Core.Ty) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionCompiles (types type) owner (entry (tree names "seed")) (compiled names type) :=
  ⟨header type _, declared type, treeElab names "seed" type (initial type) _ distinct fresh (.identifier .head) (.var .head) (.var .head)⟩

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def arguments {type : Core.Ty} (flag : Bool) (actual : Actual type) : List TypedRuntimeArgument := [⟨.bool, .bool flag, .bool⟩, ⟨type, actual.val, actual.property⟩]
private def inputs {type : Core.Ty} (flag : Bool) (actual : Actual type) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "flag" .bool (.bool flag) .bool).bindFresh owner "seed" type actual.val actual.property
private theorem boundArguments {type : Core.Ty} (flag : Bool) (actual : Actual type) :
    RuntimeParametersBind (types type) owner parameters (arguments flag actual) (inputs flag actual) :=
  .cons (.named (.tail (by decide) .head)) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named .head) (by change "seed" ∉ ["flag"]; decide) .nil)
private theorem preparation {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionPrepares (types type) owner (entry (tree names "seed")) (arguments flag actual) ⟨inputs flag actual, core names.length, type⟩ :=
  ⟨header type _, boundArguments flag actual, (compilation names type distinct fresh).body⟩
private theorem treeCost (names : List String) (previous : String) (table : LocalNameTable) (environment : Resolved.Environment)
    (value : Core.Value) (store : Core.Store) (head : LocalExpressionEvaluatesWithCost table environment store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment store (tree names previous) value store (10 * names.length + 1) := by
  induction names generalizing previous table environment with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    have eta : ⟨span, (tree rest name).value⟩ = tree rest name := by cases rest <;> rfl
    have arithmetic : 5 + (1 + (10 * rest.length + 1) + 2) + 2 = 10 * (name :: rest).length + 1 := by simp; omega
    rw [← arithmetic]
    apply TypedLetReturnTreeEvaluatesWithCost.ifTrue (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning))
    apply TypedLetReturnTreeEvaluatesWithCost.binding head
    rw [eta]
    exact ih name _ _ (.identifier .head .head)
private theorem costed {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (store : Core.Store)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionEvaluatesWithCost (types type) owner (entry (tree names "seed")) (arguments flag actual) store type actual.val store (10 * names.length + 1) :=
  .intro (preparation names flag actual distinct fresh) (treeCost names "seed" _ _ actual.val store (.identifier .head .head))

private theorem computed {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    evaluateRuntimeFunctionWithCost? (types type) owner (entry (tree names "seed")) (arguments flag actual) =
      some (type, actual.val, 10 * names.length + 1) :=
  (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (costed names flag actual [] distinct fresh)).2

theorem arbitrary_fresh_depth_retains_independent_provenance_and_original_arguments
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionCompiles (types type) owner (entry (tree names "seed")) (compiled names type) ∧
    prepareRuntimeFunction? (types type) owner (entry (tree names "seed")) (arguments flag actual) =
      some ⟨inputs flag actual, core names.length, type⟩ ∧
    (inputs flag actual).bindings.length = 2 ∧
    (inputs flag actual).environment.values = [actual.val, .bool flag] ∧
    evaluateRuntimeFunctionWithCost? (types type) owner (entry (tree names "seed")) (arguments flag actual) =
      some (type, actual.val, 10 * names.length + 1) :=
  ⟨compilation names type distinct fresh, (preparation names flag actual distinct fresh).complete,
    rfl, rfl, computed names flag actual distinct fresh⟩

theorem direct_results_recover_compiled_paths_and_every_fuel_threshold
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) (store : Core.Store) (fuel : Nat) :
    Core.Steps (10 * names.length + 1) (Core.State.initial (core names.length) [actual.val, .bool flag] store)
      (Core.State.final actual.val store) ∧
    (runRuntimeFunction? (types type) owner (entry (tree names "seed")) (arguments flag actual) fuel store =
      some (type, .done actual.val store) ↔ 10 * names.length + 1 ≤ fuel) ∧
    ((∃ checkpoint, runRuntimeFunction? (types type) owner (entry (tree names "seed")) (arguments flag actual)
      fuel store = some (type, .outOfFuel checkpoint)) ↔ fuel < 10 * names.length + 1) ∧
    10 * names.length + 1 ≤ typedLetReturnTreeFuelBound (tree names "seed") := by
  have recovered := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store)).mpr
    ⟨rfl, computed names flag actual distinct fresh⟩
  exact ⟨recovered.compiled_toSteps (compilation names type distinct fresh),
    recovered.run_done_iff, recovered.run_outOfFuel_iff, recovered.cost_le_fuelBound⟩

theorem store_free_triples_do_not_license_a_changed_final_store
    {type : Core.Ty} (actual : Actual type) (initialStore finalStore : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (types type) owner (entry (tree ["x", "y"] "seed"))
      (arguments false actual) initialStore type actual.val finalStore 21 ↔ finalStore = initialStore := by
  rw [runtimeFunctionEvaluatesWithCost_iff_evaluate, computed ["x", "y"] false actual (by decide) (by decide)]
  simp

theorem nominal_compilation_cannot_supply_an_actual_parameter (nominal : Core.DataTypeId) :
    compileRuntimeFunction? (types (.namedData nominal)) owner (entry (tree ["x"] "seed")) =
      some (compiled ["x"] (.namedData nominal)) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  refine ⟨(compilation _ _ (by decide) (by decide)).complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩; cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem actual_opaque_cells_and_captured_functions_need_no_effects (location : Core.Location) (word : Core.Word) :
    evaluateRuntimeFunctionWithCost? (types (.cell .word)) owner (entry (tree ["x", "y"] "seed"))
      (arguments true ⟨.cellRef .word location, .cellRef⟩) = some (.cell .word, .cellRef .word location, 21) ∧
    evaluateRuntimeFunctionWithCost? (types (.function .bool .word)) owner (entry (tree ["x", "y"] "seed"))
      (arguments false ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩) =
      some (.function .bool .word, .closure .bool .word (.var 1) [.word word], 21) :=
  ⟨computed _ _ _ (by decide) (by decide), computed _ _ _ (by decide) (by decide)⟩

theorem same_typed_core_is_not_independent_compilation (type : Core.Ty) :
    Core.HasType [type, .bool] (.var 0) type ∧
    ¬ RuntimeFunctionCompiles (types type) owner (entry (tree ["x"] "seed"))
      { compiled ["x"] type with core := .var 0 } := by
  refine ⟨.var rfl, ?_⟩
  intro forged
  have wrong := congrArg CompiledRuntimeFunction.core
    (forged.result_unique (compilation ["x"] type (by decide) (by decide)))
  cases wrong

private def sub (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .subtract⟩ right⟩
private def mathBody := branch (ref "flag") (bind "x" (sub zero (ref "seed")) (returned "x"))
  (bind "x" ⟨span, .unary ⟨span, .bitNot⟩ (sub (ref "seed") zero)⟩ (returned "seed"))
private def mathCore : Core.Expr := .ifE (.var 1) (.letE (.binary .wordSub (.word .zero) (.var 0)) (.var 0))
  (.letE (.unary .wordNot (.binary .wordSub (.var 0) (.word .zero))) (.var 1))
private theorem mathCompilation : RuntimeFunctionCompiles (types .word) owner (entry mathBody) ⟨initial .word, mathCore, .word⟩ :=
  ⟨header _ _, declared _, .conditional (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head))
    (.binding (.named .head) (by decide) (.subtract (.wordLiteral zeroMeaning) (.identifier .head)) (.binary .word (.var .head)) (.binary .word (.var .head))
      (.single (.expression (.identifier .head) (.var .head) (.var .head))))
    (.binding (.named .head) (by decide) (.bitNot (.subtract (.identifier .head) (.wordLiteral zeroMeaning)))
      (.unary (.binary (.var .head) .word)) (.unary (.binary (.var .head) .word))
      (.single (.expression (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head)))))⟩
private theorem mathCost (flag : Bool) (word : Core.Word) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (types .word) owner (entry mathBody) (arguments flag ⟨.word word, .word⟩)
      store .word (.word (if flag then Core.Word.zero.sub word else word)) store (if flag then 11 else 13) := by
  let actual : Actual .word := ⟨.word word, .word⟩
  apply RuntimeFunctionEvaluatesWithCost.intro (prepared := ⟨inputs flag actual, mathCore, .word⟩) ⟨header _ _, boundArguments _ _, mathCompilation.body⟩
  have seed : LocalExpressionEvaluatesWithCost (inputs flag actual).names (inputs flag actual).environment store (ref "seed") (.word word) store 1 := .identifier .head .head
  have choice : LocalExpressionEvaluatesWithCost (inputs flag actual).names (inputs flag actual).environment store (ref "flag") (.bool flag) store 1 :=
    .identifier (.tail (by change "seed" ≠ "flag"; decide) .head) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
  cases flag
  · apply TypedLetReturnTreeEvaluatesWithCost.ifFalse (branchCost := 10) choice
    apply TypedLetReturnTreeEvaluatesWithCost.binding (tailCost := 1) (.bitNot (.subtract seed (.wordLiteral zeroMeaning)))
    exact .single (.expression (.identifier (.tail (by decide) .head) (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head)))
  · apply TypedLetReturnTreeEvaluatesWithCost.ifTrue (branchCost := 8) choice
    exact .binding (.subtract (.wordLiteral zeroMeaning) seed) (.single (.expression (.identifier .head .head)))

theorem direct_triples_pay_for_ordered_and_unused_work (flag : Bool) (word : Core.Word) (store : Core.Store) (fuel : Nat) :
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry mathBody) (arguments flag ⟨.word word, .word⟩) =
      some (.word, .word (if flag then Core.Word.zero.sub word else word), if flag then 11 else 13) ∧
    (runRuntimeFunction? (types .word) owner (entry mathBody) (arguments flag ⟨.word word, .word⟩) fuel store =
      some (.word, .done (.word (if flag then Core.Word.zero.sub word else word)) store) ↔ (if flag then 11 else 13) ≤ fuel) := by
  have result := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (mathCost flag word store)).2
  exact ⟨result, (runtimeFunctionEvaluatesWithCost_iff_evaluate.mpr ⟨rfl, result⟩).run_done_iff⟩
private def checkpoint (word : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word word), [.binaryApply .wordSub (.word .zero), .letBody (.var 0) [.word word, .bool true]], store⟩

theorem actual_pending_initializer_supports_arbitrary_resumption (word : Core.Word) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? (types .word) owner (entry mathBody) (arguments true ⟨.word word, .word⟩) 8 store =
      some (.word, .outOfFuel (checkpoint word store)) ∧
    Core.Steps 3 (checkpoint word store) (Core.State.final (.word (Core.Word.zero.sub word)) store) ∧
    Core.runStateful 1 (checkpoint word store) =
      .outOfFuel ⟨.ret (.word (Core.Word.zero.sub word)), [.letBody (.var 0) [.word word, .bool true]], store⟩ ∧
    Core.runStateful 2 ⟨.ret (.word (Core.Word.zero.sub word)), [.letBody (.var 0) [.word word, .bool true]], store⟩ =
      .done (.word (Core.Word.zero.sub word)) store ∧
    Core.runStateful 3 (checkpoint word store) = .done (.word (Core.Word.zero.sub word)) store ∧
    Core.runStateful 0 { checkpoint word store with continuation := [] } = .done (.word word) store ∧
    runRuntimeFunction? (types .word) owner (entry mathBody) (arguments true ⟨.word word, .word⟩) (8 + additional) store =
      some (.word, Core.runStateful additional (checkpoint word store)) := by
  have suspended : runRuntimeFunction? (types .word) owner (entry mathBody) (arguments true ⟨.word word, .word⟩) 8 store =
      some (.word, .outOfFuel (checkpoint word store)) := by rw [mathCompilation.run_eq _ rfl]; rfl
  have recovered := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store)).mpr
    ⟨rfl, (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (mathCost true word store)).2⟩
  exact ⟨suspended, (recovered.residual_of_outOfFuel suspended).2, rfl, rfl, rfl, rfl, runRuntimeFunction?_resume suspended additional⟩

private theorem rejectArguments (args : List TypedRuntimeArgument) (wrong : args.map (·.type) ≠ [.bool, .word]) :
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry (tree ["x"] "seed")) args = none := by
  apply evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr
  apply prepareRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨prepared, preparation⟩
  have same := preparation.compiles.result_unique (compilation ["x"] .word (by decide) (by decide))
  exact wrong (runtimeFunctionPrepares_toCompiled_iff.mp ⟨prepared, preparation, same⟩).2

theorem raw_success_does_not_bypass_headers_return_contracts_or_unused_arguments (word : Core.Word) :
    evaluateTypedLetReturnTreeWithCost? owner (inputs true ⟨.word word, .word⟩).names
      (inputs true ⟨.word word, .word⟩).environment (tree ["x"] "seed") = some (.word word, 11) ∧
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry (tree ["x"] "seed") "Payload" true)
      (arguments true ⟨.word word, .word⟩) = none ∧
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry (tree ["x"] "seed") "Flag")
      (arguments true ⟨.word word, .word⟩) = none ∧
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry (tree ["x"] "seed"))
      [⟨.word, .word .zero, .word⟩, ⟨.word, .word word, .word⟩] = none ∧
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry (tree ["x"] "seed")) [] = none := by
  refine ⟨evaluateTypedLetReturnTreeWithCost?_complete (treeCost ["x"] "seed" _ _ (.word word) [] (.identifier .head .head)),
    evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr rfl, ?_, rejectArguments _ (by simp), rejectArguments _ (by simp)⟩
  apply evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr
  apply prepareRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨prepared, preparation⟩
  have same := preparation.parameters.result_unique (boundArguments true ⟨.word word, .word⟩)
  have body := preparation.body
  rw [same] at body
  have declaredBool : RuntimeFunctionHeader (types .word) (entry (tree ["x"] "seed") "Flag").value.signature .bool :=
    ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
  have expected := (compilation ["x"] .word (by decide) (by decide)).body
  have impossible := (expected.result_unique body).2.trans (declaredBool.type_unique preparation.header).symm
  cases impossible

private def unknownArm := branch (ref "flag") (returned "seed")
  ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some (named "Unknown")) (some (ref "seed"))⟩, ⟨span, .returnStmt (some (ref "x"))⟩]⟩
theorem direct_body_short_circuiting_does_not_remove_the_unselected_entry_contract (word : Core.Word) :
    evaluateTypedLetReturnTreeWithCost? owner (inputs true ⟨.word word, .word⟩).names
      (inputs true ⟨.word word, .word⟩).environment unknownArm = some (.word word, 4) ∧
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry unknownArm) (arguments true ⟨.word word, .word⟩) = none := by
  refine ⟨?_, evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr (prepareRuntimeFunction?_eq_none_iff.mpr ?_)⟩
  · apply evaluateTypedLetReturnTreeWithCost?_complete (initialStore := ([] : Core.Store))
    apply TypedLetReturnTreeEvaluatesWithCost.ifTrue (conditionCost := 1) (branchCost := 1)
    · exact .identifier (.tail (by change "seed" ≠ "flag"; decide) .head)
        (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
    · exact .single (.expression (.identifier .head .head))
  · rintro ⟨⟨targetInputs, targetCore, targetType⟩, preparation⟩
    cases preparation.body with
    | single child => cases child
    | conditional _ _ _ _ invalid =>
      cases invalid with
      | single child => cases child
      | binding meaning _ _ _ _ _ =>
        have impossible := meaning.complete
        simp only [named, interpretStructuralType?_named_eq_typeName] at impossible
        change none = some _ at impossible
        cases impossible

end Tests.FrontendRuntimeFunctionEvaluator
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeApplicationEntries
/-! Original whole declarations and supplied values precede the new entry checks.
Independent body paths fix the expected costs, stores and exact Core. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeApplicationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ReturnActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def text := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "application-return-entry.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) "original declaration range changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside annotation fixture")
private structure Parameters (types : TypeNameTable) (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner .empty params statics
  bound : RuntimeParametersBindFrom types owner .empty params args actual
private def parameters (types : TypeNameTable) (params : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Parameters types params args) := do
  match original : params, supplied : args with
  | [⟨s, .typed none f ft⟩, ⟨t, .typed none x xt⟩], [fv, xv] =>
      check (s.contains f.span && s.contains ft.span && t.contains x.span && t.contains xt.span &&
        decide (s.endByte ≤ t.startByte)) "original parameter spans/order changed"
      let fm ← meaning types ft; let xm ← meaning types xt
      if sameF : fm.type = fv.type then
        if sameX : xm.type = xv.type then
          if unused : x.value ∉ [f.value] then
            return ⟨(LocalTypeInputs.empty.bindFresh owner f.value fv.type).bindFresh owner x.value xv.type,
              (LocalInputs.empty.bindFresh owner f.value fv.type fv.value fv.valueTyped).bindFresh owner x.value xv.type xv.value xv.valueTyped,
              by
                rw [original]
                exact .cons (sameF ▸ fm.evidence) (by simp [LocalTypeInputs.empty_names])
                  (.cons (sameX ▸ xm.evidence) unused .nil),
              by
                rw [original, supplied]
                exact .cons (sameF ▸ fm.evidence) (by simp [LocalInputs.empty_names])
                  (.cons (sameX ▸ xm.evidence) unused .nil)⟩
          else throw (IO.userError "duplicate parameter")
        else throw (IO.userError "argument type differs")
      else throw (IO.userError "function type differs")
  | _, _ => throw (IO.userError "original parameter shape or actual arity changed")
private structure Reference (inputs : LocalInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression inputs.names source resolved
  lowered : Resolved.Lowers inputs.context.ids resolved core
  typing : Resolved.HasType inputs.context resolved type
private def reference (inputs : LocalInputs) (source : Syntax.Expr) : IO (Reference inputs source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          match typed : inputs.context.lookup? id, indexed : Resolved.LocalScope.index? inputs.context.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "original context row missing")
      | none => throw (IO.userError "original name missing")
  | _ => throw (IO.userError "not original identifier")
private structure Original (body : Syntax.Block) where
  blockSpan : Syntax.SourceSpan
  returnSpan : Syntax.SourceSpan
  span : Syntax.SourceSpan
  argumentsSpan : Syntax.SourceSpan
  callee : Syntax.Expr
  argument : Syntax.Expr
  shape : body = ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩)⟩]⟩
private def original (body : Syntax.Block) : IO (Original body) := do
  match shape : body with
  | ⟨bs, [⟨rs, .returnStmt (some ⟨s, .call f ⟨args, [x]⟩⟩)⟩]⟩ =>
      check (bs.contains rs && rs.contains s && s.contains f.span && s.contains args && args.contains x.span &&
        decide (f.span.endByte ≤ args.startByte)) "original return/call spans changed"
      return ⟨bs, rs, s, args, f, x, shape⟩
  | _ => throw (IO.userError "not original singleton return-call")
private structure Observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : Type where
  evidence : ∀ store, LocalExpressionEvaluatesWithCost inputs.names inputs.environment store source value store 1
private def observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : IO (Observed inputs source value) := do
  match shape : source with
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          if found : inputs.environment.lookup? id = some value then
            return ⟨fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          else throw (IO.userError "actual row changed")
      | none => throw (IO.userError "actual name missing")
  | _ => throw (IO.userError "raw child changed")
private def delayed : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .letE (.var 0) (delayed n)
private theorem delayedTyped (n : Nat) (type : Core.Ty) (rest : Core.Context) :
    Core.HasType (type :: rest) (delayed n) type := by
  induction n generalizing rest with
  | zero => exact .var rfl
  | succ n ih => exact .letE (.var rfl) (ih _)
private theorem delayedPath (n : Nat) (value : Core.Value) (rest : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (3 * n + 1) ⟨.eval (delayed n) (value :: rest), k, s⟩ ⟨.ret value, k, s⟩ := by
  induction n generalizing rest k with
  | zero => exact .cons (.var rfl) .refl
  | succ n ih =>
      have path := Core.Steps.cons .enterLet (.cons (.var (index := 0) rfl) (.cons .bindLet (ih (value :: rest) k)))
      have count : 3 * (n + 1) + 1 = 3 * n + 1 + 1 + 1 + 1 := by omega
      rw [count]; exact path
private def header (types : TypeNameTable) (source : Syntax.FunctionDecl) (output : Core.Ty) :
    IO (PLift (RuntimeFunctionHeader types source.value.signature output)) := do
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.type = output then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          return ⟨⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.evidence)⟩⟩
        else throw (IO.userError "original header policy")
      else throw (IO.userError "original return type")
  | _ => throw (IO.userError "original return shape")
private def execute (argument : TypedRuntimeArgument) (output : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (s t : Core.Store) (value : Core.Value) (bodyCost : Nat)
    (closureTyped : Core.ValueHasType (.closure argument.type output body captured) (.function argument.type output))
    (bodyPath : ∀ k, Core.Steps bodyCost ⟨.eval body (argument.value :: captured), k, s⟩ ⟨.ret value, k, t⟩) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output, .closure argument.type output body captured, closureTyped⟩
  let args := [f, argument]; let types := [(["F"],f.type),(["A"],argument.type),(["R"],output)]
  let source ← parsed text
  let ps ← parameters types source.value.signature.parameters.elements args
  let inputs := ps.actual
  let h ← header types source output
  have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  have namesEq : inputs.names = ps.statics.names := by rw [← LocalInputs.toTypeInputs_names, erased]
  have contextEq : inputs.context = ps.statics.context := by rw [← LocalInputs.toTypeInputs_context, erased]
  check (decide (inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)) =
    [("x",⟨owner,1⟩,argument.type,argument.value),("f",⟨owner,0⟩,f.type,f.value)])) "original parameter-only record"
  let rows : PLift (inputs.environment.values = args.reverse.map (·.value)) ←
    if same : inputs.environment.values = args.reverse.map (·.value) then pure ⟨same⟩
    else throw (IO.userError "actual values reversed other than once")
  let o ← original source.value.body
  let expression : Syntax.Expr := ⟨o.span,.call o.callee ⟨o.argumentsSpan,[o.argument]⟩⟩
  let fn ← reference inputs o.callee; let arg ← reference inputs o.argument
  if children : fn.type = f.type ∧ arg.type = argument.type ∧ fn.core = .var 1 ∧ arg.core = .var 0 then
    have child : LocalFunctionApplicationElaborates inputs.names inputs.context expression target output := by
      have e := LocalFunctionApplicationElaborates.call (span := o.span) (argumentsSpan := o.argumentsSpan)
        fn.resolution fn.lowered (children.1 ▸ fn.typing) arg.resolution arg.lowered (children.2.1 ▸ arg.typing)
      simpa only [target,expression,children.2.2.1,children.2.2.2] using e
    have bodyElaboration : LocalApplicationReturnBodyElaborates inputs.names inputs.context source.value.body target output := by
      rw [o.shape]; exact .application child
    let fp ← observed inputs o.callee f.value; let ap ← observed inputs o.argument argument.value
    have costed : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment s expression value t (bodyCost + 5) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        LocalFunctionApplicationEvaluatesWithCost.call (span := o.span) (argumentsSpan := o.argumentsSpan) (fp.evidence s) (ap.evidence s) (bodyPath [])
    have bodyCosted : LocalApplicationReturnBodyEvaluatesWithCost inputs.names inputs.environment s source.value.body value t (bodyCost + 5) := by
      rw [o.shape]; exact .application costed
    have manual (k) : Core.Steps (bodyCost + 5) ⟨.eval target inputs.environment.values,k,s⟩ ⟨.ret value,k,t⟩ := by
      rw [rows.down]; exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (bodyPath k)))))
    have _ := bodyCosted.deterministic ((bodyElaboration.evaluatesWithCost_iff_steps inputs.sameIds).mpr (manual []))
    let compiled : CompiledRuntimeFunction := ⟨ps.statics,target,output⟩
    let prepared : PreparedRuntimeFunction := ⟨inputs,target,output⟩
    have compilation : RuntimeApplicationFunctionCompiles types owner source compiled :=
      ⟨h.down,ps.declared,by rw [← namesEq,← contextEq]; exact bodyElaboration⟩
    have preparation : RuntimeApplicationFunctionPrepares types owner source args prepared := ⟨h.down,ps.bound,bodyElaboration⟩
    have _ := compilation.complete
    have _ := compileRuntimeApplicationFunction?_iff.mp compilation.complete
    have _ := compilation.result_unique (compileRuntimeApplicationFunction?_sound compilation.complete)
    have _ := compilation.core_hasType
    have _ := prepareRuntimeApplicationFunction?_iff.mp preparation.complete
    have _ := preparation.result_unique (prepareRuntimeApplicationFunction?_sound preparation.complete)
    have _ := preparation.core_hasType
    have _ := preparation.compiles
    have matching : args.map (·.type) = compiled.inputs.context.values.reverse := by
      change args.map (·.type) = ps.statics.context.values.reverse
      rw [← contextEq]
      simpa only [LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,
        List.map_reverse,List.reverse_reverse] using congrArg List.reverse preparation.parameters.argument_types.symm
    have _ := compilation.prepare_arguments args matching
    have _ := runtimeApplicationFunctionPrepares_toCompiled_iff.mpr ⟨compilation,matching⟩
    have _ := prepareRuntimeApplicationFunction?_factorization types owner source args
    let cost := bodyCost + 5
    have equal (fuel store) : runRuntimeApplicationFunction? types owner source args fuel store =
        inputs.runApplication? fuel expression store := by
      rw [preparation.run_eq_body, o.shape]; exact inputs.runApplicationReturnBody?_return fuel _ _ expression store
    check (decide ((compileRuntimeApplicationFunction? types owner source).map (fun c => (c.inputs.names,c.inputs.context,c.core,c.returnType)) =
      some (ps.statics.names,ps.statics.context,target,output))) "independent static record"
    check (decide ((prepareRuntimeApplicationFunction? types owner source args).map
      (fun p => (p.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)),p.core,p.returnType)) =
      some (inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)),target,output))) "independent actual full record"
    check (decide (runRuntimeApplicationFunction? types owner source args 3 s = some (output,.outOfFuel
      ⟨.eval (.var 0) inputs.environment.values,[.applyClosure argument.type output body captured],s⟩))) "exact cp3"
    if body == .loadCell (.var 1) && captured == [.cellRef .word 0] then
      check (decide (runRuntimeApplicationFunction? types owner source args 7 [] = some (output,
        .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩))) "missing-cell fault hidden"
    for fuel in List.range (cost + 3) do
      have _ := runRuntimeApplicationFunction?_eq_none_iff (types := types) (owner := owner) (declaration := source) (arguments := args) fuel s
      have _ := (runRuntimeApplicationFunction?_eq_some_iff (fuel := fuel) (store := s)).mpr ⟨prepared,preparation,rfl,rfl⟩
      have _ := compilation.run_eq args matching fuel s
      have _ := (LocalInputs.runApplicationReturnBody?_done_iff_typed_cost).mpr
        ⟨bodyElaboration.hasType,cost,bodyCosted,Nat.le_refl cost⟩
      check ((compileRuntimeFunction? types owner source).isNone && (prepareRuntimeFunction? types owner source args).isNone &&
        (runRuntimeFunction? types owner source args fuel s).isNone) "old whole entry changed"
      check (decide (runRuntimeApplicationFunction? types owner source args fuel s = inputs.runApplicationReturnBody? fuel source.value.body s ∧
        runRuntimeApplicationFunction? types owner source args fuel s = some (output,Core.runStateful fuel (.initial target inputs.environment.values s)))) "entry/body exact result"
      match stopped : runRuntimeApplicationFunction? types owner source args fuel s with
      | some (_, .done v final) => check (decide (cost ≤ fuel ∧ v = value ∧ final = t)) "independent terminal observation"
      | some (_, .outOfFuel checkpoint) =>
          have childStopped := (equal fuel s) ▸ stopped
          have _ := LocalInputs.runApplication?_residual_of_outOfFuel costed childStopped
          check (decide (fuel < cost ∧ Core.runStateful (cost - fuel) checkpoint = .done value t)) "genuine remainder"
          for additional in [0,1,cost-fuel,cost+2] do
            have _ := LocalInputs.runApplication?_resume childStopped additional
            check (decide (runRuntimeApplicationFunction? types owner source args (fuel+additional) s =
              some (output,Core.runStateful additional checkpoint))) "full entry residual transport"
      | _ => throw (IO.userError "independent successful path lost")
    for otherStore in [[],[.bool true]] do
      match stopped : runRuntimeApplicationFunction? types owner source args 3 otherStore with
      | some (tag,.outOfFuel checkpoint) =>
          have childStopped := (equal 3 otherStore) ▸ stopped
          for additional in [0,4,5,cost+2] do
            have _ := LocalInputs.runApplication?_resume childStopped additional
            check (decide (tag = output ∧ runRuntimeApplicationFunction? types owner source args (3+additional) otherStore =
              some (output,Core.runStateful additional checkpoint))) "unvalidated-store outcome hidden"
      | _ => throw (IO.userError "genuine cp3 lost before body")
  else throw (IO.userError "original independent call children")
private def rejected (types : TypeNameTable) (args : List TypedRuntimeArgument) (text : String) (badStatic : Bool) : IO Unit := do
  let source ← parsed text
  if badStatic then check (compileRuntimeApplicationFunction? types owner source).isNone "whole static gate"
  if badStatic && text.endsWith "{return f(x);}" then
    let ps ← parameters types source.value.signature.parameters.elements args
    check (decide (ps.actual.checkApplicationReturnBody? source.value.body = some (target,.word))) "local body success lost at whole header gate"
  have _ := compileRuntimeApplicationFunction?_eq_none_iff (types := types) (owner := owner) (declaration := source)
  have _ := prepareRuntimeApplicationFunction?_eq_none_iff (types := types) (owner := owner) (declaration := source) (arguments := args)
  have _ := prepareRuntimeApplicationFunction?_factorization types owner source args
  if text.endsWith "{return x;}" then
    check (decide (runRuntimeFunction? types owner source args 1 [] = some (.word,.done (w 9) []))) "old pure return success changed"
  for fuel in [0,3,20] do
    check ((prepareRuntimeApplicationFunction? types owner source args).isNone &&
      (runRuntimeApplicationFunction? types owner source args fuel []).isNone) "whole actual gate"
end ParsedRuntimeApplicationEntries
open ParsedRuntimeApplicationEntries
def frontendParsedRuntimeApplicationEntryTests : IO Unit := do
  for (n,x) in [(0,9),(0,14),(1,14),(4,14),(9,14)] do
    execute ⟨.word,w x,.word⟩ .word (delayed n) [] [] [] (w x) (3*n+1)
      (.closure .nil (delayedTyped n .word [])) (delayedPath n (w x) [] [])
  for current in [3,17] do
    execute ⟨.word,w 9,.word⟩ .word (.loadCell (.var 1)) [.cellRef .word 0] [w current] [w current] (w current) 3
      (.closure (.cons .cellRef .nil) (.loadCell (.var rfl)))
      (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
    execute ⟨.word,w 9,.word⟩ (.cell .word) (.newCell .word (.var 0)) [] [w current] [w current,w 9] (.cellRef .word 1) 3
      (.closure .nil (.newCell (.var rfl))) (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
    execute ⟨.word,w 9,.word⟩ .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
      [w current] [w 9] (w 9) 10
      (.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl))))
      (fun _ => .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
        (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))))))))
  for type in [Core.Ty.namedData ⟨99⟩,.product (.namedData ⟨4⟩) (.namedData ⟨8⟩)] do
    let a : TypedRuntimeArgument := ⟨.function type type,.closure type type (.var 0) [],.closure .nil (.var rfl)⟩
    execute a a.type (.var 0) [] [] [] a.value 1 (.closure .nil (.var rfl)) (fun _ => .cons (.var rfl) .refl)
  execute ⟨.word,w 9,.word⟩ .word (.loadCell (.var 1)) [.cellRef .word 0] [.bool true] [.bool true] (.bool true) 3
    (.closure (.cons .cellRef .nil) (.loadCell (.var rfl)))
    (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
  have _ : ¬ Core.ValueHasType (.bool true) .word := by intro impossible; cases impossible
  let f : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩
  let x : TypedRuntimeArgument := ⟨.word,w 9,.word⟩
  let types : TypeNameTable := [(["F"],f.type),(["A"],.word),(["R"],.word),(["B"],.bool)]
  for args in [[],[f],[x,f],[f,⟨.bool,.bool true,.bool⟩],[f,x,x]] do rejected types args text false
  for signature in ["function invoke<T>(f:F,x:A) returns(R)","function invoke(f:F,x:A) returns()",
      "function invoke(f:F,x:A) returns(R,R)","function invoke(f:F,x:A) returns(B)","function invoke(f:F,x:A) returns(Unknown)"] do
    rejected types [f,x] (signature ++ "{return f(x);}") true
  for statements in ["return;","return x;","","return f(x);return x;","f(x);return x;","{return f(x);}","return f(f(x));"] do
    rejected types [f,x] ("function invoke(f:F,x:A) returns(R){" ++ statements ++ "}") true
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeComputationEntries
/-! Original declarations and actual records precede source certificates and independent fixed Core transition scripts. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RuntimeComputationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"MixedActual",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def app (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"mixed-actual.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "complete original bytes"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) :
    IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside named fixture")
private structure Parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning types annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters types (s.bindFresh owner name.value arg.type)
            (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,
            by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate original parameter")
      else throw (IO.userError "original argument type mismatch")
  | _,_ => throw (IO.userError "original parameter arity")
private structure Path (core : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩
-- A bounded fixture script constructs transitions; it never calls the machine runner.
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [original]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual var missing")
    | .unit => return ⟨.unit,s,1,fun _ => by rw [original]; exact .cons .unit .refl⟩
    | .bool b => return ⟨.bool b,s,1,fun _ => by rw [original]; exact .cons .bool .refl⟩
    | .letE head tail =>
        let a ← path n head env s; let b ← path n tail (a.value::env) a.final
        return ⟨b.value,b.final,a.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.letE (a.evidence _) (b.evidence _)⟩
    | .apply fn arg =>
        let f ← path n fn env s; let a ← path n arg env f.final
        match fv : f.value with
        | .closure _ _ body captured =>
            let b ← path n body (a.value::captured) a.final
            return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.apply (fv ▸ f.evidence _) (a.evidence _) (b.evidence [])⟩
        | _ => throw (IO.userError "manual callee shape")
    | .ifE condition yes no =>
        let c ← path n condition env s
        match cv : c.value with
        | .bool true =>
            let b ← path n yes env c.final
            return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifTrue (cv ▸ c.evidence _) (b.evidence _)⟩
        | .bool false =>
            let b ← path n no env c.final
            return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifFalse (cv ▸ c.evidence _) (b.evidence _)⟩
        | _ => throw (IO.userError "manual guard shape")
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [original]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual load missing")
        | _ => throw (IO.userError "manual reference shape")
    | .newCell t (.var i) =>
        match found : env[i]? with
        | some v => return ⟨.cellRef t s.length,s++[v],3,fun _ => by rw [original]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
        | none => throw (IO.userError "manual allocation value")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Leaf (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  id : Resolved.LocalId
  index : Nat
  type : Core.Ty
  value : Core.Value
  resolution : ResolvesLocalExpression s.names source (.var id)
  lowered : Resolved.Lowers s.context.ids (.var id) (.var index)
  typing : Resolved.HasType s.context (.var id) type
  raw : LocalExpressionEvaluatesWithCost s.names env store source value store 1
private def leaf (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Leaf s env store source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨id,i,t,v,by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed),
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual)⟩
          | _,_,_ => throw (IO.userError "independent original row missing")
      | none => throw (IO.userError "independent original name missing")
  | _ => throw (IO.userError "fixture leaf is not identifier")
private structure Child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : LocalComputationElaborates s.names s.context source core type
  raw : LocalComputationEvaluatesWithCost s.names env store source value final cost
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (source.span.contains fn.span && source.span.contains argsSpan && argsSpan.contains arg.span) "original call child spans"
      let f ← leaf s env store fn; let a ← leaf s env store arg
      match ft : f.type, fv : f.value with
      | .function input output,.closure _ _ body captured =>
          if same : a.type=input then
            let b ← path 100 body (a.value::captured) store
            return ⟨.apply (.var f.index) (.var a.index),output,b.value,b.final,b.cost+5,
              by rw [original]; exact .application (.call f.resolution f.lowered (ft ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)),
              by rw [original,←(show 1+1+b.cost+3=b.cost+5 by omega)]; exact .application (.call (fv ▸ f.raw) a.raw (b.evidence []))⟩
          else throw (IO.userError "static argument differs")
      | _,_ => throw (IO.userError "static or actual Function differs")
  | _ =>
      let a ← leaf s env store source
      return ⟨.var a.index,a.type,a.value,store,1,.pure a.resolution a.lowered a.typing,.pure a.raw⟩
private structure Tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : LocalComputationReturnTreeElaborates types owner s source core type
  raw : LocalComputationReturnTreeEvaluatesWithCost owner s.names env store source value final cost
private def tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) : IO (Tree types s env store source) := do
  match original : source with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ =>
      return ⟨.unit,.unit,.unit,store,1,by rw [original]; exact .bare,by rw [original]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
      let a ← child s env store e
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .expression a.elaboration,by rw [original]; exact .expression a.raw⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ =>
      let b ← tree types s env store ⟨span,statements⟩
      return ⟨b.core,b.type,b.value,b.final,b.cost,by rw [original]; exact .block b.elaboration,by rw [original]; exact .block b.raw⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child s env store e
      if unused : name.value ∉ s.names.map Prod.fst then
        let id := Resolved.freshLocalId owner s.ids
        let b ← tree types (s.bindFresh owner name.value a.type) ((id,a.value)::env) a.final ⟨span,rest⟩
        have raw : LocalComputationReturnTreeEvaluatesWithCost owner s.names env store source b.value b.final (a.cost+b.cost+2) := by
          rw [original]; cases annotation <;> first | exact .inferred a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw) | exact .binding a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw)
        match annotationAt : annotation with
        | none => return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .inferred unused a.elaboration b.elaboration,raw⟩
        | some t =>
            let m ← meaning types t
            if same : m.1=a.type then return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .binding (same ▸ m.2.down) unused a.elaboration b.elaboration,raw⟩
            else throw (IO.userError "original binding annotation differs")
      else throw (IO.userError "shadowing is still excluded")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ =>
      let a ← child s env store e; let b ← tree types s env a.final ⟨span,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,b.value,b.final,a.cost+b.cost+2,by rw [original]; exact .discard a.elaboration b.elaboration,by rw [original]; exact .discard a.raw b.raw⟩
  | ⟨_,[⟨_,.ifThen e yes (some no)⟩]⟩ =>
      let c ← child s env store e
      if ct : c.type=.bool then
        let a ← tree types s env c.final yes; let b ← tree types s env c.final no
        if same : b.type=a.type then
          have el : LocalComputationReturnTreeElaborates types owner s source (.ifE c.core a.core b.core) a.type := by rw [original]; exact .conditional (ct ▸ c.elaboration) a.elaboration (same ▸ b.elaboration)
          match cv : c.value with
          | .bool true => return ⟨.ifE c.core a.core b.core,a.type,a.value,a.final,c.cost+a.cost+2,el,by rw [original]; exact .ifTrue (cv ▸ c.raw) a.raw⟩
          | .bool false => return ⟨.ifE c.core a.core b.core,a.type,b.value,b.final,c.cost+b.cost+2,el,by rw [original]; exact .ifFalse (cv ▸ c.raw) b.raw⟩
          | _ => throw (IO.userError "actual guard differs")
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "static guard differs")
  | _ => throw (IO.userError "outside original mixed body fixture")
termination_by sizeOf source
private def header (types : TypeNameTable) (source : Syntax.FunctionDecl) (output : Core.Ty) : IO (PLift (RuntimeFunctionHeader types source.value.signature output)) := do
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.1=output then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧
            source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          return ⟨⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.2.down)⟩⟩
        else throw (IO.userError "original header policy")
      else throw (IO.userError "original return meaning")
  | _ => throw (IO.userError "original singleton return clause")
private def verify (body : String) (f g x : TypedRuntimeArgument) (output : Core.Ty)
    (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["R"],output),(["Cell"],.cell .word)]
  let source ← parsed ("function mixed(f:F,g:G,x:X) returns(R){"++body++"}"); let args := [f,g,x]
  let ps ← parameters types .empty .empty source.value.signature.parameters.elements args; let inputs := ps.actual
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body
  let manual ← path 100 core [x.value,g.value,f.value] s
  have erased : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  check (decide (inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original one-time actual rows"
  if fixed : b.core=core ∧ b.type=output then
    have preparation : RuntimeComputationFunctionPrepares types owner source args ⟨inputs,core,output⟩ :=
      ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have compilation : RuntimeComputationFunctionCompiles types owner source ⟨ps.statics,core,output⟩ :=
      ⟨h.down,ps.declared,by rw [←erased]; exact preparation.body⟩
    have compiled := compileRuntimeComputationFunction?_iff.mpr compilation
    have prepared := prepareRuntimeComputationFunction?_iff.mpr preparation
    have _ := compileRuntimeComputationFunction?_iff.mp compiled
    have _ := prepareRuntimeComputationFunction?_iff.mp prepared
    have matching : args.map (·.type)=ps.statics.context.values.reverse := by
      have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
      simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
    have _ : (prepareRuntimeComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some ⟨ps.statics,core,output⟩ := by rw [prepareRuntimeComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
    have whole (fuel) : runRuntimeComputationFunction? types owner source args fuel s =
        some (output,Core.runStateful fuel (.initial core [x.value,g.value,f.value] s)) := by
      rw [runRuntimeComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte,args,List.reverse_cons,List.reverse_nil]; rfl
    have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
    have _ := b.raw.toStepsWithContinuation b.elaboration ids [.letBody .unit []]
    check (decide (b.value=value ∧ b.final=final ∧ b.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent raw/Core value-store-cost"
    check (decide (compileRuntimeFunction? types owner source=none ∧ compileRuntimeApplicationFunction? types owner source=none)) "old whole profiles stay separate"
    for fuel in List.range (cost+2) do
      have _ := whole fuel
      check (decide (runRuntimeComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial core [x.value,g.value,f.value] s)) ∧ runRuntimeFunction? types owner source args fuel s=none ∧ runRuntimeApplicationFunction? types owner source args fuel s=none)) "new full result versus old entry rejection"
      match exhausted : Core.runStateful fuel (.initial core [x.value,g.value,f.value] s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact actual completion"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel exhausted
          have _ := Core.runStateful_resume exhausted (cost-fuel)
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧ runRuntimeComputationFunction? types owner source args (fuel+2) s=some (output,Core.runStateful 2 cp))) "entry retains genuine residual/full resume"
      | .fault _ _ => throw (IO.userError "independent successful path faulted")
  else throw (IO.userError "independent exact Core/type")
private def reader : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def delay : Nat → Core.Expr | 0 => .var 0 | n+1 => .letE (.var 0) (delay n)
private theorem delayTyped (n : Nat) (ctx : Core.Context) (found : ctx[0]?=some .word) : Core.HasType ctx (delay n) .word := by
  induction n generalizing ctx with | zero => exact .var found | succ n ih => exact .letE (.var found) (ih _ rfl)
end RuntimeComputationEntries
open RuntimeComputationEntries
def frontendParsedRuntimeComputationEntryTests : IO Unit := do
  let x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩
  for old in [3,23] do
    verify "f(x);return g(x);" writer reader x .word (.letE (app 2 0) (app 2 1)) [w old] [w 14] (w 14) 25
    verify "f(x);{g(x);return x;}" writer reader x .word (.letE (app 2 0) (.letE (app 2 1) (.var 2))) [w old] [w 14] (w 14) 28
    verify "f(x);return g;" writer reader x reader.type (.letE (app 2 0) (.var 2)) [w old] [w 14] reader.value 18
    let alloc : TypedRuntimeArgument := ⟨.function .word (.cell .word),.closure .word (.cell .word) (.newCell .word (.var 0)) [],.closure .nil (.newCell (.var rfl))⟩
    let load : TypedRuntimeArgument := ⟨.function (.cell .word) .word,.closure (.cell .word) .word (.loadCell (.var 0)) [],.closure .nil (.loadCell (.var rfl))⟩
    for annotation in ["",":Cell"] do
      verify ("let p"++annotation++"=f(x);return g(p);") alloc load x .word (.letE (app 2 0) (app 2 0)) [w old] [w old,w 14] (w 14) 18
    for choice in [false,true] do
      let guard : TypedRuntimeArgument := ⟨.function .word .bool,.closure .word .bool (.letE (.storeCell (.var 1) (.var 0)) (.bool choice)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) .bool)⟩
      verify "if(f(x)){return g(x);}else{return x;}" guard reader x .word (.ifE (app 2 0) (app 1 0) (.var 0)) [w old] [w 14] (w 14) (if choice then 23 else 16)
    let maker : TypedRuntimeArgument := ⟨.function .word reader.type,.closure .word reader.type (.var 1) [reader.value],.closure (.cons reader.valueTyped .nil) (.var rfl)⟩
    verify "let h=f(x);return h(x);" maker reader x .word (.letE (app 2 0) (app 0 1)) [w old] [w old] (w old) 16
  for n in [0,2,5,13] do
    let f : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (delay n) [],.closure .nil (delayTyped n _ rfl)⟩
    verify "let y=f(x);return y;" f reader x .word (.letE (app 2 0) (.var 0)) [] [] (w 14) (3*n+9)
  verify "f(x);return;" writer reader x .unit (.letE (app 2 0) .unit) [w 3] [w 14] .unit 18
  verify "let p=f(x);return p;" reader reader x .word (.letE (app 2 0) (.var 0)) [.bool true] [.bool true] (.bool true) 11
  for captured in [9,31] do
    let f : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w captured],.closure (.cons .word .nil) (.var rfl)⟩
    verify "let y=f(x);return y;" f reader x .word (.letE (app 2 0) (.var 0)) [] [] (w captured) 9
  let source ← parsed "function mixed(f:F,g:G,x:X) returns(R){let p=f(x);return p;}"
  let types : TypeNameTable := [(["F"],reader.type),(["G"],reader.type),(["X"],.word),(["R"],.word)]
  let args := [reader,reader,x]; let ps ← parameters types .empty .empty source.value.signature.parameters.elements args
  let h ← header types source .word; let b ← tree types ps.actual.toTypeInputs ps.actual.environment [.bool true] source.value.body
  let env := [x.value,reader.value,reader.value]; let core := Core.Expr.letE (app 2 0) (.var 0)
  if fixed : b.core=core ∧ b.type=.word then
    have p : RuntimeComputationFunctionPrepares types owner source args ⟨ps.actual,core,.word⟩ := ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have _ := prepareRuntimeComputationFunction?_iff.mpr p
    let cp : Core.State := ⟨.ret reader.value,[.applyArgument (.var 0) env,.letBody (.var 0) env],[]⟩
    let fault := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply,.letBody (.var 0) env],[]⟩
    check (decide (runRuntimeComputationFunction? types owner source args 3 []=some (.word,.outOfFuel cp) ∧ runRuntimeComputationFunction? types owner source args 8 []=some (.word,fault) ∧ Core.runStateful 5 cp=fault)) "prepared entry preserves exact missing-store fault"
  else throw (IO.userError "fault fixture exact static Core")
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedCompiledExecution
/-! A cached result from complete source compilation determines full runtime
states for many actual argument lists, including exact guard rejection. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def parsed_variant? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "compiled-execution.sol"⟩, content }
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

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Cached", by decide⟩], by decide⟩⟩, 7⟩
private def types : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["U"], .unit),
    (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def identityClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
private def constantClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.bool false) [], .closure .nil .bool⟩
private def store_variant : Core.Store := [.bool false, .word (word 91)]

/-- Use the cached compilation, not another body/preparation lookup, on the
expected side. The actual side is the unchanged public runtime endpoint. -/
private def compareFuels_variant (declaration : Syntax.FunctionDecl) (cached : Option CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) (fuels : List Nat) (initialStore : Core.Store) : IO Unit := do
  for fuel in fuels do
    let expected := cached.bind fun compiled =>
      if arguments.map (·.type) = compiled.inputs.context.values.reverse then
        some (compiled.returnType, Core.runStateful fuel
          (Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore))
      else none
    assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel initialStore = expected))
      s!"{declaration.value.signature.name.value}: cached compilation changed the full result at fuel {fuel}"

private def accepted (content : String) (parameterTypes : List Core.Ty)
    (expectedCore : Core.Expr) (returnType : Core.Ty) : IO (Syntax.FunctionDecl × CompiledRuntimeFunction) := do
  let some declaration ← parsed_variant? content | throw (IO.userError s!"{content}: incomplete declaration")
  let some compiled := compileRuntimeFunction? types owner declaration
    | throw (IO.userError s!"{content}: compilation failed")
  assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = returnType ∧
    compiled.inputs.context.values = parameterTypes.reverse)) s!"{content}: wrong exact static output"
  assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some returnType))
    s!"{content}: actual open Core is not typed"
  return (declaration, compiled)

private def completed (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) (expected : Core.Value) (cost : Nat)
    (initialStore : Core.Store := store_variant) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) = compiled.inputs.context.values.reverse))
    "completion case did not pass the ordered argument guard"
  compareFuels_variant declaration (some compiled) arguments (List.range (cost + 3)) initialStore
  let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore
  assertTrue (decide (runRuntimeFunction? types owner declaration arguments 0 initialStore =
    some (compiled.returnType, .outOfFuel initial))) "wrong exact zero-fuel state"
  assertTrue (match runRuntimeFunction? types owner declaration arguments (cost - 1) initialStore with
    | some (_, .outOfFuel _) => true | _ => false) "completed below the independent expected cost"
  for fuel in [cost, cost + 2] do
    assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel initialStore =
      some (compiled.returnType, .done expected initialStore))) "wrong value, store, or exact completion boundary"

private def mismatched (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ compiled.inputs.context.values.reverse))
    "mismatch fixture accidentally satisfied the ordered type guard"
  compareFuels_variant declaration (some compiled) arguments (List.range 20) store_variant
  assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
    "mismatched arguments were prepared"

def frontendParsedCompiledExecutionTests : IO Unit := do
  let (bare, bareCompiled) ← accepted "function bare() { return; }" [] .unit .unit
  completed bare bareCompiled [] .unit 1
  mismatched bare bareCompiled [boolArg false]
  for index in List.range 3 do
    let name := ["x", "y", "z"][index]!
    let (declaration, compiled) ← accepted
      ("function position(x: Bool, y: Bool, z: Bool) returns (Bool) { return " ++ name ++ "; }")
      [.bool, .bool, .bool] (.var (2 - index)) .bool
    for x in [false, true] do
      for y in [false, true] do
        for z in [false, true] do
          completed declaration compiled [boolArg x, boolArg y, boolArg z] (.bool ([x, y, z][index]!)) 1
    for arguments in [[], [boolArg false], [boolArg false, boolArg true],
        [boolArg false, boolArg true, boolArg false, boolArg true],
        [wordArg 7, boolArg false, boolArg true]] do
      mismatched declaration compiled arguments
  let (subtract, subtractCompiled) ← accepted
    "function difference(x: Word, y: Word) returns (Word) { return x - y; }"
    [.word, .word] (.binary .wordSub (.var 1) (.var 0)) .word
  for left in [0, 7, 9] do
    for right in [0, 7, 9] do
      let arguments := [wordArg left, wordArg right]
      completed subtract subtractCompiled arguments (.word ((word left).sub (word right))) 5
      assertTrue (decide (runRuntimeFunction? types owner subtract arguments 4 store_variant =
        some (.word, .outOfFuel ⟨.ret (.word (word right)),
          [.binaryApply .wordSub (.word (word left))], store_variant⟩))) "cached subtraction reversed the pending operands"
  let (branch, branchCompiled) ← accepted
    "function branch(c: Bool, x: Word, y: Word) returns (Word) { return c ? x * y : x; }"
    [.bool, .word, .word] (.ifE (.var 2) (.binary .wordMul (.var 1) (.var 0)) (.var 1)) .word
  for choice in [false, true] do
    completed branch branchCompiled [boolArg choice, wordArg 7, wordArg 9]
      (.word (word (if choice then 63 else 7))) (if choice then 8 else 4)
  for arguments in [[wordArg 7, boolArg true, wordArg 9], [boolArg true, boolArg false, wordArg 9],
      [boolArg true, wordArg 7], [boolArg true, wordArg 7, wordArg 9, wordArg 1]] do
    mismatched branch branchCompiled arguments
  let (short, shortCompiled) ← accepted
    "function short(c: Bool) returns (Bool) { return c && !c; }"
    [.bool] (.ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false)) .bool
  for choice in [false, true] do
    completed short shortCompiled [boolArg choice] (.bool false) (if choice then 6 else 4)
  assertTrue (decide (runRuntimeFunction? types owner short [boolArg false] 5 store_variant =
    some (.bool, .done (.bool false) store_variant))) "false short-circuit path did not finish at five"
  assertTrue (match runRuntimeFunction? types owner short [boolArg true] 5 store_variant with
    | some (.bool, .outOfFuel _) => true | _ => false) "equal argument types erased the selected path's extra cost"
  let (cell, cellCompiled) ← accepted
    "function cell(c: Bool, x: Cell, y: Cell) returns (Cell) { return c ? x : y; }"
    [.bool, .cell .word, .cell .word] (.ifE (.var 2) (.var 1) (.var 0)) (.cell .word)
  let (closure, closureCompiled) ← accepted
    "function closure(c: Bool, x: Fn, y: Fn) returns (Fn) { return c ? x : y; }"
    [.bool, .function .bool .bool, .function .bool .bool] (.ifE (.var 2) (.var 1) (.var 0)) (.function .bool .bool)
  for choice in [false, true] do
    completed cell cellCompiled [boolArg choice, cellArg 40, cellArg 91]
      (if choice then (cellArg 40).value else (cellArg 91).value) 4 []
    completed closure closureCompiled [boolArg choice, identityClosure, constantClosure]
      (if choice then identityClosure.value else constantClosure.value) 4
  let (nominal, nominalCompiled) ← accepted
    "function nominal(x: Opaque) returns (Opaque) { return x; }"
    [.namedData ⟨91⟩] (.var 0) (.namedData ⟨91⟩)
  for arguments in [[], [boolArg false], [wordArg 0], [cellArg 0], [identityClosure]] do
    mismatched nominal nominalCompiled arguments
  for content in ["function wrong(x: Word) returns (Word) { return x > 0; }",
      "function unknown(x: Missing) { return; }", "function duplicate(x: Bool, x: Bool) { return; }",
      "function empty() {}", "function invalid(c: Bool) returns (Bool) { return c || missing; }"] do
    let some declaration ← parsed_variant? content | throw (IO.userError "whole-rejection fixture did not parse")
    let cached := compileRuntimeFunction? types owner declaration
    assertTrue cached.isNone "invalid whole declaration compiled"
    for arguments in [[], [boolArg false], [boolArg true], [wordArg 7], [boolArg false, boolArg true]] do
      compareFuels_variant declaration cached arguments [0, 1, 4, 5, 20] store_variant
  for content in ["", "function f()", "function f() { return;", "function f() { return; } trailing"] do
    assertTrue (← parsed_variant? content).isNone "malformed or partially consumed declaration entered compiled tests"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedFunctionCompilation
/-! Full canonical declarations compile before any arguments are supplied.
Matching actual arguments then use the unchanged checked runtime endpoint. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def parsed_variant2? (content : String) (location : Syntax.Parser.FunctionLocation := .module) :
    IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-function-compilation.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner_variant : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Compilation", by decide⟩], by decide⟩⟩, 4⟩
private def types_variant : TypeNameTable :=
  [(["Bool"], .bool), (["Word"], .word), (["U"], .unit), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def seven : Core.Word := ⟨7, by decide⟩
private def nine : Core.Word := ⟨9, by decide⟩
private def store_variant2 : Core.Store := [.word nine, .bool false]
private def wordArg_variant (value : Core.Word) : TypedRuntimeArgument := ⟨.word, .word value, .word⟩
private def cellArg_variant : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
private def sameCompiled : Option CompiledRuntimeFunction → Option CompiledRuntimeFunction → Bool
  | none, none => true
  | some left, some right =>
      decide (left.inputs.bindings.map (fun row => (row.name, row.id, row.type)) =
        right.inputs.bindings.map (fun row => (row.name, row.id, row.type))) &&
      decide (left.core = right.core) && decide (left.returnType = right.returnType)
  | _, _ => false

private def checkCompiled (table : TypeNameTable) (declaration : Syntax.FunctionDecl)
    (expectedTypes : List Core.Ty) (expectedCore : Core.Expr) (expectedType : Core.Ty) :
    IO CompiledRuntimeFunction := do
  let some compiled := compileRuntimeFunction? table owner_variant declaration
    | throw (IO.userError "value-free compilation failed")
  assertTrue (decide (compiled.core = expectedCore)) "compiler did not keep the exact elaborated Core"
  assertTrue (decide (compiled.returnType = expectedType)) "compiler changed the return contract"
  assertTrue (decide (compiled.inputs.context.values = expectedTypes.reverse)) "wrong static parameter types"
  assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some expectedType))
    "compiled open Core did not type-check in its parameter context"
  let names ← declaration.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name _ := parameter.value | throw (IO.userError "unexpected parameter profile")
    pure name.value
  assertTrue (decide (names.length = expectedTypes.length)) "wrong expected parameter count"
  assertTrue (decide (compiled.inputs.names = (names.zipIdx.map fun (name, index) =>
    (name, (⟨owner_variant, index⟩ : Resolved.LocalId))).reverse)) "wrong compiled name/identity table"
  return compiled

private def checkRun (table : TypeNameTable) (declaration : Syntax.FunctionDecl)
    (compiled : CompiledRuntimeFunction) (arguments : List TypedRuntimeArgument)
    (value : Core.Value) (cost : Nat) (initialStore : Core.Store := store_variant2) : IO Unit := do
  let prepared := prepareRuntimeFunction? table owner_variant declaration arguments
  assertTrue (sameCompiled (prepared.map PreparedRuntimeFunction.toCompiled) (some compiled))
    "matching actual arguments changed the compiled projection"
  let actualValues := arguments.reverse.map (·.value)
  for fuel in [0, 1, cost - 1, cost, cost + 5] do
    assertTrue (decide (runRuntimeFunction? table owner_variant declaration arguments fuel initialStore =
      some (compiled.returnType, Core.runStateful fuel (Core.State.initial compiled.core actualValues initialStore))))
      "checked entry did not run the actual compiled Core with actual argument values"
  assertTrue (decide (runRuntimeFunction? table owner_variant declaration arguments 0 initialStore =
    some (compiled.returnType, .outOfFuel (Core.State.initial compiled.core actualValues initialStore))))
    "zero-fuel state changed through compilation"
  match runRuntimeFunction? table owner_variant declaration arguments (cost - 1) initialStore with
  | some (_, .outOfFuel _) => pure ()
  | _ => throw (IO.userError "entry completed below its exact cost")
  for fuel in [cost, cost + 5] do
    assertTrue (decide (runRuntimeFunction? table owner_variant declaration arguments fuel initialStore =
      some (compiled.returnType, .done value initialStore))) "wrong result, store, or exact fuel boundary"

private def checkAccepted (content : String) (expectedTypes : List Core.Ty)
    (core : Core.Expr) (type : Core.Ty) : IO (Syntax.FunctionDecl × CompiledRuntimeFunction) := do
  let some declaration ← parsed_variant2? content | throw (IO.userError s!"{content}: expected complete declaration")
  let compiled ← checkCompiled types_variant declaration expectedTypes core type
  return (declaration, compiled)

def frontendParsedFunctionCompilationTests : IO Unit := do
  let (bare, bareCompiled) ← checkAccepted "function bare() { return; }" [] .unit .unit
  checkRun types_variant bare bareCompiled [] .unit 1
  let (literal, literalCompiled) ← checkAccepted "function literal() returns (Word) { return 7; }"
    [] (.word seven) .word
  checkRun types_variant literal literalCompiled [] (.word seven) 1
  let _ ← checkAccepted "function opaque(x: Opaque) returns (Opaque) { return x; }"
    [.namedData ⟨91⟩] (.var 0) (.namedData ⟨91⟩)
  let _ ← checkAccepted "function choice(c: Bool, x: Opaque, y: Opaque) returns (Opaque) { return c ? x : y; }"
    [.bool, .namedData ⟨91⟩, .namedData ⟨91⟩] (.ifE (.var 2) (.var 1) (.var 0)) (.namedData ⟨91⟩)
  let _ ← checkAccepted "function unused(x: Opaque) { return; }" [.namedData ⟨91⟩] .unit .unit
  let (first, firstCompiled) ← checkAccepted "function first(x: Bool, y: Bool) returns (Bool) { return x; }"
    [.bool, .bool] (.var 1) .bool
  for left in [false, true] do
    for right in [false, true] do
      checkRun types_variant first firstCompiled [boolArg left, boolArg right] (.bool left) 1
  let (branch, branchCompiled) ← checkAccepted
    "function branch(c: Bool, t: Word, f: Word) returns (Word) { return c ? ~t : f; }"
    [.bool, .word, .word] (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
  for choice in [false, true] do
    checkRun types_variant branch branchCompiled [boolArg choice, wordArg_variant seven, wordArg_variant nine]
      (.word (if choice then seven.bitNot else nine)) (if choice then 6 else 4)
  let (cell, cellCompiled) ← checkAccepted "function cell(x: Cell) returns (Cell) { return x; }"
    [.cell .word] (.var 0) (.cell .word)
  checkRun types_variant cell cellCompiled [cellArg_variant] cellArg_variant.value 1 []
  let (closure, closureCompiled) ← checkAccepted "function closure(x: Fn) returns (Fn) { return x; }"
    [.function .bool .bool] (.var 0) (.function .bool .bool)
  checkRun types_variant closure closureCompiled [closureArg] closureArg.value 1
  let some alias ← parsed_variant2? "function alias(x: Word) returns (Word) { return x; }"
    | throw (IO.userError "alias declaration did not parse")
  let aliasCompiled ← checkCompiled [(["Word"], .bool)] alias [.bool] (.var 0) .bool
  checkRun [(["Word"], .bool)] alias aliasCompiled [boolArg true] (.bool true) 1
  for arguments in [[], [boolArg true], [boolArg true, boolArg false, boolArg true],
      [wordArg_variant seven, boolArg true], [boolArg true, wordArg_variant seven]] do
    assertTrue (prepareRuntimeFunction? types_variant owner_variant first arguments).isNone
      "static success bypassed argument arity/type checking"
  for arguments in [[wordArg_variant seven, boolArg true, wordArg_variant nine],
      [boolArg true, boolArg false, wordArg_variant nine]] do
    assertTrue (prepareRuntimeFunction? types_variant owner_variant branch arguments).isNone
      "static success bypassed ordered argument types"
  for content in ["function bad() returns (Bool) { return 7; }", "function absent() { return 7; }",
      "function empty() returns () { return; }", "function many() returns (Word, Bool) { return 7; }",
      "function generic<T>() { return; }", "function constrained() where Word: Eq { return; }",
      "function duplicate(x: Bool, x: Bool) returns (Bool) { return x; }",
      "function staged(comptime x: Bool) returns (Bool) { return x; }",
      "function unknown(x: Unknown) { return; }", "function emptyBody() {}",
      "function repeated() { return; return; }", "function tail() returns (Word) { 7 }",
      "function missing(c: Bool, x: Word) returns (Word) { return c ? x : missing; }",
      "function types(c: Bool, x: Word) returns (Word) { return c ? x : c; }"] do
    let some declaration ← parsed_variant2? content | throw (IO.userError s!"{content}: rejection case should parse")
    assertTrue (compileRuntimeFunction? types_variant owner_variant declaration).isNone "invalid whole contract compiled"
    for arguments in [[], [boolArg false, wordArg_variant seven], [boolArg true, wordArg_variant nine]] do
      assertTrue (prepareRuntimeFunction? types_variant owner_variant declaration arguments).isNone
        "runtime preparation bypassed compile rejection"
  for content in ["function publicOnly() public { return; }", "function payableOnly() payable { return; }"] do
    let some declaration ← parsed_variant2? content .contract | throw (IO.userError "contract modifier case did not parse")
    assertTrue (compileRuntimeFunction? types_variant owner_variant declaration).isNone "unsupported modifier compiled"
  for content in ["", "function f()", "function f() { return;", "function f() { return 7 }",
      "function f() { return; } trailing", "function f() public { return; }"] do
    assertTrue (← parsed_variant2? content).isNone "malformed, diagnosed, or incompletely consumed source accepted"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeFunctionEntries
/-! Fully parsed declarations enter the restricted runtime profile through
their actual header, parameter list, and body. No function lookup or call
continuation is simulated by this external-entry test. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def parsed_variant3? (content : String) (location : Syntax.Parser.FunctionLocation := .module) :
    IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-runtime-function.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner_variant2 : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Entry", by decide⟩], by decide⟩⟩, 0⟩
private def store_variant3 : Core.Store := [.word nine, .bool true]
private def types_variant2 : TypeNameTable :=
  [(["Bool"], .bool), (["Word"], .word), (["U"], .unit), (["Pkg", "Flag"], .bool),
   (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def closure : Core.Value := .closure .bool .bool (.var 0) []
private theorem closureTyped : Core.ValueHasType closure (.function .bool .bool) :=
  .closure .nil (.var rfl)

private def checkOrder (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (inputs : LocalInputs) : IO Unit := do
  let names ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name _ := parameter.value
      | throw (IO.userError "accepted a non-runtime parameter")
    pure name.value
  assertTrue (decide (names.length = arguments.length)) "accepted mismatched arity"
  let expected : List (String × Resolved.LocalId × Core.Ty × Core.Value) :=
    (names.zip arguments).zipIdx.map fun (entry, index) =>
      (entry.1, (⟨owner_variant2, index⟩ : Resolved.LocalId), entry.2.type, entry.2.value)
  let actual := inputs.bindings.map fun binding =>
    (binding.name, binding.id, binding.type, binding.value)
  assertTrue (decide (actual = expected.reverse))
    "entry changed argument pairing, identity allocation, or runtime row order"

private def checkAccepted_variant (table : TypeNameTable) (content : String)
    (arguments : List TypedRuntimeArgument) (expectedCore : Core.Expr) (type : Core.Ty)
    (value : Core.Value) (cost : Nat) (initialStore : Core.Store := store_variant3) : IO Unit := do
  let some source ← parsed_variant3? content
    | throw (IO.userError s!"{content}: expected a complete declaration")
  let some prepared := prepareRuntimeFunction? table owner_variant2 source arguments
    | throw (IO.userError s!"{content}: valid restricted entry was rejected")
  checkOrder source arguments prepared.inputs
  assertTrue (decide (prepared.core = expectedCore ∧ prepared.returnType = type))
    s!"{content}: wrong exact Core or declared return type"
  assertTrue (decide (prepared.inputs.checkReturnBody? source.value.body =
    some (prepared.core, prepared.returnType))) s!"{content}: prepared a substitute Core"
  assertTrue (decide (runRuntimeFunction? table owner_variant2 source arguments 0 initialStore =
    some (type, .outOfFuel (Core.State.initial prepared.core prepared.inputs.environment.values initialStore))))
    s!"{content}: zero fuel did not expose the actual prepared initial state"
  for fuel in [0, 1, 3, 4, 5, 6, 8, cost - 1, cost, cost + 5] do
    assertTrue (decide (runRuntimeFunction? table owner_variant2 source arguments fuel initialStore =
      prepared.inputs.runReturnBody? fuel source.value.body initialStore))
      s!"{content}: entry changed body execution or a suspended state"
  for fuel in [0, cost - 1] do
    match runRuntimeFunction? table owner_variant2 source arguments fuel initialStore with
    | some (actualType, .outOfFuel _) =>
        assertTrue (decide (actualType = type)) s!"{content}: exhaustion changed the return type"
    | _ => throw (IO.userError s!"{content}: execution did not exhaust below its exact cost")
  for fuel in [cost, cost + 5] do
    assertTrue (decide (runRuntimeFunction? table owner_variant2 source arguments fuel initialStore =
      some (type, .done value initialStore)))
      s!"{content}: wrong value, preserved store, or exact completion threshold"

private def checkRejected (content : String) (arguments : List TypedRuntimeArgument := [])
    (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let some source ← parsed_variant3? content location
    | throw (IO.userError s!"{content}: profile rejection case should parse without diagnostics")
  assertTrue (prepareRuntimeFunction? types_variant2 owner_variant2 source arguments).isNone
    s!"{content}: unsupported or mismatched declaration entered the runtime profile"
  for fuel in [0, 1, 4, 20] do
    assertTrue (runRuntimeFunction? types_variant2 owner_variant2 source arguments fuel store_variant3).isNone
      s!"{content}: running bypassed whole declaration preparation"

private def checkInferredLocal : IO Unit := do
  let some source ← parsed_variant3? "function local() returns (Word) { let x = 7; return x; }"
    | throw (IO.userError "original inferred local declaration did not parse")
  assertTrue (match source.value.body.value with
    | [⟨ls,.letDecl name none (some ⟨_,.literal ⟨_,.decimal spelling⟩⟩)⟩,
        ⟨rs,.returnStmt (some ⟨_,.identifier returned⟩)⟩] =>
        decide (name.value = "x" ∧ returned.value = "x" ∧ spelling = "7") &&
        source.value.body.span.contains ls && source.value.body.span.contains rs
    | _ => false) "original missing annotation or written initializer was changed"
  let core : Core.Expr := .letE (.word seven) (.var 0)
  let some prepared := prepareRuntimeFunction? types_variant2 owner_variant2 source []
    | throw (IO.userError "inferred initialized local was rejected")
  checkOrder source [] prepared.inputs
  assertTrue (decide (prepared.core = core ∧ prepared.returnType = .word) &&
    (prepared.inputs.checkReturnBody? source.value.body).isNone)
    "inferred local changed exact Core or broadened the old singleton body"
  for initialStore in [store_variant3, []] do
    have paths (k : List Core.Frame) : Core.Steps 4 ⟨.eval core [], k, initialStore⟩
        ⟨.ret (.word seven), k, initialStore⟩ :=
      .cons .enterLet (.cons .word (.cons .bindLet (.cons (.var rfl) .refl)))
    have _ := paths []
    for fuel in List.range 7 ++ [20] do
      assertTrue (match runRuntimeFunction? types_variant2 owner_variant2 source [] fuel initialStore with
        | some (.word,.done value final) => decide (4 ≤ fuel ∧ value = .word seven ∧ final = initialStore)
        | some (.word,.outOfFuel saved) => decide (fuel < 4 ∧ saved.store = initialStore)
        | _ => false) "inferred local changed its independently counted four steps"
    let saved : Core.State := ⟨.ret (.word seven),[.letBody (.var 0) []],initialStore⟩
    assertTrue (decide (runRuntimeFunction? types_variant2 owner_variant2 source [] 2 initialStore = some (.word,.outOfFuel saved) ∧
      Core.runStateful 2 saved = .done (.word seven) initialStore)) "inferred local lost its genuine pending let"

private def checkDiscardLiteral : IO Unit := do
  let some source ← parsed_variant3? "function before() { 7; return; }"
    | throw (IO.userError "original discarded literal declaration did not parse")
  assertTrue (match source.value.body.value with
    | [⟨ss,.expression ⟨es,.literal ⟨_,.decimal spelling⟩⟩ true⟩, ⟨rs,.returnStmt none⟩] =>
        decide (spelling = "7") && ss.contains es && source.value.body.span.contains ss &&
        source.value.body.span.contains rs
    | _ => false) "original expression, semicolon or bare return was changed"
  let core : Core.Expr := .letE (.word seven) .unit
  let some prepared := prepareRuntimeFunction? types_variant2 owner_variant2 source []
    | throw (IO.userError "strict discarded literal was rejected")
  checkOrder source [] prepared.inputs
  assertTrue (decide (prepared.core = core ∧ prepared.returnType = .unit) &&
    (prepared.inputs.checkReturnBody? source.value.body).isNone)
    "discard changed exact Core or widened the old singleton adapter"
  for initialStore in [store_variant3, []] do
    have paths (k : List Core.Frame) : Core.Steps 4 ⟨.eval core [], k, initialStore⟩
        ⟨.ret .unit, k, initialStore⟩ :=
      .cons .enterLet (.cons .word (.cons .bindLet (.cons .unit .refl)))
    have _ := paths []
    for fuel in List.range 7 ++ [20] do
      assertTrue (match runRuntimeFunction? types_variant2 owner_variant2 source [] fuel initialStore with
        | some (.unit,.done value final) => decide (4 ≤ fuel ∧ value = .unit ∧ final = initialStore)
        | some (.unit,.outOfFuel saved) => decide (fuel < 4 ∧ saved.store = initialStore)
        | _ => false) "discarded literal work was skipped or counted twice"
    for spent in List.range 4 do
      let some (.unit,.outOfFuel saved) := runRuntimeFunction? types_variant2 owner_variant2 source [] spent initialStore
        | throw (IO.userError "genuine discard checkpoint absent")
      for remaining in List.range 7 do
        assertTrue (decide (Core.runStateful remaining saved =
          Core.runStateful (spent + remaining) (.initial core [] initialStore))) "discard checkpoint was restarted"
    let saved : Core.State := ⟨.ret (.word seven),[.letBody .unit []],initialStore⟩
    assertTrue (decide (runRuntimeFunction? types_variant2 owner_variant2 source [] 2 initialStore = some (.unit,.outOfFuel saved) ∧
      Core.runStateful 2 saved = .done .unit initialStore)) "discard lost the actual pending expression value"

private def checkTerminalBlock : IO Unit := do
  let some source ← parsed_variant3? "function nested() { { return; } }"
    | throw (IO.userError "original nested declaration did not parse")
  match atBody : source.value.body with
  | ⟨outerSpan, [⟨innerSpan, .block [⟨returnSpan, .returnStmt none⟩]⟩]⟩ =>
      have _ : TypedLetReturnTreeElaborates types_variant2 owner_variant2 .empty source.value.body .unit .unit := by
        rw [atBody]; exact .block (.single .bare)
      assertTrue (outerSpan.contains innerSpan && innerSpan.contains returnSpan &&
        decide (outerSpan.startByte < innerSpan.startByte ∧ innerSpan.endByte < outerSpan.endByte))
        "original inner braces were replaced by the outer block range"
  | _ => throw (IO.userError "original nested return AST changed")
  let some prepared := prepareRuntimeFunction? types_variant2 owner_variant2 source []
    | throw (IO.userError "terminal block was rejected")
  checkOrder source [] prepared.inputs
  assertTrue (decide (prepared.core = .unit ∧ prepared.returnType = .unit) &&
    (prepared.inputs.checkReturnBody? source.value.body).isNone) "wrapper changed Core or the old adapter"
  for initialStore in [store_variant3, []] do
    have paths (k : List Core.Frame) : Core.Steps 1 ⟨.eval .unit [], k, initialStore⟩
        ⟨.ret .unit, k, initialStore⟩ := .cons .unit .refl
    have _ := paths []
    for fuel in List.range 4 ++ [20] do
      assertTrue (decide (runRuntimeFunction? types_variant2 owner_variant2 source [] fuel initialStore =
        some (.unit, Core.runStateful fuel (.initial .unit [] initialStore)))) "wrapper added a transition"
      assertTrue (match runRuntimeFunction? types_variant2 owner_variant2 source [] fuel initialStore with
        | some (.unit, .done value final) => decide (1 ≤ fuel ∧ value = .unit ∧ final = initialStore)
        | some (.unit, .outOfFuel cp) => decide (fuel = 0 ∧ cp = .initial .unit [] initialStore ∧
            Core.runStateful 1 cp = .done .unit initialStore)
        | _ => false) "wrapped return changed its genuine one-step residual"

def frontendParsedRuntimeFunctionEntryTests : IO Unit := do
  checkInferredLocal
  checkDiscardLiteral
  checkTerminalBlock
  checkAccepted_variant types_variant2 "function empty() { return; }" [] .unit .unit .unit 1
  checkAccepted_variant types_variant2 "function explicit() returns (U,) { return; }" [] .unit .unit .unit 1
  checkAccepted_variant types_variant2 "/* lead */ function literal() returns (Word) { return ((0007)); }"
    [] (.word seven) .word (.word seven) 1
  checkAccepted_variant types_variant2 "function invert() returns (Word) { return ~7; }"
    [] (.unary .wordNot (.word seven)) .word (.word seven.bitNot) 3
  for left in [false, true] do
    for right in [false, true] do
      checkAccepted_variant types_variant2 "function first(left: Bool, right: Bool) returns (Bool) { return left; }"
        [boolArg left, boolArg right] (.var 1) .bool (.bool left) 1
      checkAccepted_variant types_variant2 "function last(left: Bool, right: Bool) returns (Bool) { return right; }"
        [boolArg left, boolArg right] (.var 0) .bool (.bool right) 1
  for choice in [false, true] do
    let arguments := [boolArg choice, wordArg_variant seven, wordArg_variant nine]
    checkAccepted_variant types_variant2
      "function choose(c: Pkg /* qualified */ . Flag, t: Word, f: Word,) returns (Word) { return c ? t : f; }"
      arguments (.ifE (.var 2) (.var 1) (.var 0)) .word (.word (if choice then seven else nine)) 4
    checkAccepted_variant types_variant2
      "function selected(c: Bool, t: Word, f: Word) returns (Word) { return c ? ~t : f; }"
      arguments (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
      (.word (if choice then seven.bitNot else nine)) (if choice then 6 else 4)
    checkAccepted_variant types_variant2
      "function logical(c: Bool, t: Word, f: Word) returns (Bool) { return c && !c; }"
      arguments (.ifE (.var 2) (.unary .boolNot (.var 2)) (.bool false)) .bool (.bool false)
      (if choice then 6 else 4)
    checkAccepted_variant types_variant2
      "function bitwise(c: Bool, t: Word, f: Word) returns (Word) { return t ^ f; }"
      arguments (.binary .wordXor (.var 1) (.var 0)) .word (.word (seven.bitXor nine)) 5
    checkRejected "function missing(c: Bool, t: Word, f: Word) returns (Word) { return c ? t : missing; }"
      arguments
    checkRejected "function branches(c: Bool, t: Word, f: Word) returns (Word) { return c ? t : c; }"
      arguments
  checkAccepted_variant [(["Word"], .bool)] "function alias(x: Word) returns (Word) { return x; }"
    [boolArg true] (.var 0) .bool (.bool true) 1
  checkAccepted_variant types_variant2 "function cell(x: Cell) returns (Cell) { return x; }"
    [⟨.cell .word, .cellRef .word 40, .cellRef⟩] (.var 0) (.cell .word) (.cellRef .word 40) 1 []
  checkAccepted_variant types_variant2 "function closure(x: Fn) returns (Fn) { return x; }"
    [⟨.function .bool .bool, closure, closureTyped⟩] (.var 0) (.function .bool .bool) closure 1
  -- Every source position is checked across several arities, not only endpoints.
  let pool : List (String × TypedRuntimeArgument) :=
    [("Bool", boolArg false), ("Word", wordArg_variant seven), ("Bool", boolArg true), ("Word", wordArg_variant nine),
     ("U", ⟨.unit, .unit, .unit⟩), ("Cell", ⟨.cell .word, .cellRef .word 40, .cellRef⟩),
     ("Fn", ⟨.function .bool .bool, closure, closureTyped⟩), ("Word", wordArg_variant seven.bitNot)]
  for arity in [1, 2, 3, 4, 5, 6, 7, 8] do
    let rows := pool.take arity
    let parameters := String.intercalate ", " (rows.zipIdx.map fun (row, index) => s!"p{index}: {row.1}")
    for (selected, index) in rows.zipIdx do
      let content := s!"function projection_{arity}_{index}({parameters}) returns ({selected.1})"
        ++ " { return " ++ s!"p{index};" ++ " }"
      checkAccepted_variant types_variant2 content (rows.map Prod.snd) (.var (arity - 1 - index))
        selected.2.type selected.2.value 1 []
  let mismatch := "function mismatch() returns (Bool) { return 7; }"
  let some mismatched ← parsed_variant3? mismatch
    | throw (IO.userError "return mismatch example did not parse")
  assertTrue (decide (LocalInputs.empty.checkReturnBody? mismatched.value.body =
    some (.word seven, .word))) "entry contract incorrectly changed the body-only endpoint"
  checkRejected mismatch
  checkAccepted_variant types_variant2 "function addition() returns (Word) { return 7 + 9; }" []
    (.binary .wordAdd (.word seven) (.word nine)) .word (.word (seven.add nine)) 5
  checkAccepted_variant types_variant2 "function subtraction() returns (Word) { return 7 - 9; }" []
    (.binary .wordSub (.word seven) (.word nine)) .word (.word (seven.sub nine)) 5
  checkAccepted_variant types_variant2 "function multiplication() returns (Word) { return 7 * 9; }" []
    (.binary .wordMul (.word seven) (.word nine)) .word (.word (seven.mul nine)) 5
  for content in [
      "function absent() { return 7; }", "function bare() returns (Word) { return; }",
      "function empty() returns () { return; }", "function many() returns (Word, Bool) { return 7; }",
      "function unknown() returns (Unknown) { return; }",
      "function application() returns (Word<Bool>) { return 7; }",
      "function proxy() returns (@Word) { return 7; }",
      "function tuple() returns ((Word, Bool)) { return 7; }",
      "function generic<T>() { return; }", "function constrained() where Word: Eq { return; }",
      "function emptyBody() {}",
      "function repeated() { return; return; }", "function tail() returns (Word) { 7 }",
      "function discarded() { return; missing; }",
      "function call() returns (Word) { return missing(); }"] do
    checkRejected content
  for content in ["function publicOnly() public { return; }",
      "function payableOnly() payable { return; }", "function both() public payable { return; }"] do
    checkRejected content [] .contract
  for (content, arguments) in [
      ("function arity(x: Bool) returns (Bool) { return x; }", []),
      ("function arity() { return; }", [boolArg false]),
      ("function arity(x: Bool) returns (Bool) { return x; }", [boolArg false, boolArg true]),
      ("function duplicate(x: Bool, x: Bool) returns (Bool) { return x; }", [boolArg false, boolArg true]),
      ("function mismatch(x: Word) returns (Word) { return x; }", [boolArg true]),
      ("function compile(comptime x: Bool) returns (Bool) { return x; }", [boolArg true])] do
    checkRejected content arguments
  for content in ["", "function f()", "function f() { return;", "function f() { return 7 }",
      "function f() { return; } trailing", "function f() public { return; }"] do
    assertTrue (← parsed_variant3? content).isNone
      s!"{content}: accepted malformed, diagnosed, or incompletely consumed declaration text"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeFunctionEvaluator
/-! Original complete declarations and actual arguments retain the full gate.
Independent body certificates, Core, triples and checkpoint expectations never
come from the new entry evaluator's output. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def owner_variant3 : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"DirectEntry", by decide⟩], by decide⟩⟩, 17⟩
private def word_variant (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word_variant n)
private def wordArg_variant2 (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg_variant (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types_variant3 : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .word .word), (["Opaque"], .namedData ⟨91⟩), (["Pkg", "Token"], .namedData ⟨92⟩)]
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed_variant4? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "direct-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span.source = file.id ∧ source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) &&
        source.span.contains source.value.body.span) "original declaration range changed"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "parser invariant")
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let some source ← parsed_variant4? content | throw (IO.userError s!"incomplete declaration: {content}")
  return source

private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def reference (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "certificate name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "certificate actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "certificate expected original reference")
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table env store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table env store operand
      match atValue : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (atValue ▸ child.costed)⟩
      | _ => throw (IO.userError "certificate expected Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table env store left
      let second ← reference table env store right
      match atLeft : first.value, atRight : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]; exact .subtract (atLeft ▸ first.costed) (atRight ▸ second.costed)⟩
      | _, _ => throw (IO.userError "certificate subtraction expected Words")
  | _ => throw (IO.userError "expression outside independent certificate script")
private structure Certificate (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner_variant3 table env store body value store cost
private def certify (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (body : Syntax.Block) (choices : List Bool) : IO (Certificate table env store body) := do
  match atBody : body with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let child ← expression table env store initializer
      let id := Resolved.freshLocalId owner_variant3 (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, child.value) :: env) store ⟨span, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by rw [atBody]; exact .binding child.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "independent branch script missing")
      let guard ← reference table env store condition
      if agrees : guard.value = .bool choice then
        match atChoice : choice with
        | true =>
            let child ← certify table env store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifTrue (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
        | false =>
            let child ← certify table env store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifFalse (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
      else throw (IO.userError "independent branch script disagrees with actual guard")
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past bare return"
      return ⟨.unit, 1, by rw [atBody]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past return"
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [atBody]; exact .single (.expression child.costed)⟩
  | _ => throw (IO.userError "body outside independent certificate script")
termination_by sizeOf body

private structure Entry where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  provenance : RuntimeFunctionCompiles types_variant3 owner_variant3 source compiled
private def compile (content : String) (core : Core.Expr) (type : Core.Ty) (parameters : List Core.Ty) : IO Entry := do
  let source ← parsed content
  match accepted : compileRuntimeFunction? types_variant3 owner_variant3 source with
  | none => throw (IO.userError "positive original declaration did not compile")
  | some compiled =>
      let names ← source.value.signature.parameters.elements.mapM fun parameter => do
        let .typed none name annotation := parameter.value | throw (IO.userError "parameter shape changed")
        assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains annotation.span) "original parameter positions changed"
        pure name.value
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ compiled.inputs.context.values = parameters.reverse ∧
        compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner_variant3, index⟩ : Resolved.LocalId)))).reverse ∧
        compiled.inputs.bindings.length = parameters.length ∧ Core.infer? parameters.reverse core = some type)) "independent Core/type or original parameter-only layout changed"
      let provenance := compileRuntimeFunction?_sound accepted
      let wrong := Core.Expr.ifE (.bool true) core core
      if different : wrong ≠ compiled.core then
        have _ : ¬ RuntimeFunctionCompiles types_variant3 owner_variant3 source { compiled with core := wrong } := by
          intro alternative
          exact different (congrArg CompiledRuntimeFunction.core (alternative.result_unique provenance))
        assertTrue (decide (Core.infer? parameters.reverse wrong = some type)) "wrong-Core contrast lost the same type"
      else throw (IO.userError "wrong Core unexpectedly matched")
      return ⟨source, compiled, provenance⟩
private def checked (entry : Entry) (arguments : List TypedRuntimeArgument) (choices : List Bool)
    (value : Core.Value) (cost : Nat) : IO Unit := do
  if matching : arguments.map (·.type) = entry.compiled.inputs.context.values.reverse then
    match preparedAt : prepareRuntimeFunction? types_variant3 owner_variant3 entry.source arguments with
    | none => throw (IO.userError "matching actual arguments did not prepare")
    | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      have _ := prepareRuntimeFunction?_factorization types_variant3 owner_variant3 entry.source arguments
      assertTrue (decide (prepared.core = entry.compiled.core ∧ prepared.returnType = entry.compiled.returnType ∧
        prepared.inputs.names = entry.compiled.inputs.names ∧ prepared.inputs.context.values = entry.compiled.inputs.context.values ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value))) "arguments were rebound/reversed twice or locals leaked into parameters"
      assertTrue (decide (evaluateRuntimeFunctionWithCost? types_variant3 owner_variant3 entry.source arguments =
        some (entry.compiled.returnType, value, cost))) "independent direct entry triple changed"
      for store in stores do
        let certificate ← certify prepared.inputs.names prepared.inputs.environment store entry.source.value.body choices
        assertTrue (decide (certificate.value = value ∧ certificate.cost = cost)) "independent original-AST certificate changed"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation certificate.costed
        have computed := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        let reflected := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, computed⟩
        have _ := independent.deterministic reflected
        have _ := reflected.compiled_toSteps entry.provenance
        have _ := reflected.cost_le_fuelBound
        have _ := entry.provenance.run_done_of_fuelBound arguments matching store (typedLetReturnTreeFuelBound entry.source.value.body) (Nat.le_refl _)
        for replacement in stores do
          if different : replacement ≠ store then
            have _ : ¬ RuntimeFunctionEvaluatesWithCost types_variant3 owner_variant3 entry.source arguments store prepared.returnType certificate.value replacement certificate.cost :=
              fun impossible => different (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp impossible).1
            pure ()
        let initial := Core.State.initial entry.compiled.core (arguments.reverse.map (·.value)) store
        let run := fun fuel => runRuntimeFunction? types_variant3 owner_variant3 entry.source arguments fuel store
        for fuel in List.range (typedLetReturnTreeFuelBound entry.source.value.body + 3) do
          have _ := reflected.run_done_iff (fuel := fuel)
          have _ := reflected.run_outOfFuel_iff (fuel := fuel)
          have _ := reflected.compiled_run_done_iff (fuel := fuel) entry.provenance
          have _ := reflected.compiled_run_outOfFuel_iff (fuel := fuel) entry.provenance
          assertTrue (decide (run fuel = some (entry.compiled.returnType, Core.runStateful fuel initial))) "actual compiled Core/full result changed"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = entry.compiled.returnType ∧ v = value ∧ s = store)
            | some (t, .outOfFuel state) => decide (fuel < cost ∧ t = entry.compiled.returnType ∧ state.store = store)
            | _ => false) "independent threshold/value/own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
            if same : t = prepared.returnType then
              have _ := reflected.residual_of_outOfFuel (show run spent = some (prepared.returnType, .outOfFuel checkpoint) by simpa only [same] using exhausted)
              if actualOut : Core.runStateful spent initial = .outOfFuel checkpoint then
                have _ := reflected.compiled_residual_of_outOfFuel entry.provenance actualOut
                pure ()
              else throw (IO.userError "actual compiled path disagreed with entry checkpoint")
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "actual full checkpoint resumption changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "independent remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (t, .done value store))) "restart impersonated checkpoint resumption"
            else throw (IO.userError "checkpoint changed declared return type")
          | _ => throw (IO.userError "actual below-cost checkpoint missing")
  else throw (IO.userError "positive fixture changed ordered argument types")
private def rejected (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  match preparation : prepareRuntimeFunction? types_variant3 owner_variant3 source arguments with
  | some _ => throw (IO.userError "invalid whole gate prepared")
  | none =>
      have directNone := evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr preparation
      have _ := evaluateRuntimeFunctionWithCost?_eq_none_iff.mp directNone
      assertTrue (evaluateRuntimeFunctionWithCost? types_variant3 owner_variant3 source arguments).isNone "preparation failure was hidden by raw success"
      for store in stores do
        for fuel in [0, 1, 60] do assertTrue (runRuntimeFunction? types_variant3 owner_variant3 source arguments fuel store).isNone "whole rejection exposed a checkpoint"
private def spine (depth level : Nat) (annotation : String) : String × Core.Expr :=
  match depth with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 1 else 0))
  | count + 1 =>
      let (tail, core) := spine count (level + 1) annotation
      ("if(c){" ++ s!"let z{level}: {annotation}=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail ++
        "}else{" ++ s!"let z{level}: {annotation}=y;return z{level};" ++ "}",
        .ifE (.var (level + 3)) (.letE (.var (if level = 0 then 1 else 0)) core) (.letE (.var level) (.var 0)))

def frontendParsedRuntimeFunctionEvaluatorTests : IO Unit := do
  for depth in [0, 1, 2, 5, 12] do
    let (body, core) := spine depth 0 "Word"
    let entry ← compile ("function deep(c: Bool,d: Bool,x: Word,y: Word) returns (Word){" ++ body ++ "}") core .word [.bool, .bool, .word, .word]
    for c in [false, true] do
      checked entry [boolArg_variant c, boolArg_variant false, wordArg_variant2 9, wordArg_variant2 2] (if depth = 0 then [] else if c then List.replicate depth true else [false])
        (w (if depth = 0 || c then 9 else 2)) (if depth = 0 then 1 else if c then 6 * depth + 1 else 7)
  let ordered ← compile "function ordered(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x - y;if(d){let q: Word=z;return ~q;}else{let q: Word=y - z;return q;}}else{let z: Word=y - x;return y;}}"
    (.ifE (.var 3) (.letE (.binary .wordSub (.var 1) (.var 0)) (.ifE (.var 3) (.letE (.var 0) (.unary .wordNot (.var 0)))
      (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 1))) .word [.bool, .bool, .word, .word]
  for (x, y) in [(9, 2), (2, 9), (0, Core.wordModulus - 1), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        checked ordered [boolArg_variant c, boolArg_variant d, wordArg_variant2 x, wordArg_variant2 y] (if c then [true, d] else [false])
          (if c then if d then w (Core.wordModulus - 1 - (x + Core.wordModulus - y) % Core.wordModulus)
            else w (y + Core.wordModulus - (x + Core.wordModulus - y) % Core.wordModulus) else w y) (if c then if d then 19 else 21 else 11)
  let bare ← compile "function bare(){return;}" .unit .unit []
  checked bare [] [] .unit 1
  let strict ← compile "function strict(x: Word,y: Word) returns (Word){let unused: Word=x - y;return y;}"
    (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 1)) .word [.word, .word]
  checked strict [wordArg_variant2 9, wordArg_variant2 2] [] (w 2) 8
  for store in stores do
    let env := [w 2, w 9]
    assertTrue (decide (runRuntimeFunction? types_variant3 owner_variant3 strict.source [wordArg_variant2 9, wordArg_variant2 2] 6 store = some (.word, .outOfFuel
      ⟨.ret (w 7), [.letBody (.var 1) env], store⟩) ∧
      runRuntimeFunction? types_variant3 owner_variant3 strict.source [wordArg_variant2 9, wordArg_variant2 2] 7 store = some (.word, .outOfFuel
        ⟨.eval (.var 1) (w 7 :: env), [], store⟩))) "strict unused initializer or actual captured tail scope changed"
  let closure : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩
  for (name, x, y) in [("Cell", (⟨.cell .word, .cellRef .word 999, .cellRef⟩ : TypedRuntimeArgument), ⟨.cell .word, .cellRef .word 40, .cellRef⟩),
      ("Fn", closure, ⟨.function .word .word, .closure .word .word (.var 0) [], .closure .nil (.var rfl)⟩), ("Unit", ⟨.unit, .unit, .unit⟩, ⟨.unit, .unit, .unit⟩)] do
    let entry ← compile (s!"function opaque(c: Bool,x: {name},y: {name}) returns ({name})" ++ "{if(c){let z: " ++ name ++
      "=x;let q: " ++ name ++ "=y;return z;}else{let z: " ++ name ++ "=y;return z;}}")
      (.ifE (.var 2) (.letE (.var 1) (.letE (.var 1) (.var 1))) (.letE (.var 0) (.var 0))) x.type [.bool, x.type, y.type]
    for c in [false, true] do checked entry [boolArg_variant c, x, y] [c] (if c then x.value else y.value) (if c then 10 else 7)
  let unused ← compile "function unused(x: Word,y: Bool){return;}" .unit .unit [.word, .bool]
  checked unused [wordArg_variant2 9, boolArg_variant true] [] .unit 1
  for arguments in [[], [wordArg_variant2 9], [boolArg_variant true, wordArg_variant2 9], [boolArg_variant true, boolArg_variant true], [wordArg_variant2 9, boolArg_variant true, wordArg_variant2 2]] do
    assertTrue (decide (evaluateTypedLetReturnTreeWithCost? owner_variant3 [] [] unused.source.value.body = some (.unit, 1))) "unused argument contrast lost raw body success"
    rejected unused.source arguments
  for header in ["function generic<T>()", "function many() returns (Unit,Bool)", "function empty() returns ()", "function unknown() returns (Unknown)",
      "function duplicate(x: Word,x: Bool)", "function staged(comptime x: Word)", "function unknownParameter(x: Unknown)", "function wrong() returns (Word)"] do
    let source ← parsed (header ++ "{return;}")
    assertTrue (compileRuntimeFunction? types_variant3 owner_variant3 source).isNone "invalid header/parameter/return contract compiled"
    for store in stores do
      let certificate ← certify [] [] store source.value.body []
      assertTrue (decide (certificate.value = .unit ∧ certificate.cost = 1 ∧
        evaluateTypedLetReturnTreeWithCost? owner_variant3 [] [] source.value.body = some (.unit, 1))) "whole rejection lost independently successful raw body"
    for arguments in [[], [wordArg_variant2 9], [wordArg_variant2 9, boolArg_variant true]] do rejected source arguments
  for (result, body) in [("Bool", "{if(c){let z: Word=x;return z;}else{return x;}}"),
      ("Word", "{if(c){let z: Word=x;return z;}else{let z: Unknown=x;return z;}}"),
      ("Word", "{if(c){let z: Bool=x;return z;}else{return x;}}"),
      ("Word", "{if(c){let x: Word=x;return x;}else{return x;}}"),
      ("Word", "{if(c){let z: Word=x;return z;}else{return missing;}}"),
      ("Word", "{if(c){let z: Word=x;return z;}else{return c;}}") ] do
    let source ← parsed (s!"function raw(c: Bool,x: Word) returns ({result})" ++ body)
    let arguments := [boolArg_variant true, wordArg_variant2 9]
    let some actual := bindRuntimeParameters? types_variant3 owner_variant3 source.value.signature.parameters.elements arguments
      | throw (IO.userError "raw/whole contrast lost original actual parameters")
    for store in stores do
      let certificate ← certify actual.names actual.environment store source.value.body [true]
      assertTrue (decide (certificate.value = w 9 ∧ certificate.cost = 7 ∧ actual.environment.values = arguments.reverse.map (·.value) ∧
        evaluateTypedLetReturnTreeWithCost? owner_variant3 actual.names actual.environment source.value.body = some (w 9, 7))) "raw selected certificate changed"
    rejected source arguments
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨_, typed⟩; cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (name, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩)] do
    for depth in [1, 3] do
      let (body, core) := spine depth 0 name
      let entry ← compile (s!"function nominal(c: Bool,d: Bool,x: {name},y: {name}) returns ({name})" ++ "{" ++ body ++ "}") core type [.bool, .bool, type, type]
      for arguments in [[], [boolArg_variant true, boolArg_variant false, wordArg_variant2 9, wordArg_variant2 2], [boolArg_variant true, boolArg_variant false, closure, closure]] do rejected entry.source arguments
  for content in ["function missing(x){return x;}", "function unfinished(){return;", "function trailing(){return;} trailing"] do
    assertTrue (← parsed_variant4? content).isNone "incomplete source acquired entry meaning"

end Tests
end
