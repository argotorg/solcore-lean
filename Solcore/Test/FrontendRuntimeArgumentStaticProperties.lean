import Solcore.Frontend.RuntimeFunctionStaticProperties
import Solcore.Frontend.RuntimeFunctionEntryExecutionProperties

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
    .single <| .expression (.logicalAnd (.identifier .head) (.logicalNot (.identifier .head)))
      (.ifE (.var .head) (.unary (.var .head)) .bool)
      (.ifE (.var .head) (.unary (.var .head)) .bool)⟩
private theorem truePrepares : RuntimeFunctionPrepares (table .bool) owner (declaration andNot)
    [boolArg true] (prepared andCore (boolArg true)) :=
  transportConcrete falsePrepares rfl (binding (boolArg true))
private theorem falseCost (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table .bool) owner (declaration andNot)
      [boolArg false] store .bool (.bool false) store 4 :=
  .intro falsePrepares (.single <| .expression (.andFalse (.identifier .head .head)))
private theorem trueCost (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table .bool) owner (declaration andNot)
      [boolArg true] store .bool (.bool false) store 6 := by
  have leaf : LocalExpressionEvaluatesWithCost (inputs (boolArg true)).names
      (inputs (boolArg true)).environment store (ref "c") (.bool true) store 1 :=
    .identifier .head .head
  exact .intro truePrepares (.single <| .expression (.andTrue leaf (.logicalNot leaf)))

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
  have impossible := ((TerminalReturnTreeElaborates.single expectedBody).result_unique body).2.trans
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
    .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩

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
    .intro (cellPrepares left) (.single <| .expression (.identifier .head .head))
  have rightCost : RuntimeFunctionEvaluatesWithCost (table (.cell .word)) owner (declaration (ref "c"))
      [cellArg right] store (.cell .word) (.cellRef .word right) store 1 :=
    .intro transported (.single <| .expression (.identifier .head .head))
  exact ⟨prepareRuntimeFunction?_static_projection_eq rfl, leftCost.run_done_iff.mpr (by decide),
    rightCost.run_done_iff.mpr (by decide), by intro same; exact different (Core.Value.cellRef.inj same).2⟩

end Tests.FrontendRuntimeArgumentStatic
