import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.TypedLetReturnBody

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
