import Solcore.Frontend.RuntimeFunctionParameterReturnProperties

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
