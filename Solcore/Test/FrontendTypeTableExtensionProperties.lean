import Solcore.Frontend.RuntimeFunction

/-! Existing meanings retain exact static compilation. One-way extension may
enable unknown annotations; duplicate membership does not license shadowing. -/

set_option autoImplicit false

namespace Tests.FrontendTypeTableExtension

open Solcore Solcore.Frontend

private def owner (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"TableExtension", by decide⟩], by decide⟩⟩, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "table-extension.sol"⟩, 29, 11⟩
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def body (conditional : Bool) : Syntax.Block :=
  if conditional then ⟨span, [⟨span, .ifThen (ref "c") (returned "x") (some (returned "y"))⟩]⟩ else returned "x"
private def parameters := [parameter "c" "Cond", parameter "x" "Payload", parameter "y" "Payload"]
private def types (payload : Core.Ty) : TypeNameTable := [(["Payload"], payload), (["Cond"], .bool)]
private def entry (result : String) (conditional : Bool) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "choose"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation result]⟩⟩, none⟩, body conditional⟩⟩
private def inputs (id : Resolved.DeclarationId) (payload : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh id "c" .bool).bindFresh id "x" payload).bindFresh id "y" payload
private def core (conditional : Bool) : Core.Expr := if conditional then .ifE (.var 2) (.var 1) (.var 0) else .var 1
private def compiled (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) : CompiledRuntimeFunction :=
  ⟨inputs id payload, core conditional, payload⟩
private theorem payloadMeaning (payload : Core.Ty) :
    TypeNameDenotes (types payload) (annotation "Payload") payload := .named .head
private theorem conditionMeaning (payload : Core.Ty) :
    TypeNameDenotes (types payload) (annotation "Cond") .bool := .named (.tail (by decide) .head)
private theorem declared (id : Resolved.DeclarationId) (payload : Core.Ty) :
    RuntimeParametersDeclare (types payload) id parameters (inputs id payload) :=
  .cons (conditionMeaning payload).structural (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (payloadMeaning payload).structural (by change "x" ∉ ["c"]; decide)
      (.cons (payloadMeaning payload).structural (by change "y" ∉ ["x", "c"]; decide) .nil))
private theorem header (payload : Core.Ty) (conditional : Bool) :
    RuntimeFunctionHeader (types payload) (entry "Payload" conditional).value.signature payload :=
  ⟨rfl, rfl, rfl, rfl, .single (payloadMeaning payload).structural⟩
private theorem compilation (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) :
    RuntimeFunctionCompiles (types payload) id (entry "Payload" conditional) (compiled id payload conditional) := by
  cases conditional
  · exact runtimeFunction_parameter_compiles (index := 1) (declared id payload)
      rfl (payloadMeaning payload) (header payload false) rfl
  · exact runtimeFunction_conditional_parameters_compiles (conditionIndex := 0) (thenIndex := 1) (elseIndex := 2)
      (declared id payload) rfl rfl rfl (conditionMeaning payload) (payloadMeaning payload) (payloadMeaning payload)
      (header payload true) rfl

theorem annotations_headers_rows_and_both_whole_compilations_retain_the_exact_original_data
    (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types payload) next) :
    TypeNameDenotes next (annotation "Payload") payload ∧
    RuntimeReturnTypeDenotes next (entry "Payload" conditional).value.signature.returnsClause payload ∧
    RuntimeFunctionHeader next (entry "Payload" conditional).value.signature payload ∧
    RuntimeParametersDeclare next id parameters (inputs id payload) ∧
    RuntimeFunctionCompiles next id (entry "Payload" conditional) (compiled id payload conditional) ∧
    interpretTypeName? next (annotation "Payload") = some payload ∧
    declareRuntimeParameters? next id parameters = some (inputs id payload) ∧
    compileRuntimeFunction? next id (entry "Payload" conditional) = some (compiled id payload conditional) :=
  ⟨(payloadMeaning payload).extend_types extension, (header payload conditional).returnsMeaning.extend_types extension,
    (header payload conditional).extend_types extension, (declared id payload).extend_types extension,
    (compilation id payload conditional).extend_types extension,
    interpretTypeName?_some_of_extends extension (payloadMeaning payload).complete,
    declareRuntimeParameters?_some_of_extends extension (declared id payload).complete,
    compileRuntimeFunction?_some_of_extends extension (compilation id payload conditional).complete⟩

theorem arbitrary_initial_rows_and_the_same_fresh_identity_are_retained
    (id : Resolved.DeclarationId) (payload : Core.Ty) (initial : LocalTypeInputs)
    (unused : "next" ∉ initial.names.map Prod.fst) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types payload) next) :
    RuntimeParametersDeclareFrom (types payload) id initial [parameter "next" "Payload"]
      (initial.bindFresh id "next" payload) ∧
    RuntimeParametersDeclareFrom next id initial [parameter "next" "Payload"]
      (initial.bindFresh id "next" payload) ∧
    (initial.bindFresh id "next" payload).bindings =
      ⟨"next", Resolved.freshLocalId id initial.ids, payload⟩ :: initial.bindings := by
  have original : RuntimeParametersDeclareFrom (types payload) id initial [parameter "next" "Payload"]
      (initial.bindFresh id "next" payload) := .cons (payloadMeaning payload).structural unused .nil
  exact ⟨original, original.extend_types extension, rfl⟩

theorem a_nonempty_nominal_initial_row_needs_no_old_annotation_meaning_or_value
    (payload : Core.Ty) (dataType : Core.DataTypeId) (extras : TypeNameTable) :
    let initial := LocalTypeInputs.empty.bindFresh (owner 1) "retained" (.namedData dataType)
    RuntimeParametersDeclareFrom (types payload ++ extras) (owner 0) initial [parameter "next" "Payload"]
      (initial.bindFresh (owner 0) "next" payload) ∧
    (initial.bindFresh (owner 0) "next" payload).context =
      [(⟨owner 0, 0⟩, payload), (⟨owner 1, 0⟩, .namedData dataType)] := by
  intro initial
  exact ⟨(arbitrary_initial_rows_and_the_same_fresh_identity_are_retained (owner 0) payload initial
    (by change "next" ∉ ["retained"]; decide) _ (TypeNameTable.Extends.append_right _ extras)).2.1, rfl⟩

theorem fresh_prepend_and_arbitrary_right_duplicates_compose_without_overriding_meanings
    (id : Resolved.DeclarationId) (payload : Core.Ty) (dataType : Core.DataTypeId)
    (extras : TypeNameTable) (conditional : Bool) :
    TypeNameTable.Extends (types payload) (types payload) ∧
    TypeNameTable.Extends (types payload) (types payload ++ extras) ∧
    compileRuntimeFunction?
      (((["Fresh"], .namedData dataType) :: types payload) ++
        ((["Payload"], .word) :: (["Cond"], .unit) :: extras)) id (entry "Payload" conditional) =
      some (compiled id payload conditional) := by
  have prepend : TypeNameTable.Extends (types payload) ((["Fresh"], .namedData dataType) :: types payload) :=
    TypeNameTable.Extends.cons_fresh (types payload) ["Fresh"] (.namedData dataType)
    (by change ["Fresh"] ∉ [["Payload"], ["Cond"]]; decide)
  have extension : TypeNameTable.Extends (types payload)
      (((["Fresh"], .namedData dataType) :: types payload) ++ ((["Payload"], .word) :: (["Cond"], .unit) :: extras)) :=
    prepend.trans (TypeNameTable.Extends.append_right _ ((["Payload"], .word) :: (["Cond"], .unit) :: extras))
  exact ⟨TypeNameTable.Extends.refl _, TypeNameTable.Extends.append_right _ _,
    compileRuntimeFunction?_some_of_extends extension (compilation id payload conditional).complete⟩

private def duplicate (payload : Core.Ty) : TypeNameTable := (["Payload"], payload) :: types payload
private theorem duplicates_extend (payload : Core.Ty) :
    TypeNameTable.Extends (types payload) (duplicate payload) ∧ TypeNameTable.Extends (duplicate payload) (types payload) := by
  constructor
  · intro key type found
    cases found with
    | head => exact .head
    | tail different found => exact .tail different (.tail different found)
  · intro key type found
    cases found with
    | head => exact .head
    | tail _ found => exact found

theorem a_nonfresh_same_meaning_prefix_preserves_every_optional_result
    (payload : Core.Ty) (key : List String) (source : Syntax.TypeExpr) (id : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) (declaration : Syntax.FunctionDecl) :
    ["Payload"] ∈ (types payload).map Prod.fst ∧ types payload ≠ duplicate payload ∧
    TypeNameTable.lookup? (types payload) key = TypeNameTable.lookup? (duplicate payload) key ∧
    interpretTypeName? (types payload) source = interpretTypeName? (duplicate payload) source ∧
    declareRuntimeParameters? (types payload) id params = declareRuntimeParameters? (duplicate payload) id params ∧
    compileRuntimeFunction? (types payload) id declaration = compileRuntimeFunction? (duplicate payload) id declaration := by
  obtain ⟨forward, backward⟩ := duplicates_extend payload
  refine ⟨by simp [types], ?_, TypeNameTable.lookup?_eq_of_mutual_extends forward backward key,
    interpretTypeName?_eq_of_mutual_extends forward backward source,
    declareRuntimeParameters?_eq_of_mutual_extends forward backward id params,
    compileRuntimeFunction?_eq_of_mutual_extends forward backward id declaration⟩
  intro same
  have lengths := congrArg List.length same
  change 2 = 3 at lengths
  cases lengths

theorem mutually_extending_nonidentical_tables_retain_unknown_header_rejection
    (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) :
    compileRuntimeFunction? (types payload) id (entry "Unknown" conditional) = none ∧
    compileRuntimeFunction? (duplicate payload) id (entry "Unknown" conditional) = none := by
  have rejected : compileRuntimeFunction? (types payload) id (entry "Unknown" conditional) = none := by
    simp only [compileRuntimeFunction?, entry, interpretRuntimeFunctionHeader?,
      interpretRuntimeReturnType?, annotation, interpretStructuralType?_named_eq_typeName]
    rfl
  have same := compileRuntimeFunction?_eq_of_mutual_extends
    (duplicates_extend payload).1 (duplicates_extend payload).2 id (entry "Unknown" conditional)
  exact ⟨rejected, same.symm.trans rejected⟩

theorem adding_an_unknown_nominal_meaning_can_turn_rejection_into_exact_compilation
    (id : Resolved.DeclarationId) (dataType : Core.DataTypeId) (conditional : Bool) :
    TypeNameTable.Extends [(["Cond"], .bool)] (types (.namedData dataType)) ∧
    compileRuntimeFunction? [(["Cond"], .bool)] id (entry "Payload" conditional) = none ∧
    compileRuntimeFunction? (types (.namedData dataType)) id (entry "Payload" conditional) =
      some (compiled id (.namedData dataType) conditional) ∧
    ¬ TypeNameTable.Extends (types (.namedData dataType)) [(["Cond"], .bool)] ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData dataType := by
  refine ⟨TypeNameTable.Extends.cons_fresh _ ["Payload"] (.namedData dataType) (by decide),
    ?_, (compilation id (.namedData dataType) conditional).complete, ?_, ?_⟩
  · simp only [compileRuntimeFunction?, entry, interpretRuntimeFunctionHeader?,
      interpretRuntimeReturnType?, annotation, interpretStructuralType?_named_eq_typeName]
    rfl
  · intro backward
    have found := TypeNameTable.lookup?_iff.mpr (backward (.head : TypeNameTable.Lookup (types (.namedData dataType)) ["Payload"] _))
    change (none : Option Core.Ty) = some (.namedData dataType) at found
    cases found
  · rintro ⟨⟨type, value, typed⟩, same⟩
    cases same
    cases typed with
    | constructed found _ =>
        simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem retaining_old_rows_is_not_enough_when_a_prefix_changes_the_first_meaning :
    TypeNameTable.lookup? (types .bool) ["Cond"] = some .bool ∧
    TypeNameTable.lookup? ((["Cond"], .word) :: types .bool) ["Cond"] = some .word ∧
    ¬ TypeNameTable.Extends (types .bool) ((["Cond"], .word) :: types .bool) := by
  refine ⟨rfl, rfl, ?_⟩
  intro extension
  have changed := (extension (.tail (by decide) (.head : TypeNameTable.Lookup [(["Cond"], .bool)] ["Cond"] .bool))).type_unique
    (.head : TypeNameTable.Lookup ((["Cond"], .word) :: types .bool) ["Cond"] .word)
  cases changed

private def qualified : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, "Pkg"⟩, [⟨span, "Thing"⟩]⟩⟩⟩ none⟩
theorem exact_component_keys_do_not_flatten_into_a_single_dotted_spelling
    (payload : Core.Ty) (dataType : Core.DataTypeId) :
    let old : TypeNameTable := [(["Pkg", "Thing"], payload)]
    let next := (["Pkg.Thing"], .namedData dataType) :: old
    TypeNameTable.Extends old next ∧ interpretTypeName? next qualified = some payload ∧
    interpretTypeName? old (annotation "Pkg.Thing") = none ∧
    interpretTypeName? next (annotation "Pkg.Thing") = some (.namedData dataType) := by
  intro old next
  have extension : TypeNameTable.Extends old next :=
    TypeNameTable.Extends.cons_fresh old ["Pkg.Thing"] (.namedData dataType)
      (by change ["Pkg.Thing"] ∉ [["Pkg", "Thing"]]; decide)
  exact ⟨extension, interpretTypeName?_some_of_extends extension rfl, rfl, rfl⟩

theorem common_actual_arguments_preserve_every_run_exact_checkpoint_and_cost
    (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types payload) next) (arguments : List TypedRuntimeArgument)
    (fuel cost : Nat) (initialStore finalStore : Core.Store) (type : Core.Ty) (value : Core.Value) (checkpoint : Core.State) :
    runRuntimeFunction? (types payload) id (entry "Payload" conditional) arguments fuel initialStore =
      runRuntimeFunction? next id (entry "Payload" conditional) arguments fuel initialStore ∧
    (RuntimeFunctionEvaluatesWithCost (types payload) id (entry "Payload" conditional) arguments initialStore type value finalStore cost ↔
      RuntimeFunctionEvaluatesWithCost next id (entry "Payload" conditional) arguments initialStore type value finalStore cost) ∧
    (runRuntimeFunction? (types payload) id (entry "Payload" conditional) arguments fuel initialStore = some (type, .outOfFuel checkpoint) ↔
      runRuntimeFunction? next id (entry "Payload" conditional) arguments fuel initialStore = some (type, .outOfFuel checkpoint)) := by
  have first := compilation id payload conditional
  have second := first.extend_types extension
  have same := first.run_eq_of_same_core second rfl rfl arguments fuel initialStore
  exact ⟨same, first.cost_iff_of_same_core second rfl rfl, by rw [same]⟩

end Tests.FrontendTypeTableExtension
