import Solcore.Frontend.RuntimeFunction

/-! Preserve actual input bundles, not merely their static projections.
Original annotations, independent provenance and manual paths fix expectations. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeTypeExtension
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RuntimeExtension", by decide⟩], by decide⟩⟩, 0⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "runtime-extension.sol"⟩, 17, 4⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) (annotation : Syntax.TypeExpr) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ annotation⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Cond"], .bool)]
private def parameters := [parameter "p" (named "Payload"), parameter "c" (named "Cond")]
private def pair : Syntax.Expr := ⟨span, .tuple ⟨span, [ref "saved", ref "c"]⟩⟩
private def body : Syntax.Block := ⟨span, [⟨span, .block [
  ⟨span, .letDecl ⟨span, "saved"⟩ (some (named "Payload")) (some (ref "p"))⟩,
  ⟨span, .expression pair true⟩, ⟨span, .returnStmt (some (ref "saved"))⟩]⟩]⟩
private def core : Core.Expr := .letE (.var 1) (.letE (.pair (.var 0) (.var 1)) (.var 1))
private def entry (result : String := "Payload") : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "same"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [named result]⟩⟩, none⟩, body⟩⟩
private def static (type : Core.Ty) := (LocalTypeInputs.empty.bindFresh owner "p" type).bindFresh owner "c" .bool
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def arguments {type : Core.Ty} (value : Actual type) (choice : Bool) : List TypedRuntimeArgument :=
  [⟨type, value.val, value.property⟩, ⟨.bool, .bool choice, .bool⟩]
private def inputs {type : Core.Ty} (value : Actual type) (choice : Bool) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "p" type value.val value.property).bindFresh owner "c" .bool (.bool choice) .bool
private def prepared {type : Core.Ty} (value : Actual type) (choice : Bool) : PreparedRuntimeFunction :=
  ⟨inputs value choice, core, type⟩
private theorem bound {type : Core.Ty} (value : Actual type) (choice : Bool) :
    RuntimeParametersBind (types type) owner parameters (arguments value choice) (inputs value choice) :=
  .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "c" ∉ ["p"]; decide) .nil)
private theorem header (type : Core.Ty) : RuntimeFunctionHeader (types type) entry.value.signature type :=
  ⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩
private theorem elaborated (type : Core.Ty) :
    TypedLetReturnTreeElaborates (types type) owner (static type) body core type := by
  have tail : TypedLetReturnTreeElaborates (types type) owner ((static type).bindFresh owner "saved" type)
      ⟨span, [⟨span, .expression pair true⟩, ⟨span, .returnStmt (some (ref "saved"))⟩]⟩
      (.letE (.pair (.var 0) (.var 1)) ((Core.Expr.var 0).weakenAt 0)) type :=
    .discard (.pair (.identifier .head) (.identifier (.tail (by change "saved" ≠ "c"; decide) .head)))
      (.pair (.var .head) (.var (.tail (by change id 2 ≠ id 1; decide) .head)))
      (.pair (.var .head) (.var (.tail (by change id 2 ≠ id 1; decide) .head)))
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
  simp only [Core.Expr.weakenAt] at tail
  exact .block (.binding (.named .head) (by change "saved" ∉ ["c", "p"]; decide)
    (.identifier (.tail (by change "c" ≠ "p"; decide) .head))
    (.var (.tail (by change id 1 ≠ id 0; decide) .head)) (.var (.tail (by change id 1 ≠ id 0; decide) .head)) tail)
private theorem preparation {type : Core.Ty} (value : Actual type) (choice : Bool) :
    RuntimeFunctionPrepares (types type) owner entry (arguments value choice) (prepared value choice) :=
  ⟨header type, bound value choice, elaborated type⟩
private theorem counted {type : Core.Ty} (value : Actual type) (choice : Bool) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (inputs value choice).names (inputs value choice).environment
      store body value.val store 11 :=
  .block (.binding (name := ⟨span, "saved"⟩) (initializer := ref "p") (initializerCost := 1) (tailCost := 8)
    (.identifier (.tail (by change "c" ≠ "p"; decide) .head) (.tail (by change id 1 ≠ id 0; decide) .head))
    (.discard (expression := pair) (expressionCost := 5) (tailCost := 1)
      (.pair (left := ref "saved") (right := ref "c") (.identifier .head .head) (.identifier (.tail (by change "saved" ≠ "c"; decide) .head)
        (.tail (by change id 2 ≠ id 1; decide) .head))) (.single (.expression (.identifier .head .head)))))
private theorem path (value : Core.Value) (choice : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 11 ⟨.eval core [.bool choice, value], k, store⟩ ⟨.ret value, k, store⟩ :=
  CostStepComposition.letE (.cons (.var rfl) .refl)
    (CostStepComposition.letE (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
      (.cons (.var rfl) (.cons .applyPair .refl))))) (.cons (.var rfl) .refl))
private theorem runExact {type : Core.Ty} (value : Actual type) (choice : Bool) (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? (types type) owner entry (arguments value choice) fuel store =
      some (type, Core.runStateful fuel (Core.State.initial core [.bool choice, value.val] store)) :=
  runRuntimeFunction?_eq_some_iff.mpr ⟨prepared value choice, preparation value choice, rfl, rfl⟩

theorem arbitrary_initial_actual_rows_and_values_are_not_erased
    (initial : LocalInputs) (argument : TypedRuntimeArgument) (own : Resolved.DeclarationId)
    (unused : "next" ∉ initial.names.map Prod.fst) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types argument.type) next) :
    RuntimeParametersBindFrom (types argument.type) own initial [parameter "next" (named "Payload")] [argument]
      (initial.bindFresh own "next" argument.type argument.value argument.valueTyped) ∧
    RuntimeParametersBindFrom next own initial [parameter "next" (named "Payload")] [argument]
      (initial.bindFresh own "next" argument.type argument.value argument.valueTyped) := by
  have original : RuntimeParametersBindFrom (types argument.type) own initial [parameter "next" (named "Payload")] [argument]
      (initial.bindFresh own "next" argument.type argument.value argument.valueTyped) := .cons (.named .head) unused .nil
  exact ⟨original, original.extend_types extension⟩

private def sparse : LocalInputs := ⟨[⟨"old", id 7, .unit, .unit, .unit⟩,
  ⟨"old", ⟨other, 99⟩, .bool, .bool true, .bool⟩, ⟨"old", id 2, .unit, .unit, .unit⟩], by decide⟩
theorem sparse_mixed_owners_and_duplicate_old_spellings_keep_max_plus_one (extras : TypeNameTable) :
    ¬ (sparse.names.map Prod.fst).Nodup ∧ Resolved.freshLocalId owner sparse.ids = id 8 ∧
    RuntimeParametersBindFrom (types .bool ++ extras) owner sparse [parameter "next" (named "Payload")]
      [⟨.bool, .bool false, .bool⟩] (sparse.bindFresh owner "next" .bool (.bool false) .bool) ∧
    (sparse.bindFresh owner "next" .bool (.bool false) .bool).environment.values = [.bool false, .unit, .bool true, .unit] :=
  ⟨by decide, rfl, (arbitrary_initial_actual_rows_and_values_are_not_erased sparse ⟨.bool, .bool false, .bool⟩ owner
    (by decide) _ (TypeNameTable.Extends.append_right _ extras)).2, rfl⟩

theorem independent_whole_preparation_preserves_the_full_actual_bundle
    {type : Core.Ty} (value : Actual type) (choice : Bool) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types type) next) :
    RuntimeParametersBind next owner parameters (arguments value choice) (inputs value choice) ∧
    bindRuntimeParameters? next owner parameters (arguments value choice) = some (inputs value choice) ∧
    RuntimeFunctionPrepares next owner entry (arguments value choice) (prepared value choice) ∧
    RuntimeFunctionHasType next owner entry (arguments value choice) type ∧
    prepareRuntimeFunction? next owner entry (arguments value choice) = some (prepared value choice) ∧
    (prepared value choice).inputs.environment.values = [.bool choice, value.val] :=
  ⟨RuntimeParametersBind.extend_types (bound value choice) extension,
    bindRuntimeParameters?_some_of_extends extension (bound value choice).complete,
    (preparation value choice).extend_types extension, (preparation value choice).hasType.extend_types extension,
    prepareRuntimeFunction?_some_of_extends extension (preparation value choice).complete, rfl⟩

theorem one_way_extension_preserves_every_present_fuel_result
    {type : Core.Ty} (value : Actual type) (choice : Bool) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types type) next) (store : Core.Store) (fuel : Nat) (k : List Core.Frame) :
    runRuntimeFunction? next owner entry (arguments value choice) fuel store =
      some (type, Core.runStateful fuel (Core.State.initial core [.bool choice, value.val] store)) ∧
    Core.Steps 11 ⟨.eval core [.bool choice, value.val], k, store⟩ ⟨.ret value.val, k, store⟩ ∧
    (runRuntimeFunction? (types type) owner entry (arguments value choice) fuel store = some (type, .done value.val store) ↔ 11 ≤ fuel) :=
  ⟨runRuntimeFunction?_some_of_extends extension (runExact value choice fuel store), path _ choice store k,
    (RuntimeFunctionEvaluatesWithCost.intro (preparation value choice) (counted value choice store)).run_done_iff⟩

private def duplicate (type : Core.Ty) := (["Payload"], type) :: types type
private theorem mutualExtension (type : Core.Ty) : TypeNameTable.Extends (types type) (duplicate type) ∧ TypeNameTable.Extends (duplicate type) (types type) := by
  constructor
  · intro key result found
    cases found with
    | head => exact .head
    | tail different found => exact .tail different (.tail different found)
  · intro key result found
    cases found with
    | head => exact .head
    | tail _ found => exact found
theorem unequal_mutual_tables_preserve_whole_options_not_just_success
    (type : Core.Ty) (own : Resolved.DeclarationId) (params : List Syntax.FunctionParameter)
    (declaration : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    types type ≠ duplicate type ∧
    bindRuntimeParameters? (types type) own params args = bindRuntimeParameters? (duplicate type) own params args ∧
    prepareRuntimeFunction? (types type) own declaration args = prepareRuntimeFunction? (duplicate type) own declaration args ∧
    runRuntimeFunction? (types type) own declaration args fuel store = runRuntimeFunction? (duplicate type) own declaration args fuel store := by
  refine ⟨?_, bindRuntimeParameters?_eq_of_mutual_extends (mutualExtension type).1 (mutualExtension type).2 own params args,
    prepareRuntimeFunction?_eq_of_mutual_extends (mutualExtension type).1 (mutualExtension type).2 own declaration args,
    runRuntimeFunction?_eq_of_mutual_extends (mutualExtension type).1 (mutualExtension type).2 own declaration args fuel store⟩
  intro same
  have lengths := congrArg List.length same
  change 2 = 3 at lengths
  cases lengths

private def checkpoint (value : Core.Value) (choice : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.pair value (.bool choice)), [.letBody (.var 1) [value, .bool choice, value]], store⟩
theorem genuine_saved_pair_states_and_remaining_two_steps_are_identical
    {type : Core.Ty} (value : Actual type) (choice : Bool) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types type) next) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? (types type) owner entry (arguments value choice) 9 store = some (type, .outOfFuel (checkpoint value.val choice store)) ∧
    runRuntimeFunction? next owner entry (arguments value choice) 9 store = some (type, .outOfFuel (checkpoint value.val choice store)) ∧
    Core.Steps 2 (checkpoint value.val choice store) (Core.State.final value.val store) ∧
    runRuntimeFunction? next owner entry (arguments value choice) (9 + additional) store =
      some (type, Core.runStateful additional (checkpoint value.val choice store)) := by
  have stopped : runRuntimeFunction? (types type) owner entry (arguments value choice) 9 store =
      some (type, .outOfFuel (checkpoint value.val choice store)) := runExact value choice 9 store
  have transported := runRuntimeFunction?_some_of_extends extension stopped
  exact ⟨stopped, transported, .cons .bindLet (.cons (.var rfl) .refl), runRuntimeFunction?_resume transported additional⟩

theorem empty_and_single_tuple_parameters_are_not_component_argument_lists
    {type : Core.Ty} (value : Actual type) (choice : Bool) (extras : TypeNameTable) :
    bindRuntimeParameters? (types type ++ extras) owner [] [] = some .empty ∧
    RuntimeParametersBind (types type ++ extras) owner
      [parameter "one" ⟨span, .tuple [named "Payload", named "Cond"]⟩]
      [⟨.product type .bool, .pair value.val (.bool choice), .pair value.property .bool⟩]
      (LocalInputs.empty.bindFresh owner "one" (.product type .bool) (.pair value.val (.bool choice)) (.pair value.property .bool)) ∧
    bindRuntimeParameters? (types type) owner parameters [] = none := by
  have original : RuntimeParametersBind (types type) owner [parameter "one" ⟨span, .tuple [named "Payload", named "Cond"]⟩]
      [⟨.product type .bool, .pair value.val (.bool choice), .pair value.property .bool⟩]
      (LocalInputs.empty.bindFresh owner "one" (.product type .bool) (.pair value.val (.bool choice)) (.pair value.property .bool)) :=
    .cons (.pair (.named .head) (.named (.tail (by decide) .head))) (by simp [LocalInputs.empty, LocalInputs.names]) .nil
  exact ⟨rfl, RuntimeParametersBind.extend_types original (TypeNameTable.Extends.append_right _ extras), rfl⟩

theorem unknown_meaning_can_enable_the_same_actual_arguments
    {type : Core.Ty} (value : Actual type) (choice : Bool) :
    TypeNameTable.Extends [(["Cond"], .bool)] (types type) ∧
    bindRuntimeParameters? [(["Cond"], .bool)] owner parameters (arguments value choice) = none ∧
    bindRuntimeParameters? (types type) owner parameters (arguments value choice) = some (inputs value choice) ∧
    prepareRuntimeFunction? [(["Cond"], .bool)] owner entry (arguments value choice) = none ∧
    prepareRuntimeFunction? (types type) owner entry (arguments value choice) = some (prepared value choice) := by
  refine ⟨TypeNameTable.Extends.cons_fresh _ ["Payload"] type (by decide), ?_, (bound value choice).complete,
    ?_, (preparation value choice).complete⟩
  · apply bindRuntimeParameters?_eq_none_iff.mpr
    rintro ⟨output, evidence⟩
    cases evidence with
    | cons meaning _ _ =>
        have accepted := meaning.complete
        simp only [named, interpretStructuralType?_named_eq_typeName] at accepted
        change none = some type at accepted
        cases accepted
  · simp only [prepareRuntimeFunction?, entry, interpretRuntimeFunctionHeader?, interpretRuntimeReturnType?, named,
      interpretStructuralType?_named_eq_typeName]
    rfl

theorem mutually_extending_tables_keep_unknown_header_rejection
    {type : Core.Ty} (value : Actual type) (choice : Bool) (fuel : Nat) (store : Core.Store) :
    prepareRuntimeFunction? (types type) owner (entry "Unknown") (arguments value choice) = none ∧
    prepareRuntimeFunction? (duplicate type) owner (entry "Unknown") (arguments value choice) = none ∧
    runRuntimeFunction? (duplicate type) owner (entry "Unknown") (arguments value choice) fuel store = none := by
  have absent : prepareRuntimeFunction? (types type) owner (entry "Unknown") (arguments value choice) = none := by
    simp only [prepareRuntimeFunction?, entry, interpretRuntimeFunctionHeader?, interpretRuntimeReturnType?, named,
      interpretStructuralType?_named_eq_typeName]
    rfl
  have same := prepareRuntimeFunction?_eq_of_mutual_extends (mutualExtension type).1 (mutualExtension type).2 owner (entry "Unknown") (arguments value choice)
  exact ⟨absent, same.symm.trans absent, by simp [runRuntimeFunction?, same.symm.trans absent]⟩

theorem retained_rows_do_not_license_changed_first_meanings (value : Actual .word) :
    TypeNameTable.lookup? ((["Payload"], .bool) :: types .word) ["Payload"] = some .bool ∧
    ¬ TypeNameTable.Extends (types .word) ((["Payload"], .bool) :: types .word) ∧
    bindRuntimeParameters? ((["Payload"], .bool) :: types .word) owner parameters (arguments value true) = none := by
  refine ⟨rfl, ?_, ?_⟩
  · intro extension
    cases (extension (.head : TypeNameTable.Lookup (types .word) ["Payload"] .word)).type_unique
      (.head : TypeNameTable.Lookup ((["Payload"], .bool) :: types .word) ["Payload"] .bool)
  · apply bindRuntimeParameters?_eq_none_iff.mpr
    rintro ⟨output, evidence⟩
    cases evidence with
    | cons meaning _ _ => cases meaning.type_unique (.named (.head : TypeNameTable.Lookup
        ((["Payload"], .bool) :: types .word) ["Payload"] .bool))

theorem nominal_static_compilation_cannot_invent_actual_arguments (nominal : Core.DataTypeId) (extras : TypeNameTable) :
    compileRuntimeFunction? (types (.namedData nominal) ++ extras) owner entry = some ⟨static (.namedData nominal), core, .namedData nominal⟩ ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  have original : RuntimeFunctionCompiles (types (.namedData nominal)) owner entry ⟨static (.namedData nominal), core, .namedData nominal⟩ :=
    ⟨header _, .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named (.tail (by decide) .head)) (by change "c" ∉ ["p"]; decide) .nil), elaborated _⟩
  refine ⟨compileRuntimeFunction?_some_of_extends (TypeNameTable.Extends.append_right _ extras) original.complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩; cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem opaque_actual_cells_and_closures_survive_extension (location : Core.Location) (word : Core.Word)
    (extras : TypeNameTable) (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? (types (.cell .word) ++ extras) owner entry (arguments ⟨.cellRef .word location, .cellRef⟩ true) fuel store =
      some (.cell .word, Core.runStateful fuel (Core.State.initial core [.bool true, .cellRef .word location] store)) ∧
    runRuntimeFunction? (types (.function .bool .word) ++ extras) owner entry
      (arguments ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ false) fuel store =
      some (.function .bool .word, Core.runStateful fuel (Core.State.initial core [.bool false, .closure .bool .word (.var 1) [.word word]] store)) :=
  ⟨runRuntimeFunction?_some_of_extends (TypeNameTable.Extends.append_right _ extras) (runExact _ true fuel store),
    runRuntimeFunction?_some_of_extends (TypeNameTable.Extends.append_right _ extras) (runExact _ false fuel store)⟩

private def number (n : Nat) : Actual .word := ⟨.word (Core.Word.ofNatModulo n), .word⟩
theorem the_same_compiled_projection_does_not_identify_different_actual_preparations :
    (prepared (number 3) true).toCompiled = (prepared (number 7) true).toCompiled ∧
    prepared (number 3) true ≠ prepared (number 7) true ∧
    runRuntimeFunction? (types .word) owner entry (arguments (number 3) true) 11 [] = some (.word, .done (number 3).val []) ∧
    runRuntimeFunction? (types .word) owner entry (arguments (number 7) true) 11 [] = some (.word, .done (number 7).val []) ∧
    (number 3).val ≠ (number 7).val := by
  have different : (number 3).val ≠ (number 7).val := by
    intro same
    have words := Core.Value.word.inj same
    have numbers := congrArg Fin.val words
    change 3 = 7 at numbers
    cases numbers
  refine ⟨rfl, ?_, runExact (number 3) true 11 [], runExact (number 7) true 11 [], different⟩
  intro same
  have rows := congrArg (fun prepared : PreparedRuntimeFunction => prepared.inputs.environment.values) same
  exact different (List.cons.inj (List.cons.inj rows).2).1

end Tests.FrontendRuntimeTypeExtension
