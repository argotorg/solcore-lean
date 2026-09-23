import Solcore.Frontend.LocalFunctionApplication

/-! Simultaneous identity relabeling leaves spellings, positional Core, values,
and complete machine results unchanged. Injectivity and allocation boundaries
are exercised separately rather than treated as source binding policies. -/

set_option autoImplicit false

namespace Tests.FrontendLocalIdentityRenaming

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"IdentityRenaming", by decide⟩], by decide⟩⟩, 0⟩
private def localId (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def shift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 10 }
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  cases left
  cases right
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases owners
  cases indices
  rfl
private def span : Syntax.SourceSpan := ⟨⟨.main, "identity-renaming.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def neg (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ operand⟩
private def andE (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .logicalAnd⟩ right⟩
private def orE (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .logicalOr⟩ right⟩
private def inputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "b" .bool (.bool true) .bool).bindFresh
    owner "a" .bool (.bool (!choice)) .bool).bindFresh owner "a" .bool (.bool choice) .bool
private def renamed (choice : Bool) : LocalInputs := (inputs choice).mapIds shift shift_injective
private def source : Syntax.Expr :=
  ⟨span, .conditional (neg (ref "a")) span (andE (ref "b") (ref "a")) span (orE (ref "a") (ref "b"))⟩
private def core : Core.Expr := .ifE (.unary .boolNot (.var 0))
  (.ifE (.var 2) (.var 0) (.bool false)) (.ifE (.var 0) (.bool true) (.var 2))
private theorem names_ne : "a" ≠ "b" := by decide
private theorem ids20_ne : localId 2 ≠ localId 0 := by decide
private theorem ids10_ne : localId 1 ≠ localId 0 := by decide
private theorem checked (choice : Bool) : (inputs choice).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete
    (.conditional (.logicalNot (.identifier .head))
      (.logicalAnd (.identifier (.tail names_ne (.tail names_ne .head))) (.identifier .head))
      (.logicalOr (.identifier .head) (.identifier (.tail names_ne (.tail names_ne .head)))))
    (.ifE (.unary (.var .head)) (.ifE (.var (.tail ids20_ne (.tail ids10_ne .head))) (.var .head) .bool)
      (.ifE (.var .head) .bool (.var (.tail ids20_ne (.tail ids10_ne .head)))))
    (.ifE (.unary (.var .head)) (.ifE (.var (.tail ids20_ne (.tail ids10_ne .head))) (.var .head) .bool)
      (.ifE (.var .head) .bool (.var (.tail ids20_ne (.tail ids10_ne .head)))))

theorem offset_is_injective_and_keeps_same_name_shadowing (choice : Bool) (store : Core.Store) :
    Function.Injective shift ∧ (inputs choice).ids = [localId 2, localId 1, localId 0] ∧
    (renamed choice).ids = [localId 12, localId 11, localId 10] ∧
    LocalExpressionEvaluates (renamed choice).names (renamed choice).environment store (ref "a") (.bool choice) store :=
  ⟨shift_injective, rfl, rfl, .identifier .head .head⟩

theorem boolean_forms_keep_exact_core_and_typing (choice : Bool) (type : Core.Ty) :
    (inputs choice).check? source = some (core, .bool) ∧
    (renamed choice).check? source = some (core, .bool) ∧
    (LocalExpressionHasType (renamed choice).names (renamed choice).context source type ↔
      LocalExpressionHasType (inputs choice).names (inputs choice).context source type) :=
  ⟨checked choice, ((inputs choice).check?_mapIds shift shift_injective source).trans (checked choice),
    (inputs choice).hasType_mapIds_iff shift shift_injective⟩

theorem same_fuel_preserves_complete_suspended_and_done_results (choice : Bool) (store : Core.Store) :
    (∀ fuel, (renamed choice).run? fuel source store = (inputs choice).run? fuel source store) ∧
    (renamed choice).run? 8 source store = some (.bool, .outOfFuel
      (Core.State.initial (if choice then .bool true else .var 0)
        (Resolved.LocalScope.values (inputs choice).environment) store)) ∧
    (renamed choice).run? 9 source store = some (.bool, .done (.bool choice) store) := by
  refine ⟨fun fuel => (inputs choice).run?_mapIds shift shift_injective fuel source store, ?_, ?_⟩
  · rw [renamed, LocalInputs.run?_mapIds, LocalInputs.run?, checked]; cases choice <;> rfl
  · rw [renamed, LocalInputs.run?_mapIds, LocalInputs.run?, checked]; cases choice <;> rfl

private def unsupported : Syntax.Expr := ⟨span, .literal ⟨span, .string "7"⟩⟩
private def badRights : List Syntax.Expr := [ref "missing", unsupported]
private theorem bad_check (right : Syntax.Expr) (member : right ∈ badRights) :
    (inputs false).check? (andE (ref "a") right) = none := by
  simp only [badRights, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, andE, ref, unsupported,
    interpretWordLiteral?, numericLiteralValue?,
    inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

theorem skipped_failed_syntax_keeps_raw_evaluation_iff_and_check_failure
    (value : Core.Value) (initialStore finalStore : Core.Store) :
    ∀ right ∈ badRights,
      LocalExpressionEvaluates (inputs false).names (inputs false).environment initialStore
        (andE (ref "a") right) (.bool false) initialStore ∧
      (LocalExpressionEvaluates (renamed false).names (renamed false).environment initialStore
        (andE (ref "a") right) value finalStore ↔
        LocalExpressionEvaluates (inputs false).names (inputs false).environment initialStore
          (andE (ref "a") right) value finalStore) ∧
      (inputs false).check? (andE (ref "a") right) = none ∧
      (renamed false).check? (andE (ref "a") right) = none := by
  intro right member
  exact ⟨.andFalse (.identifier .head .head), (inputs false).evaluates_mapIds_iff shift shift_injective,
    bad_check right member,
    ((inputs false).check?_mapIds shift shift_injective _).trans (bad_check right member)⟩

private def aliases : LocalNameTable := [("a", localId 0), ("b", localId 0), ("a", localId 1)]
private def rawContext : Resolved.Context := [(localId 0, .bool), (localId 1, .bool)]
private def aliasValues : Resolved.Environment := [(localId 0, .bool false), (localId 1, .bool true)]

theorem raw_aliases_and_repeated_names_are_preserved (value : Core.Value) (initialStore finalStore : Core.Store) :
    (LocalNameTable.mapIds shift aliases).lookup? "a" = some (localId 10) ∧
    (LocalNameTable.mapIds shift aliases).lookup? "b" = some (localId 10) ∧
    elaborateLocalExpression? (LocalNameTable.mapIds shift aliases)
      (Resolved.LocalScope.mapIds shift rawContext) (ref "b") = some (.var 0, .bool) ∧
    (LocalExpressionEvaluates (LocalNameTable.mapIds shift aliases) (Resolved.LocalScope.mapIds shift aliasValues)
      initialStore (ref "b") value finalStore ↔ LocalExpressionEvaluates aliases aliasValues initialStore (ref "b") value finalStore) := by
  have accepted : elaborateLocalExpression? aliases rawContext (ref "b") = some (.var 0, .bool) :=
    elaborateLocalExpression?_complete (.identifier (.tail names_ne .head)) (.var .head) (.var .head)
  exact ⟨rfl, rfl, (elaborateLocalExpression?_mapIds shift shift_injective aliases rawContext _).trans accepted,
    localExpressionEvaluates_mapIds_iff shift shift_injective⟩

private def merge (_ : Resolved.LocalId) : Resolved.LocalId := localId 0
private def distinctNames : LocalNameTable := [("a", localId 0), ("b", localId 1)]
private def distinctValues : Resolved.Environment := [(localId 0, .bool true), (localId 1, .bool false)]

/-- Positional Boolean typing does not detect identity capture by a merging map. -/
theorem merging_distinct_ids_changes_core_position_and_value (store : Core.Store) :
    (¬ Function.Injective merge) ∧
    Core.EnvironmentHasTypes (Resolved.LocalScope.values (Resolved.LocalScope.mapIds merge distinctValues))
      (Resolved.LocalScope.values (Resolved.LocalScope.mapIds merge rawContext)) ∧
    elaborateLocalExpression? distinctNames rawContext (ref "b") = some (.var 1, .bool) ∧
    elaborateLocalExpression? (LocalNameTable.mapIds merge distinctNames)
      (Resolved.LocalScope.mapIds merge rawContext) (ref "b") = some (.var 0, .bool) ∧
    LocalExpressionEvaluates distinctNames distinctValues store (ref "b") (.bool false) store ∧
    LocalExpressionEvaluates (LocalNameTable.mapIds merge distinctNames)
      (Resolved.LocalScope.mapIds merge distinctValues) store (ref "b") (.bool true) store ∧
    Core.runStateful 1 (Core.State.initial (.var 1) (Resolved.LocalScope.values distinctValues) store) =
      .done (.bool false) store ∧
    Core.runStateful 1 (Core.State.initial (.var 0)
      (Resolved.LocalScope.values (Resolved.LocalScope.mapIds merge distinctValues)) store) = .done (.bool true) store := by
  refine ⟨?_, .cons .bool (.cons .bool .nil), ?_, ?_,
    .identifier (.tail names_ne .head) (.tail (Ne.symm ids10_ne) .head),
    .identifier (.tail names_ne .head) .head, rfl, rfl⟩
  · intro injective
    exact ids10_ne (injective (show merge (localId 1) = merge (localId 0) from rfl))
  · exact elaborateLocalExpression?_complete (.identifier (.tail names_ne .head))
      (.var (.tail (Ne.symm ids10_ne) .head)) (.var (.tail (Ne.symm ids10_ne) .head))
  · exact elaborateLocalExpression?_complete (.identifier (.tail names_ne .head)) (.var .head) (.var .head)

theorem merged_duplicate_ids_cannot_form_a_typed_bundle :
    Resolved.LocalScope.ids (Resolved.LocalScope.mapIds merge rawContext) = [localId 0, localId 0] ∧
    ¬ ∃ bundle : LocalInputs, bundle.ids = Resolved.LocalScope.ids (Resolved.LocalScope.mapIds merge rawContext) := by
  refine ⟨rfl, ?_⟩
  rintro ⟨bundle, same⟩
  have distinct := bundle.ids_nodup
  change bundle.ids.Nodup at distinct
  rw [same] at distinct
  change [localId 0, localId 0].Nodup at distinct
  simp at distinct

private def allocated : LocalInputs := LocalInputs.empty.bindFresh owner "x" .unit .unit .unit
private def mappedThenAllocated : LocalInputs :=
  (LocalInputs.empty.mapIds shift shift_injective).bindFresh owner "x" .unit .unit .unit

theorem allocation_does_not_commute_with_identity_offset :
    (allocated.mapIds shift shift_injective).ids = [localId 10] ∧
    mappedThenAllocated.ids = [localId 0] ∧ allocated.mapIds shift shift_injective ≠ mappedThenAllocated := by
  refine ⟨rfl, rfl, ?_⟩
  intro same
  have different := congrArg LocalInputs.ids same
  change [localId 10] = [localId 0] at different
  exact (by decide : [localId 10] ≠ [localId 0]) different

end Tests.FrontendLocalIdentityRenaming
