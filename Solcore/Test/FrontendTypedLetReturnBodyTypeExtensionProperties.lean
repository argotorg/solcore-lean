import Solcore.Frontend.TypedLetReturnBodyRunnerTypeExtensionProperties
import Solcore.Frontend.TypedLetReturnBodyFuelBoundProperties
import Solcore.Frontend.TypedLetReturnBodyResumptionProperties

/-! First-match meaning extension keeps fixed inputs and exact source results.
Repairing an unknown annotation is different from changing an existing meaning. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBodyTypeExtension

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTypeTables", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-type-tables.sol"⟩, 191, 10⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def binding (annotation : Syntax.TypeExpr) (name : String) (value : Syntax.Expr) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩
private def returned (value : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some value)⟩]⟩
private def statements (annotation : Syntax.TypeExpr) : List String → String → List Syntax.Statement
  | [], previous => (returned (ref previous)).value
  | name :: rest, previous => binding annotation name (ref previous) :: statements annotation rest name
private def chain (annotation : Syntax.TypeExpr) (names : List String) (previous : String) : Syntax.Block := ⟨span, statements annotation names previous⟩
private def chainCore : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .letE (.var 0) (chainCore count)
private def initial (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"seed", id 0, type⟩, ⟨"side", id 1, .word⟩, ⟨"c", id 2, .bool⟩], by change [id 0, id 1, id 2].Nodup; decide⟩
private theorem chainElaborated (names : List String) (previous : String) (type : Core.Ty)
    (table : TypeNameTable) (annotation : Syntax.TypeExpr) (meaning : TypeNameDenotes table annotation type)
    (inputs : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ inputs.names.map Prod.fst)
    (resolution : ResolvesLocalExpression inputs.names (ref previous) resolved)
    (lowered : Resolved.Lowers inputs.ids resolved (.var 0)) (typing : Resolved.HasType inputs.context resolved type) :
    TypedLetReturnBodyElaborates table owner inputs (chain annotation names previous) (chainCore names.length) type := by
  induction names generalizing previous inputs resolved with
  | nil =>
      simp only [chain, statements, returned, List.length_nil, chainCore]
      exact .terminal (.single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing))
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      simp only [chain, statements, List.length_cons, chainCore]
      apply TypedLetReturnBodyElaborates.binding (name := ⟨span, name⟩) meaning (fresh name (by simp)) resolution lowered typing
      apply ih name (inputs.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
private theorem seedChain (names : List String) (type : Core.Ty) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "c"]) :
    TypedLetReturnBodyElaborates (types type) owner (initial type) (chain (named "Payload") names "seed") (chainCore names.length) type :=
  chainElaborated names "seed" type (types type) (named "Payload") (.named .head) (initial type) _ distinct fresh
    (.identifier .head) (.var .head) (.var .head)
private theorem oneElab (type : Core.Ty) (table : TypeNameTable) (annotation : Syntax.TypeExpr)
    (meaning : TypeNameDenotes table annotation type) :
    TypedLetReturnBodyElaborates table owner (initial type) (chain annotation ["x"] "seed") (chainCore 1) type :=
  chainElaborated ["x"] "seed" type table annotation meaning (initial type) _ (by decide)
    (by change ∀ name ∈ ["x"], name ∉ ["seed", "side", "c"]; decide) (.identifier .head) (.var .head) (.var .head)

theorem arbitrary_length_independent_static_provenance_retains_the_exact_core_and_type
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "c"])
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types type) next) :
    TypedLetReturnBodyElaborates next owner (initial type) (chain (named "Payload") names "seed") (chainCore names.length) type ∧
    TypedLetReturnBodyHasType next owner (initial type) (chain (named "Payload") names "seed") type ∧
    elaborateTypedLetReturnBody? next owner (initial type) (chain (named "Payload") names "seed") = some (chainCore names.length, type) :=
  ⟨(seedChain names type distinct fresh).extend_types extension, (seedChain names type distinct fresh).hasType.extend_types extension,
    elaborateTypedLetReturnBody?_some_of_extends extension (seedChain names type distinct fresh).complete⟩

theorem nominal_static_chains_extend_without_creating_runtime_inhabitants
    (names : List String) (nominal : Core.DataTypeId) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "c"]) (extras : TypeNameTable) :
    elaborateTypedLetReturnBody? (types (.namedData nominal) ++ extras) owner (initial (.namedData nominal))
      (chain (named "Payload") names "seed") = some (chainCore names.length, .namedData nominal) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(arbitrary_length_independent_static_provenance_retains_the_exact_core_and_type names _ distinct fresh _ (TypeNameTable.Extends.append_right _ extras)).2.2, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def hidden (type later : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Payload"], later)]
private theorem hiddenExtends (type first second : Core.Ty) : TypeNameTable.Extends (hidden type first) (hidden type second) := by
  intro key result found
  cases found with
  | head => exact .head
  | tail different rest =>
      cases rest with
      | head => exact False.elim (different rfl)
      | tail _ absent => cases absent
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def inputs {type : Core.Ty} (actual : Actual type) (side : Core.Word) (choice : Bool) : LocalInputs :=
  ⟨[⟨"seed", id 0, type, actual.val, actual.property⟩, ⟨"side", id 1, .word, .word side, .word⟩,
    ⟨"c", id 2, .bool, .bool choice, .bool⟩], by change [id 0, id 1, id 2].Nodup; decide⟩

theorem different_hidden_duplicates_preserve_complete_static_and_actual_options
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (choice : Bool) (body : Syntax.Block) (fuel : Nat) (store : Core.Store) :
    hidden type .word ≠ hidden type .bool ∧
    elaborateTypedLetReturnBody? (hidden type .word) owner (initial type) body = elaborateTypedLetReturnBody? (hidden type .bool) owner (initial type) body ∧
    (inputs actual side choice).checkTypedLetReturnBody? (hidden type .word) owner body = (inputs actual side choice).checkTypedLetReturnBody? (hidden type .bool) owner body ∧
    (inputs actual side choice).runTypedLetReturnBody? (hidden type .word) owner fuel body store =
      (inputs actual side choice).runTypedLetReturnBody? (hidden type .bool) owner fuel body store := by
  refine ⟨?_, elaborateTypedLetReturnBody?_eq_of_mutual_extends (hiddenExtends type .word .bool) (hiddenExtends type .bool .word) owner _ body,
    (inputs actual side choice).checkTypedLetReturnBody?_eq_of_mutual_extends (hiddenExtends type .word .bool) (hiddenExtends type .bool .word) owner body,
    (inputs actual side choice).runTypedLetReturnBody?_eq_of_mutual_extends (hiddenExtends type .word .bool) (hiddenExtends type .bool .word) owner fuel body store⟩
  intro same
  have later := congrArg (fun table => table[1]?) same
  cases later

private def subtract : Syntax.Expr := ⟨span, .binary (ref "seed") ⟨span, .subtract⟩ (ref "side")⟩
private def terminal : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") (returned (ref "y"))
  (some (returned ⟨span, .unary ⟨span, .bitNot⟩ (ref "y")⟩))⟩]⟩
private def ordered : Syntax.Block := ⟨span, binding (named "Payload") "x" subtract :: binding (named "Payload") "y" (ref "x") :: terminal.value⟩
private def terminalCore : Core.Expr := .ifE (.var 4) (.var 0) (.unary .wordNot (.var 0))
private def core : Core.Expr := .letE (.binary .wordSub (.var 0) (.var 1)) (.letE (.var 0) terminalCore)
private theorem orderedElab : TypedLetReturnBodyElaborates (types .word) owner (initial .word) ordered core .word :=
  .binding (.named .head) (by decide)
    (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head))) (.binary (.var .head) (.var (.tail (by decide) .head)))
    (.binding (.named .head) (by decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.conditional
        (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
        (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
        (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
        (.single (.expression (.identifier .head) (.var .head) (.var .head)))
        (.single (.expression (.bitNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))))))
private theorem runExact (seed side : Core.Word) (choice : Bool) (store : Core.Store) (fuel : Nat) (result : Core.StatefulRunResult)
    (ran : Core.runStateful fuel (Core.State.initial core [.word seed, .word side, .bool choice] store) = result) :
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? (types .word) owner fuel ordered store = some (.word, result) :=
  LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨core, orderedElab.complete, ran⟩

theorem one_way_extension_preserves_the_exact_successful_pair_even_before_completion
    (seed side : Core.Word) (choice : Bool) (store : Core.Store) (fuel : Nat) (next : TypeNameTable) (extension : TypeNameTable.Extends (types .word) next) :
    (inputs ⟨.word seed, .word⟩ side choice).checkTypedLetReturnBody? next owner ordered = some (core, .word) ∧
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? next owner fuel ordered store =
      some (.word, Core.runStateful fuel (Core.State.initial core [.word seed, .word side, .bool choice] store)) :=
  ⟨LocalInputs.checkTypedLetReturnBody?_some_of_extends (inputs := inputs ⟨.word seed, .word⟩ side choice) extension orderedElab.complete,
    LocalInputs.runTypedLetReturnBody?_some_of_extends extension (runExact seed side choice store fuel _ rfl)⟩

private def checkpoint (seed side : Core.Word) (choice : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.var 0) (.unary .wordNot (.var 0))
    [.word (seed.sub side), .word (seed.sub side), .word seed, .word side, .bool choice]], store⟩
theorem mutually_extending_tables_keep_the_genuine_checkpoint_and_asymmetric_residual_result
    (seed side : Core.Word) (choice : Bool) (store : Core.Store) (additional : Nat) :
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? (hidden .word .word) owner 12 ordered store = some (.word, .outOfFuel (checkpoint seed side choice store)) ∧
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? (hidden .word .bool) owner 12 ordered store = some (.word, .outOfFuel (checkpoint seed side choice store)) ∧
    Core.runStateful (if choice then 2 else 4) (checkpoint seed side choice store) =
      .done (.word (if choice then seed.sub side else (seed.sub side).bitNot)) store ∧
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? (hidden .word .bool) owner (12 + additional) ordered store =
      some (.word, Core.runStateful additional (checkpoint seed side choice store)) := by
  have original : (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? (types .word) owner 12 ordered store =
      some (.word, .outOfFuel (checkpoint seed side choice store)) := runExact seed side choice store 12 _ (by cases choice <;> rfl)
  have left := LocalInputs.runTypedLetReturnBody?_some_of_extends (TypeNameTable.Extends.append_right (types .word) [(["Payload"], .word)]) original
  have right := ((inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody?_eq_of_mutual_extends
    (hiddenExtends .word .word .bool) (hiddenExtends .word .bool .word) owner 12 ordered store).symm.trans left
  exact ⟨left, right, by cases choice <;> rfl, LocalInputs.runTypedLetReturnBody?_resume right additional⟩

private theorem oneCompleted {type : Core.Ty} (actual : Actual type) (side : Core.Word) (choice : Bool) (store : Core.Store) :
    (inputs actual side choice).runTypedLetReturnBody? (types type) owner 4 (chain (named "Payload") ["x"] "seed") store = some (type, .done actual.val store) :=
  LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨chainCore 1, (oneElab type (types type) (named "Payload") (.named .head)).complete, rfl⟩
theorem opaque_actual_cells_and_closures_keep_their_exact_completed_pairs_under_extension
    (location : Core.Location) (word side : Core.Word) (choice : Bool) (store : Core.Store) (extras : TypeNameTable) :
    (inputs (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word)) side choice).runTypedLetReturnBody? (types (.cell .word) ++ extras) owner 4
      (chain (named "Payload") ["x"] "seed") store = some (.cell .word, .done (.cellRef .word location) store) ∧
    (inputs (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word)) side choice).runTypedLetReturnBody?
      (types (.function .bool .word) ++ extras) owner 4 (chain (named "Payload") ["x"] "seed") store =
        some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨LocalInputs.runTypedLetReturnBody?_some_of_extends (TypeNameTable.Extends.append_right _ extras) (oneCompleted _ side choice store),
    LocalInputs.runTypedLetReturnBody?_some_of_extends (TypeNameTable.Extends.append_right _ extras) (oneCompleted _ side choice store)⟩

theorem adding_an_unknown_alias_repairs_whole_acceptance_with_the_same_fixed_inputs
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (choice : Bool) (store : Core.Store) (fuel : Nat) :
    TypeNameTable.Extends (types type) ((["Alias"], type) :: types type) ∧
    (inputs actual side choice).runTypedLetReturnBody? (types type) owner fuel (chain (named "Alias") ["x"] "seed") store = none ∧
    (inputs actual side choice).runTypedLetReturnBody? ((["Alias"], type) :: types type) owner fuel (chain (named "Alias") ["x"] "seed") store =
      some (type, Core.runStateful fuel (Core.State.initial (chainCore 1) [actual.val, .word side, .bool choice] store)) ∧
    typedLetReturnBodyFuelBound (chain (named "Alias") ["x"] "seed") = 4 := by
  refine ⟨TypeNameTable.Extends.cons_fresh _ ["Alias"] type (by change ["Alias"] ∉ [["Payload"]]; decide), ?_,
    LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨chainCore 1, (oneElab type ((["Alias"], type) :: types type) (named "Alias") (.named .head)).complete, rfl⟩, ?_⟩
  · apply LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr
    simp [LocalInputs.checkTypedLetReturnBody?, chain, statements, binding, elaborateTypedLetReturnBody?, interpretTypeName?, named, types,
      qualifiedTypeNameKey, TypeNameTable.lookup?, Syntax.NonemptyList.toList]
  · simp [chain, statements, binding, returned, ref, typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]

theorem retaining_every_old_row_does_not_make_a_changed_first_meaning_an_extension :
    (∀ row ∈ types .word, row ∈ ((["Payload"], Core.Ty.bool) :: types .word)) ∧
    ¬ TypeNameTable.Extends (types .word) ((["Payload"], .bool) :: types .word) ∧
    elaborateTypedLetReturnBody? (types .word) owner (initial .word) (chain (named "Payload") ["x"] "seed") = some (chainCore 1, .word) ∧
    elaborateTypedLetReturnBody? ((["Payload"], .bool) :: types .word) owner (initial .word) (chain (named "Payload") ["x"] "seed") = none := by
  refine ⟨fun row member => List.mem_cons_of_mem _ member, ?_, (oneElab .word (types .word) (named "Payload") (.named .head)).complete, ?_⟩
  · intro extension
    have conflict := (extension (.head : TypeNameTable.Lookup (types .word) ["Payload"] .word)).type_unique (.head : TypeNameTable.Lookup _ ["Payload"] .bool)
    cases conflict
  · have seedAccepted : elaborateLocalExpression? (initial .word).names (initial .word).context (ref "seed") = some (.var 0, .word) :=
      elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
    simp [chain, statements, binding, elaborateTypedLetReturnBody?, seedAccepted, interpretTypeName?, named, types,
      qualifiedTypeNameKey, TypeNameTable.lookup?, Syntax.NonemptyList.toList]

private def qualified : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Pkg"⟩, [⟨span, "Token"⟩]⟩⟩⟩ none⟩
theorem qualified_components_are_not_replaced_by_a_single_dotted_key (type : Core.Ty) :
    TypeNameTable.Extends [(["Pkg", "Token"], type)] [(["Pkg.Token"], .bool), (["Pkg", "Token"], type)] ∧
    elaborateTypedLetReturnBody? [(["Pkg.Token"], .bool), (["Pkg", "Token"], type)] owner (initial type) (chain qualified ["x"] "seed") = some (chainCore 1, type) ∧
    elaborateTypedLetReturnBody? [(["Pkg.Token"], type)] owner (initial type) (chain qualified ["x"] "seed") = none := by
  refine ⟨TypeNameTable.Extends.cons_fresh _ ["Pkg.Token"] .bool (by change ["Pkg.Token"] ∉ [["Pkg", "Token"]]; decide),
    (oneElab type _ qualified (.named (.tail (by decide) .head))).complete, ?_⟩
  simp [chain, statements, binding, elaborateTypedLetReturnBody?, interpretTypeName?, qualified, qualifiedTypeNameKey,
    TypeNameTable.lookup?, Syntax.NonemptyList.toList]

end Tests.FrontendTypedLetReturnBodyTypeExtension
