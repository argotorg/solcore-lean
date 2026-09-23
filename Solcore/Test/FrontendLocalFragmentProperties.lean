import Solcore.Frontend.LocalFragmentProperties
import Solcore.Frontend.TypedLetReturnTreeProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluation
import Solcore.Core.LocalFragment
import Solcore.Core.FuelResumptionProperties

/-! Exact original-source witnesses supply membership; independent positional
paths retain values and costs, not identical suspended environments. -/
set_option autoImplicit false
namespace Tests.FrontendLocalFragment
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LocalFragment", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "local-fragment.sol"⟩, 17, 9⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def chain : Bool → List String → String → Syntax.Block
  | _, [], previous => returned previous
  | annotated, name :: rest, previous =>
      ⟨span, ⟨span, .letDecl ⟨span, name⟩ (if annotated then some annotation else none)
        (some (ref previous))⟩ :: (chain (!annotated) rest name).value⟩
private def core : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var index) (core n 0)
private def seed (type : Core.Ty) := LocalTypeInputs.empty.bindFresh owner "seed" type
private theorem chain_eta (flag : Bool) (names : List String) (previous : String) :
    (⟨span, (chain flag names previous).value⟩ : Syntax.Block) = chain flag names previous := by cases names <;> rfl
private theorem elaborated (flag : Bool) (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr) (index : Nat) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var index)) (typed : Resolved.HasType initial.context resolved type) :
    TypedLetReturnTreeElaborates (types type) owner initial (chain flag names previous) (core names.length index) type := by
  induction names generalizing flag previous initial resolved index with
  | nil =>
      simp only [chain, List.length_nil, core]
      exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typed)
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      have tail := ih (!flag) name (initial.bindFresh owner name type) _ 0 parts.2 (by
        intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩)
        (.identifier .head) (.var .head) (.var .head)
      cases flag
      · exact .inferred (fresh name (by simp)) resolution lowered typed (by simpa only [chain_eta] using tail)
      · exact .binding (.named .head) (fresh name (by simp)) resolution lowered typed (by simpa only [chain_eta] using tail)
private theorem seedElab (flag : Bool) (names : List String) (type : Core.Ty)
    (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (chain flag names "seed") (core names.length 0) type := by
  apply elaborated flag names "seed" type (seed type) _ 0 distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head
private theorem path (n index : Nat) (values : Core.Environment) (value : Core.Value)
    (found : values[index]? = some value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*n+1) ⟨.eval (core n index) values, k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing index values k with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      have steps := Core.Steps.cons .enterLet (.cons (.var found) (.cons .bindLet (ih 0 (value :: values) rfl k)))
      simpa [core, Nat.mul_add, Nat.add_assoc] using steps
private theorem typedCore (n index : Nat) (context : Core.Context) (type : Core.Ty)
    (found : context[index]? = some type) (definitions : Core.DataEnvironment) :
    Core.HasType context (core n index) type definitions := by
  induction n generalizing index context with
  | zero => exact .var found
  | succ n ih => exact .letE (.var found) (ih 0 (type :: context) rfl)

theorem original_mixed_lists_determine_fragment_membership
    (flag : Bool) (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (chain flag names "seed") (core names.length 0) type ∧
    Core.Expr.LocalFragment (core names.length 0) ∧
    elaborateTypedLetReturnTree? (types type) owner (seed type) (chain flag names "seed") = some (core names.length 0, type) := by
  have original := seedElab flag names type distinct fresh
  exact ⟨original, original.localFragment, original.complete⟩

theorem expression_singleton_and_terminal_tree_keep_their_exact_children (type : Core.Ty) :
    Core.Expr.LocalFragment (.var 0) ∧ Core.Expr.LocalFragment (.ifE (.var 0) (.var 0) (.var 0)) ∧
    Core.Expr.LocalFragment .unit := by
  have leaf : ReturnBodyElaborates (seed type).names (seed type).context (returned "seed") (.var 0) type :=
    .expression (.identifier .head) (.var .head) (.var .head)
  have expression : elaborateLocalExpression? (seed type).names (seed type).context (ref "seed") = some (.var 0, type) :=
    leaf.complete
  have boolLeaf : ReturnBodyElaborates (seed .bool).names (seed .bool).context (returned "seed") (.var 0) .bool :=
    .expression (.identifier .head) (.var .head) (.var .head)
  have tree : TerminalReturnTreeElaborates (seed .bool).names (seed .bool).context
      ⟨span, [⟨span, .ifThen (ref "seed") (returned "seed") (some (returned "seed"))⟩]⟩
      (.ifE (.var 0) (.var 0) (.var 0)) .bool :=
    .conditional (.identifier .head) (.var .head) (.var .head) (.single boolLeaf) (.single boolLeaf)
  have bare : ReturnBodyElaborates (seed type).names (seed type).context
      ⟨span, [⟨span, .returnStmt none⟩]⟩ .unit .unit := .bare
  exact ⟨elaborateLocalExpression?_localFragment expression, tree.localFragment, bare.localFragment⟩

theorem nominal_static_transport_needs_no_runtime_inhabitant
    (nominal : Core.DataTypeId) (inserted : Core.Ty) (definitions : Core.DataEnvironment) :
    Core.HasType [inserted, .namedData nominal] ((core 2 0).weakenAt 0) (.namedData nominal) definitions ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  have fragment := (seedElab false ["x", "y"] (.namedData nominal) (by decide) (by decide)).localFragment
  refine ⟨(typedCore 2 0 [.namedData nominal] _ rfl definitions).weakenAt_zero_localFragment fragment inserted, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem retained_type_prefix_preserves_and_reflects_full_inference
    (flag : Bool) (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (leading suffix : Core.Context) (inserted result : Core.Ty) (definitions : Core.DataEnvironment) :
    (Core.HasType (leading ++ inserted :: suffix) ((core names.length 0).weakenAt leading.length) result definitions ↔
      Core.HasType (leading ++ suffix) (core names.length 0) result definitions) ∧
    Core.infer? (leading ++ inserted :: suffix) ((core names.length 0).weakenAt leading.length) definitions =
      Core.infer? (leading ++ suffix) (core names.length 0) definitions := by
  have fragment := (seedElab flag names type distinct fresh).localFragment
  exact ⟨fragment.hasType_insert_iff leading suffix inserted, fragment.infer_insert leading suffix inserted definitions⟩

theorem arbitrary_original_positions_transport_exact_paths_both_ways
    (flag : Bool) (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr) (index : Nat) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var index)) (typed : Resolved.HasType initial.context resolved type)
    (leading suffix : Core.Environment) (value inserted : Core.Value)
    (found : (leading ++ suffix)[index]? = some value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*names.length+1)
      ⟨.eval ((core names.length index).weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩ ⟨.ret value, k, store⟩ ∧
    Core.Steps (3*names.length+1) ⟨.eval (core names.length index) (leading ++ suffix), k, store⟩ ⟨.ret value, k, store⟩ := by
  have fragment := (elaborated flag names previous type initial resolved index distinct fresh resolution lowered typed).localFragment
  have original := path names.length index (leading ++ suffix) value found store []
  have shifted := fragment.steps_insert leading suffix inserted original []
  exact ⟨fragment.steps_insert leading suffix inserted original k, fragment.steps_reflect_insert leading suffix inserted shifted k⟩

theorem a_retained_row_really_shifts_the_original_initializer
    (type : Core.Ty) (value inserted : Core.Value) (choice : Bool) (store : Core.Store) (k : List Core.Frame) :
    TypedLetReturnTreeElaborates (types type) owner ((seed type).bindFresh owner "kept" .bool)
      (chain false ["copy"] "seed") (.letE (.var 1) (.var 0)) type ∧
    ((core 1 1).weakenAt 1) = .letE (.var 2) (.var 0) ∧
    Core.Steps 4 ⟨.eval (.letE (.var 2) (.var 0)) [.bool choice, inserted, value], k, store⟩ ⟨.ret value, k, store⟩ := by
  have original : TypedLetReturnTreeElaborates (types type) owner ((seed type).bindFresh owner "kept" .bool)
      (chain false ["copy"] "seed") (core 1 1) type := by
    apply elaborated false ["copy"] "seed" type _ _ 1 (by decide)
    · intro name member
      have same : name = "copy" := List.mem_singleton.mp member
      subst name
      change "copy" ∉ ["kept", "seed"]
      decide
    · exact .identifier (.tail (by change "kept" ≠ "seed"; decide) .head)
    · exact .var (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
    · exact .var (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
  have shifted := original.localFragment.steps_insert [.bool choice] [value] inserted
    (path 1 1 [.bool choice, value] value rfl store []) k
  exact ⟨original, by simp [core, Core.Expr.weakenAt], by simpa [core, Core.Expr.weakenAt] using shifted⟩

theorem insertion_keeps_arbitrary_final_store_iff_without_asserting_evaluation
    (flag : Bool) (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (leading suffix : Core.Environment) (inserted value : Core.Value) (initialStore finalStore : Core.Store) (cost : Nat) :
    (Core.Evaluates (leading ++ inserted :: suffix) initialStore ((core names.length 0).weakenAt leading.length) value finalStore ↔
      Core.Evaluates (leading ++ suffix) initialStore (core names.length 0) value finalStore) ∧
    (Core.Steps cost (Core.State.initial ((core names.length 0).weakenAt leading.length) (leading ++ inserted :: suffix) initialStore)
      (Core.State.final value finalStore) ↔ Core.Steps cost (Core.State.initial (core names.length 0) (leading ++ suffix) initialStore)
      (Core.State.final value finalStore)) := by
  have fragment := (seedElab flag names type distinct fresh).localFragment
  exact ⟨fragment.evaluates_insert_iff leading suffix inserted, fragment.steps_insert_iff leading suffix inserted⟩

theorem preexisting_cells_and_closures_are_not_created_or_inspected
    (location : Core.Location) (word : Core.Word) (inserted : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    Core.ValueHasType (.closure .bool .word (.var 1) [.word word]) (.function .bool .word) ∧
    Core.Steps 7 ⟨.eval ((core 2 0).weakenAt 0) [inserted, .cellRef .word location], k, store⟩ ⟨.ret (.cellRef .word location), k, store⟩ ∧
    Core.Steps 7 ⟨.eval ((core 2 0).weakenAt 0) [inserted, .closure .bool .word (.var 1) [.word word]], k, store⟩
      ⟨.ret (.closure .bool .word (.var 1) [.word word]), k, store⟩ := by
  have cellFragment := (seedElab false ["x", "y"] (.cell .word) (by decide) (by decide)).localFragment
  have closureFragment := (seedElab false ["x", "y"] (.function .bool .word) (by decide) (by decide)).localFragment
  exact ⟨.cellRef, .closure (.cons .word .nil) (.var rfl),
    (path 2 0 [_] _ rfl store []).weakenAt_zero_localFragment cellFragment inserted k,
    (path 2 0 [_] _ rfl store []).weakenAt_zero_localFragment closureFragment inserted k⟩

private def checkpoint (value : Core.Value) (environment : Core.Environment) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (.var 0) environment], store⟩
theorem exact_cost_does_not_identify_suspended_environments
    (value inserted : Core.Value) (store : Core.Store) (additional : Nat) :
    Core.runStateful 2 (Core.State.initial (core 1 0) [value] store) = .outOfFuel (checkpoint value [value] store) ∧
    Core.runStateful 2 (Core.State.initial ((core 1 0).weakenAt 0) [inserted, value] store) =
      .outOfFuel (checkpoint value [inserted, value] store) ∧
    checkpoint value [value] store ≠ checkpoint value [inserted, value] store ∧
    Core.Steps 2 (checkpoint value [value] store) (Core.State.final value store) ∧
    Core.Steps 2 (checkpoint value [inserted, value] store) (Core.State.final value store) ∧
    Core.runStateful (2 + additional) (Core.State.initial ((core 1 0).weakenAt 0) [inserted, value] store) =
      Core.runStateful additional (checkpoint value [inserted, value] store) := by
  have exhausted : Core.runStateful 2 (Core.State.initial ((core 1 0).weakenAt 0) [inserted, value] store) =
      .outOfFuel (checkpoint value [inserted, value] store) := by simp only [core, Core.Expr.weakenAt]; rfl
  refine ⟨rfl, exhausted, ?_, .cons .bindLet (.cons (.var rfl) .refl), .cons .bindLet (.cons (.var rfl) .refl),
    (Core.runStateful_resume exhausted additional).symm⟩
  intro same
  have lengths := congrArg (fun state => state.continuation) same
  simp only [checkpoint, List.cons.injEq, Core.Frame.letBody.injEq] at lengths
  cases lengths.1.2.2

theorem retained_continuation_endpoints_need_not_be_completed_runs (store : Core.Store) :
    Core.Steps 4 ⟨.eval ((core 1 0).weakenAt 0) [.unit, .bool true], [.unaryApply .wordNot], store⟩
      ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot (.bool true)) ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ := by
  have fragment := (seedElab false ["x"] .bool (by decide) (by decide)).localFragment
  exact ⟨(path 1 0 [.bool true] _ rfl store []).weakenAt_zero_localFragment fragment .unit _, rfl⟩

theorem typing_and_membership_do_not_replace_exact_source_provenance (type : Core.Ty) (definitions : Core.DataEnvironment) :
    Core.HasType [type] (.var 0) type definitions ∧ Core.Expr.LocalFragment (.var 0) ∧
    ¬ TypedLetReturnTreeElaborates (types type) owner (seed type) (chain false ["x"] "seed") (.var 0) type ∧
    Core.HasType [type] (.first (.pair (.var 0) .unit)) type definitions ∧
    ¬ Core.Expr.LocalFragment (.first (.pair (.var 0) .unit)) := by
  refine ⟨.var rfl, .var, ?_, .first (.pair (.var rfl) .unit), fun impossible => by cases impossible⟩
  intro competing
  cases (competing.result_unique (seedElab false ["x"] type (by decide) (by decide))).1

private def skipped : Syntax.Block :=
  ⟨span, [⟨span, .ifThen (ref "seed") (returned "seed") (some (returned "missing"))⟩]⟩
theorem a_selected_raw_value_does_not_check_the_other_written_arm (type : Core.Ty) (store : Core.Store) :
    TypedLetReturnTreeEvaluates owner (seed type).names [(Resolved.freshLocalId owner [], .bool true)] store skipped (.bool true) store ∧
    elaborateTypedLetReturnTree? [] owner (seed type) skipped = none ∧
    Core.Expr.LocalFragment (.ifE (.var 0) (.var 0) (.var 99)) ∧
    Core.Evaluates [.bool true] store (.ifE (.var 0) (.var 0) (.var 99)) (.bool true) store ∧
    ¬ Core.Expr.LocalFragment (.ifE (.bool true) (.var 0) (.first (.pair (.var 0) .unit))) := by
  refine ⟨.ifTrue (.identifier .head .head) (.single (.expression (.identifier .head .head))), ?_,
    .ifE .var .var .var, .ifTrue (.var rfl) (.var rfl), ?_⟩
  case refine_2 =>
    intro fragment
    cases fragment with
    | ifE _ _ other => cases other
  apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
  rintro ⟨_, typed⟩
  cases typed with
  | single child => cases child
  | conditional _ _ other =>
      cases other with
      | single child =>
          cases child with
          | expression child =>
              cases child with
              | identifier named _ =>
                  have impossible := LocalNameTable.lookup?_iff.mpr named
                  change none = some _ at impossible
                  cases impossible

theorem fragment_membership_does_not_make_indices_valid (index : Nat) (value : Core.Value) (store finalStore : Core.Store) :
    Core.Expr.LocalFragment (.var index) ∧ Core.infer? [] (.var index) = none ∧
    ¬ Core.Evaluates [] store (.var index) value finalStore := by
  refine ⟨.var, by cases index <;> rfl, ?_⟩
  intro evaluation
  cases evaluation with
  | var found => simp at found

end Tests.FrontendLocalFragment
