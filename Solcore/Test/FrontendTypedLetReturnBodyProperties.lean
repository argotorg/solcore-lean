import Solcore.Frontend.TypedLetReturnBodyProperties
import Solcore.Frontend.TypedLetReturnTreeEmbeddingProperties
import Solcore.Frontend.TypedLetReturnBodyEmbeddingProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties
import Solcore.Core.Safety

/-! Independent, value-free let chains preserve original initializer scopes and
already shifted tails. Negative results describe only this restricted adapter. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBody

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TypedPrefix", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "typed-prefix.sol"⟩, 133, 11⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Payload"], .word), (["Word"], .word)]
private def inputs (type : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "seed" type
private def returned (name : String) : Syntax.Statement := ⟨span, .returnStmt (some (ref name))⟩
private def binding (name previous : String) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some (annotation "Payload")) (some (ref previous))⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => [returned previous]
  | name :: rest, previous => binding name previous :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def core : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .letE (.var 0) (core count)

private theorem chainElaborated (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var 0))
    (typed : Resolved.HasType initial.context resolved type) :
    TypedLetReturnBodyElaborates (types type) owner initial (chain names previous) (core names.length) type := by
  induction names generalizing previous initial resolved with
  | nil =>
      simp only [chain, statements, List.length_nil, core]
      exact .terminal (.single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typed))
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      simp only [chain, statements, List.length_cons, core]
      apply TypedLetReturnBodyElaborates.binding (name := ⟨span, name⟩) (annotation := annotation "Payload")
        (.named .head) (fresh name (by simp)) resolution lowered typed
      apply ih name (initial.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head

private theorem seedChain (names : List String) (type : Core.Ty)
    (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnBodyElaborates (types type) owner (inputs type) (chain names "seed") (core names.length) type := by
  apply chainElaborated names "seed" type (inputs type) _ distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head

private theorem coreTyped (count : Nat) (type : Core.Ty) (context : Core.Context) (definitions : Core.DataEnvironment) :
    Core.HasType (type :: context) (core count) type definitions := by
  induction count generalizing context with
  | zero => exact .var rfl
  | succ count ih => exact .letE (.var rfl) (ih (type :: context))

theorem arbitrary_length_and_type_chains_have_independent_exact_source_provenance
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (definitions : Core.DataEnvironment) :
    TypedLetReturnBodyElaborates (types type) owner (inputs type) (chain names "seed") (core names.length) type ∧
    TypedLetReturnBodyHasType (types type) owner (inputs type) (chain names "seed") type ∧
    elaborateTypedLetReturnBody? (types type) owner (inputs type) (chain names "seed") = some (core names.length, type) ∧
    Core.HasType [type] (core names.length) type definitions ∧ (chain names "seed").value.length = names.length + 1 := by
  have exact := seedChain names type distinct fresh
  refine ⟨exact, exact.hasType, elaborateTypedLetReturnBody?_iff.mpr exact, coreTyped _ type [] definitions, ?_⟩
  clear exact distinct fresh
  suffices ∀ previous, (statements names previous).length = names.length + 1 from this "seed"
  induction names with
  | nil => intro previous; rfl
  | cons name rest ih => intro previous; simp only [statements, List.length_cons, ih]

theorem nominal_let_chains_do_not_require_or_create_runtime_inhabitants
    (names : List String) (nominal : Core.DataTypeId) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    elaborateTypedLetReturnBody? (types (.namedData nominal)) owner (inputs (.namedData nominal)) (chain names "seed") =
      some (core names.length, .namedData nominal) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(seedChain names _ distinct fresh).complete, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem all_static_interfaces_retain_the_exact_independently_derived_result
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    {candidate : Core.Expr} {candidateType : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? (types type) owner (inputs type) (chain names "seed") = some (candidate, candidateType)) :
    candidate = core names.length ∧ candidateType = type ∧ Core.HasType [type] candidate candidateType ∧
    TypedLetReturnBodyHasType (types type) owner (inputs type) (chain names "seed") candidateType ∧
    (∃ other, TypedLetReturnBodyElaborates (types type) owner (inputs type) (chain names "seed") other type) ∧
    (∃ other, elaborateTypedLetReturnBody? (types type) owner (inputs type) (chain names "seed") = some (other, type)) := by
  have exact := seedChain names type distinct fresh
  have reflected := elaborateTypedLetReturnBody?_elaborates accepted
  have same := reflected.result_unique exact
  refine ⟨same.1, same.2, elaborateTypedLetReturnBody?_core_hasType accepted,
    elaborateTypedLetReturnBody?_sound accepted, ?_, ?_⟩
  · exact (typedLetReturnBodyHasType_iff_elaborates_exact.mp exact.hasType)
  · exact (typedLetReturnBodyHasType_iff_elaborates.mp exact.hasType)

private def twoBody (blockSpan firstSpan secondSpan returnSpan : Syntax.SourceSpan) : Syntax.Block := ⟨blockSpan,
  [⟨firstSpan, (binding "x" "seed").value⟩, ⟨secondSpan, (binding "y" "x").value⟩, ⟨returnSpan, (returned "x").value⟩]⟩
private def twoCore : Core.Expr := .letE (.var 0) (.letE (.var 0) (.var 1))
private theorem twoTail (type : Core.Ty) (blockSpan secondSpan returnSpan : Syntax.SourceSpan) :
    TypedLetReturnBodyElaborates (types type) owner ((inputs type).bindFresh owner "x" type)
      ⟨blockSpan, [⟨secondSpan, (binding "y" "x").value⟩, ⟨returnSpan, (returned "x").value⟩]⟩
      (.letE (.var 0) (.var 1)) type :=
  .binding (.named .head) (by change "y" ∉ ["x", "seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (.terminal (.single (.expression (.identifier (.tail (by change "y" ≠ "x"; decide) .head))
      (.var (.tail (by change id 2 ≠ id 1; decide) .head)) (.var (.tail (by change id 2 ≠ id 1; decide) .head)))))
private theorem twoElaborated (type : Core.Ty) (blockSpan firstSpan secondSpan returnSpan : Syntax.SourceSpan) :
    TypedLetReturnBodyElaborates (types type) owner (inputs type)
      (twoBody blockSpan firstSpan secondSpan returnSpan) twoCore type :=
  .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (twoTail type blockSpan secondSpan returnSpan)

theorem written_let_spans_and_old_scope_positions_do_not_add_a_second_weakening
    (type : Core.Ty) (blockSpan firstSpan secondSpan returnSpan : Syntax.SourceSpan) :
    (twoBody blockSpan firstSpan secondSpan returnSpan).span = blockSpan ∧
    (twoBody blockSpan firstSpan secondSpan returnSpan).value.map (·.span) = [firstSpan, secondSpan, returnSpan] ∧
    elaborateTypedLetReturnBody? (types type) owner (inputs type) (twoBody blockSpan firstSpan secondSpan returnSpan) = some (twoCore, type) ∧
    elaborateLocalExpression? (inputs type).names (inputs type).context (ref "seed") = some (.var 0, type) ∧
    elaborateLocalExpression? ((inputs type).bindFresh owner "x" type).names
      ((inputs type).bindFresh owner "x" type).context (ref "x") = some (.var 0, type) :=
  ⟨rfl, rfl, (twoElaborated type blockSpan firstSpan secondSpan returnSpan).complete,
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head),
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)⟩

theorem successful_children_recover_the_original_initializer_and_exact_remaining_source (type : Core.Ty) :
    ∃ declaredType initializerCore tailCore,
      "x" ∉ (inputs type).names.map Prod.fst ∧ interpretTypeName? (types type) (annotation "Payload") = some declaredType ∧
      elaborateLocalExpression? (inputs type).names (inputs type).context (ref "seed") = some (initializerCore, declaredType) ∧
      elaborateTypedLetReturnBody? (types type) owner ((inputs type).bindFresh owner "x" declaredType)
        ⟨span, [binding "y" "x", returned "x"]⟩ = some (tailCore, type) ∧ twoCore = .letE initializerCore tailCore :=
  elaborateTypedLetReturnBody?_binding_children (twoElaborated type span span span span).complete

theorem a_same_typed_wrong_tail_does_not_supply_exact_source_provenance (type : Core.Ty) :
    Core.HasType [type] (.letE (.var 0) (.letE (.var 0) (.var 0))) type ∧
    ¬ TypedLetReturnBodyElaborates (types type) owner (inputs type) (twoBody span span span span)
      (.letE (.var 0) (.letE (.var 0) (.var 0))) type := by
  refine ⟨.letE (.var rfl) (.letE (.var rfl) (.var rfl)), ?_⟩
  intro wrong
  have same := (wrong.result_unique (twoElaborated type span span span span)).1
  cases same

private inductive Bad where
  | noAnnotation | noInitializer | unknownAnnotation | mismatchedInitializer | missingUnused | selfReference
  | forwardReference | existingName | duplicateName | invalidArm | branchPrefix | extraReturn | blockWrapper
private def badBody : Bad → Syntax.Block
  | .noAnnotation => ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ none (some (ref "seed"))⟩, returned "seed"]⟩
  | .noInitializer => ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some (annotation "Payload")) none⟩, returned "seed"]⟩
  | .unknownAnnotation => ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some (annotation "Unknown")) (some (ref "seed"))⟩, returned "seed"]⟩
  | .mismatchedInitializer => ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some (annotation "Word")) (some (ref "seed"))⟩, returned "seed"]⟩
  | .missingUnused => ⟨span, [binding "x" "missing", returned "seed"]⟩
  | .selfReference => ⟨span, [binding "x" "x", returned "seed"]⟩
  | .forwardReference => ⟨span, [binding "x" "y", binding "y" "seed", returned "seed"]⟩
  | .existingName => ⟨span, [binding "seed" "seed", returned "seed"]⟩
  | .duplicateName => ⟨span, [binding "x" "seed", binding "x" "seed", returned "seed"]⟩
  | .invalidArm => ⟨span, [binding "x" "seed", ⟨span, .ifThen (ref "seed") ⟨span, [returned "seed"]⟩ (some ⟨span, [returned "missing"]⟩)⟩]⟩
  | .branchPrefix => ⟨span, [⟨span, .ifThen (ref "seed") (chain ["x"] "seed") (some ⟨span, [returned "seed"]⟩)⟩]⟩
  | .extraReturn => ⟨span, [binding "x" "seed", returned "x", returned "seed"]⟩
  | .blockWrapper => ⟨span, [⟨span, .block (chain ["x"] "seed").value⟩]⟩

theorem omitted_parts_name_capture_unused_failures_and_outside_shapes_are_adapter_failures (bad : Bad) :
    elaborateTypedLetReturnBody? (types .bool) owner (inputs .bool) (badBody bad) = none ∧
    ¬ ∃ type, TypedLetReturnBodyHasType (types .bool) owner (inputs .bool) (badBody bad) type := by
  have rejected : elaborateTypedLetReturnBody? (types .bool) owner (inputs .bool) (badBody bad) = none := by
    have seedAccepted : elaborateLocalExpression? (inputs .bool).names (inputs .bool).context (ref "seed") = some (.var 0, .bool) :=
      elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
    cases bad <;> simp [badBody, chain, statements, binding, returned, elaborateTypedLetReturnBody?,
      elaborateTerminalReturnTree?, elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?,
      ref, inputs, types, annotation, interpretTypeName?, qualifiedTypeNameKey, TypeNameTable.lookup?,
      Syntax.NonemptyList.toList, LocalTypeInputs.bindFresh, LocalTypeInputs.names, LocalTypeInputs.empty, LocalNameTable.lookup?]
    intro initializerCore initializerType accepted same
    simp [elaborateLocalExpression?, resolveLocalExpression?, ref, inputs, LocalTypeInputs.bindFresh,
      LocalTypeInputs.names, LocalTypeInputs.empty, LocalNameTable.lookup?] at seedAccepted
    rw [seedAccepted] at accepted
    cases accepted
    cases same
  exact ⟨rejected, elaborateTypedLetReturnBody?_eq_none_iff.mp rejected⟩

private def parameter : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, "seed"⟩ (annotation "Payload")⟩
private def declaration : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "prefix"⟩, none, ⟨span, [parameter]⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation "Payload"]⟩⟩, none⟩, twoBody span span span span⟩⟩

theorem valid_header_and_parameter_compile_the_exact_prefix_while_the_tree_adapter_still_rejects (type : Core.Ty) :
    RuntimeFunctionHeader (types type) declaration.value.signature type ∧
    RuntimeParametersDeclare (types type) owner [parameter] (inputs type) ∧
    elaborateTypedLetReturnBody? (types type) owner (inputs type) declaration.value.body = some (twoCore, type) ∧
    elaborateTerminalReturnTree? (inputs type).names (inputs type).context declaration.value.body = none ∧
    compileRuntimeFunction? (types type) owner declaration = some ⟨inputs type, twoCore, type⟩ := by
  refine ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    (twoElaborated type span span span span).complete,
    by simp [declaration, twoBody, binding, elaborateTerminalReturnTree?], ?_⟩
  have compiled : RuntimeFunctionCompiles (types type) owner declaration ⟨inputs type, twoCore, type⟩ :=
    ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
      .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
      (twoElaborated type span span span span).returnTree⟩
  exact compiled.complete

private def otherId : Resolved.LocalId := ⟨{ owner with declarationIndex := 1 }, 999⟩
private def sparse (type : Core.Ty) : LocalTypeInputs := ⟨
  [⟨"seed", id 7, type⟩, ⟨"old", id 2, type⟩, ⟨"other", otherId, .bool⟩],
  by change [id 7, id 2, otherId].Nodup; decide⟩

theorem sparse_same_owner_and_large_unrelated_ids_do_not_turn_freshness_into_row_count (type : Core.Ty) :
    (sparse type).ids.length = 3 ∧ Resolved.freshLocalId owner (sparse type).ids = id 8 ∧
    ((sparse type).bindFresh owner "x" type).ids = [id 8, id 7, id 2, otherId] ∧
    elaborateTypedLetReturnBody? (types type) owner (sparse type) (chain ["x"] "seed") =
      some (.letE (.var 0) (.var 0), type) := by
  refine ⟨rfl, by rfl, rfl, ?_⟩
  apply TypedLetReturnBodyElaborates.complete
  apply chainElaborated ["x"] "seed" type (sparse type) _ (by decide)
  · intro name member
    have same : name = "x" := List.mem_singleton.mp member
    subst name
    change "x" ∉ ["seed", "old", "other"]
    decide
  · exact .identifier .head
  · exact .var .head
  · exact .var .head

theorem existing_terminal_provenance_embeds_without_any_type_or_value_invention
    (initial : LocalTypeInputs) (table : TypeNameTable) (body : Syntax.Block) (result : Core.Ty) (expression : Core.Expr)
    (tree : TerminalReturnTreeElaborates initial.names initial.context body expression result) :
    TypedLetReturnBodyHasType table owner initial body result ∧
    TypedLetReturnBodyElaborates table owner initial body expression result ∧
    elaborateTypedLetReturnBody? table owner initial body = some (expression, result) :=
  ⟨tree.hasType.typedLetReturnBody table owner, tree.typedLetReturnBody table owner,
    tree.typedLetReturnBody_complete table owner⟩

theorem old_return_and_conditional_shapes_keep_the_entire_optional_result
    (table : TypeNameTable) (initial : LocalTypeInputs) (value : Option Syntax.Expr)
    (condition : Syntax.Expr) (yes no : Syntax.Block) :
    elaborateTypedLetReturnBody? table owner initial ⟨span, [⟨span, .returnStmt value⟩]⟩ =
      elaborateReturnBody? initial.names initial.context ⟨span, [⟨span, .returnStmt value⟩]⟩ ∧
    elaborateTypedLetReturnBody? table owner initial ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ =
      elaborateTerminalReturnTree? initial.names initial.context ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ ∧
    elaborateTypedLetReturnBody? table owner initial
      ⟨span, [⟨span, .ifThen condition ⟨span, [⟨span, .returnStmt value⟩]⟩ (some ⟨span, [⟨span, .returnStmt none⟩]⟩)⟩]⟩ =
      elaborateConditionalReturnBody? initial.names initial.context
        ⟨span, [⟨span, .ifThen condition ⟨span, [⟨span, .returnStmt value⟩]⟩ (some ⟨span, [⟨span, .returnStmt none⟩]⟩)⟩]⟩ :=
  ⟨elaborateTypedLetReturnBody?_single table owner initial value span span,
    elaborateTypedLetReturnBody?_conditional table owner initial condition yes no span span,
    elaborateTypedLetReturnBody?_conditional_singletons table owner initial condition value none span span span span span span⟩

end Tests.FrontendTypedLetReturnBody
