import Solcore.Frontend.TypedLetReturnTreeProperties
import Solcore.Frontend.TypedLetReturnTreeEmbeddingProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties
import Solcore.Core.Safety

/-! Independent finite let/if trees retain lexical scopes and exact Core.
All positive source derivations are constructed without checker premises. -/
set_option autoImplicit false
namespace Tests.FrontendTypedLetReturnTree
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTrees", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "typed-let-trees.sol"⟩, 17, 9⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Word"], .word), (["Flag"], .bool)]
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def bind (name : String) (initial : Syntax.Expr) (tail : Syntax.Block)
    (typeName : String := "Payload") : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some (annotation typeName)) (some initial)⟩ :: tail.value⟩
private def guard : Syntax.Expr := ⟨span, .binary ⟨span, .literal ⟨span, .decimal "0"⟩⟩
  ⟨span, .equal⟩ ⟨span, .literal ⟨span, .decimal "0"⟩⟩⟩
private def branch (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen guard yes (some no)⟩]⟩
private def guardCore : Core.Expr := .binary .wordEq (.word .zero) (.word .zero)
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private theorem guardAccepted (initial : LocalTypeInputs) :
    elaborateLocalExpression? initial.names initial.context guard = some (guardCore, .bool) :=
  elaborateLocalExpression?_complete (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning))
    (.binary .word .word) (.binary .word .word)
private def tree : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => bind name (ref previous) (branch (tree rest name) (returned name))
private def treeCore : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .letE (.var 0) (.ifE guardCore (treeCore count) (.var 0))
private def seed (type : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "seed" type

private theorem treeElaborated (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var 0))
    (typed : Resolved.HasType initial.context resolved type) :
    TypedLetReturnTreeElaborates (types type) owner initial (tree names previous) (treeCore names.length) type := by
  induction names generalizing previous initial resolved with
  | nil =>
      simp only [tree, List.length_nil, treeCore]
      exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typed)
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      simp only [tree, List.length_cons, treeCore, bind]
      apply TypedLetReturnTreeElaborates.binding (name := ⟨span, name⟩) (annotation := annotation "Payload")
        (.named .head) (fresh name (by simp)) resolution lowered typed
      apply TypedLetReturnTreeElaborates.conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning))
        (.binary .word .word) (.binary .word .word)
      · apply ih name (initial.bindFresh owner name type) _ parts.2
        · intro next member
          simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
          exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
        · exact .identifier .head
        · exact .var .head
        · exact .var .head
      · exact .single (.expression (.identifier .head) (.var .head) (.var .head))
private theorem seedTree (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (tree names "seed") (treeCore names.length) type := by
  apply treeElaborated names "seed" type (seed type) _ distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head
private theorem coreTyped (count : Nat) (type : Core.Ty) (context : Core.Context) (definitions : Core.DataEnvironment) :
    Core.HasType (type :: context) (treeCore count) type definitions := by
  induction count generalizing context with
  | zero => exact .var rfl
  | succ count ih => exact .letE (.var rfl) (.ifE (.binary .word .word) (ih (type :: context)) (.var rfl))

theorem arbitrary_alternating_depth_has_value_free_exact_provenance
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (definitions : Core.DataEnvironment) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (tree names "seed") (treeCore names.length) type ∧
    TypedLetReturnTreeHasType (types type) owner (seed type) (tree names "seed") type ∧
    elaborateTypedLetReturnTree? (types type) owner (seed type) (tree names "seed") = some (treeCore names.length, type) ∧
    Core.HasType [type] (treeCore names.length) type definitions :=
  ⟨seedTree names type distinct fresh, (seedTree names type distinct fresh).hasType,
    elaborateTypedLetReturnTree?_iff.mpr (seedTree names type distinct fresh), coreTyped _ type [] definitions⟩

theorem nominal_trees_do_not_supply_runtime_inhabitants
    (names : List String) (nominal : Core.DataTypeId) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    elaborateTypedLetReturnTree? (types (.namedData nominal)) owner (seed (.namedData nominal)) (tree names "seed") =
      some (treeCore names.length, .namedData nominal) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(seedTree names _ distinct fresh).complete, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem typing_and_success_fix_the_independent_core_and_type
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    {candidate : Core.Expr} {candidateType : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? (types type) owner (seed type) (tree names "seed") = some (candidate, candidateType)) :
    candidate = treeCore names.length ∧ candidateType = type ∧ Core.HasType [type] candidate candidateType ∧
    TypedLetReturnTreeHasType (types type) owner (seed type) (tree names "seed") candidateType ∧
    (∃ core, TypedLetReturnTreeElaborates (types type) owner (seed type) (tree names "seed") core type) ∧
    (∃ core, elaborateTypedLetReturnTree? (types type) owner (seed type) (tree names "seed") = some (core, type)) := by
  have exactTree := seedTree names type distinct fresh
  have same := (elaborateTypedLetReturnTree?_elaborates accepted).result_unique exactTree
  exact ⟨same.1, (elaborateTypedLetReturnTree?_sound accepted).type_unique exactTree.hasType,
    elaborateTypedLetReturnTree?_core_hasType accepted, elaborateTypedLetReturnTree?_sound accepted,
    (typedLetReturnTreeHasType_iff_elaborates_exact.mp exactTree.hasType),
    (typedLetReturnTreeHasType_iff_elaborates.mp exactTree.hasType)⟩

private def duplicateInputs : LocalTypeInputs := ⟨[⟨"seed", id 7, .word⟩, ⟨"seed", id 2, .bool⟩], by decide⟩
theorem initial_spellings_need_no_new_duplicate_free_premise :
    ¬ (duplicateInputs.names.map Prod.fst).Nodup ∧
    elaborateTypedLetReturnTree? (types .word) owner duplicateInputs (tree ["z"] "seed") = some (treeCore 1, .word) := by
  refine ⟨by decide, ?_⟩
  exact (treeElaborated ["z"] "seed" .word duplicateInputs (.var (id 7)) (by decide)
    (by intro name member; simp only [List.mem_singleton] at member; subst name; decide)
    (.identifier .head) (.var .head) (.var .head)).complete

private def inputs : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh owner "c" .bool).bindFresh owner "x" .word).bindFresh owner "y" .word
private def sub (left right : String) : Syntax.Expr := ⟨span, .binary (ref left) ⟨span, .subtract⟩ (ref right)⟩
private def sibling := branch (bind "z" (sub "x" "y") (returned "z")) (bind "z" (sub "y" "x") (returned "z"))
private def siblingCore : Core.Expr := .ifE guardCore
  (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))
private theorem xR : ResolvesLocalExpression inputs.names (ref "x") (.var (id 1)) := .identifier (.tail (by decide) .head)
private theorem xL : Resolved.Lowers inputs.ids (.var (id 1)) (.var 1) := .var (.tail (by decide) .head)
private theorem xT : Resolved.HasType inputs.context (.var (id 1)) .word := .var (.tail (by decide) .head)
private theorem siblingElaborated : TypedLetReturnTreeElaborates (types .word) owner inputs sibling siblingCore .word :=
  .conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (.binary .word .word) (.binary .word .word)
    (.binding (.named .head) (by decide) (.subtract xR (.identifier .head)) (.binary xL (.var .head)) (.binary xT (.var .head))
      (.single (.expression (.identifier .head) (.var .head) (.var .head))))
    (.binding (.named .head) (by decide) (.subtract (.identifier .head) xR) (.binary (.var .head) xL) (.binary (.var .head) xT)
      (.single (.expression (.identifier .head) (.var .head) (.var .head))))

theorem sibling_lexical_scopes_share_a_fresh_id_without_reordering_initializers :
    Resolved.freshLocalId owner inputs.ids = id 3 ∧
    (inputs.bindFresh owner "z" .word).ids = id 3 :: inputs.ids ∧
    (inputs.bindFresh owner "other" .bool).ids = (inputs.bindFresh owner "z" .word).ids ∧
    TypedLetReturnTreeElaborates (types .word) owner inputs sibling siblingCore .word ∧
    elaborateTypedLetReturnTree? (types .word) owner inputs sibling = some (siblingCore, .word) :=
  ⟨rfl, rfl, rfl, siblingElaborated, siblingElaborated.complete⟩

theorem same_typed_alternative_core_is_not_source_provenance (definitions : Core.DataEnvironment) :
    Core.HasType [.word, .word, .bool] (.var 1) .word definitions ∧
    ¬ TypedLetReturnTreeElaborates (types .word) owner inputs sibling (.var 1) .word := by
  refine ⟨.var rfl, ?_⟩
  intro wrong
  cases (wrong.result_unique siblingElaborated).1

private def parameter (name typeName : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (annotation typeName)⟩
private def declaration : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "sibling"⟩, none, ⟨span, [parameter "c" "Flag", parameter "x" "Payload", parameter "y" "Payload"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation "Payload"]⟩⟩, none⟩, sibling⟩⟩
theorem valid_header_and_parameters_compile_recursive_bodies_while_old_adapters_reject :
    RuntimeFunctionHeader (types .word) declaration.value.signature .word ∧
    RuntimeParametersDeclare (types .word) owner declaration.value.signature.parameters.elements inputs ∧
    elaborateTypedLetReturnTree? (types .word) owner inputs sibling = some (siblingCore, .word) ∧
    elaborateTerminalReturnTree? inputs.names inputs.context sibling = none ∧
    elaborateTypedLetReturnBody? (types .word) owner inputs sibling = none ∧
    compileRuntimeFunction? (types .word) owner declaration = some ⟨inputs, siblingCore, .word⟩ := by
  have header : RuntimeFunctionHeader (types .word) declaration.value.signature .word := ⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩
  have declared : RuntimeParametersDeclare (types .word) owner declaration.value.signature.parameters.elements inputs :=
    .cons (.named (.tail (by decide) (.tail (by decide) .head))) (by decide)
      (.cons (.named .head) (by decide) (.cons (.named .head) (by decide) .nil))
  have oldTree : elaborateTerminalReturnTree? inputs.names inputs.context sibling = none := by
    simp [sibling, branch, bind, elaborateTerminalReturnTree?, guardAccepted]
  have oldPrefix : elaborateTypedLetReturnBody? (types .word) owner inputs sibling = none := by
    simpa only [sibling, branch, elaborateTypedLetReturnBody?] using oldTree
  refine ⟨header, declared, siblingElaborated.complete, oldTree, oldPrefix, ?_⟩
  exact (show RuntimeFunctionCompiles (types .word) owner declaration ⟨inputs, siblingCore, .word⟩ from
    ⟨header, declared, siblingElaborated⟩).complete

private def badBodies : List Syntax.Block :=
  [bind "unused" (ref "x") (returned "x") "Missing",
    bind "unused" (ref "x") (returned "x") "Flag", bind "unused" (ref "missing") (returned "x"),
    bind "x" (ref "y") (returned "x"), bind "z" (ref "z") (returned "x"),
    branch (bind "z" (ref "x") (returned "z")) (returned "z")]
private theorem badRejected (body : Syntax.Block) (member : body ∈ badBodies) :
    elaborateTypedLetReturnTree? (types .word) owner inputs body = none := by
  have xAccepted : elaborateLocalExpression? inputs.names inputs.context (ref "x") = some (.var 1, .word) :=
    elaborateLocalExpression?_complete xR (by simpa only [LocalTypeInputs.context_ids] using xL) xT
  have missing (name : String) (absent : name ∉ ["y", "x", "c"]) :
      elaborateLocalExpression? inputs.names inputs.context (ref name) = none := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at absent
    simp [elaborateLocalExpression?, resolveLocalExpression?, ref, inputs, LocalTypeInputs.bindFresh,
      LocalTypeInputs.names, LocalTypeInputs.empty, LocalNameTable.lookup?,
      Ne.symm absent.1, Ne.symm absent.2.1, Ne.symm absent.2.2]
  have noMissing := missing "missing" (by decide)
  have noZ := missing "z" (by decide)
  have names : inputs.names.map Prod.fst = ["y", "x", "c"] := rfl
  have payload : interpretStructuralType? (types .word) (annotation "Payload") = some .word := by simp only [annotation, interpretStructuralType?_named_eq_typeName]; rfl
  have flag : interpretStructuralType? (types .word) (annotation "Flag") = some .bool := by simp only [annotation, interpretStructuralType?_named_eq_typeName]; rfl
  have unknown : interpretStructuralType? (types .word) (annotation "Missing") = none := by simp only [annotation, interpretStructuralType?_named_eq_typeName]; rfl
  simp only [badBodies, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [bind, elaborateTypedLetReturnTree?, names, unknown]
  · simp [bind, elaborateTypedLetReturnTree?, names, flag, xAccepted]
  · simp [bind, elaborateTypedLetReturnTree?, names, payload, noMissing]
  · simp [bind, elaborateTypedLetReturnTree?, names]
  · simp [bind, elaborateTypedLetReturnTree?, names, payload, noZ]
  · apply Option.eq_none_iff_forall_not_mem.mpr
    rintro ⟨core, type⟩ accepted
    obtain ⟨_, _, _, _, _, other, _⟩ := elaborateTypedLetReturnTree?_conditional_children accepted
    simp only [returned, elaborateTypedLetReturnTree?, elaborateReturnBody?, noZ, reduceCtorEq] at other
private def buried : Nat → Syntax.Block → Syntax.Block
  | 0, bad => bad
  | depth + 1, bad => branch (returned "x") (buried depth bad)
private theorem buriedUntyped (depth : Nat) (bad : Syntax.Block)
    (absent : ¬ ∃ type, TypedLetReturnTreeHasType (types .word) owner inputs bad type) :
    ¬ ∃ type, TypedLetReturnTreeHasType (types .word) owner inputs (buried depth bad) type := by
  induction depth with
  | zero => exact absent
  | succ depth ih =>
      rintro ⟨type, typing⟩
      cases typing with
      | single child => cases child
      | conditional _ _ other => exact ih ⟨_, other⟩
theorem unselected_unused_and_scope_invalid_children_remain_rejected_at_every_depth
    (depth : Nat) (bad : Syntax.Block) (member : bad ∈ badBodies) :
    elaborateTypedLetReturnTree? (types .word) owner inputs (buried depth bad) = none ∧
    ¬ ∃ type, TypedLetReturnTreeHasType (types .word) owner inputs (buried depth bad) type := by
  have absent := buriedUntyped depth bad (elaborateTypedLetReturnTree?_eq_none_iff.mp (badRejected bad member))
  exact ⟨elaborateTypedLetReturnTree?_eq_none_iff.mpr absent, absent⟩

theorem old_successes_embed_without_equating_arbitrary_new_optional_results (type : Core.Ty) :
    TypedLetReturnTreeHasType (types type) owner (seed type) (returned "seed") type ∧
    TypedLetReturnTreeElaborates (types type) owner (seed type) (returned "seed") (.var 0) type ∧
    elaborateTypedLetReturnTree? (types type) owner (seed type) (returned "seed") = some (.var 0, type) ∧
    TypedLetReturnTreeHasType (types type) owner (seed type) (bind "z" (ref "seed") (returned "z")) type ∧
    TypedLetReturnTreeElaborates (types type) owner (seed type) (bind "z" (ref "seed") (returned "z")) (.letE (.var 0) (.var 0)) type ∧
    elaborateTypedLetReturnTree? (types type) owner (seed type) (bind "z" (ref "seed") (returned "z")) = some (.letE (.var 0) (.var 0), type) := by
  have oldTree : TerminalReturnTreeElaborates (seed type).names (seed type).context (returned "seed") (.var 0) type :=
    .single (.expression (.identifier .head) (.var .head) (.var .head))
  have oldPrefix : TypedLetReturnBodyElaborates (types type) owner (seed type)
      (bind "z" (ref "seed") (returned "z")) (.letE (.var 0) (.var 0)) type :=
    .binding (.named .head) (by change "z" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))
  exact ⟨oldTree.hasType.typedLetReturnTree _ _, oldTree.typedLetReturnTree _ _,
    elaborateTypedLetReturnTree?_some_of_terminalReturnTree _ _ oldTree.complete,
    oldPrefix.hasType.returnTree, oldPrefix.returnTree, elaborateTypedLetReturnTree?_some_of_typedLetReturnBody oldPrefix.complete⟩

theorem first_binding_decomposition_retains_old_scope_and_the_extended_tail (type : Core.Ty) :
    ∃ initializerCore tailCore,
      elaborateLocalExpression? (seed type).names (seed type).context (ref "seed") = some (initializerCore, type) ∧
      elaborateTypedLetReturnTree? (types type) owner ((seed type).bindFresh owner "z" type)
        (branch (returned "z") (returned "z")) = some (tailCore, type) ∧ treeCore 1 = .letE initializerCore tailCore := by
  obtain ⟨declaredType, initializerCore, tailCore, _, meaning, initial, tailAccepted, shape⟩ :=
    elaborateTypedLetReturnTree?_binding_children (seedTree ["z"] type (by decide) (by decide)).complete
  have originalMeaning : interpretTypeName? (types type) (annotation "Payload") = some declaredType := by
    simpa only [annotation, interpretStructuralType?_named_eq_typeName] using meaning
  have same : type = declaredType := by
    change some type = some declaredType at originalMeaning
    exact Option.some.inj originalMeaning
  subst declaredType
  exact ⟨initializerCore, tailCore, initial, tailAccepted, shape⟩

private def qualified : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, "Pkg"⟩, [⟨span, "Token"⟩]⟩⟩⟩ none⟩
private def qualifiedBody : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, "z"⟩ (some qualified) (some (ref "seed"))⟩ :: (returned "z").value⟩
theorem qualified_components_keep_their_meaning_and_do_not_flatten (type : Core.Ty) :
    TypedLetReturnTreeElaborates [(["Pkg", "Token"], type)] owner (seed type) qualifiedBody (.letE (.var 0) (.var 0)) type ∧
    elaborateTypedLetReturnTree? [(["Pkg", "Token"], type)] owner (seed type) qualifiedBody = some (.letE (.var 0) (.var 0), type) ∧
    elaborateTypedLetReturnTree? [(["Pkg.Token"], type)] owner (seed type) qualifiedBody = none := by
  have elaboration : TypedLetReturnTreeElaborates [(["Pkg", "Token"], type)] owner (seed type)
      qualifiedBody (.letE (.var 0) (.var 0)) type :=
    .binding (.named .head) (by change "z" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
  refine ⟨elaboration, elaboration.complete, ?_⟩
  have unused : "z" ∉ (seed type).names.map Prod.fst := by change "z" ∉ ["seed"]; decide
  have missing : interpretStructuralType? [(["Pkg.Token"], type)] qualified = none := by simp only [qualified, interpretStructuralType?_named_eq_typeName]; rfl
  simp only [qualifiedBody, elaborateTypedLetReturnTree?, if_pos unused, missing]
  rfl

theorem singleton_option_and_bare_unit_are_unchanged (table : TypeNameTable) (initial : LocalTypeInputs)
    (expression : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) :
    elaborateTypedLetReturnTree? table owner initial ⟨blockSpan, [⟨returnSpan, .returnStmt expression⟩]⟩ =
      elaborateReturnBody? initial.names initial.context ⟨blockSpan, [⟨returnSpan, .returnStmt expression⟩]⟩ ∧
    TypedLetReturnTreeElaborates table owner initial ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit .unit :=
  ⟨elaborateTypedLetReturnTree?_single table owner initial expression blockSpan returnSpan, .single .bare⟩

end Tests.FrontendTypedLetReturnTree
