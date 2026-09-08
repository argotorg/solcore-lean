import Solcore.Frontend.TypedLetReturnTreeEmbeddingProperties
import Solcore.Frontend.TerminalReturnTreeEmbeddingProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties
import Solcore.Frontend.ConditionalReturnBodyEvaluation

/-! Arbitrary-depth static trees retain every original branch and positional
reference. The raw skip contrast below uses only the old conditional judgment. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalReturnTree

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ReturnTree", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "return-tree.sol"⟩, 61, 7⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (source : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt source⟩]⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block :=
  ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def names : LocalNameTable := [("y", id 2), ("x", id 1), ("c", id 0)]
private def context (type : Core.Ty) : Resolved.Context := [(id 2, type), (id 1, type), (id 0, .bool)]
private def x := returned (some (ref "x"))
private def y := returned (some (ref "y"))
private def bare := returned none
private theorem xTyped (type : Core.Ty) : LocalExpressionHasType names (context type) (ref "x") type :=
  .identifier (.tail (by decide) .head) (.tail (by decide) .head)
private theorem yTyped (type : Core.Ty) : LocalExpressionHasType names (context type) (ref "y") type := .identifier .head .head
private theorem guardTyped (type : Core.Ty) : LocalExpressionHasType names (context type) (ref "c") .bool :=
  .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem guardResolves : ResolvesLocalExpression names (ref "c") (.var (id 0)) :=
  .identifier (.tail (by decide) (.tail (by decide) .head))
private theorem guardLowers (type : Core.Ty) : Resolved.Lowers (Resolved.LocalScope.ids (context type)) (.var (id 0)) (.var 2) :=
  .var (.tail (by change id 2 ≠ id 0; decide) (.tail (by change id 1 ≠ id 0; decide) .head))
private theorem guardResolvedType (type : Core.Ty) : Resolved.HasType (context type) (.var (id 0)) .bool :=
  .var (.tail (by decide) (.tail (by decide) .head))
private theorem xElab (type : Core.Ty) : ReturnBodyElaborates names (context type) x (.var 1) type :=
  .expression (.identifier (.tail (by decide) .head)) (.var (.tail (by change id 2 ≠ id 1; decide) .head)) (.var (.tail (by decide) .head))
private theorem yElab (type : Core.Ty) : ReturnBodyElaborates names (context type) y (.var 0) type :=
  .expression (.identifier .head) (.var .head) (.var .head)
private def spine : Nat → Syntax.Block → Syntax.Block → Syntax.Block
  | 0, first, _ => first
  | depth + 1, first, side => branch (ref "c") (spine depth first side) side
private def spineCore : Nat → Core.Expr → Core.Expr → Core.Expr
  | 0, first, _ => first
  | depth + 1, first, side => .ifE (.var 2) (spineCore depth first side) side
private theorem spineTyped (depth : Nat) (payload result : Core.Ty) {first side : Syntax.Block}
    (firstTyped : ReturnBodyHasType names (context payload) first result)
    (sideTyped : ReturnBodyHasType names (context payload) side result) :
    TerminalReturnTreeHasType names (context payload) (spine depth first side) result := by
  induction depth with
  | zero => exact .single firstTyped
  | succ depth ih => exact .conditional (guardTyped payload) ih (.single sideTyped)
private theorem spineElab (depth : Nat) (payload result : Core.Ty) {first side : Syntax.Block} {firstCore sideCore : Core.Expr}
    (firstElab : ReturnBodyElaborates names (context payload) first firstCore result)
    (sideElab : ReturnBodyElaborates names (context payload) side sideCore result) :
    TerminalReturnTreeElaborates names (context payload) (spine depth first side) (spineCore depth firstCore sideCore) result := by
  induction depth with
  | zero => exact .single firstElab
  | succ depth ih => exact .conditional guardResolves (guardLowers payload) (guardResolvedType payload) ih (.single sideElab)

theorem arbitrary_depth_keeps_independent_typing_and_exact_unshifted_positions
    (depth : Nat) (type : Core.Ty) (definitions : Core.DataEnvironment) :
    TerminalReturnTreeHasType names (context type) (spine depth x y) type ∧
    TerminalReturnTreeElaborates names (context type) (spine depth x y) (spineCore depth (.var 1) (.var 0)) type ∧
    elaborateTerminalReturnTree? names (context type) (spine depth x y) = some (spineCore depth (.var 1) (.var 0), type) ∧
    Core.HasType [type, type, .bool] (spineCore depth (.var 1) (.var 0)) type definitions := by
  have exactTree := spineElab depth type type (xElab type) (yElab type)
  refine ⟨spineTyped depth type type (.expression (xTyped type)) (.expression (yTyped type)), exactTree, exactTree.complete, ?_⟩
  clear exactTree
  induction depth with
  | zero => exact .var rfl
  | succ depth ih => exact .ifE (.var rfl) ih (.var rfl)

theorem bare_unit_leaves_are_not_replaced_by_unit_typed_variable_leaves (depth : Nat) :
    TerminalReturnTreeHasType names (context .unit) (spine depth bare x) .unit ∧
    elaborateTerminalReturnTree? names (context .unit) (spine depth bare x) = some (spineCore depth .unit (.var 1), .unit) :=
  ⟨spineTyped depth .unit .unit .bare (.expression (xTyped .unit)), (spineElab depth .unit .unit .bare (xElab .unit)).complete⟩

theorem nominal_tree_checking_requires_no_runtime_inhabitant (depth : Nat) (dataType : Core.DataTypeId) :
    elaborateTerminalReturnTree? names (context (.namedData dataType)) (spine depth x y) =
      some (spineCore depth (.var 1) (.var 0), .namedData dataType) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData dataType) := by
  refine ⟨(spineElab depth _ _ (xElab _) (yElab _)).complete, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ =>
      simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def asymmetric := branch (ref "c") x (spine 2 x y)
private def asymmetricCore : Core.Expr := .ifE (.var 2) (.var 1) (.ifE (.var 2) (.ifE (.var 2) (.var 1) (.var 0)) (.var 0))
private theorem asymmetricElab (type : Core.Ty) : TerminalReturnTreeElaborates names (context type) asymmetric asymmetricCore type :=
  .conditional guardResolves (guardLowers type) (guardResolvedType type) (.single (xElab type)) (spineElab 2 type type (xElab type) (yElab type))
theorem asymmetric_child_inversion_retains_both_original_ordered_subtrees (type : Core.Ty) :
    elaborateTerminalReturnTree? names (context type) asymmetric = some (asymmetricCore, type) ∧
    ∃ conditionCore thenCore elseCore,
      elaborateLocalExpression? names (context type) (ref "c") = some (conditionCore, .bool) ∧
      elaborateTerminalReturnTree? names (context type) x = some (thenCore, type) ∧
      elaborateTerminalReturnTree? names (context type) (spine 2 x y) = some (elseCore, type) ∧
      asymmetricCore = .ifE conditionCore thenCore elseCore :=
  ⟨(asymmetricElab type).complete, elaborateTerminalReturnTree?_children (asymmetricElab type).complete⟩

theorem typing_and_a_same_typed_wrong_core_do_not_replace_exact_source_provenance (type : Core.Ty)
    {candidate : Core.Expr} {candidateType : Core.Ty}
    (accepted : elaborateTerminalReturnTree? names (context type) asymmetric = some (candidate, candidateType)) :
    candidate = asymmetricCore ∧ candidateType = type ∧ Core.HasType (context type).values candidate candidateType ∧
    Core.HasType (context type).values (.var 1) type ∧
    TerminalReturnTreeHasType names (context type) asymmetric candidateType ∧
    ¬ TerminalReturnTreeElaborates names (context type) asymmetric (.var 1) type := by
  have exact := elaborateTerminalReturnTree?_elaborates accepted
  have same := exact.result_unique (asymmetricElab type)
  refine ⟨same.1, same.2, elaborateTerminalReturnTree?_core_hasType accepted, .var rfl,
    elaborateTerminalReturnTree?_sound accepted, ?_⟩
  intro wrong
  have changed := (wrong.result_unique (asymmetricElab type)).1
  cases changed

theorem independent_source_typing_supplies_all_static_existence_interfaces (depth : Nat) (type : Core.Ty) :
    (∃ result, TerminalReturnTreeElaborates names (context type) (spine depth x y) result type) ∧
    (∃ result, elaborateTerminalReturnTree? names (context type) (spine depth x y) = some (result, type)) ∧
    (TerminalReturnTreeHasType names (context type) (spine depth x y) type ↔
      ∃ result, TerminalReturnTreeElaborates names (context type) (spine depth x y) result type) ∧
    (TerminalReturnTreeHasType names (context type) (spine depth x y) type ↔
      ∃ result, elaborateTerminalReturnTree? names (context type) (spine depth x y) = some (result, type)) := by
  have typing : TerminalReturnTreeHasType names (context type) (spine depth x y) type :=
    spineTyped depth type type (.expression (xTyped type)) (.expression (yTyped type))
  exact ⟨typing.elaborates_exact, typing.elaborates,
    terminalReturnTreeHasType_iff_elaborates_exact, terminalReturnTreeHasType_iff_elaborates⟩

private theorem oldConditional (type : Core.Ty) : ConditionalReturnBodyElaborates names (context type) (spine 1 x y)
    (.ifE (.var 2) (.var 1) (.var 0)) type :=
  .intro guardResolves (guardLowers type) (guardResolvedType type) (xElab type) (yElab type)
theorem all_three_old_profiles_embed_without_adding_or_replacing_core (type : Core.Ty) :
    TerminalReturnTreeHasType names (context type) x type ∧
    TerminalReturnTreeElaborates names (context type) x (.var 1) type ∧
    elaborateTerminalReturnTree? names (context type) x = some (.var 1, type) ∧
    TerminalReturnTreeHasType names (context type) (spine 1 x y) type ∧
    TerminalReturnTreeElaborates names (context type) (spine 1 x y) (.ifE (.var 2) (.var 1) (.var 0)) type ∧
    elaborateTerminalReturnTree? names (context type) (spine 1 x y) = some (.ifE (.var 2) (.var 1) (.var 0), type) ∧
    TerminalReturnTreeHasType names (context type) bare .unit ∧
    TerminalReturnTreeElaborates names (context type) bare .unit .unit ∧
    elaborateTerminalReturnTree? names (context type) bare = some (.unit, .unit) := by
  have terminal : TerminalReturnBodyElaborates names (context type) bare .unit .unit := .single .bare
  exact ⟨(xElab type).hasType.returnTree, (xElab type).returnTree, (xElab type).returnTree_complete,
    (oldConditional type).hasType.returnTree, (oldConditional type).returnTree, (oldConditional type).returnTree_complete,
    terminal.hasType.returnTree, terminal.returnTree, terminal.returnTree_complete⟩

theorem full_optional_agreement_is_retained_on_exact_old_shapes
    (table : LocalNameTable) (scope : Resolved.Context) (condition : Syntax.Expr) (first side : Option Syntax.Expr) :
    elaborateTerminalReturnTree? table scope (returned first) = elaborateReturnBody? table scope (returned first) ∧
    elaborateTerminalReturnTree? table scope (returned first) = elaborateTerminalReturnBody? table scope (returned first) ∧
    elaborateTerminalReturnTree? table scope (branch condition (returned first) (returned side)) =
      elaborateConditionalReturnBody? table scope (branch condition (returned first) (returned side)) ∧
    elaborateTerminalReturnTree? table scope (branch condition (returned first) (returned side)) =
      elaborateTerminalReturnBody? table scope (branch condition (returned first) (returned side)) :=
  ⟨elaborateTerminalReturnTree?_single table scope first span span,
    elaborateTerminalReturnTree?_single_terminal table scope first span span,
    elaborateTerminalReturnTree?_conditional_singletons table scope condition first side span span span span span span,
    elaborateTerminalReturnTree?_conditional_singletons_terminal table scope condition first side span span span span span span⟩

theorem outer_spans_and_alternative_typing_leave_the_deep_core_and_type_fixed
    (depth : Nat) (type otherType : Core.Ty) (blockSpan ifSpan : Syntax.SourceSpan)
    (other : TerminalReturnTreeHasType names (context type) (spine (depth + 1) x y) otherType) :
    otherType = type ∧ elaborateTerminalReturnTree? names (context type)
      ⟨blockSpan, [⟨ifSpan, .ifThen (ref "c") (spine depth x y) (some y)⟩]⟩ =
        some (spineCore (depth + 1) (.var 1) (.var 0), type) := by
  have exact := spineElab (depth + 1) type type (xElab type) (yElab type)
  exact ⟨other.type_unique exact.hasType,
    (elaborateTerminalReturnTree?_spans names (context type) (ref "c") (spine depth x y) y blockSpan ifSpan span span).trans
      (elaborateTerminalReturnTree?_iff.mpr exact)⟩

private inductive Bad where | missing | guard | mismatch | statements
private def badBase : Bad → Syntax.Block
  | .missing => returned (some (ref "missing"))
  | .guard => branch (ref "x") bare bare
  | .mismatch => branch (ref "c") bare x
  | .statements => ⟨span, [⟨span, .returnStmt none⟩, ⟨span, .returnStmt none⟩]⟩
private def badSpine : Nat → Bad → Syntax.Block
  | 0, bad => badBase bad
  | depth + 1, bad => branch (ref "c") bare (badSpine depth bad)
private theorem badBaseUntyped (bad : Bad) : ¬ ∃ type, TerminalReturnTreeHasType names (context .word) (badBase bad) type := by
  rintro ⟨type, typing⟩
  cases bad
  · cases typing with
    | single child =>
      cases child with
      | expression expressionTyped =>
        obtain ⟨resolved, resolution, _⟩ := expressionTyped.resolves
        have checked := resolution.complete
        simp [resolveLocalExpression?, ref, names, LocalNameTable.lookup?] at checked
  · cases typing with
    | single child => cases child
    | conditional guard _ _ => cases guard.type_unique (xTyped .word)
  · cases typing with
    | single child => cases child
    | conditional _ thenTyped elseTyped =>
      cases thenTyped with
      | single child =>
        cases child
        cases elseTyped with
        | single child =>
          cases child with
          | expression expressionTyped => cases expressionTyped.type_unique (xTyped .word)
  · cases typing with | single child => cases child
private theorem badUntyped (depth : Nat) (bad : Bad) : ¬ ∃ type, TerminalReturnTreeHasType names (context .word) (badSpine depth bad) type := by
  induction depth with
  | zero => exact badBaseUntyped bad
  | succ depth ih =>
    rintro ⟨type, typing⟩
    cases typing with
    | single child => cases child
    | conditional _ _ elseTyped => exact ih ⟨type, elseTyped⟩

theorem every_deep_missing_guard_mismatch_and_extra_statement_failure_remains_rejected (depth : Nat) (bad : Bad) :
    elaborateTerminalReturnTree? names (context .word) (badSpine depth bad) = none ∧
    ¬ ∃ type, TerminalReturnTreeHasType names (context .word) (badSpine depth bad) type :=
  ⟨elaborateTerminalReturnTree?_eq_none_iff.mpr (badUntyped depth bad), badUntyped depth bad⟩

theorem the_old_raw_skipped_arm_judgment_does_not_certify_the_new_recursive_checker
    (depth : Nat) (bad : Bad) (store : Core.Store) :
    ConditionalReturnBodyEvaluates names [(id 2, .word .zero), (id 1, .word .zero), (id 0, .bool false)] store
      (branch (ref "c") (badSpine depth bad) bare) .unit store ∧
    elaborateTerminalReturnTree? names (context .word) (branch (ref "c") (badSpine depth bad) bare) = none := by
  refine ⟨.ifFalse (.identifier (.tail (by decide) (.tail (by decide) .head))
    (.tail (by decide) (.tail (by decide) .head))) .bare, ?_⟩
  apply elaborateTerminalReturnTree?_eq_none_iff.mpr
  rintro ⟨type, typing⟩
  cases typing with
  | single child => cases child
  | conditional _ thenTyped _ => exact badUntyped depth bad ⟨type, thenTyped⟩

theorem the_old_terminal_adapter_still_rejects_every_genuinely_deep_good_tree (depth : Nat) (type : Core.Ty) :
    elaborateTerminalReturnTree? names (context type) (spine (depth + 2) x y) =
      some (spineCore (depth + 2) (.var 1) (.var 0), type) ∧
    elaborateTerminalReturnBody? names (context type) (spine (depth + 2) x y) = none := by
  refine ⟨(spineElab _ type type (xElab type) (yElab type)).complete, ?_⟩
  have guardChecked : elaborateLocalExpression? names (context type) (ref "c") = some (.var 2, .bool) :=
    elaborateLocalExpression?_complete guardResolves (guardLowers type) (guardResolvedType type)
  simp [spine, branch, elaborateTerminalReturnBody?, elaborateConditionalReturnBody?, guardChecked, elaborateReturnBody?]

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Flag"], .bool)]
private def entry (depth : Nat) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "deep"⟩, none,
    ⟨span, [parameter "c" "Flag", parameter "x" "Payload", parameter "y" "Payload"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation "Payload"]⟩⟩, none⟩, spine (depth + 2) x y⟩⟩
private def inputs (type : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh owner "c" .bool).bindFresh owner "x" type).bindFresh owner "y" type
theorem a_valid_header_and_complete_parameters_compile_the_exact_deep_tree
    (depth : Nat) (type : Core.Ty) :
    RuntimeFunctionHeader (types type) (entry depth).value.signature type ∧
    RuntimeParametersDeclare (types type) owner (entry depth).value.signature.parameters.elements (inputs type) ∧
    compileRuntimeFunction? (types type) owner (entry depth) =
      some ⟨inputs type, spineCore (depth + 2) (.var 1) (.var 0), type⟩ := by
  have declared : RuntimeParametersDeclare (types type) owner (entry depth).value.signature.parameters.elements (inputs type) :=
    .cons (.named (.tail (by decide) .head)) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "x" ∉ ["c"]; decide) (.cons (.named .head) (by change "y" ∉ ["x", "c"]; decide) .nil))
  have compilation : RuntimeFunctionCompiles (types type) owner (entry depth)
      ⟨inputs type, spineCore (depth + 2) (.var 1) (.var 0), type⟩ :=
    ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, declared, TypedLetReturnBodyElaborates.returnTree <| .terminal (spineElab _ type type (xElab type) (yElab type))⟩
  exact ⟨compilation.header, declared, compilation.complete⟩

end Tests.FrontendTerminalReturnTree
