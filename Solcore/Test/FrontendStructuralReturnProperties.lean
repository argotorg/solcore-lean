import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionCompilationTypeExtensionProperties
import Solcore.Frontend.TypedLetReturnBodyProperties

/-! Independent structural return contracts meet the existing entry only through
original parameter/body provenance. Static types do not supply runtime arguments. -/
set_option autoImplicit false
namespace Tests.FrontendStructuralReturn
open Solcore Solcore.Frontend
private def clause (s t : Syntax.SourceSpan) (annotations : List Syntax.TypeExpr) : Option Syntax.ReturnClause :=
  some ⟨s, ⟨t, annotations⟩⟩
private def signature (s : Syntax.SourceSpan) (returns : Option Syntax.ReturnClause)
    (parameters : List Syntax.FunctionParameter := []) : Syntax.FunctionSignature :=
  ⟨s, ⟨s, "structural"⟩, none, ⟨s, parameters⟩, ⟨none, none⟩, returns, none⟩

theorem independent_structural_headers_keep_arbitrary_ranges_and_unique_results
    (s t : Syntax.SourceSpan) (table : TypeNameTable) (annotation : Syntax.TypeExpr) (type : Core.Ty)
    (meaning : StructuralTypeDenotes table annotation type) :
    RuntimeReturnTypeDenotes table (clause s t [annotation]) type ∧
    RuntimeFunctionHeader table (signature s (clause s t [annotation])) type ∧
    interpretRuntimeFunctionHeader? table (signature s (clause s t [annotation])) = some type ∧
    (∀ other, RuntimeFunctionHeader table (signature s (clause s t [annotation])) other → other = type) := by
  have header : RuntimeFunctionHeader table (signature s (clause s t [annotation])) type :=
    ⟨rfl, rfl, rfl, rfl, .single meaning⟩
  exact ⟨.single meaning, header, interpretRuntimeFunctionHeader?_iff.mpr header, fun _ other => other.type_unique header⟩

theorem absent_and_single_empty_tuple_are_unit_but_multiple_return_annotations_stay_rejected
    (s t : Syntax.SourceSpan) (table : TypeNameTable) (left right third : Syntax.TypeExpr) :
    RuntimeReturnTypeDenotes table none .unit ∧
    RuntimeReturnTypeDenotes table (clause s t [⟨s, .tuple []⟩]) .unit ∧
    interpretRuntimeReturnType? table none = some .unit ∧
    interpretRuntimeReturnType? table (clause s t [⟨s, .tuple []⟩]) = some .unit ∧
    interpretRuntimeReturnType? table (clause s t []) = none ∧
    interpretRuntimeReturnType? table (clause s t [left, right]) = none ∧
    interpretRuntimeReturnType? table (clause s t [left, right, third]) = none := by
  refine ⟨.absent, .single .unit, rfl, ?_, rfl, rfl, ?_⟩ <;>
    simp [interpretRuntimeReturnType?, interpretStructuralType?, clause]

theorem old_named_return_evidence_still_enters_through_its_explicit_embedding
    (s t : Syntax.SourceSpan) (table : TypeNameTable) (annotation : Syntax.TypeExpr) (type : Core.Ty)
    (old : TypeNameDenotes table annotation type) :
    (∃ key, (key, type) ∈ table) ∧
    RuntimeReturnTypeDenotes table (clause s t [annotation]) type ∧
    RuntimeReturnTypeDenotes table (clause s t [⟨s, .tuple [annotation]⟩]) type :=
  ⟨old.mem, .single old.structural, .single (.single old.structural)⟩

private def span : Syntax.SourceSpan := ⟨⟨.main, "structural-return.sol"⟩, 233, 4⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"StructuralReturn", by decide⟩], by decide⟩⟩, 0⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def table (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def annotation : Nat → Syntax.TypeExpr
  | 0 => ⟨span, .tuple []⟩
  | n + 1 => ⟨span, .tuple [⟨span, .tuple [named "Payload"]⟩, annotation n]⟩
private def product (type : Core.Ty) : Nat → Core.Ty
  | 0 => .unit
  | n + 1 => .product type (product type n)
private def source : Nat → Syntax.Expr
  | 0 => ⟨span, .tuple ⟨span, []⟩⟩
  | n + 1 => ⟨span, .tuple ⟨span, [⟨span, .identifier ⟨span, "seed"⟩⟩, source n]⟩⟩
private def resolved (id : Resolved.LocalId) : Nat → Resolved.Expr
  | 0 => .unit
  | n + 1 => .pair (.var id) (resolved id n)
private def core : Nat → Core.Expr
  | 0 => .unit
  | n + 1 => .pair (.var 0) (core n)
private def value (actual : Core.Value) : Nat → Core.Value
  | 0 => .unit
  | n + 1 => .pair actual (value actual n)
private def parameter (type : Syntax.TypeExpr) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, "seed"⟩ type⟩
private def body (n : Nat) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (source n))⟩]⟩
private def entry (returnClause : Option Syntax.ReturnClause) (parameters : List Syntax.FunctionParameter) (body : Syntax.Block) : Syntax.FunctionDecl :=
  ⟨span, ⟨signature span returnClause parameters, body⟩⟩
private def declaration (n : Nat) := entry (clause span span [annotation n]) [parameter (named "Payload")] (body n)
private def initial (type : Core.Ty) := LocalTypeInputs.empty.bindFresh owner "seed" type
private def compiled (type : Core.Ty) (n : Nat) : CompiledRuntimeFunction := ⟨initial type, core n, product type n⟩
private theorem meaning (type : Core.Ty) (n : Nat) : StructuralTypeDenotes (table type) (annotation n) (product type n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.single (.named .head)) ih
private theorem header (type : Core.Ty) (n : Nat) : RuntimeFunctionHeader (table type) (declaration n).value.signature (product type n) :=
  ⟨rfl, rfl, rfl, rfl, .single (meaning type n)⟩
private theorem expression (type : Core.Ty) (n : Nat) :
    ResolvesLocalExpression (initial type).names (source n) (resolved (Resolved.freshLocalId owner []) n) ∧
    Resolved.Lowers (initial type).ids (resolved (Resolved.freshLocalId owner []) n) (core n) ∧
    Resolved.HasType (initial type).context (resolved (Resolved.freshLocalId owner []) n) (product type n) := by
  induction n with
  | zero => exact ⟨.unit, .unit, .unit⟩
  | succ n ih => exact ⟨.pair (.identifier .head) ih.1, .pair (.var .head) ih.2.1, .pair (.var .head) ih.2.2⟩
private theorem compilation (type : Core.Ty) (n : Nat) : RuntimeFunctionCompiles (table type) owner (declaration n) (compiled type n) :=
  ⟨header type n, .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    .single (.expression (expression type n).1 (expression type n).2.1 (expression type n).2.2)⟩
private abbrev Actual (type : Core.Ty) := { actual : Core.Value // Core.ValueHasType actual type }
private def arguments {type : Core.Ty} (actual : Actual type) : List TypedRuntimeArgument := [⟨type, actual.val, actual.property⟩]
private def inputs {type : Core.Ty} (actual : Actual type) := LocalInputs.empty.bindFresh owner "seed" type actual.val actual.property
private theorem preparation {type : Core.Ty} (actual : Actual type) (n : Nat) :
    RuntimeFunctionPrepares (table type) owner (declaration n) (arguments actual) ⟨inputs actual, core n, product type n⟩ :=
  ⟨header type n, .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil, (compilation type n).body⟩
private theorem raw (table : LocalNameTable) (environment : Resolved.Environment) (id : Resolved.LocalId)
    (actual : Core.Value) (store : Core.Store) (n : Nat) :
    LocalExpressionEvaluatesWithCost (("seed", id) :: table) ((id, actual) :: environment) store (source n) (value actual n) store (4 * n + 1) := by
  induction n with
  | zero => exact .unit
  | succ n ih =>
      have count : 4 * (n + 1) + 1 = 1 + (4 * n + 1) + 3 := by omega
      rw [count]; exact .pair (.identifier .head .head) ih
private theorem costed {type : Core.Ty} (actual : Actual type) (n : Nat) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table type) owner (declaration n) (arguments actual) store
      (product type n) (value actual.val n) store (4 * n + 1) :=
  .intro (preparation actual n) (.single (.expression (raw [] [] _ actual.val store n)))
private theorem path (actual : Core.Value) (store : Core.Store) (n : Nat) :
    ∀ k, Core.Steps (4 * n + 1) ⟨.eval (core n) [actual], k, store⟩ ⟨.ret (value actual n), k, store⟩ := by
  induction n with
  | zero => intro k; exact .cons .unit .refl
  | succ n ih =>
      intro k
      have steps := Core.Steps.cons .enterPair (.cons (.var (index := 0) rfl) (.cons .enterPairRight
        ((ih (.pairApply actual :: k)).trans (.cons .applyPair .refl))))
      simpa [core, value, Nat.mul_add, Nat.add_assoc] using steps

theorem arbitrary_nested_returns_compile_without_supplied_values (type : Core.Ty) (n : Nat) :
    RuntimeFunctionCompiles (table type) owner (declaration n) (compiled type n) ∧
    compileRuntimeFunction? (table type) owner (declaration n) = some (compiled type n) ∧
    (compiled type n).inputs.bindings.length = 1 ∧
    interpretTypeName? (table type) (annotation n) = none :=
  ⟨compilation type n, (compilation type n).complete, rfl, by cases n <;> rfl⟩

theorem actual_arguments_execute_the_original_body_at_its_independent_cost
    {type : Core.Ty} (actual : Actual type) (n fuel : Nat) (store : Core.Store) (k : List Core.Frame) :
    prepareRuntimeFunction? (table type) owner (declaration n) (arguments actual) = some ⟨inputs actual, core n, product type n⟩ ∧
    (inputs actual).environment.values = (arguments actual).reverse.map (·.value) ∧
    Core.Steps (4 * n + 1) ⟨.eval (core n) [actual.val], k, store⟩ ⟨.ret (value actual.val n), k, store⟩ ∧
    (runRuntimeFunction? (table type) owner (declaration n) (arguments actual) fuel store =
      some (product type n, .done (value actual.val n) store) ↔ 4 * n + 1 ≤ fuel) ∧
    ((∃ checkpoint, runRuntimeFunction? (table type) owner (declaration n) (arguments actual) fuel store =
      some (product type n, .outOfFuel checkpoint)) ↔ fuel < 4 * n + 1) :=
  ⟨(preparation actual n).complete, rfl, path actual.val store n k, (costed actual n store).run_done_iff, (costed actual n store).run_outOfFuel_iff⟩

theorem typed_products_preserve_the_entire_compiled_record_under_semantic_extension
    (type : Core.Ty) (n : Nat) (next : TypeNameTable) (extension : TypeNameTable.Extends (table type) next) :
    RuntimeFunctionCompiles next owner (declaration n) (compiled type n) ∧
    compileRuntimeFunction? next owner (declaration n) = some (compiled type n) :=
  ⟨(compilation type n).extend_types extension, compileRuntimeFunction?_some_of_extends extension (compilation type n).complete⟩

theorem nominal_returns_and_even_unused_nominal_parameters_do_not_supply_actual_values (nominal : Core.DataTypeId) :
    compileRuntimeFunction? (table (.namedData nominal)) owner (declaration 2) = some (compiled (.namedData nominal) 2) ∧
    compileRuntimeFunction? (table (.namedData nominal)) owner (declaration 0) = some (compiled (.namedData nominal) 0) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  refine ⟨(compilation _ _).complete, (compilation _ _).complete, ?_⟩
  rintro ⟨⟨type, actual, typed⟩, same⟩; cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem opaque_actual_values_form_products_without_allocation_or_invocation (location : Core.Location) (word : Core.Word) :
    evaluateRuntimeFunctionWithCost? (table (.cell .word)) owner (declaration 1)
      (arguments ⟨.cellRef .word location, .cellRef⟩) = some (.product (.cell .word) .unit, .pair (.cellRef .word location) .unit, 5) ∧
    evaluateRuntimeFunctionWithCost? (table (.function .bool .word)) owner (declaration 1)
      (arguments ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩) =
      some (.product (.function .bool .word) .unit, .pair (.closure .bool .word (.var 1) [.word word]) .unit, 5) :=
  ⟨(runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (costed _ 1 [])).2,
    (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (costed _ 1 [])).2⟩

theorem store_replay_preserves_results_but_not_a_different_final_store
    {type : Core.Ty} (actual : Actual type) (n : Nat) (initial final : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table type) owner (declaration n) (arguments actual) initial
      (product type n) (value actual.val n) final (4 * n + 1) ↔ final = initial := by
  have computed := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (costed actual n initial)).2
  rw [runtimeFunctionEvaluatesWithCost_iff_evaluate, computed]; simp

theorem genuine_pair_checkpoint_keeps_the_unit_tail_and_original_actual_argument
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? (table type) owner (declaration 1) (arguments actual) 4 store =
      some (.product type .unit, .outOfFuel ⟨.ret .unit, [.pairApply actual.val], store⟩) ∧
    Core.Steps 1 ⟨.ret .unit, [.pairApply actual.val], store⟩ (.final (.pair actual.val .unit) store) ∧
    runRuntimeFunction? (table type) owner (declaration 1) (arguments actual) (4 + additional) store =
      some (.product type .unit, Core.runStateful additional ⟨.ret .unit, [.pairApply actual.val], store⟩) ∧
    Core.runStateful 0 (.final .unit store) = .done .unit store := by
  have exhausted : runRuntimeFunction? (table type) owner (declaration 1) (arguments actual) 4 store =
      some (.product type .unit, .outOfFuel ⟨.ret .unit, [.pairApply actual.val], store⟩) := by
    rw [(compilation type 1).run_eq (arguments actual) rfl]; rfl
  exact ⟨exhausted, ((costed actual 1 store).residual_of_outOfFuel exhausted).2, runRuntimeFunction?_resume exhausted additional, rfl⟩

theorem same_typed_swapped_core_is_not_compilation :
    Core.HasType [.unit] (.pair .unit (.var 0)) (.product .unit .unit) ∧
    ¬ RuntimeFunctionCompiles (table .unit) owner (declaration 1) { compiled .unit 1 with core := .pair .unit (.var 0) } := by
  refine ⟨.pair .unit (.var rfl), ?_⟩
  intro forged
  have wrong := congrArg CompiledRuntimeFunction.core (forged.result_unique (compilation .unit 1))
  cases wrong

private def strictBody : Syntax.Block := ⟨span,
  [⟨span, .letDecl ⟨span, "unused"⟩ (some (named "Payload")) (some ⟨span, .identifier ⟨span, "seed"⟩⟩)⟩,
   ⟨span, .returnStmt (some (source 1))⟩]⟩
private def strictDeclaration := entry (clause span span [annotation 1]) [parameter (named "Payload")] strictBody
private def strictCore : Core.Expr := .letE (.var 0) (.pair (.var 1) .unit)
private theorem strictCompilation (type : Core.Ty) :
    RuntimeFunctionCompiles (table type) owner strictDeclaration ⟨initial type, strictCore, .product type .unit⟩ :=
  ⟨header type 1, (compilation type 1).parameters,
    .binding (.named .head) (by change "unused" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.pair (.identifier (.tail (by change "unused" ≠ "seed"; decide) .head)) .unit)
        (.pair (.var (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)) .unit)
        (.pair (.var (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)) .unit)))⟩

theorem named_unused_initializers_remain_strict_before_a_structural_product_return
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) (fuel : Nat) :
    RuntimeFunctionCompiles (table type) owner strictDeclaration ⟨initial type, strictCore, .product type .unit⟩ ∧
    RuntimeFunctionEvaluatesWithCost (table type) owner strictDeclaration (arguments actual) store
      (.product type .unit) (.pair actual.val .unit) store 8 ∧
    (runRuntimeFunction? (table type) owner strictDeclaration (arguments actual) fuel store =
      some (.product type .unit, .done (.pair actual.val .unit) store) ↔ 8 ≤ fuel) := by
  have cost : RuntimeFunctionEvaluatesWithCost (table type) owner strictDeclaration (arguments actual) store
      (.product type .unit) (.pair actual.val .unit) store 8 := by
    apply RuntimeFunctionEvaluatesWithCost.intro (declaration := strictDeclaration) (prepared := ⟨inputs actual, strictCore, .product type .unit⟩)
      ⟨header type 1, (preparation actual 1).parameters, (strictCompilation type).body⟩
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 5)
    · exact .identifier .head .head
    · apply TypedLetReturnTreeEvaluatesWithCost.single
      apply ReturnBodyEvaluatesWithCost.expression
      apply LocalExpressionEvaluatesWithCost.pair (leftCost := 1) (rightCost := 1)
      · exact .identifier (.tail (by change "unused" ≠ "seed"; decide) .head) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
      · exact .unit
  exact ⟨strictCompilation type, cost, cost.run_done_iff⟩

private def letBody (annotation : Syntax.TypeExpr) : Syntax.Block :=
  ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some annotation) (some (source 0))⟩, ⟨span, .returnStmt (some (source 0))⟩]⟩
theorem structural_annotations_remain_outside_the_old_named_only_and_prefix_adapters
    (types : TypeNameTable) (elements : List Syntax.TypeExpr) :
    interpretTypeName? types ⟨span, .tuple elements⟩ = none ∧
    elaborateTypedLetReturnBody? types owner .empty (letBody ⟨span, .tuple elements⟩) = none := by
  constructor
  · rfl
  · apply elaborateTypedLetReturnBody?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    cases typing with
    | terminal child => cases child with | single child => cases child
    | binding meaning _ _ _ => cases meaning

theorem raw_unit_success_does_not_bypass_a_missing_child_in_the_return_annotation :
    evaluateTypedLetReturnTreeWithCost? owner [] [] (body 0) = some (.unit, 1) ∧
    compileRuntimeFunction? [] owner
      (entry (clause span span [⟨span, .tuple [annotation 0, named "Missing"]⟩]) [] (body 0)) = none ∧
    evaluateRuntimeFunctionWithCost? [] owner
      (entry (clause span span [⟨span, .tuple [annotation 0, named "Missing"]⟩]) [] (body 0)) [] = none := by
  refine ⟨evaluateTypedLetReturnTreeWithCost?_complete
    (TypedLetReturnTreeEvaluatesWithCost.single (owner := owner) (initialStore := []) (.expression .unit)), ?_, ?_⟩
  · simp [compileRuntimeFunction?, entry, signature, clause, interpretRuntimeFunctionHeader?, interpretRuntimeReturnType?,
      interpretStructuralType?, annotation, named, TypeNameTable.lookup?]
  · apply evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr
    simp [prepareRuntimeFunction?, entry, signature, clause, interpretRuntimeFunctionHeader?, interpretRuntimeReturnType?,
      interpretStructuralType?, annotation, named, TypeNameTable.lookup?]

end Tests.FrontendStructuralReturn
