import Solcore.Frontend.LocalInputsCostInvariance
import Solcore.Frontend.LocalInputsRenamingProperties
import Solcore.Frontend.RuntimeFunctionStoreProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Core.UnsignedDivision

/-! Ordered unsigned division and remainder use actual inputs, including zero
divisors. Independent source evidence reaches the complete terminal entry. -/

set_option autoImplicit false

namespace Tests.FrontendWordDivision

open Solcore Solcore.Frontend

private inductive Kind where | quotient | remainder
private def sourceOp : Kind → Syntax.BinaryOp | .quotient => .divide | .remainder => .modulo
private def coreOp : Kind → Core.BinaryOp | .quotient => .wordDiv | .remainder => .wordMod
private def result (kind : Kind) (left right : Core.Word) : Core.Word :=
  match kind with | .quotient => left.udiv right | .remainder => left.umod right
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Division", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "division.sol"⟩, 23, 4⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def binary (kind : Kind) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .binary left ⟨span, sourceOp kind⟩ right⟩
private def source (kind : Kind) := binary kind (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core (kind : Kind) : Core.Expr := .binary (coreOp kind) (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (kind : Kind) (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names (source kind)
      (.binary (coreOp kind) (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) := by
  cases kind
  · exact .divide (.identifier (.tail names_ne .head)) (.identifier .head)
  · exact .modulo (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (kind : Kind) (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context (source kind) .word := by
  cases kind
  · exact .divide (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
  · exact .modulo (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (kind : Kind) (left right : Core.Word) :
    (inputs left right).check? (source kind) = some (core kind, .word) :=
  elaborateLocalExpression?_complete (resolved kind left right)
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    ((resolved kind left right).preserves_type (typed kind left right))
private theorem costed (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (source kind) (.word (result kind left right)) store 5 := by
  cases kind
  · exact .divide (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
      (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
  · exact .modulo (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
      (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_have_independent_typing_raw_cost_and_outer_continuation_paths
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (continuation : List Core.Frame) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context (source kind) .word ∧
    (inputs left right).check? (source kind) = some (core kind, .word) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store (source kind) (.word (result kind left right)) store ∧
    Core.Steps 5 ⟨.eval (core kind) [.word right, .word left], continuation, store⟩
      ⟨.ret (.word (result kind left right)), continuation, store⟩ := by
  refine ⟨typed kind left right, checked kind left right, ?_,
    (costed kind left right store).toStepsWithContinuation (resolved kind left right)
      (.binary (.var (.tail ids_ne .head)) (.var .head)) continuation⟩
  cases kind
  · exact .divide (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
  · exact .modulo (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem exact_five_step_threshold_includes_every_zero_case
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    ((inputs left right).run? fuel (source kind) store =
      some (.word, .done (.word (result kind left right)) store) ↔ 5 ≤ fuel) ∧
    ((∃ suspended, Core.runStateful fuel (Core.State.initial (core kind) [.word right, .word left] store) =
      .outOfFuel suspended) ↔ fuel < 5) := by
  refine ⟨?_, (costed kind left right store).checked_runStateful_outOfFuel_iff (checked kind left right)
    (inputs left right).sameIds⟩
  simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure, Option.some.injEq,
    Prod.mk.injEq, true_and] using (costed kind left right store).checked_runStateful_done_iff
      (fuel := fuel) (checked kind left right) (inputs left right).sameIds

private def pending (kind : Kind) (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word right), [.binaryApply (coreOp kind) (.word left)], store⟩
theorem original_left_then_right_checkpoints_resume_the_genuine_remaining_step
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    Core.runStateful 2 (Core.State.initial (core kind) [.word right, .word left] store) =
      .outOfFuel ⟨.ret (.word left), [.binaryRight (coreOp kind) (.var 0) [.word right, .word left]], store⟩ ∧
    (inputs left right).run? 4 (source kind) store = some (.word, .outOfFuel (pending kind left right store)) ∧
    Core.Steps 1 (pending kind left right store) (Core.State.final (.word (result kind left right)) store) ∧
    (inputs left right).run? (4 + additional) (source kind) store =
      some (.word, Core.runStateful additional (pending kind left right store)) := by
  have exhausted : Core.runStateful 4 (Core.State.initial (core kind) [.word right, .word left] store) =
      .outOfFuel (pending kind left right store) := by cases kind <;> rfl
  have publicExhausted := LocalInputs.run?_eq_some_iff.mpr ⟨core kind, checked kind left right, exhausted⟩
  exact ⟨by cases kind <;> rfl, publicExhausted,
    ((costed kind left right store).checked_residual_of_outOfFuel
      (checked kind left right) (inputs left right).sameIds exhausted).2,
    LocalInputs.run?_resume publicExhausted additional⟩

theorem zero_divisors_and_dividends_are_total_without_reducing_the_fuel
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    result kind left .zero = .zero ∧ result kind .zero right = .zero ∧
    ((inputs left .zero).run? fuel (source kind) store = some (.word, .done (.word .zero) store) ↔ 5 ≤ fuel) := by
  have zeroRight : result kind left .zero = .zero := by
    cases kind; exact Core.Word.udiv_zero left; exact Core.Word.umod_zero left
  refine ⟨zeroRight, ?_, ?_⟩
  · cases kind <;> simp only [result, Core.Word.udiv, Core.Word.umod] <;> split
    all_goals apply Fin.ext
    all_goals first | exact Nat.zero_div _ | exact Nat.zero_mod _ | rfl
  · simpa only [zeroRight] using (exact_five_step_threshold_includes_every_zero_case kind left .zero store fuel).1

theorem nonzero_operands_agree_with_the_existing_unsigned_core_interface
    (left right : Core.Word) (nonzero : right ≠ .zero) :
    result .quotient left right = left / right ∧ result .remainder left right = left % right :=
  ⟨Core.Word.udiv_nonzero left right nonzero, Core.Word.umod_nonzero left right nonzero⟩

theorem ordered_nonzero_high_bit_and_maximum_values_distinguish_quotient_from_remainder :
    result .quotient (Core.Word.ofNatModulo 7) (Core.Word.ofNatModulo 3) = Core.Word.ofNatModulo 2 ∧
    result .remainder (Core.Word.ofNatModulo 7) (Core.Word.ofNatModulo 3) = Core.Word.ofNatModulo 1 ∧
    result .quotient (Core.Word.ofNatModulo 3) (Core.Word.ofNatModulo 7) = .zero ∧
    result .remainder (Core.Word.ofNatModulo 3) (Core.Word.ofNatModulo 7) = Core.Word.ofNatModulo 3 ∧
    result .remainder (Core.Word.ofNatModulo 7) .zero ≠ Core.Word.ofNatModulo 7 % Core.Word.zero ∧
    result .quotient .maximum (Core.Word.ofNatModulo (2 ^ 255)) = Core.Word.ofNatModulo 1 ∧
    result .remainder .maximum (Core.Word.ofNatModulo (2 ^ 255)) = Core.Word.ofNatModulo (2 ^ 255 - 1) := by decide

theorem successful_cost_requires_both_original_ordered_word_children (kind : Kind)
    {table : LocalNameTable} {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {left right : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment initialStore (binary kind left right) value finalStore cost) :
    ∃ l r middle lc rc, LocalExpressionEvaluatesWithCost table environment initialStore left (.word l) middle lc ∧
      LocalExpressionEvaluatesWithCost table environment middle right (.word r) finalStore rc ∧
      value = .word (result kind l r) ∧ cost = lc + rc + 3 := by
  cases kind <;> cases evaluation <;> exact ⟨_, _, _, _, _, by assumption, by assumption, rfl, rfl⟩

private def typedInputs (l r : Core.Ty) (left right : Core.Value)
    (lt : Core.ValueHasType left l) (rt : Core.ValueHasType right r) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" l left lt).bindFresh owner "r" r right rt
theorem either_non_word_type_rejects_without_conversions (kind : Kind)
    (l r : Core.Ty) (left right : Core.Value) (lt : Core.ValueHasType left l) (rt : Core.ValueHasType right r)
    (wrong : l ≠ .word ∨ r ≠ .word) (fuel : Nat) (store : Core.Store) :
    (typedInputs l r left right lt rt).run? fuel (source kind) store = none := by
  apply (LocalInputs.run?_eq_none_iff fuel store).mpr
  cases accepted : (typedInputs l r left right lt rt).check? (source kind) with
  | none => rfl
  | some output =>
    rcases output with ⟨outputCore, outputType⟩
    have whole := LocalInputs.check?_iff_hasType.mp ⟨outputCore, accepted⟩
    have first : LocalExpressionHasType (typedInputs l r left right lt rt).names
        (typedInputs l r left right lt rt).context (ref "l") l := .identifier (.tail names_ne .head) (.tail ids_ne .head)
    have second : LocalExpressionHasType (typedInputs l r left right lt rt).names
        (typedInputs l r left right lt rt).context (ref "r") r := .identifier .head .head
    cases kind
    · cases whole with
      | divide a b => exact False.elim (wrong.elim
          (fun bad => bad (first.type_unique a)) (fun bad => bad (second.type_unique b)))
    · cases whole with
      | modulo a b => exact False.elim (wrong.elim
          (fun bad => bad (first.type_unique a)) (fun bad => bad (second.type_unique b)))

theorem zero_operands_do_not_resolve_a_missing_other_operand (kind : Kind) :
    (inputs .zero .zero).check? (binary kind (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (binary kind (ref "missing") (ref "r")) = none := by
  cases kind <;> constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?,
    binary, sourceOp, ref, inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
private def skipped (kind : Kind) : Syntax.Expr := ⟨span,
  .conditional ⟨span, .binary (ref "l") ⟨span, .equal⟩ (ref "l")⟩ span (ref "l") span
    (binary kind (ref "l") (ref "missing"))⟩
theorem raw_selected_path_does_not_license_an_invalid_written_divisor (kind : Kind) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs .zero .zero).names (inputs .zero .zero).environment
      store (skipped kind) (.word .zero) store 8 ∧ (inputs .zero .zero).check? (skipped kind) = none := by
  have leaf : LocalExpressionEvaluatesWithCost (inputs .zero .zero).names (inputs .zero .zero).environment
      store (ref "l") (.word .zero) store 1 := .identifier (.tail names_ne .head) (.tail ids_ne .head)
  refine ⟨.ifTrue (.equal leaf leaf) leaf, ?_⟩
  cases kind <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, skipped,
    binary, sourceOp, ref, inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

theorem spans_injective_ids_and_fresh_unused_inputs_preserve_the_arithmetic
    (kind : Kind) (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) (s o : Syntax.SourceSpan) :
    ((inputs left right).mapIds mapping injective).run? fuel (source kind) store =
      (inputs left right).run? fuel (source kind) store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store (source kind) (.word (result kind left right)) store 5 ∧
    resolveLocalExpression? (inputs left right).names (source kind) =
      resolveLocalExpression? (inputs left right).names ⟨s, .binary (ref "l") ⟨o, sourceOp kind⟩ (ref "r")⟩ := by
  have avoids : AvoidsLocalName "unused" (source kind) := by
    cases kind
    · exact .divide (.identifier (by decide)) (.identifier (by decide))
    · exact .modulo (.identifier (by decide)) (.identifier (by decide))
  refine ⟨(inputs left right).run?_mapIds mapping injective fuel (source kind) store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed kind left right store), ?_⟩
  cases kind
  · exact resolveLocalExpression?_divide_spans _ _ _ _ _ _ _
  · exact resolveLocalExpression?_modulo_spans _ _ _ _ _ _ _

theorem arbitrary_identity_maps_store_replay_and_value_erasure_keep_the_contract
    (kind : Kind) (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (first replacement : Core.Store) :
    ResolvesLocalExpression (LocalNameTable.mapIds mapping (inputs left right).names) (source kind)
      (.binary (coreOp kind) (.var (mapping ⟨owner, 0⟩)) (.var (mapping ⟨owner, 1⟩))) ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      replacement (source kind) (.word (result kind left right)) replacement 5 ∧
    5 ≤ localExpressionFuelBound (source kind) ∧ localExpressionFuelBound (source kind) = 5 ∧
    (inputs left right).toTypeInputs.context = (inputs left right).context := by
  exact ⟨(resolved kind left right).mapIds mapping, (costed kind left right first).change_store replacement,
    (costed kind left right first).cost_le_fuelBound,
    by cases kind <;> simp [localExpressionFuelBound, source, binary, sourceOp, ref], (inputs left right).toTypeInputs_context⟩

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (annotation "Word")⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def returned (value : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some value)⟩]⟩
private def entryBody (kind : Kind) : Syntax.Block := ⟨span, [⟨span,
  .ifThen ⟨span, .binary (ref "l") ⟨span, .equal⟩ (ref "r")⟩
    (returned (source kind)) (some (returned (ref "l")))⟩]⟩
private def declaration (kind : Kind) (name : String := "Word") : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "division"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation name]⟩⟩, none⟩, entryBody kind⟩⟩
private def compiled (kind : Kind) : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word,
    .ifE (.binary .wordEq (.var 1) (.var 0)) (core kind) (.var 1), .word⟩
private theorem compilation (kind : Kind) : RuntimeFunctionCompiles types owner (declaration kind) (compiled kind) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil), .conditional <| .intro
    (.equal (.identifier (.tail names_ne .head)) (.identifier .head))
    (.binary (.var (.tail ids_ne .head)) (.var .head)) (.binary (.var (.tail ids_ne .head)) (.var .head))
    (.expression (resolved kind .zero .zero) (.binary (.var (.tail ids_ne .head)) (.var .head))
      ((resolved kind .zero .zero).preserves_type (typed kind .zero .zero)))
    (.expression (.identifier (.tail names_ne .head)) (.var (.tail ids_ne .head)) (.var (.tail ids_ne .head)))⟩
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (kind : Kind) (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration kind) (arguments left right) ⟨inputs left right, (compiled kind).core, .word⟩ :=
  ⟨(compilation kind).header, .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil), (compilation kind).body⟩

theorem terminal_compilation_uses_actual_arguments_and_selected_exact_cost
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    RuntimeFunctionCompiles types owner (declaration kind) (compiled kind) ∧
    RuntimeFunctionPrepares types owner (declaration kind) (arguments left right) ⟨inputs left right, (compiled kind).core, .word⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration kind) (arguments left right) store .word
      (.word (if left == right then result kind left right else left)) store (if left == right then 12 else 8) ∧
    runRuntimeFunction? types owner (declaration kind) (arguments left right) fuel store = some (.word,
      Core.runStateful fuel (Core.State.initial (compiled kind).core [.word right, .word left] store)) := by
  refine ⟨compilation kind, preparation kind left right, ?_, (compilation kind).run_eq _ rfl fuel store⟩
  apply RuntimeFunctionEvaluatesWithCost.intro (preparation kind left right)
  have l : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (ref "l") (.word left) store 1 := .identifier (.tail names_ne .head) (.tail ids_ne .head)
  have r : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (ref "r") (.word right) store 1 := .identifier .head .head
  have comparison := LocalExpressionEvaluatesWithCost.equal (span := span) (operatorSpan := span) l r
  cases choice : (left == right)
  · exact .conditional (.ifFalse (by simpa only [choice] using comparison) (.expression l))
  · exact .conditional (.ifTrue (by simpa only [choice] using comparison) (.expression (costed kind left right store)))

theorem terminal_selected_threshold_bound_and_actual_compiled_path
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    (runRuntimeFunction? types owner (declaration kind) (arguments left right) fuel store =
      some (.word, .done (.word (if left == right then result kind left right else left)) store) ↔
      (if left == right then 12 else 8) ≤ fuel) ∧
    Core.Steps (if left == right then 12 else 8)
      (Core.State.initial (compiled kind).core ((arguments left right).reverse.map (·.value)) store)
      (Core.State.final (.word (if left == right then result kind left right else left)) store) ∧
    (if left == right then 12 else 8) ≤ terminalReturnBodyFuelBound (declaration kind).value.body := by
  have evaluation := (terminal_compilation_uses_actual_arguments_and_selected_exact_cost kind left right store fuel).2.2.1
  exact ⟨evaluation.run_done_iff, evaluation.compiled_toSteps (compilation kind), evaluation.cost_le_fuelBound⟩

theorem a_boolean_declared_return_cannot_replace_the_word_result (kind : Kind) :
    compileRuntimeFunction? types owner (declaration kind "Bool") = none := by
  apply compileRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨candidate, accepted⟩
  have sameInputs := accepted.parameters.result_unique (compilation kind).parameters
  have body := accepted.body
  rw [sameInputs] at body
  have sameType := ((compilation kind).body.result_unique body).2
  have header : RuntimeFunctionHeader types (declaration kind "Bool").value.signature .bool :=
    ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
  cases sameType.trans (accepted.header.type_unique header)

end Tests.FrontendWordDivision
