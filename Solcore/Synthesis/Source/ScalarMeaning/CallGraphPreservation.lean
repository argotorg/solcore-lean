import Solcore.Synthesis.Source.ScalarMeaning.CallGraphEquations
import Solcore.Synthesis.Source.ScalarMeaning.PrimitivePreservation

/-! Simulation lemmas for helper calls whose argument is copied into a fresh
temporary first, and their instance, together with the shared and raw opcode
cases, for the actual `CallGraphRenderer.renderWithFunctions`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target functionAcceptsAt)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)

section Generic

variable {render : RenderFn} {admits : Context → Prop} {called : List String}

/-- A call to an earlier helper printed as one fresh `word` temporary bound to
`callee(value)`: the argument value is passed to the helper's denotation in
the call context, as Core applies its closure. -/
theorem applyResult_spec {index : Nat} {argument : CoreExpr} {functions locals : List String}
    {indent first : Nat} {value : Rendered} {callee : String}
    (outside : locals.length ≤ index) (found : functions[index - locals.length]? = some callee)
    (spec : RenderSpec admits called argument .word functions locals indent first value) :
    RenderSpec admits called (.apply (.var index) argument) .word functions locals indent first
      (resultOf indent .word value.lines value.nextId (.call1 callee (.name value.value))) := by
  obtain ⟨statements, lines, le, valueClassified, names, simulates⟩ := spec
  unfold RenderSpec resultOf
  dsimp only
  refine ⟨statements ++ [.letDecl (temporary value.nextId) (LocalType.ofTarget .word)
      (.call1 callee (.name value.value))], ?_, by omega,
    Or.inr (allocated_temporary le (Nat.lt_succ_self _)), ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines, Stmt.listLines, List.append_nil]
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with mem | same | same | same
    · exact named_mono (names name mem) (Nat.le_refl _) (by omega)
    · exact named_allocated ⟨value.nextId, same, le, by omega⟩
    · subst same
      exact Or.inr (Or.inl (List.mem_of_getElem? found))
    · subst same
      exact named_of_classified valueClassified (Nat.le_refl _) (by omega)
  · refine result_simulates (target := .word) (fun context environment store scope outer
      admitted agree lengthOk functionsOk => ?_) le
    obtain ⟨argumentCore, argumentSource, scope₁, outer₁, added₁, argumentEvaluates,
      argumentRepresents, argumentExec, argumentLookup, argumentKeeps, argumentShape,
      argumentScope, argumentAdded⟩ :=
      simulates context environment store scope outer admitted agree lengthOk functionsOk
    obtain ⟨word, rfl, rfl⟩ := argumentRepresents
    obtain ⟨parameterType, resultType, body, captured, closureFound, behaves⟩ :=
      functionsOk (index - locals.length) callee found
    obtain ⟨result, bodyEvaluates, callResult⟩ := behaves word store
    have closureAt : environment[index]? =
        some (.closure parameterType resultType body captured) := by
      rw [List.getElem?_drop] at closureFound
      have position : locals.length + (index - locals.length) = index := by omega
      rwa [position] at closureFound
    refine ⟨.word result, .word result.val, scope₁, outer₁, added₁, ?_, ⟨result, rfl, rfl⟩,
      argumentExec, ?_, argumentKeeps, argumentShape, argumentScope, argumentAdded⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .apply (.var closureAt) argumentEvaluates bodyEvaluates
    · simp [Expr.eval, argumentLookup, callResult]

/-- A direct call to an earlier helper whose argument is copied first. -/
def SnapshotApplyInversion (render : RenderFn) : Prop :=
  ∀ (functions : List String) (target : Target) (locals : List String) (indent first index : Nat)
    (argument : CoreExpr) (rendered : Rendered),
    render functions target locals indent first (.apply (.var index) argument) = .ok rendered →
    target = .word ∧ locals.length ≤ index ∧ ∃ callee value,
      functions[index - locals.length]? = some callee ∧
      render functions .word locals indent first argument = .ok value ∧
      rendered = resultOf indent .word (snapshotOf indent value).lines (value.nextId + 1)
        (.call1 callee (.name (temporary value.nextId)))

theorem renderIH_snapshotApply (inversion : SnapshotApplyInversion render) {index : Nat}
    {argument : CoreExpr} (argumentIH : RenderIH render admits called argument) :
    RenderIH render admits called (.apply (.var index) argument) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  simp only [functionAcceptsAt, Bool.and_eq_true] at accepted
  obtain ⟨_, argumentAccepted⟩ := accepted
  obtain ⟨rfl, outside, callee, value, found, valueEquation, rfl⟩ :=
    inversion functions target locals indent first index argument rendered equation
  exact applyResult_spec outside found (snapshot_spec (argumentIH functions depth prior .word
    locals indent first value argumentAccepted valueEquation fresh))

end Generic

/-! ### The actual call-graph renderer -/

theorem callGraph_word : WordInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first value rendered equation
  rw [CallGraphEquations.word] at equation
  exact (Except.ok.inj equation).symm

theorem callGraph_bool : BoolInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first value rendered equation
  rw [CallGraphEquations.bool] at equation
  exact (Except.ok.inj equation).symm

theorem callGraph_var : VarInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first index rendered equation
  rw [CallGraphEquations.var] at equation
  cases found : locals[index]? with
  | none =>
      rw [found] at equation
      cases equation
  | some binding =>
      rw [found] at equation
      exact ⟨binding, rfl, (Except.ok.inj equation).symm⟩

theorem callGraph_letE : LetInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first initializer body rendered equation
  rw [CallGraphEquations.letE] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, rest, valueEquation, restEquation, (Except.ok.inj equation).symm⟩

theorem callGraph_ifE : IfInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first condition yes no rendered equation
  rw [CallGraphEquations.ifE] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    (Except.ok.inj equation).symm⟩

theorem callGraph_unary : UnaryInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first op sourceOp operand rendered selected equation
  rw [CallGraphEquations.unary functions target locals indent first op sourceOp operand
    selected] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, valueEquation, (Except.ok.inj equation).symm⟩

theorem callGraph_binary : BinaryInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first op sourceOp left right rendered selected equation
  rw [CallGraphEquations.binary functions target locals indent first op sourceOp left right
    selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨leftValue, rightValue, leftEquation, rightEquation, (Except.ok.inj equation).symm⟩

theorem callGraph_clz : ClzInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first operand rendered equation
  rw [CallGraphEquations.clz] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, valueEquation, (Except.ok.inj equation).symm⟩

theorem callGraph_primitiveBinary :
    PrimitiveBinaryInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first op build left right rendered selected equation
  rw [CallGraphEquations.binary_primitive functions target locals indent first op build left
    right selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨leftValue, rightValue, leftEquation, rightEquation, (Except.ok.inj equation).symm⟩

theorem callGraph_ternary : TernaryInversion CallGraphRenderer.renderWithFunctions := by
  intro functions target locals indent first op one two three rendered equation
  rw [CallGraphEquations.ternary] at equation
  obtain ⟨oneValue, oneEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨twoValue, twoEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨threeValue, threeEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨oneValue, twoValue, threeValue, oneEquation, twoEquation, threeEquation,
    (Except.ok.inj equation).symm⟩

theorem callGraph_apply : SnapshotApplyInversion CallGraphRenderer.renderWithFunctions :=
  fun _ _ _ _ _ _ _ _ equation => CallGraphEquations.apply_ok equation

theorem callGraph_unary_spec {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (operandIH : RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees
      operand) :
    RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees
      (.unary op operand) := by
  cases selected : sourceUnary? op with
  | some _ => exact renderIH_unary callGraph_unary selected operandIH
  | none =>
      cases op
      case boolNot => simp [sourceUnary?] at selected
      case wordNot => simp [sourceUnary?] at selected
      case wordClz =>
        exact renderIH_clz callGraph_clz (by decide)
          (fun _ admitted => admitted.reaches (by decide)) operandIH
      all_goals
        refine renderIH_error _ fun functions target locals indent first rendered equation => ?_
        rw [CallGraphEquations.unary_unsupported _ _ _ _ _ _ _ rfl] at equation
        cases equation

theorem callGraph_binary_spec {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (leftIH : RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees
      left)
    (rightIH : RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees
      right) :
    RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees
      (.binary op left right) := by
  cases selected : sourceBinary? op with
  | some _ => exact renderIH_binary callGraph_binary selected leftIH rightIH
  | none =>
      cases extended : primitiveBinary? op with
      | some build =>
          exact renderIH_primitiveBinary callGraph_primitiveBinary extended
            (primitiveBinary_names extended)
            (fun context frames leftName rightName leftWord rightWord admitted =>
              primitiveBinary_agree extended context frames leftName rightName leftWord
                rightWord admitted)
            leftIH rightIH
      | none =>
          refine renderIH_error _ fun functions target locals indent first rendered equation => ?_
          have unsupported : CallGraphRenderer.supportedBinary op = false := by
            cases op <;> simp_all [sourceBinary?, primitiveBinary?,
              CallGraphRenderer.supportedBinary, PrimitiveRenderer.supportedBinary,
              Source.supportedBinary]
          rw [CallGraphEquations.binary_unsupported _ _ _ _ _ _ _ _ unsupported] at equation
          cases equation

/-- Every admitted expression that the actual call-graph renderer accepts
satisfies its rendering specification in every primitive call context, with
or without earlier helpers. -/
theorem callGraph_render_spec :
    (expression : CoreExpr) →
      RenderIH CallGraphRenderer.renderWithFunctions PrimitiveContext primitiveCallees expression
  | .word value => renderIH_word callGraph_word value
  | .bool value => renderIH_bool callGraph_bool value
  | .var index => renderIH_var callGraph_var index
  | .letE initializer body =>
      renderIH_letE callGraph_letE (callGraph_render_spec initializer)
        (callGraph_render_spec body)
  | .ifE condition yes no =>
      renderIH_ifE callGraph_ifE (callGraph_render_spec condition) (callGraph_render_spec yes)
        (callGraph_render_spec no)
  | .unary _ operand => callGraph_unary_spec (callGraph_render_spec operand)
  | .binary _ left right =>
      callGraph_binary_spec (callGraph_render_spec left) (callGraph_render_spec right)
  | .ternary op one two three =>
      renderIH_ternary callGraph_ternary (by cases op <;> decide)
        (fun context frames oneName twoName threeName oneWord twoWord threeWord admitted =>
          ternary_agree op context frames oneName twoName threeName oneWord twoWord threeWord
            admitted)
        (callGraph_render_spec one) (callGraph_render_spec two) (callGraph_render_spec three)
  | .apply (.var _) argument =>
      renderIH_snapshotApply callGraph_apply (callGraph_render_spec argument)
  | .apply (.word _) _ | .apply (.bool _) _ | .apply .unit _ | .apply (.integer _) _
  | .apply (.pair _ _) _ | .apply (.first _) _ | .apply (.second _) _
  | .apply (.lambda _ _ _) _ | .apply (.apply _ _) _ | .apply (.inLeft _ _) _
  | .apply (.inRight _ _) _ | .apply (.caseE _ _ _) _ | .apply (.newCell _ _) _
  | .apply (.loadCell _) _ | .apply (.storeCell _ _) _ | .apply (.construct _ _) _
  | .apply (.matchData _ _ _ _) _ | .apply (.unary _ _) _ | .apply (.binary _ _ _) _
  | .apply (.ternary _ _ _ _) _ | .apply (.letE _ _) _ | .apply (.ifE _ _ _) _ =>
      renderIH_rejected _ fun _ _ _ => rfl
  | .unit => renderIH_rejected _ fun _ _ _ => rfl
  | .integer _ => renderIH_rejected _ fun _ _ _ => rfl
  | .pair _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .first _ => renderIH_rejected _ fun _ _ _ => rfl
  | .second _ => renderIH_rejected _ fun _ _ _ => rfl
  | .lambda _ _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .inLeft _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .inRight _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .caseE _ _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .newCell _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .loadCell _ => renderIH_rejected _ fun _ _ _ => rfl
  | .storeCell _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .construct _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .matchData _ _ _ _ => renderIH_rejected _ fun _ _ _ => rfl

end Solcore.Synthesis.Source.ScalarMeaning
