import Solcore.Frontend.ExpectedDataLambdaApplicationProperties
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Core.Typing

/- Checked lambda bodies do not type their actual arguments or enlarge the closed gate. -/
set_option autoImplicit false
namespace Tests.ExpectedDataLambdaBoundaries
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"LambdaBoundary", by decide⟩], by decide⟩⟩, 295⟩
private def name (s : Syntax.SourceSpan) : Syntax.Identifier := ⟨s, "p"⟩
private def ref (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s, .identifier (name s)⟩
private def unit (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s, .tuple ⟨s, []⟩⟩
private def output (s : Syntax.SourceSpan) (e : Syntax.Expr) : Syntax.Block :=
  ⟨s, [⟨s, .returnStmt (some e)⟩]⟩
private def lambda (s : Syntax.SourceSpan) (b : Syntax.Block) : Syntax.Expr :=
  ⟨s, .lambda s ⟨s, [⟨s, .inferred (name s)⟩]⟩ none b⟩
private def identity (s : Syntax.SourceSpan) := lambda s (output s (ref s))
private def call (s : Syntax.SourceSpan) (f a : Syntax.Expr) : Syntax.Expr :=
  ⟨s, .call f ⟨s, [a]⟩⟩
private def neg (s : Syntax.SourceSpan) (e : Syntax.Expr) : Syntax.Expr :=
  ⟨s, .unary ⟨s, .logicalNot⟩ e⟩

private theorem identity_checked (s : Syntax.SourceSpan) (inputs : LocalTypeInputs)
    (type : Core.Ty) (wf : type.WellFormed []) :
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner inputs
      (identity s) (.function type type) = some (.lambda type type (.var 0)) :=
  (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
    (.lambda (.lambda .inferred .omitted) wf wf
      (.expression (elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head))))

variable (s : Syntax.SourceSpan) (store : Core.Store)

/-- Word identity still returns actual Unit; this operational bridge is not whole-call typing. -/
theorem checked_word_identity_accepts_actual_unit :
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      (identity s) (.function .word .word) = some (.lambda .word .word (.var 0)) ∧
    Core.infer? [] (.apply (.lambda .word .word (.var 0)) .unit) = none ∧
    ClosedSourceExpressionEvaluates owner [] [] (store.map RuntimeValue.ofCore)
      (call s (identity s) (unit s)) .unit (store.map RuntimeValue.ofCore) ∧
    Core.Evaluates [] store (.apply (.lambda .word .word (.var 0)) .unit) .unit store ∧
    (∀ actual final, ClosedSourceExpressionEvaluates owner [] [] (store.map RuntimeValue.ofCore)
      (call s (identity s) (unit s)) actual final ↔
        actual = .unit ∧ final = store.map RuntimeValue.ofCore) := by
  have original : ClosedSourceExpressionEvaluates owner [] [] (store.map RuntimeValue.ofCore)
      (call s (identity s) (unit s)) .unit (store.map RuntimeValue.ofCore) :=
    .call .inferred (.creation .inferred) .unit (.expression (.reference .head .head))
  have core : Core.Evaluates [] store (.apply (.lambda .word .word (.var 0)) .unit) .unit store :=
    .apply .lambda .unit (.var rfl)
  have checked := identity_checked s .empty .word .word
  refine ⟨checked, by decide, original, core, ?_⟩
  intro actual final
  have image := closedSourceExpectedDataLambda_application_core_iff
    (owner := owner) (initialStore := store) (callSpan := s) (argumentsSpan := s)
    (argument := unit s) (environment := []) (actualValue := actual) (actualFinal := final)
    .inferred (.expression .reference) checked rfl .unit .unit .unit
  constructor
  · intro evaluated
    obtain ⟨result, finalStore, same, sameFinal, evaluatedCore⟩ := image.mp evaluated
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluatedCore core
    exact ⟨by simpa only [RuntimeValue.ofCore] using same, sameFinal⟩
  · rintro ⟨rfl, rfl⟩
    exact image.mpr ⟨.unit, store, by simp only [RuntimeValue.ofCore], rfl, core⟩

/-- The original unary body checks and evaluates successfully and is admitted by the data gate. -/
theorem checked_unary_body_is_outside_closed_gate :
    let b := output s (neg s (ref s))
    let f := lambda s b
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      f (.function .bool .bool) = some (.lambda .bool .bool (.unary .boolNot (.var 0))) ∧
    (ClosedSourceDataBody b) ∧
    (∀ (choice : Bool) (initial : List RuntimeValue),
      ClosedSourceBodyEvaluates owner [("p", Resolved.freshLocalId owner [])]
        [(Resolved.freshLocalId owner [], .bool choice)] initial b
        (.bool (!choice)) initial) ∧
    Core.Evaluates [] store
      (.apply (.lambda .bool .bool (.unary .boolNot (.var 0))) (.bool true)) (.bool false) store := by
  have checked : elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      (lambda s (output s (neg s (ref s)))) (.function .bool .bool) =
        some (.lambda .bool .bool (.unary .boolNot (.var 0))) :=
    (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
      (.lambda (.lambda .inferred .omitted) .bool .bool
        (.expression (elaborateLocalExpression?_complete (.logicalNot (.identifier .head))
          (.unary (.var .head)) (.unary (.var .head)))))
  refine ⟨checked, ?_, ?_, .apply .lambda .bool (.unary (.var rfl) rfl)⟩
  · exact .expression (.logicalNot .reference)
  · intro choice initial
    exact .expression (.logicalNot (.reference .head .head))

/-- An original unary argument checks, lowers and evaluates and is admitted by the data gate. -/
theorem checked_unary_argument_is_outside_closed_gate :
    let inputs := LocalTypeInputs.empty.bindFresh owner "p" .bool
    let id := Resolved.freshLocalId owner []
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner inputs
      (identity s) (.function .bool .bool) = some (.lambda .bool .bool (.var 0)) ∧
    elaborateLocalExpression? inputs.names inputs.context (neg s (ref s)) =
      some (.unary .boolNot (.var 0), .bool) ∧
    ResolvesLocalExpression inputs.names (neg s (ref s)) (.unary .boolNot (.var id)) ∧
    Resolved.Lowers [id] (.unary .boolNot (.var id)) (.unary .boolNot (.var 0)) ∧
    (ClosedSourceDataExpression (neg s (ref s))) ∧
    (∀ (choice : Bool) (initial : List RuntimeValue),
      ClosedSourceExpressionEvaluates owner inputs.names [(id, .bool choice)]
        initial (neg s (ref s)) (.bool (!choice)) initial) ∧
    Core.Evaluates [.bool true] store
      (.apply (.lambda .bool .bool (.var 0)) (.unary .boolNot (.var 0))) (.bool false) store := by
  have resolution : ResolvesLocalExpression
      (LocalTypeInputs.empty.bindFresh owner "p" .bool).names (neg s (ref s))
      (.unary .boolNot (.var (Resolved.freshLocalId owner []))) := .logicalNot (.identifier .head)
  have lowering : Resolved.Lowers [Resolved.freshLocalId owner []]
      (.unary .boolNot (.var (Resolved.freshLocalId owner []))) (.unary .boolNot (.var 0)) :=
    .unary (.var .head)
  have typed : Resolved.HasType (LocalTypeInputs.empty.bindFresh owner "p" .bool).context
      (.unary .boolNot (.var (Resolved.freshLocalId owner []))) .bool := .unary (.var .head)
  refine ⟨identity_checked s _ .bool .bool, elaborateLocalExpression?_complete resolution lowering typed,
    resolution, lowering, ?_, ?_, .apply .lambda (.unary (.var rfl) rfl) (.var rfl)⟩
  · exact .logicalNot .reference
  · intro choice initial
    exact .logicalNot (.reference .head .head)

/-- Marked and multiple parameters supply neither the shape premise nor expected checking. -/
theorem marked_and_multiple_parameters_are_not_admitted (type : Core.Ty) :
    let p : Syntax.LambdaParameter := ⟨s, .inferred (name s)⟩
    let marked : Syntax.Expr := ⟨s, .lambda s
      ⟨s, [⟨s, .typed (some s) (name s) ⟨s, .tuple []⟩⟩]⟩ none (output s (unit s))⟩
    let multiple : Syntax.Expr := ⟨s, .lambda s ⟨s, [p, p]⟩ none (output s (unit s))⟩
    (¬ ∃ name body, SourceUnaryLambdaShape marked name body) ∧
    (¬ ∃ name body, SourceUnaryLambdaShape multiple name body) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      marked (.function type type) = none ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      multiple (.function type type) = none := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · rintro ⟨name, body, shape⟩; cases shape
  · rintro ⟨name, body, shape⟩; cases shape

end Tests.ExpectedDataLambdaBoundaries
