import Solcore.Frontend.SourceCoreElaboration
import Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedClosedEvaluationMeaning
open Frontend SourceInference SourceCoreElaboration
open SourceCoreElaboration.Internal

/-- Only actually consumed implementation rows must be valid. The full ledger is retained. -/
def UsedValid (context : Context) (solved : List SolvedRequirement) (used : List RequirementId) : Prop :=
  ∀ row proof, row ∈ solved → row.id ∈ used → row.evidence = .implementation proof → SolvedRequirementValid context row

theorem UsedValid.mono {context : Context} {solved : List SolvedRequirement} {small large : List RequirementId}
    (valid : UsedValid context solved large) (subset : ∀ id, id ∈ small → id ∈ large) : UsedValid context solved small := by
  intro row proof member used actual
  exact valid row proof member (subset row.id used) actual

theorem selected_proves {context : Context} {solved : List SolvedRequirement} {used : List RequirementId}
    {resolution : IntegerLiteralResolution} {implementation : ProgramImplId}
    (selected : NumericLiteralEvidenceReceipts.Selected solved resolution implementation)
    (ledger : context.solvedRequirements = solved) (valid : UsedValid context solved used)
    (usedHere : resolution.requirement ∈ used) : RequirementProves context resolution.requirement resolution.predicate := by
  obtain ⟨row, singleton, predicate, evidence⟩ := selected
  have member : row ∈ solved.filter (fun row => decide (row.id = resolution.requirement)) := by rw [singleton]; simp
  obtain ⟨member, identity⟩ := List.mem_filter.mp member
  have identifier : row.id = resolution.requirement := of_decide_eq_true identity
  exact ⟨row, ⟨ledger ▸ member, identifier⟩, predicate,
    valid row _ member (identifier ▸ usedHere) evidence⟩

def bindingValue (binding : Staged.Binding) : Int := by
  cases binding with
  | mk binder value => exact value

/-- An actual compiler lookup refers to the same initialized ordinary source cell. -/
def EnvironmentRep (actual : Staged.Environment) (environment : Dynamic.Environment) (heap : Dynamic.Heap) : Prop :=
  ∀ id binding, Staged.lookup actual id = some binding → ∃ location cell,
    Dynamic.Environment.LooksUp environment id location ∧ Dynamic.Heap.Reads heap location cell ∧
    cell.generalized = none ∧ cell.value = some (.integer (bindingValue binding))

private theorem of_raw {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap} {id : ExpressionId}
    {node : ExpressionNode} {value : Dynamic.Value}
    (found : source.lookupExpression? id = some node) (empty : node.coercions = [])
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions value heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id value heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found) raw
  rw [empty]
  exact .nil

private theorem integer_literal {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {solved : List SolvedRequirement} {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution} {validated : NativeIntegerLiteral}
    (found : source.lookupExpression? id = some node) (form : node.form = .integerLiteral literal resolution)
    (accepted : validateNativeIntegerLiteral solved node literal resolution = .ok validated)
    (ledger : context.solvedRequirements = solved) (valid : UsedValid context solved validated.consumedRequirements) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id (.integer validated.value) heap := by
  have metadata := validateNativeIntegerLiteral_sound accepted
  have proves := selected_proves (NumericLiteralEvidenceReceipts.integer accepted) ledger valid
    (by rw [metadata.consumedRequirements]; simp)
  have constructs : Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.integer validated.value) := by
    rw [metadata.value]
    cases resolution with
    | mk raw target requirement =>
      have targetEq := metadata.targetType
      dsimp only at targetEq
      subst target
      exact .integer metadata.meaning proves
  apply of_raw found metadata.coercions
  rw [form, metadata.requirements, metadata.coercions]
  exact .integerLiteral rfl constructs

private theorem word_literal {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {solved : List SolvedRequirement} {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution} {validated : WordIntegerLiteral}
    (found : source.lookupExpression? id = some node) (form : node.form = .integerLiteral literal resolution)
    (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated)
    (ledger : context.solvedRequirements = solved) (valid : UsedValid context solved validated.consumedRequirements) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id (.word validated.value) heap := by
  have metadata := validateWordIntegerLiteral_sound accepted
  have proves := selected_proves (NumericLiteralEvidenceReceipts.word accepted) ledger valid
    (by rw [metadata.consumedRequirements]; simp)
  have constructs : Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.word validated.value) := by
    rw [metadata.value]
    cases resolution with
    | mk raw target requirement =>
      have targetEq := metadata.targetType
      dsimp only at targetEq
      subst target
      exact .word metadata.meaning proves
  apply of_raw found metadata.coercions
  rw [form, metadata.requirements, metadata.coercions]
  exact .integerLiteral rfl constructs

private theorem group {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id inner : ExpressionId} {node : ExpressionNode} {value : Dynamic.Value}
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (child : Dynamic.ExpressionEvaluates program context evidence source environment heap inner value heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id value heap := by
  apply of_raw found coercions
  rw [form, requirements, coercions]
  exact .group rfl child

private theorem builtin {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id callee : ExpressionId} {node : ExpressionNode} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {values : List Dynamic.Value} {value : Dynamic.Value}
    (found : source.lookupExpression? id = some node) (form : node.form = .call callee arguments (.builtinFunction function))
    (validated : Staged.BuiltinChecked source node callee arguments function)
    (children : Dynamic.ExpressionsEvaluate program context evidence source environment heap arguments values heap)
    (applies : Dynamic.BuiltinApplies function values value) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id value heap := by
  apply of_raw found validated.coercions
  rw [form, validated.requirements, validated.coercions]
  exact .builtinCall rfl children (.builtin applies)

private theorem binary_applies {function : BuiltinFunctionId} {operation : Staged.BinaryOperation}
    (selected : Staged.binaryOperation? function = some operation) (a b : Int) :
    Dynamic.BuiltinApplies function [.integer a, .integer b] (.integer (Staged.applyBinary operation a b)) := by
  cases function <;> simp only [Staged.binaryOperation?] at selected <;> try contradiction
  all_goals cases selected
  · exact .integerSub a b
  · exact .integerAdd a b
  · exact .integerMul a b

private theorem comparison_applies {function : BuiltinFunctionId} {operation : Staged.Comparison}
    (selected : Staged.comparison? function = some operation) (a b : Int) :
    Dynamic.BuiltinApplies function [.integer a, .integer b] (.bool (Staged.applyComparison operation a b)) := by
  cases function <;> simp only [Staged.comparison?] at selected <;> try contradiction
  all_goals cases selected
  · exact .integerEq a b
  · exact .integerLt a b


private theorem conditional {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id condition yes no : ExpressionId} {node : ExpressionNode} {truth : Bool} {value : Dynamic.Value}
    (found : source.lookupExpression? id = some node) (form : node.form = .conditional condition yes no)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (test : Dynamic.ExpressionEvaluates program context evidence source environment heap condition (.bool truth) heap)
    (branch : Dynamic.ExpressionEvaluates program context evidence source environment heap (if truth then yes else no) value heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id value heap := by
  apply of_raw found coercions
  rw [form, requirements, coercions]
  cases truth
  · exact .conditionalFalse rfl test branch
  · exact .conditionalTrue rfl test branch

variable {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {solved : List SolvedRequirement} {actual : Staged.Environment}
  {environment : Dynamic.Environment} {heap : Dynamic.Heap}
  (ledger : context.solvedRequirements = solved) (environments : EnvironmentRep actual environment heap)

include ledger environments in
/-- The three mutually dependent checks yield independent source executions.
Validation-only children are retained, and only the selected branch executes. -/
theorem checked_meaning (fuel : Nat) :
    (∀ {id result}, Staged.IntegerChecked solved source actual true fuel id result →
      UsedValid context solved result.consumedRequirements →
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.integer result.value) heap) ∧
    (∀ {id result}, Staged.WordChecked solved source actual true fuel id result →
      UsedValid context solved result.consumedRequirements →
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.word result.value) heap) ∧
    (∀ {id result}, Staged.BoolChecked solved source actual true fuel id result →
      UsedValid context solved result.consumedRequirements →
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.bool result.value) heap) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intro id result checked valid <;> cases checked
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro id result checked valid
      cases checked with
      | literal found form accepted => exact integer_literal found form accepted ledger valid
      | «local» found form _ requirements coercions _ selected _ _ _ _ =>
        obtain ⟨location, cell, lookup, read, ordinary, initialized⟩ := environments _ _ selected
        apply of_raw found coercions
        rw [form, requirements, coercions]
        exact .local rfl lookup read ordinary initialized
      | group found form _ requirements coercions child =>
        exact group found form requirements coercions (ih.1 child valid)
      | binary found form operation validated leftChecked rightChecked =>
        have left := ih.1 leftChecked (valid.mono (by intro id member; exact List.mem_append_left _ member))
        have right := ih.1 rightChecked (valid.mono (by intro id member; exact List.mem_append_right _ member))
        exact builtin found form validated (.cons left (.cons right .nil)) (binary_applies operation _ _)
      | fromWord found form validated child =>
        exact builtin found form validated (.cons (ih.2.1 child valid) .nil) (.wordToInteger _)
      | conditional found form _ requirements coercions guardChecked yesChecked noChecked =>
        rename_i condition yes no node guardResult leftResult rightResult typed
        have guard := ih.2.2 guardChecked (valid.mono (by
          intro id member
          exact List.mem_append_left _ (List.mem_append_left _ member)))
        cases truth : guardResult.value with
        | false =>
          have branch := ih.1 (by simpa only [truth, Bool.true_and, Bool.not_false] using noChecked)
            (valid.mono (by intro id member; exact List.mem_append_right _ member))
          simpa only [truth, Bool.false_eq_true, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)
        | true =>
          have branch := ih.1 (by simpa only [truth, Bool.true_and] using yesChecked)
            (valid.mono (by intro id member; exact List.mem_append_left _ (List.mem_append_right _ member)))
          simpa only [truth, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)
    · intro id result checked valid
      cases checked with
      | literal found form accepted => exact word_literal found form accepted ledger valid
      | group found form _ requirements coercions child =>
        exact group found form requirements coercions (ih.2.1 child valid)
      | fromInteger found form validated child =>
        exact builtin found form validated (.cons (ih.1 child valid) .nil) (.wordFromInteger _)
      | conditional found form _ requirements coercions guardChecked yesChecked noChecked =>
        rename_i condition yes no node guardResult leftResult rightResult typed
        have guard := ih.2.2 guardChecked (valid.mono (by
          intro id member
          exact List.mem_append_left _ (List.mem_append_left _ member)))
        cases truth : guardResult.value with
        | false =>
          have branch := ih.2.1 (by simpa only [truth, Bool.true_and, Bool.not_false] using noChecked)
            (valid.mono (by intro id member; exact List.mem_append_right _ member))
          simpa only [truth, Bool.false_eq_true, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)
        | true =>
          have branch := ih.2.1 (by simpa only [truth, Bool.true_and] using yesChecked)
            (valid.mono (by intro id member; exact List.mem_append_left _ (List.mem_append_right _ member)))
          simpa only [truth, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)
    · intro id result checked valid
      cases checked with
      | literal found form _ requirements coercions _ =>
        apply of_raw found coercions
        rw [form, requirements, coercions]
        exact .builtinBoolean rfl
      | group found form _ requirements coercions child =>
        exact group found form requirements coercions (ih.2.2 child valid)
      | comparison found form operation validated leftChecked rightChecked =>
        have left := ih.1 leftChecked (valid.mono (by intro id member; exact List.mem_append_left _ member))
        have right := ih.1 rightChecked (valid.mono (by intro id member; exact List.mem_append_right _ member))
        exact builtin found form validated (.cons left (.cons right .nil)) (comparison_applies operation _ _)
      | conditional found form _ requirements coercions guardChecked yesChecked noChecked =>
        rename_i condition yes no node guardResult leftResult rightResult typed
        have guard := ih.2.2 guardChecked (valid.mono (by
          intro id member
          exact List.mem_append_left _ (List.mem_append_left _ member)))
        cases truth : guardResult.value with
        | false =>
          have branch := ih.2.2 (by simpa only [truth, Bool.true_and, Bool.not_false] using noChecked)
            (valid.mono (by intro id member; exact List.mem_append_right _ member))
          simpa only [truth, Bool.false_eq_true, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)
        | true =>
          have branch := ih.2.2 (by simpa only [truth, Bool.true_and] using yesChecked)
            (valid.mono (by intro id member; exact List.mem_append_left _ (List.mem_append_right _ member)))
          simpa only [truth, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)


/-- An empty compiler environment places no restriction on the source heap. -/
theorem EnvironmentRep.empty (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    EnvironmentRep [] environment heap := by
  intro id binding found
  change none = some binding at found
  contradiction

include ledger environments in
/-- Actual accepted Integer evaluation yields the exact validation/consumption
tree and an independent source execution, preserving the entire input heap. -/
theorem integer_of_accepted {fuel : Nat} {id : ExpressionId} {result : StagedIntegerEvaluation}
    (accepted : Staged.integer solved source actual true fuel id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.IntegerChecked solved source actual true fuel id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.integer result.value) heap := by
  have checked := Staged.integer_checked accepted
  exact ⟨checked, (checked_meaning ledger environments fuel).1 checked valid⟩

include ledger environments in
/-- Conversions use the same source Word carrier, including modulo conversion. -/
theorem word_of_accepted {fuel : Nat} {id : ExpressionId} {result : StagedWordEvaluation}
    (accepted : Staged.word solved source actual true fuel id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.WordChecked solved source actual true fuel id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.word result.value) heap := by
  have checked := Staged.word_checked accepted
  exact ⟨checked, (checked_meaning ledger environments fuel).2.1 checked valid⟩

include ledger environments in
/-- Comparisons and conditional selection follow the independent source rules. -/
theorem bool_of_accepted {fuel : Nat} {id : ExpressionId} {result : StagedBoolEvaluation}
    (accepted : Staged.bool solved source actual true fuel id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.BoolChecked solved source actual true fuel id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.bool result.value) heap := by
  have checked := Staged.bool_checked accepted
  exact ⟨checked, (checked_meaning ledger environments fuel).2.2 checked valid⟩

include ledger in
/-- The existing public Integer evaluator is sound for every accepted closed
fragment. Unused ledger rows and all source heap cells are retained. -/
theorem evaluateStagedInteger_sound {id : ExpressionId} {result : StagedIntegerEvaluation}
    (accepted : evaluateStagedInteger solved source id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.IntegerChecked solved source [] true (source.nodes.length + 1) id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.integer result.value) heap :=
  integer_of_accepted ledger (EnvironmentRep.empty environment heap) accepted valid

include ledger in
/-- The existing public Word evaluator returns its exact validation receipt and
same-heap source witness, without imposing validity on unused ledger rows. -/
theorem evaluateStagedWord_sound {id : ExpressionId} {result : StagedWordEvaluation}
    (accepted : evaluateStagedWord solved source id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.WordChecked solved source [] true (source.nodes.length + 1) id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.word result.value) heap :=
  word_of_accepted ledger (EnvironmentRep.empty environment heap) accepted valid

include ledger in
/-- Both branches are statically checked and consumed in order. The independent
source witness executes only the selected branch. -/
theorem evaluateStagedBool_sound {id : ExpressionId} {result : StagedBoolEvaluation}
    (accepted : evaluateStagedBool solved source id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.BoolChecked solved source [] true (source.nodes.length + 1) id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.bool result.value) heap :=
  bool_of_accepted ledger (EnvironmentRep.empty environment heap) accepted valid

end Solcore.SourceSemantics.CoreLowering.SourceStagedClosedEvaluationMeaning
