import Solcore.Surface.Multi.NonAssociativeInvariantBridge

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

@[simp] theorem sequence2View_pair_first
    {file : WorkspaceFile} {tokens : List Token}
    (first second : EbnfExpr)
    (left : EbnfValue file tokens first)
    (right : EbnfValue file tokens second) :
    (EbnfValue.sequence2View first second
      (EbnfValue.sequence [first, second]
        (EbnfValues.cons first [second] left
          (EbnfValues.cons second [] right EbnfValues.nil)))).1 = left := by
  have rebuilt := EbnfValue.sequence2_of_view first second
    (EbnfValue.sequence [first, second]
      (EbnfValues.cons first [second] left
        (EbnfValues.cons second [] right EbnfValues.nil)))
  have valuesEq := EbnfValue.sequence_injective _ rebuilt
  exact (EbnfValues.cons_injective _ _ valuesEq).1

@[simp] theorem EbnfValue.ruleView_ruleAtom
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (value : RuleValue rule) :
    EbnfValue.ruleView (file := file) (tokens := tokens) rule
      (EbnfValue.ruleAtom (file := file) (tokens := tokens) rule value) =
        value := by
  apply EbnfValue.ruleAtom_injective rule
  exact EbnfValue.rule_of_view rule (EbnfValue.ruleAtom rule value)

/-- The lower-precedence value selected by the first child of a
nonassociative source-rule input. -/
def nonAssociativeOperandValue
    {file : WorkspaceFile} {tokens : List Token} :
    (level : NonAssociativeLevel) →
      EbnfValue file tokens (m2cV1.rhs level.rule) → RuleValue level.rule
  | .relational, input =>
      EbnfValue.ruleView .bitOr
        (EbnfValue.sequence2View
          (.atom (.nonterminal .bitOr))
          (.optional NonAssociativeLevel.relational.tailExpr) input).1
  | .equality, input =>
      EbnfValue.ruleView .relational
        (EbnfValue.sequence2View
          (.atom (.nonterminal .relational))
          (.optional NonAssociativeLevel.equality.tailExpr) input).1

/-- The exact safety condition needed only when the outer optional is absent:
the lower-precedence operand must not already expose this level's operator. -/
def NonAssociativePassThroughInputSafe
    {file : WorkspaceFile} {tokens : List Token}
    (level : NonAssociativeLevel)
    (input : EbnfValue file tokens (m2cV1.rhs level.rule)) : Prop :=
  ¬ NonAssociativeInputPresent level input →
    ∀ first, ¬ CompletedNonAssociativeValue level
      (nonAssociativeOperandValue level input) first

/-- Completed output reverses to a present optional once the sole
pass-through case is ruled out on its exact lower-precedence input. -/
theorem RuleReduction.nonAssociative_input_present_of_completed_of_safe
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {level : NonAssociativeLevel}
    {input : EbnfValue file tokens (m2cV1.rhs level.rule)}
    {output : RuleValue level.rule}
    (reduces : RuleReduction file tokens level.rule
      origin finish input output)
    (safe : NonAssociativePassThroughInputSafe level input)
    {first : Located InfixOperator}
    (completed : CompletedNonAssociativeValue level output first) :
    NonAssociativeInputPresent level input := by
  cases level <;> cases reduces
  case relational.relationalNone =>
    apply (safe (by
      rintro ⟨presentLeft, tail, inputEq⟩
      simp only [NonAssociativeLevel.tailExpr] at inputEq
      have outer := EbnfValue.sequence_injective _ inputEq
      rcases EbnfValues.cons_injective _ _ outer with ⟨_, rest⟩
      rcases EbnfValues.cons_injective _ _ rest with ⟨optionalEq, _⟩
      have impossible := EbnfValue.optional_injective _ optionalEq
      contradiction) first (by
      simpa [nonAssociativeOperandValue, NonAssociativeLevel.tailExpr,
        EbnfExpr.children] using completed)).elim
  case equality.equalityNone =>
    apply (safe (by
      rintro ⟨presentLeft, tail, inputEq⟩
      simp only [NonAssociativeLevel.tailExpr] at inputEq
      have outer := EbnfValue.sequence_injective _ inputEq
      rcases EbnfValues.cons_injective _ _ outer with ⟨_, rest⟩
      rcases EbnfValues.cons_injective _ _ rest with ⟨optionalEq, _⟩
      have impossible := EbnfValue.optional_injective _ optionalEq
      contradiction) first (by
      simpa [nonAssociativeOperandValue, NonAssociativeLevel.tailExpr,
        EbnfExpr.children] using completed)).elim
  all_goals exact ⟨_, _, rfl⟩

/-- The semantic safety residual is restricted to inputs actually assembled
by coherent canonical root reductions, avoiding the unrestricted artificial
`relationalNone` counterexample. -/
def CoherentNonAssociativePassThroughSafe
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) : Prop :=
  ∀ (level : NonAssociativeLevel) (origin finish : Boundary tokens)
      (context : GuardContext tokens)
      (priorValues : PrefixValues file tokens
        (CanonicalCompleteRootItem tokens level.rule origin finish context))
      (complete : CompleteItem
        (CanonicalCompleteRootItem tokens level.rule origin finish context).raw),
    CoherentPrefix file tokens memo correct final
        (CanonicalCompleteRootItem tokens level.rule origin finish context)
        priorValues →
      NonAssociativePassThroughInputSafe level
        (RootAction.unpack level.rule
          (PrefixValues.fullValue
            (CanonicalCompleteRootItem tokens level.rule origin finish context)
            complete priorValues))

/-- Coherent reduction inversion exposes the exact source-rule input and,
under pass-through safety, proves that input's outer optional is present. -/
theorem coherentReduction_nonAssociative_inputPresent_of_completed
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (safe : CoherentNonAssociativePassThroughSafe
      file tokens memo correct final)
    (level : NonAssociativeLevel) (origin finish : Boundary tokens)
    (context : GuardContext tokens) (output : RuleValue level.rule)
    (reduction : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens level.rule origin finish context)
      output)
    (completed : ∃ first,
      CompletedNonAssociativeValue level output first) :
    ∃ input : EbnfValue file tokens (m2cV1.rhs level.rule),
      RuleReduction file tokens level.rule origin finish input output ∧
      NonAssociativeInputPresent level input := by
  rcases completed with ⟨first, completed⟩
  cases reduction with
  | reduce item priorValues output reached complete coherent action =>
      have inputSafe := safe level origin finish context priorValues
        complete coherent
      have reduces := (actionReduces_eleven_shapes_exact.mp action)
      have exactReduces : RuleReduction file tokens level.rule origin finish
          (RootAction.unpack level.rule
            (PrefixValues.fullValue
              (CanonicalCompleteRootItem tokens level.rule origin finish context)
              complete priorValues)) output := by
        simpa [CanonicalCompleteRootItem] using reduces
      exact ⟨_, exactReduces,
        exactReduces.nonAssociative_input_present_of_completed_of_safe
          inputSafe completed⟩

/-- The remaining structural inversion after semantic pass-through has been
removed: a coherent root whose exact reduction input is present exposes the
corresponding reached present-optional completion. -/
def CoherentNonAssociativePresentInputHasPresentCompletion
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) : Prop :=
  ∀ (level : NonAssociativeLevel) (origin cursor : Boundary tokens)
      (context : GuardContext tokens)
      (priorValues : PrefixValues file tokens
        (CanonicalCompleteRootItem tokens level.rule origin cursor context))
      (complete : CompleteItem
        (CanonicalCompleteRootItem tokens level.rule origin cursor context).raw),
    CoherentPrefix file tokens memo correct final
        (CanonicalCompleteRootItem tokens level.rule origin cursor context)
        priorValues →
    NonAssociativeInputPresent level
      (RootAction.unpack level.rule
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens level.rule origin cursor context)
          complete priorValues)) →
    ∃ (rootWaiting sequence : ContextualItemKey tokens)
        (rootShared : Boundary tokens)
        (sequenceWaiting optional : ContextualItemKey tokens)
        (optionalShared : Boundary tokens) (site : OptionalSite),
      ContextualEdgeReach file tokens memo correct final
          (.completed rootWaiting sequence
            (CanonicalCompleteRootItem tokens level.rule origin cursor context)
            rootShared) ∧
        ContextualEdgeReach file tokens memo correct final
          (.completed sequenceWaiting optional sequence optionalShared) ∧
        optional.raw.production = .opt site .some

/-- Semantic pass-through safety and the now-pure structural inversion imply
the original completed-value-to-present-completion residual. -/
theorem coherentNonAssociativeCompletedHasPresentCompletion_of_safe
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (safe : CoherentNonAssociativePassThroughSafe
      file tokens memo correct final)
    (inversion : CoherentNonAssociativePresentInputHasPresentCompletion
      file tokens memo correct final) :
    CoherentNonAssociativeCompletedHasPresentCompletion
      file tokens memo correct final := by
  intro level origin cursor context output reduction completed
  rcases completed with ⟨first, completed⟩
  cases reduction with
  | reduce _ priorValues _ _ complete coherent action =>
      have inputSafe := safe level origin cursor context priorValues
        complete coherent
      have reduces := actionReduces_eleven_shapes_exact.mp action
      have exactReduces : RuleReduction file tokens level.rule origin cursor
          (RootAction.unpack level.rule
            (PrefixValues.fullValue
              (CanonicalCompleteRootItem tokens level.rule origin cursor context)
              complete priorValues)) output := by
        simpa [CanonicalCompleteRootItem] using reduces
      exact inversion level origin cursor context priorValues complete coherent
        (exactReduces.nonAssociative_input_present_of_completed_of_safe
          inputSafe completed)

end Solcore.Surface.Multi
