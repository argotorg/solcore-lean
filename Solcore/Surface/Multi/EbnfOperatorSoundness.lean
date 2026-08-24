import Solcore.Surface.Multi.OperatorSafeDelimiterRun

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem grammarOperatorEffectsAgree_member
    {level : NonAssociativeLevel} {branches : List EbnfExpr}
    {branch : EbnfExpr} {before after : DelimiterStack}
    (agrees : grammarOperatorEffectsAgree level branches before after = true)
    (member : branch ∈ branches) :
    grammarOperatorEffect? level branch before = some after := by
  induction branches with
  | nil => simp at member
  | cons head rest induction =>
      simp only [List.mem_cons] at member
      simp [grammarOperatorEffectsAgree] at agrees
      rcases member with rfl | member
      · exact agrees.1
      · exact induction agrees.2 member

private theorem grammarOperatorChoice_member
    {level : NonAssociativeLevel} {branches : List EbnfExpr}
    {branch : EbnfExpr} {before after : DelimiterStack}
    (computed : grammarOperatorChoicesEffect? level branches before =
      some after)
    (member : branch ∈ branches) :
    grammarOperatorEffect? level branch before = some after := by
  cases branches with
  | nil => simp [grammarOperatorChoicesEffect?] at computed
  | cons head rest =>
      simp only [grammarOperatorChoicesEffect?] at computed
      split at computed
      case h_1 => contradiction
      case h_2 firstAfter firstEffect =>
        split at computed
        case isFalse => contradiction
        case isTrue agrees =>
          have afterEq := Option.some.inj computed
          subst after
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact firstEffect
          · exact grammarOperatorEffectsAgree_member agrees member

private theorem grammarOperatorRepeatedEffect_exact
    {level : NonAssociativeLevel} {expression child : EbnfExpr}
    {before after : DelimiterStack}
    (unfolded : grammarOperatorEffect? level expression before =
      (match grammarOperatorEffect? level child before with
       | some childAfter =>
           if childAfter = before then some before else none
       | none => none))
    (computed : grammarOperatorEffect? level expression before = some after) :
    after = before ∧
      grammarOperatorEffect? level child before = some before := by
  rw [unfolded] at computed
  generalize childEq : grammarOperatorEffect? level child before = result
    at computed
  cases result with
  | none => contradiction
  | some childAfter =>
      change (if childAfter = before then some before else none) =
        some after at computed
      by_cases same : childAfter = before
      · rw [if_pos same] at computed
        subst childAfter
        exact ⟨(Option.some.inj computed).symm, rfl⟩
      · rw [if_neg same] at computed
        contradiction

/-- A recognition accepted by the operator skeleton realizes an annotated
delimiter run which excludes the selected operator at empty depth. -/
theorem EbnfRecognizes.operatorSafeDelimiterRun
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {start finish : Boundary tokens}
    (recognized : EbnfRecognizes file tokens expression start finish)
    (level : NonAssociativeLevel) (before after : DelimiterStack)
    (effect : grammarOperatorEffect? level expression before = some after) :
    OperatorSafeDelimiterRun level tokens before start finish after := by
  refine EbnfRecognizes.rec
    (motive_1 := fun expression start finish _ =>
      ∀ level before after,
        grammarOperatorEffect? level expression before = some after →
        OperatorSafeDelimiterRun level tokens before start finish after)
    (motive_2 := fun expressions start finish _ =>
      ∀ level before after,
        grammarOperatorEffects? level expressions before = some after →
        OperatorSafeDelimiterRun level tokens before start finish after)
    (motive_3 := fun element start finish _ =>
      ∀ level before,
        grammarOperatorEffect? level element before = some before →
        OperatorSafeDelimiterRun level tokens before start finish before)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    recognized level before after effect
  · intro terminal matched level before after effect
    exact matchedTerminal_operatorSafeDelimiterRun matched effect
  · intro rule start finish body bodyRun level before after effect
    have notModule : rule ≠ .module := by
      intro equality
      subst rule
      simp [grammarOperatorEffect?] at effect
    by_cases empty : before = []
    · subst before
      have safe : grammarOperatorSafeRule level rule = true := by
        cases safeEq : grammarOperatorSafeRule level rule with
        | false =>
            simp [grammarOperatorEffect?, notModule, safeEq] at effect
        | true => rfl
      have stackEq : [] = after := Option.some.inj
        (by simpa [grammarOperatorEffect?, notModule, safe] using effect)
      subst after
      exact bodyRun level [] []
        (grammarOperatorSafeRule_effect level rule safe)
    · have stackEq : before = after := Option.some.inj
        (by simpa [grammarOperatorEffect?, notModule, empty] using effect)
      subst after
      have ordinary := body.delimiterRun [] []
        (grammarRule_delimiterEffect_empty rule)
        (grammarRule_tokenOnly rule notModule)
      simpa using ordinary.operatorSafeAppendStack level before empty
  · intro children start finish body bodyRun level before after effect
    exact bodyRun level before after
      (by simpa only [grammarOperatorEffect?] using effect)
  · intro child start finish body bodyRun level before after effect
    exact bodyRun level before after
      (by simpa only [grammarOperatorEffect?] using effect)
  · intro branches branch start finish body bodyRun level before after effect
    have member := List.get_mem branches branch
    exact bodyRun level before after
      (grammarOperatorChoice_member
        (by simpa only [grammarOperatorEffect?] using effect) member)
  · intro child cursor level before after effect
    have exactEffect := grammarOperatorRepeatedEffect_exact
      (expression := .optional child) (child := child)
      (by simp only [grammarOperatorEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact .nil before cursor
  · intro child start finish body bodyRun level before after effect
    have exactEffect := grammarOperatorRepeatedEffect_exact
      (expression := .optional child) (child := child)
      (by simp only [grammarOperatorEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact bodyRun level before before childEffect
  · intro child cursor level before after effect
    have exactEffect := grammarOperatorRepeatedEffect_exact
      (expression := .star child) (child := child)
      (by simp only [grammarOperatorEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact .nil before cursor
  · intro child start middle finish head tail headRun tailRun level before
      after effect
    have exactEffect := grammarOperatorRepeatedEffect_exact
      (expression := .star child) (child := child)
      (by simp only [grammarOperatorEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact (headRun level before before childEffect).append
      (tailRun level before before effect)
  · intro child start finish head headRun level before after effect
    have exactEffect := grammarOperatorRepeatedEffect_exact
      (expression := .plus child) (child := child)
      (by simp only [grammarOperatorEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact headRun level before before childEffect
  · intro child start middle finish head tail headRun tailRun level before
      after effect
    have exactEffect := grammarOperatorRepeatedEffect_exact
      (expression := .plus child) (child := child)
      (by simp only [grammarOperatorEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact (headRun level before before childEffect).append
      (tailRun level before before effect)
  · intro element cursor level before after effect
    have exactEffect := grammarOperatorRepeatedEffect_exact
      (expression := .list0 element) (child := element)
      (by simp only [grammarOperatorEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact .nil before cursor
  · intro element start middle finish head tail headRun tailRun level before
      after effect
    have exactEffect := grammarOperatorRepeatedEffect_exact
      (expression := .list0 element) (child := element)
      (by simp only [grammarOperatorEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact (headRun level before before childEffect).append
      (tailRun level before childEffect)
  · intro element start middle finish head tail headRun tailRun level before
      after effect
    have exactEffect := grammarOperatorRepeatedEffect_exact
      (expression := .list1 element) (child := element)
      (by simp only [grammarOperatorEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact (headRun level before before childEffect).append
      (tailRun level before childEffect)
  · intro cursor level before after effect
    have stackEq : before = after := Option.some.inj
      (by simpa only [grammarOperatorEffects?] using effect)
    subst after
    exact .nil before cursor
  · intro expression rest start middle finish head tail headRun tailRun level
      before after effect
    simp only [grammarOperatorEffects?] at effect
    generalize headEq : grammarOperatorEffect? level expression before = result
      at effect
    cases result with
    | none => contradiction
    | some between =>
        exact (headRun level before between headEq).append
          (tailRun level between after effect)
  · intro element cursor level before effect
    exact .nil before cursor
  · intro element start afterComma middle finish comma commaStart commaFinish
      head tail headRun tailRun level before effect
    have commaRun := matchedTerminal_operatorSafeDelimiterRun comma
      (level := level) (before := before) (after := before) (by
        simp [grammarOperatorEffect?, grammarForbiddenTerminal,
          grammarTerminalDelimiterStep?])
    rw [commaStart, commaFinish] at commaRun
    exact commaRun.append
      ((headRun level before before effect).append
        (tailRun level before effect))

/-- The lower-precedence operand rule has an operator-safe empty-stack run. -/
theorem EbnfRecognizes.operand_operatorSafeDelimiterRun
    {file : WorkspaceFile} {tokens : List Token}
    {level : NonAssociativeLevel} {start finish : Boundary tokens}
    (recognized : EbnfRecognizes file tokens
      (m2cV1.rhs level.operandRule) start finish) :
    OperatorSafeDelimiterRun level tokens [] start finish [] :=
  recognized.operatorSafeDelimiterRun level [] []
    (grammarOperatorSafeRule_effect level level.operandRule
      (grammarOperatorSafeRule_operand level))

end Solcore.Surface.Multi
