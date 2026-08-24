import Solcore.Surface.Multi.EbnfDelimiterRuntime

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- A checked retained-token EBNF recognition realizes its statically
verified delimiter effect on the exact recognized interval. -/
theorem EbnfRecognizes.delimiterRun
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {start finish : Boundary tokens}
    (recognized : EbnfRecognizes file tokens expression start finish)
    (before after : DelimiterStack)
    (effect : grammarDelimiterEffect? expression before = some after)
    (tokenOnly : grammarTokenOnly expression = true) :
    DelimiterRun tokens before start finish after := by
  refine EbnfRecognizes.rec
    (motive_1 := fun expression start finish _ =>
      ∀ before after,
        grammarDelimiterEffect? expression before = some after →
        grammarTokenOnly expression = true →
        DelimiterRun tokens before start finish after)
    (motive_2 := fun expressions start finish _ =>
      ∀ before after,
        grammarDelimiterEffects? expressions before = some after →
        grammarTokensOnly expressions = true →
        DelimiterRun tokens before start finish after)
    (motive_3 := fun element start finish _ =>
      ∀ before,
        grammarDelimiterEffect? element before = some before →
        grammarTokenOnly element = true →
        DelimiterRun tokens before start finish before)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    recognized before after effect tokenOnly
  · intro terminal matched before after effect tokenOnly
    exact matchedTerminal_delimiterRun matched
      (by simpa only [grammarDelimiterEffect?] using effect) tokenOnly
  · intro rule start finish body bodyRun before after effect tokenOnly
    have stackEq : before = after := Option.some.inj
      (by simpa only [grammarDelimiterEffect?] using effect)
    subst after
    have notModule : rule ≠ .module := of_decide_eq_true
      (by simpa only [grammarTokenOnly] using tokenOnly)
    have emptyRun := bodyRun [] []
      (grammarRule_delimiterEffect_empty rule)
      (grammarRule_tokenOnly rule notModule)
    simpa using emptyRun.appendStack before
  · intro children start finish body bodyRun before after effect tokenOnly
    exact bodyRun before after
      (by simpa only [grammarDelimiterEffect?] using effect)
      (by simpa only [grammarTokenOnly] using tokenOnly)
  · intro child start finish body bodyRun before after effect tokenOnly
    exact bodyRun before after
      (by simpa only [grammarDelimiterEffect?] using effect)
      (by simpa only [grammarTokenOnly] using tokenOnly)
  · intro branches branch start finish body bodyRun before after effect
      tokenOnly
    have member := List.get_mem branches branch
    have branchEffect := grammarDelimiterChoice_member
      (by simpa only [grammarDelimiterEffect?] using effect) member
    have allTokenOnly : grammarTokensOnly branches = true := by
      simpa only [grammarTokenOnly] using tokenOnly
    exact bodyRun before after branchEffect
      (grammarTokensOnly_member allTokenOnly member)
  · intro child cursor before after effect tokenOnly
    have exactEffect := grammarRepeatedEffect_exact
      (expression := .optional child) (child := child)
      (by simp only [grammarDelimiterEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact .nil before cursor
  · intro child start finish body bodyRun before after effect tokenOnly
    have exactEffect := grammarRepeatedEffect_exact
      (expression := .optional child) (child := child)
      (by simp only [grammarDelimiterEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact bodyRun before before childEffect
      (by simpa only [grammarTokenOnly] using tokenOnly)
  · intro child cursor before after effect tokenOnly
    have exactEffect := grammarRepeatedEffect_exact
      (expression := .star child) (child := child)
      (by simp only [grammarDelimiterEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact .nil before cursor
  · intro child start middle finish head tail headRun tailRun before after
      effect tokenOnly
    have exactEffect := grammarRepeatedEffect_exact
      (expression := .star child) (child := child)
      (by simp only [grammarDelimiterEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact (headRun before before childEffect
      (by simpa only [grammarTokenOnly] using tokenOnly)).append
        (tailRun before before effect tokenOnly)
  · intro child start finish head headRun before after effect tokenOnly
    have exactEffect := grammarRepeatedEffect_exact
      (expression := .plus child) (child := child)
      (by simp only [grammarDelimiterEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact headRun before before childEffect
      (by simpa only [grammarTokenOnly] using tokenOnly)
  · intro child start middle finish head tail headRun tailRun before after
      effect tokenOnly
    have exactEffect := grammarRepeatedEffect_exact
      (expression := .plus child) (child := child)
      (by simp only [grammarDelimiterEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact (headRun before before childEffect
      (by simpa only [grammarTokenOnly] using tokenOnly)).append
        (tailRun before before effect tokenOnly)
  · intro element cursor before after effect tokenOnly
    have exactEffect := grammarRepeatedEffect_exact
      (expression := .list0 element) (child := element)
      (by simp only [grammarDelimiterEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact .nil before cursor
  · intro element start middle finish head tail headRun tailRun before after
      effect tokenOnly
    have exactEffect := grammarRepeatedEffect_exact
      (expression := .list0 element) (child := element)
      (by simp only [grammarDelimiterEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact (headRun before before childEffect
      (by simpa only [grammarTokenOnly] using tokenOnly)).append
        (tailRun before childEffect
          (by simpa only [grammarTokenOnly] using tokenOnly))
  · intro element start middle finish head tail headRun tailRun before after
      effect tokenOnly
    have exactEffect := grammarRepeatedEffect_exact
      (expression := .list1 element) (child := element)
      (by simp only [grammarDelimiterEffect?]; rfl) effect
    rcases exactEffect with ⟨afterEq, childEffect⟩
    subst after
    exact (headRun before before childEffect
      (by simpa only [grammarTokenOnly] using tokenOnly)).append
        (tailRun before childEffect
          (by simpa only [grammarTokenOnly] using tokenOnly))
  · intro cursor before after effect tokenOnly
    have stackEq : before = after := Option.some.inj
      (by simpa only [grammarDelimiterEffects?] using effect)
    subst after
    exact .nil before cursor
  · intro expression rest start middle finish head tail headRun tailRun
      before after effect tokenOnly
    simp only [grammarTokensOnly, Bool.and_eq_true] at tokenOnly
    simp only [grammarDelimiterEffects?] at effect
    generalize headEq : grammarDelimiterEffect? expression before = result
      at effect
    cases result with
    | none => contradiction
    | some between =>
        exact (headRun before between headEq tokenOnly.1).append
          (tailRun between after effect tokenOnly.2)
  · intro element cursor before effect tokenOnly
    exact .nil before cursor
  · intro element start afterComma middle finish comma commaStart commaFinish
      head tail headRun tailRun before effect tokenOnly
    have commaRun := matchedTerminal_delimiterRun comma
      (before := before) (after := before)
      (by simp [grammarTerminalDelimiterStep?])
      (by simp [grammarTokenOnly])
    rw [commaStart, commaFinish] at commaRun
    exact commaRun.append
      ((headRun before before effect tokenOnly).append
        (tailRun before effect tokenOnly))

/-- Every recognized non-root source rule has equal delimiter depth at its
two boundaries. -/
theorem EbnfRecognizes.sourceRule_sameDelimiterDepth
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {start finish : Boundary tokens}
    (notModule : rule ≠ .module)
    (recognized : EbnfRecognizes file tokens (m2cV1.rhs rule) start finish) :
    SameDelimiterDepth tokens start finish :=
  recognized.delimiterRun [] [] (grammarRule_delimiterEffect_empty rule)
    (grammarRule_tokenOnly rule notModule)

end Solcore.Surface.Multi
