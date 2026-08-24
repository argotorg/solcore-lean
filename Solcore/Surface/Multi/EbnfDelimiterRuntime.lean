import Solcore.Surface.Multi.EbnfDelimiterBalance

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

mutual

/-- Whether an EBNF expression consumes retained tokens only. -/
def grammarTokenOnly : EbnfExpr → Bool
  | .atom (.terminal .endOfFile) => false
  | .atom (.terminal _) => true
  | .atom (.nonterminal rule) => decide (rule ≠ .module)
  | .sequence children
  | .choice children => grammarTokensOnly children
  | .group child
  | .optional child
  | .star child
  | .plus child
  | .list0 child
  | .list1 child => grammarTokenOnly child

/-- Pointwise retained-token check for displayed children. -/
def grammarTokensOnly : List EbnfExpr → Bool
  | [] => true
  | child :: rest => grammarTokenOnly child && grammarTokensOnly rest

end

/-- The fixed source rows other than `module` consume retained tokens only. -/
def grammarRulesTokenOnlyBool : Bool :=
  allGrammarRuleIds.all fun rule =>
    decide (rule = .module) || grammarTokenOnly (m2cV1.rhs rule)

set_option linter.unusedSimpArgs false in
theorem grammarRulesTokenOnlyBool_eq_true :
    grammarRulesTokenOnlyBool = true := by
  simp [grammarRulesTokenOnlyBool, allGrammarRuleIds, grammarTokenOnly,
    grammarTokensOnly, m2cV1, m2cV1Rhs, Grammar.terminal,
    Grammar.hardKeyword, Grammar.contextualKeyword, Grammar.pragmaName,
    Grammar.symbol, Grammar.category, Grammar.nonterminal, Grammar.sequence,
    Grammar.choice, Grammar.group, Grammar.optional, Grammar.star,
    Grammar.plus, Grammar.list0, Grammar.list1, Grammar.identifier,
    Grammar.pathComponent]

/-- Every non-root source row is retained-token-only. -/
theorem grammarRule_tokenOnly
    (rule : GrammarRuleId) (notModule : rule ≠ .module) :
    grammarTokenOnly (m2cV1.rhs rule) = true := by
  have accepted := (List.all_eq_true.mp
    grammarRulesTokenOnlyBool_eq_true) rule
      (by cases rule <;> simp [allGrammarRuleIds])
  simp [notModule] at accepted
  exact accepted

/-- Compose adjacent exact delimiter runs. -/
theorem DelimiterRun.append
    {tokens : List Token} {first middle last : Boundary tokens}
    {before between after : DelimiterStack}
    (left : DelimiterRun tokens before first middle between)
    (right : DelimiterRun tokens between middle last after) :
    DelimiterRun tokens before first last after := by
  induction left with
  | nil => exact right
  | cons before next finish cursor start endCursor token atStart lookup
      step rest induction =>
      exact .cons before next after cursor start last token atStart lookup step
        (induction right)

private theorem DelimiterStep.append
    {before after : DelimiterStack} {token : TokenKind}
    (step : DelimiterStep before token after) (suffix : DelimiterStack) :
    DelimiterStep (before ++ suffix) token (after ++ suffix) := by
  cases token <;> simp_all [DelimiterStep]
  case symbol symbol =>
    cases symbol <;> simp_all
    all_goals
      cases before with
      | nil => simp_all
      | cons head tail => cases head <;> simp_all

/-- Add an untouched outer delimiter suffix to every stack in a run. -/
theorem DelimiterRun.appendStack
    {tokens : List Token} {before after : DelimiterStack}
    {start finish : Boundary tokens}
    (run : DelimiterRun tokens before start finish after)
    (suffix : DelimiterStack) :
    DelimiterRun tokens (before ++ suffix) start finish (after ++ suffix) := by
  induction run with
  | nil => exact .nil _ _
  | cons before next finishStack cursor start endCursor token atStart lookup
      step rest induction =>
      exact .cons (before ++ suffix) (next ++ suffix)
        (finishStack ++ suffix) cursor start endCursor token atStart lookup
        (step.append suffix) induction

set_option linter.unusedSimpArgs false in
theorem matchedTerminal_delimiterRun
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol} (matched : MatchedTerminal file tokens terminal)
    {before after : DelimiterStack}
    (effect : grammarTerminalDelimiterStep? before terminal = some after)
    (tokenOnly : grammarTokenOnly (.atom (.terminal terminal)) = true) :
    DelimiterRun tokens before matched.cursor.beforeBoundary
      matched.cursor.afterBoundary after := by
  cases matched with
  | mk cursor value span terminalAt matchedEvidence =>
      cases terminalAt with
      | retained token inRange lookup valid =>
          refine .cons before after after cursor cursor.beforeBoundary
            cursor.afterBoundary token rfl lookup ?_ (.nil after _)
          cases terminal <;> simp_all [TerminalMatches,
            grammarTerminalDelimiterStep?, DelimiterStep, grammarTokenOnly]
          case symbol symbol =>
            cases symbol <;> simp_all
            all_goals
              cases before with
              | nil => simp_all
              | cons head tail => cases head <;> simp_all
          case category category =>
            have same : after = before := effect.symm
            subst after
            cases category with
            | identifier =>
                obtain ⟨text, payload, parsed, parsedOk⟩ := matchedEvidence
                rw [payload]
                simp [DelimiterStep]
            | pathComponent =>
                rcases matchedEvidence with
                  ⟨text, payload, parsed, parsedOk⟩ |
                  ⟨keyword, payload, parsed, parsedOk⟩
                · rw [payload]
                  simp [DelimiterStep]
                · rw [payload]
                  simp [DelimiterStep]
            | decimalLiteral =>
                obtain ⟨spelling, digits, payload⟩ := matchedEvidence
                rw [payload]
                simp [DelimiterStep]
            | hexadecimalLiteral =>
                obtain ⟨spelling, digits, payload⟩ := matchedEvidence
                rw [payload]
                simp [DelimiterStep]
            | stringLiteral =>
                obtain ⟨spelling, decoded, payload⟩ := matchedEvidence
                rw [payload]
                simp [DelimiterStep]
            | assemblyBlock =>
                obtain ⟨slice, payload⟩ := matchedEvidence
                rw [payload]
                simp [DelimiterStep]
      | endOfFile atEnd =>
          cases terminal with
          | hardKeyword keyword => exact False.elim matchedEvidence
          | contextualKeyword keyword => exact False.elim matchedEvidence
          | pragmaName kind => exact False.elim matchedEvidence
          | symbol symbol => exact False.elim matchedEvidence
          | category category =>
              cases category <;> exact False.elim matchedEvidence
          | endOfFile => exact Bool.noConfusion tokenOnly

theorem grammarTokensOnly_member
    {expressions : List EbnfExpr} {expression : EbnfExpr}
    (checked : grammarTokensOnly expressions = true)
    (member : expression ∈ expressions) :
    grammarTokenOnly expression = true := by
  induction expressions with
  | nil => simp at member
  | cons head rest induction =>
      simp only [List.mem_cons] at member
      simp [grammarTokensOnly] at checked
      rcases member with rfl | member
      · exact checked.1
      · exact induction checked.2 member

theorem grammarDelimiterEffectsAgree_member
    {branches : List EbnfExpr} {branch : EbnfExpr}
    {before after : DelimiterStack}
    (agrees : grammarDelimiterEffectsAgree branches before after = true)
    (member : branch ∈ branches) :
    grammarDelimiterEffect? branch before = some after := by
  induction branches with
  | nil => simp at member
  | cons head rest induction =>
      simp only [List.mem_cons] at member
      simp [grammarDelimiterEffectsAgree] at agrees
      rcases member with rfl | member
      · exact agrees.1
      · exact induction agrees.2 member

theorem grammarDelimiterChoice_member
    {branches : List EbnfExpr} {branch : EbnfExpr}
    {before after : DelimiterStack}
    (computed : grammarDelimiterChoicesEffect? branches before = some after)
    (member : branch ∈ branches) :
    grammarDelimiterEffect? branch before = some after := by
  cases branches with
  | nil => simp [grammarDelimiterChoicesEffect?] at computed
  | cons head rest =>
      simp only [grammarDelimiterChoicesEffect?] at computed
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
          · exact grammarDelimiterEffectsAgree_member agrees member

theorem grammarRepeatedEffect_exact
    {expression child : EbnfExpr} {before after : DelimiterStack}
    (unfolded : grammarDelimiterEffect? expression before =
      (match grammarDelimiterEffect? child before with
       | some childAfter =>
           if childAfter = before then some before else none
       | none => none))
    (computed : grammarDelimiterEffect? expression before = some after) :
    after = before ∧ grammarDelimiterEffect? child before = some before := by
  rw [unfolded] at computed
  generalize childEq : grammarDelimiterEffect? child before = result at computed
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

end Solcore.Surface.Multi
