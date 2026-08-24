import Solcore.Surface.Multi.EbnfOperatorSoundness
import Solcore.Surface.Multi.OperandBoundaryExclusion

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem delimiterStep_unique
    {before left right : DelimiterStack} {token : TokenKind}
    (leftStep : DelimiterStep before token left)
    (rightStep : DelimiterStep before token right) :
    left = right := by
  cases token <;> simp_all [DelimiterStep]
  case symbol symbol =>
    cases symbol <;> simp_all
    all_goals
      cases before with
      | nil => simp_all
      | cons head tail => cases head <;> simp_all

private theorem delimiterRun_ordered
    {tokens : List Token} {before after : DelimiterStack}
    {start finish : Boundary tokens}
    (run : DelimiterRun tokens before start finish after) :
    start.val ≤ finish.val := by
  induction run with
  | nil => exact Nat.le_refl _
  | cons before next finishStack cursor start endCursor token atStart lookup
      step rest induction =>
      have atStartValue := congrArg Fin.val atStart
      change cursor.val = start.val at atStartValue
      have restStart : cursor.val + 1 ≤ endCursor.val := induction
      omega

private theorem operatorSafeStep_excludesMatched
    {file : WorkspaceFile} {tokens : List Token}
    {level : NonAssociativeLevel} {before : DelimiterStack}
    {cursor : TerminalCursor tokens} {start : Boundary tokens}
    {token : Token} {symbol : Symbol}
    (atStart : cursor.beforeBoundary = start)
    (lookup : tokens[cursor.val]? = some token)
    (allowed : before = [] →
      grammarForbiddenTokenKind level token.payload = false)
    (beforeEmpty : before = [])
    (matched : MatchedTerminal file tokens (.symbol symbol))
    (matchedAt : matched.cursor.beforeBoundary = start)
    (forbidden :
      grammarForbiddenTokenKind level (.symbol symbol) = true) : False := by
  have cursorEq : cursor = matched.cursor := by
    apply Fin.ext
    have boundaryEq : cursor.beforeBoundary = matched.cursor.beforeBoundary :=
      atStart.trans matchedAt.symm
    exact congrArg (fun value : Boundary tokens => value.val) boundaryEq
  subst cursor
  cases matched with
  | mk matchedCursor value span terminalAt matchedEvidence =>
      cases terminalAt with
      | retained matchedToken inRange matchedLookup valid =>
          have tokenEq : token = matchedToken := Option.some.inj
            (lookup.symm.trans matchedLookup)
          subst matchedToken
          have payload : token.payload = .symbol symbol := by
            simpa [TerminalMatches] using matchedEvidence
          have excluded := allowed beforeEmpty
          rw [payload, forbidden] at excluded
          contradiction
      | endOfFile atEnd =>
          exact False.elim matchedEvidence

/-- An operator-safe long run cannot pass a forbidden operator at a boundary
already reached at empty delimiter depth. -/
theorem OperatorSafeDelimiterRun.excludesMatchedAtSameDepth
    {file : WorkspaceFile} {tokens : List Token}
    {level : NonAssociativeLevel} {origin split finish : Boundary tokens}
    {initial final : DelimiterStack} {symbol : Symbol}
    (long : OperatorSafeDelimiterRun level tokens initial origin finish final)
    (short : DelimiterRun tokens initial origin split [])
    (matched : MatchedTerminal file tokens (.symbol symbol))
    (matchedAt : matched.cursor.beforeBoundary = split)
    (forbidden :
      grammarForbiddenTokenKind level (.symbol symbol) = true)
    (later : split.val < finish.val) : False := by
  induction long generalizing split with
  | nil stack cursor =>
      have ordered := delimiterRun_ordered short
      omega
  | cons before after finishStack cursor start endCursor token atStart lookup
      step allowed rest induction =>
      cases short with
      | nil =>
          exact operatorSafeStep_excludesMatched atStart lookup allowed rfl
            matched matchedAt forbidden
      | cons shortBefore shortAfter shortFinish shortCursor shortStart
          shortEnd shortToken shortAtStart shortLookup shortStep shortRest =>
          have cursorEq : cursor = shortCursor := by
            apply Fin.ext
            have boundaryEq : cursor.beforeBoundary =
                shortCursor.beforeBoundary :=
              atStart.trans shortAtStart.symm
            exact congrArg (fun value : Boundary tokens => value.val)
              boundaryEq
          subst shortCursor
          have tokenEq : token = shortToken := Option.some.inj
            (lookup.symm.trans shortLookup)
          subst shortToken
          have afterEq : after = shortAfter :=
            delimiterStep_unique step shortStep
          subst shortAfter
          exact induction shortRest matchedAt later

/-- The six constructors of a found nonassociative operator are all rejected
by the corresponding operator-safe run. -/
theorem OperatorSafeDelimiterRun.excludesFoundAtSameDepth
    {file : WorkspaceFile} {tokens : List Token}
    {level : NonAssociativeLevel} {origin split finish : Boundary tokens}
    {operator : Located InfixOperator}
    (long : OperatorSafeDelimiterRun level tokens [] origin finish [])
    (short : SameDelimiterDepth tokens origin split)
    (found : FoundNonAssociativeOperatorAt
      file tokens split level operator)
    (later : split.val < finish.val) : False := by
  cases found with
  | less matched matchedAt =>
      exact long.excludesMatchedAtSameDepth short matched matchedAt rfl later
  | greater matched matchedAt =>
      exact long.excludesMatchedAtSameDepth short matched matchedAt rfl later
  | lessEqual matched matchedAt =>
      exact long.excludesMatchedAtSameDepth short matched matchedAt rfl later
  | greaterEqual matched matchedAt =>
      exact long.excludesMatchedAtSameDepth short matched matchedAt rfl later
  | equal matched matchedAt =>
      exact long.excludesMatchedAtSameDepth short matched matchedAt rfl later
  | notEqual matched matchedAt =>
      exact long.excludesMatchedAtSameDepth short matched matchedAt rfl later

private theorem ContextualRecognizes.unguarded
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {rule : GrammarRuleId}
    {start finish : Boundary tokens}
    (recognized : ContextualRecognizes file tokens memo correct final
      (.rule rule) start finish) :
    UnguardedRecognizes file tokens (.rule rule) start finish := by
  obtain ⟨item, reached, complete, lhs, origin, current⟩ := recognized
  exact ⟨item.raw, reached.toUnguarded, complete, lhs, origin, current⟩

/-- The fixed grammar unconditionally satisfies the G10 operand-prefix
exclusion interface. -/
theorem nonAssociativeOperandPrefixExclusive
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) :
    NonAssociativeOperandPrefixExclusive file tokens memo correct final := by
  intro level origin split finish operator short long found later
  have notModule : level.operandRule ≠ .module := by
    cases level <;> decide
  have shortDepth := short.unguarded.ebnf.sourceRule_sameDelimiterDepth
    notModule
  have longSafe := long.unguarded.ebnf.operand_operatorSafeDelimiterRun
  exact longSafe.excludesFoundAtSameDepth shortDepth found later

/-- Consequently, every finite executable table for the fixed grammar is
accepted without an additional certificate premise. -/
theorem nonAssociativeOperandPrefixExclusiveTable_eq_true
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) :
    nonAssociativeOperandPrefixExclusiveTable
      file tokens owned correct final = true :=
  (nonAssociativeOperandPrefixExclusiveTable_eq_true_iff
    owned correct final).mpr
      (nonAssociativeOperandPrefixExclusive file tokens memo correct final)

end Solcore.Surface.Multi
