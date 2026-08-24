import Solcore.Surface.Multi.EbnfOperatorSafety

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- Token-level form of the operator set rejected by the static checker. -/
def grammarForbiddenTokenKind :
    NonAssociativeLevel → TokenKind → Bool
  | .relational, .symbol .less => true
  | .relational, .symbol .greater => true
  | .relational, .symbol .lessEqual => true
  | .relational, .symbol .greaterEqual => true
  | .equality, .symbol .equalEqual => true
  | .equality, .symbol .notEqual => true
  | _, _ => false

/-- A delimiter run which never consumes a selected forbidden operator while
its stack is empty. -/
inductive OperatorSafeDelimiterRun
    (level : NonAssociativeLevel) (tokens : List Token) :
    DelimiterStack → Boundary tokens → Boundary tokens →
      DelimiterStack → Prop where
  | nil (stack : DelimiterStack) (cursor : Boundary tokens) :
      OperatorSafeDelimiterRun level tokens stack cursor cursor stack
  | cons
      (before after finish : DelimiterStack)
      (cursor : TerminalCursor tokens)
      (start endCursor : Boundary tokens)
      (token : Token)
      (atStart : cursor.beforeBoundary = start)
      (lookup : tokens[cursor.val]? = some token)
      (step : DelimiterStep before token.payload after)
      (allowed : before = [] →
        grammarForbiddenTokenKind level token.payload = false)
      (rest : OperatorSafeDelimiterRun level tokens after
        cursor.afterBoundary endCursor finish) :
      OperatorSafeDelimiterRun level tokens before start endCursor finish

/-- Forget the operator exclusion annotations. -/
theorem OperatorSafeDelimiterRun.toDelimiterRun
    {level : NonAssociativeLevel} {tokens : List Token}
    {before after : DelimiterStack} {start finish : Boundary tokens}
    (run : OperatorSafeDelimiterRun level tokens before start finish after) :
    DelimiterRun tokens before start finish after := by
  induction run with
  | nil => exact .nil _ _
  | cons before next finishStack cursor start endCursor token atStart lookup
      step allowed rest induction =>
      exact .cons before next finishStack cursor start endCursor token atStart
        lookup step induction

/-- Compose adjacent operator-safe delimiter runs. -/
theorem OperatorSafeDelimiterRun.append
    {level : NonAssociativeLevel} {tokens : List Token}
    {first middle last : Boundary tokens}
    {before between after : DelimiterStack}
    (left : OperatorSafeDelimiterRun level tokens before first middle between)
    (right : OperatorSafeDelimiterRun level tokens between middle last after) :
    OperatorSafeDelimiterRun level tokens before first last after := by
  induction left with
  | nil => exact right
  | cons before next finishStack cursor start endCursor token atStart lookup
      step allowed rest induction =>
      exact .cons before next after cursor start last token atStart lookup step
        allowed (induction right)

/-- A nonempty untouched suffix protects every token in an ordinary run from
being observed at the outer empty depth. -/
theorem DelimiterRun.operatorSafeAppendStack
    {tokens : List Token} {before after : DelimiterStack}
    {start finish : Boundary tokens}
    (run : DelimiterRun tokens before start finish after)
    (level : NonAssociativeLevel) (suffix : DelimiterStack)
    (suffixNonempty : suffix ≠ []) :
    OperatorSafeDelimiterRun level tokens (before ++ suffix) start finish
      (after ++ suffix) := by
  induction run with
  | nil => exact .nil _ _
  | cons before next finishStack cursor start endCursor token atStart lookup
      step rest induction =>
      refine .cons (before ++ suffix) (next ++ suffix)
        (finishStack ++ suffix) cursor start endCursor token atStart lookup
        (DelimiterStep.append step suffix) ?_ induction
      intro empty
      exact False.elim
        (suffixNonempty (List.append_eq_nil_iff.mp empty).2)

private theorem terminalMatches_forbiddenTokenKind_false
    {level : NonAssociativeLevel} {terminal : TerminalSymbol} {token : Token}
    (matched : TerminalMatches terminal (.retained token))
    (allowed : grammarForbiddenTerminal level terminal = false) :
    grammarForbiddenTokenKind level token.payload = false := by
  cases terminal with
  | hardKeyword keyword =>
      change token.payload = .hardKeyword keyword at matched
      rw [matched]
      cases level <;> rfl
  | contextualKeyword keyword =>
      change token.payload = .identifier keyword.spelling at matched
      rw [matched]
      cases level <;> rfl
  | pragmaName kind =>
      change token.payload = .pragmaName kind at matched
      rw [matched]
      cases level <;> rfl
  | symbol symbol =>
      change token.payload = .symbol symbol at matched
      rw [matched]
      cases level <;> cases symbol <;> exact allowed
  | category category =>
      cases category with
      | identifier =>
          obtain ⟨text, parsed, payload, parsedOk⟩ := matched
          rw [payload]
          cases level <;> rfl
      | pathComponent =>
          rcases matched with
            ⟨text, parsed, payload, parsedOk⟩ |
            ⟨keyword, parsed, payload, parsedOk⟩
          · rw [payload]
            cases level <;> rfl
          · rw [payload]
            cases level <;> rfl
      | decimalLiteral =>
          obtain ⟨spelling, digits, payload⟩ := matched
          rw [payload]
          cases level <;> rfl
      | hexadecimalLiteral =>
          obtain ⟨spelling, digits, payload⟩ := matched
          rw [payload]
          cases level <;> rfl
      | stringLiteral =>
          obtain ⟨spelling, decoded, payload⟩ := matched
          rw [payload]
          cases level <;> rfl
      | assemblyBlock =>
          obtain ⟨slice, payload⟩ := matched
          rw [payload]
          cases level <;> rfl
  | endOfFile => exact False.elim matched

private theorem delimiterRun_adjacent_step
    {tokens : List Token} {before after : DelimiterStack}
    {start finish : Boundary tokens} (target : TerminalCursor tokens)
    (run : DelimiterRun tokens before start finish after)
    (startEq : start = target.beforeBoundary)
    (finishEq : finish = target.afterBoundary) :
    ∃ token : Token,
      tokens[target.val]? = some token ∧
        DelimiterStep before token.payload after := by
  cases run with
  | nil stack cursor =>
      have impossible : target.beforeBoundary = target.afterBoundary :=
        startEq.symm.trans finishEq
      have values := congrArg Fin.val impossible
      have coercions := terminalCursor_boundary_coercions_exact target
      omega
  | cons runBefore next finishStack cursor runStart endCursor token atStart
      lookup step rest =>
      have cursorEq : cursor = target := by
        apply Fin.ext
        have boundaryEq : cursor.beforeBoundary = target.beforeBoundary :=
          atStart.trans startEq
        exact congrArg (fun value : Boundary tokens => value.val) boundaryEq
      subst cursor
      rw [finishEq] at rest
      have stackEq :=
        delimiterRun_functional rest (.nil next target.afterBoundary)
      refine ⟨token, lookup, ?_⟩
      rw [stackEq]
      exact step

/-- One accepted checked terminal yields one annotated operator-safe step. -/
theorem matchedTerminal_operatorSafeDelimiterRun
    {file : WorkspaceFile} {tokens : List Token}
    {level : NonAssociativeLevel} {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    {before after : DelimiterStack}
    (effect : grammarOperatorEffect? level (.atom (.terminal terminal))
      before = some after) :
    OperatorSafeDelimiterRun level tokens before
      matched.cursor.beforeBoundary matched.cursor.afterBoundary after := by
  have notEof : terminal ≠ .endOfFile := by
    intro equality
    subst terminal
    simp [grammarOperatorEffect?] at effect
  have notBlocked : ¬(before = [] ∧
      grammarForbiddenTerminal level terminal = true) := by
    intro blocked
    simp [grammarOperatorEffect?, notEof, blocked] at effect
  have delimiterEffect :
      grammarTerminalDelimiterStep? before terminal = some after := by
    simpa [grammarOperatorEffect?, notEof, notBlocked] using effect
  have tokenOnly : grammarTokenOnly (.atom (.terminal terminal)) = true := by
    cases terminal <;> simp_all [grammarTokenOnly]
  have ordinary := matchedTerminal_delimiterRun matched delimiterEffect tokenOnly
  obtain ⟨token, lookup, step⟩ :=
    delimiterRun_adjacent_step matched.cursor ordinary rfl rfl
  refine .cons before after after matched.cursor
    matched.cursor.beforeBoundary matched.cursor.afterBoundary token rfl lookup
    step ?_ (.nil after _)
  intro empty
  have terminalAllowed :
      grammarForbiddenTerminal level terminal = false := by
    cases forbiddenEq : grammarForbiddenTerminal level terminal with
    | false => rfl
    | true => exact False.elim (notBlocked ⟨empty, forbiddenEq⟩)
  cases matched with
  | mk matchedCursor value span terminalAt matchedEvidence =>
      cases terminalAt with
      | retained retainedToken inRange retainedLookup valid =>
          have tokenEq : token = retainedToken := Option.some.inj
            (lookup.symm.trans retainedLookup)
          subst retainedToken
          exact terminalMatches_forbiddenTokenKind_false
            matchedEvidence terminalAllowed
      | endOfFile atEnd =>
          cases terminal with
          | hardKeyword keyword => exact False.elim matchedEvidence
          | contextualKeyword keyword => exact False.elim matchedEvidence
          | pragmaName kind => exact False.elim matchedEvidence
          | symbol symbol => exact False.elim matchedEvidence
          | category category =>
              cases category <;> exact False.elim matchedEvidence
          | endOfFile => exact False.elim (notEof rfl)

end Solcore.Surface.Multi
