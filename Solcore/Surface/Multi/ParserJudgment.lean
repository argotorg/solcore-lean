import Solcore.Surface.Multi.ParserCore

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- The least context-free chart relation with every grammar guard ignored. -/
inductive UnguardedReach
    (file : WorkspaceFile)
    (tokens : List Token) : DottedItem tokens → Prop where
  | seed
      (production : ProductionId)
      (cursor : Boundary tokens) :
      UnguardedReach file tokens {
        production := production
        dot := ⟨0, Nat.zero_lt_succ _⟩
        origin := cursor
        current := cursor
      }
  | predict
      (waiting : DottedItem tokens)
      (predicted : ProductionId)
      (reached : UnguardedReach file tokens waiting)
      (next : NextSymbol waiting
        (GrammarSymbol.nonterminal predicted.lhs)) :
      UnguardedReach file tokens {
        production := predicted
        dot := ⟨0, Nat.zero_lt_succ _⟩
        origin := waiting.current
        current := waiting.current
      }
  | scan
      (before after : DottedItem tokens)
      (cursor : TerminalCursor tokens)
      (terminal : TerminalSymbol)
      (value : TerminalStreamValue)
      (span : SourceSpan)
      (reached : UnguardedReach file tokens before)
      (next : NextSymbol before (GrammarSymbol.terminal terminal))
      (atCurrent : cursor.beforeBoundary = before.current)
      (terminalAt : TerminalAt file tokens cursor value span)
      (terminalMatches : TerminalMatches terminal value)
      (advance : AdvanceItem before cursor.afterBoundary after) :
      UnguardedReach file tokens after
  | complete
      (waiting finished after : DottedItem tokens)
      (waitingReached : UnguardedReach file tokens waiting)
      (finishedReached : UnguardedReach file tokens finished)
      (next : NextSymbol waiting
        (GrammarSymbol.nonterminal finished.production.lhs))
      (finishedComplete : CompleteItem finished)
      (sameCursor : waiting.current = finished.origin)
      (advance : AdvanceItem waiting finished.current after) :
      UnguardedReach file tokens after

/-- Recognition by one complete item in the unguarded least relation. -/
def UnguardedRecognizes
    (file : WorkspaceFile)
    (tokens : List Token)
    (symbol : NonterminalSymbol)
    (start finish : Boundary tokens) : Prop :=
  ∃ item : DottedItem tokens,
    UnguardedReach file tokens item ∧
      CompleteItem item ∧
      item.production.lhs = symbol ∧
      item.origin = start ∧
      item.current = finish

/-- A recognized finish maximal among those no later than one upper bound. -/
def GreatestUnguardedEnd
    (file : WorkspaceFile)
    (tokens : List Token)
    (symbol : NonterminalSymbol)
    (start upperBound finish : Boundary tokens) : Prop :=
  UnguardedRecognizes file tokens symbol start finish ∧
    finish.val ≤ upperBound.val ∧
    ∀ other : Boundary tokens,
      UnguardedRecognizes file tokens symbol start other →
        other.val ≤ upperBound.val →
        other.val ≤ finish.val

/-- An exact terminal-class slice containing retained terminals and no EOF. -/
def ExactSlice
    (file : WorkspaceFile)
    (tokens : List Token)
    (start finish : Boundary tokens)
    (classes : List TerminalSymbol) : Prop :=
  finish.val = start.val + classes.length ∧
    ∀ index : Fin classes.length,
      ∃ cursor : TerminalCursor tokens,
      ∃ token : Token,
        cursor.beforeBoundary.val = start.val + index.val ∧
          TerminalAt file tokens cursor (.retained token) token.span ∧
          TerminalMatches (classes.get index) (.retained token)

/-- The greatest recognized finish below one upper bound is functional. -/
theorem greatestUnguardedEnd_functional
    {file : WorkspaceFile}
    {tokens : List Token}
    {symbol : NonterminalSymbol}
    {start upperBound left right : Boundary tokens}
    (leftGreatest :
      GreatestUnguardedEnd file tokens symbol start upperBound left)
    (rightGreatest :
      GreatestUnguardedEnd file tokens symbol start upperBound right) :
    left = right := by
  rcases leftGreatest with
    ⟨leftRecognized, leftBounded, leftMaximal⟩
  rcases rightGreatest with
    ⟨rightRecognized, rightBounded, rightMaximal⟩
  apply Fin.ext
  exact Nat.le_antisymm
    (rightMaximal left leftRecognized leftBounded)
    (leftMaximal right rightRecognized rightBounded)

/-- A closing delimiter retained on the delimiter stack. -/
inductive DelimiterCloser where
  | rightParen
  | rightBracket
  | rightBrace
  deriving Repr, BEq, DecidableEq

/-- The expected closing delimiters, nearest closer first. -/
abbrev DelimiterStack := List DelimiterCloser

/-- One exact deterministic delimiter-stack transition. -/
def DelimiterStep
    (before : DelimiterStack) (token : TokenKind)
    (after : DelimiterStack) : Prop :=
  match token with
  | .symbol .leftParen => after = .rightParen :: before
  | .symbol .leftBracket => after = .rightBracket :: before
  | .symbol .leftBrace => after = .rightBrace :: before
  | .symbol .rightParen =>
      match before with
      | .rightParen :: rest => after = rest
      | _ => False
  | .symbol .rightBracket =>
      match before with
      | .rightBracket :: rest => after = rest
      | _ => False
  | .symbol .rightBrace =>
      match before with
      | .rightBrace :: rest => after = rest
      | _ => False
  | _ => after = before

/-- A fixed delimiter step has a unique output stack. -/
private theorem delimiterStep_functional
    {before : DelimiterStack} {token : TokenKind}
    {left right : DelimiterStack}
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

/-- The least exact token-by-token composition of delimiter steps. -/
inductive DelimiterRun
    (tokens : List Token) :
    DelimiterStack → Boundary tokens → Boundary tokens →
      DelimiterStack → Prop where
  | nil
      (stack : DelimiterStack)
      (cursor : Boundary tokens) :
      DelimiterRun tokens stack cursor cursor stack
  | cons
      (before after finish : DelimiterStack)
      (cursor : TerminalCursor tokens)
      (start endCursor : Boundary tokens)
      (token : Token)
      (atStart : cursor.beforeBoundary = start)
      (lookup : tokens[cursor.val]? = some token)
      (step : DelimiterStep before token.payload after)
      (rest : DelimiterRun tokens after cursor.afterBoundary
        endCursor finish) :
      DelimiterRun tokens before start endCursor finish

/-- A delimiter run never moves its current boundary backward. -/
private theorem DelimiterRun.ordered
    {tokens : List Token} {before finish : DelimiterStack}
    {start endCursor : Boundary tokens}
    (run : DelimiterRun tokens before start endCursor finish) :
    start.val ≤ endCursor.val := by
  induction run with
  | nil => exact Nat.le_refl _
  | cons before after finish cursor start endCursor token atStart lookup
      step rest induction =>
      have atStartValue := congrArg Fin.val atStart
      have beforeValue : cursor.beforeBoundary.val = cursor.val := rfl
      have afterValue : cursor.afterBoundary.val = cursor.val + 1 := rfl
      omega

/-- A fixed half-open delimiter run has a unique output stack. -/
theorem delimiterRun_functional
    {tokens : List Token} {before : DelimiterStack}
    {start endCursor : Boundary tokens}
    {left right : DelimiterStack}
    (leftRun : DelimiterRun tokens before start endCursor left)
    (rightRun : DelimiterRun tokens before start endCursor right) :
    left = right := by
  induction leftRun generalizing right with
  | nil stack cursor =>
      cases rightRun with
      | nil => rfl
      | cons before after finish stepCursor start endCursor token atStart
          lookup step rest =>
          have ordered := rest.ordered
          have atStartValue := congrArg Fin.val atStart
          have beforeValue : stepCursor.beforeBoundary.val =
              stepCursor.val := rfl
          have afterValue : stepCursor.afterBoundary.val =
              stepCursor.val + 1 := rfl
          omega
  | cons before after finish cursor start endCursor token atStart lookup
      step rest induction =>
      cases rightRun with
      | nil =>
          have ordered := rest.ordered
          have atStartValue := congrArg Fin.val atStart
          have beforeValue : cursor.beforeBoundary.val = cursor.val := rfl
          have afterValue : cursor.afterBoundary.val = cursor.val + 1 := rfl
          omega
      | cons _ rightAfter rightFinish rightCursor _ _ rightToken rightAtStart
          rightLookup rightStep rightRest =>
          have cursorEq : cursor = rightCursor := by
            apply Fin.ext
            exact congrArg (fun value : Boundary tokens => value.val)
              (atStart.trans rightAtStart.symm)
          subst rightCursor
          have tokenEq : token = rightToken := by
            exact Option.some.inj (lookup.symm.trans rightLookup)
          subst rightToken
          have afterEq : after = rightAfter :=
            delimiterStep_functional step rightStep
          subst rightAfter
          exact induction rightRest

/-- Convert a nonempty list to its head-cons-tail representation. -/
private def NonemptyList.toList {alpha : Type}
    (values : NonemptyList alpha) : List alpha :=
  values.head :: values.tail

/-- The head-cons-tail representation determines a nonempty list. -/
private theorem NonemptyList.toList_injective {alpha : Type} :
    Function.Injective (@NonemptyList.toList alpha) := by
  intro left right equality
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only [NonemptyList.toList] at equality
          cases equality
          rfl

/-- A delimiter run whose stack remains nonempty at every boundary. -/
inductive ProtectedDelimiterRun
    (tokens : List Token) :
    NonemptyList DelimiterCloser → Boundary tokens →
      Boundary tokens → NonemptyList DelimiterCloser → Prop where
  | nil
      (stack : NonemptyList DelimiterCloser)
      (cursor : Boundary tokens) :
      ProtectedDelimiterRun tokens stack cursor cursor stack
  | cons
      (before after finish : NonemptyList DelimiterCloser)
      (cursor : TerminalCursor tokens)
      (start endCursor : Boundary tokens)
      (token : Token)
      (atStart : cursor.beforeBoundary = start)
      (lookup : tokens[cursor.val]? = some token)
      (step : DelimiterStep
        (before.head :: before.tail) token.payload
        (after.head :: after.tail))
      (rest : ProtectedDelimiterRun tokens after cursor.afterBoundary
        endCursor finish) :
      ProtectedDelimiterRun tokens before start endCursor finish

/-- Forget the nonempty-stack invariant of a protected delimiter run. -/
private theorem ProtectedDelimiterRun.toDelimiterRun
    {tokens : List Token}
    {before finish : NonemptyList DelimiterCloser}
    {start endCursor : Boundary tokens}
    (run : ProtectedDelimiterRun tokens before start endCursor finish) :
    DelimiterRun tokens before.toList start endCursor finish.toList := by
  induction run with
  | nil => exact .nil _ _
  | cons before after finish cursor start endCursor token atStart lookup
      step rest induction =>
      exact .cons before.toList after.toList finish.toList cursor start
        endCursor token atStart lookup step induction

/-- A protected run also has a unique nonempty output stack. -/
private theorem protectedDelimiterRun_functional
    {tokens : List Token}
    {before : NonemptyList DelimiterCloser}
    {start endCursor : Boundary tokens}
    {left right : NonemptyList DelimiterCloser}
    (leftRun : ProtectedDelimiterRun tokens before start endCursor left)
    (rightRun : ProtectedDelimiterRun tokens before start endCursor right) :
    left = right := by
  apply NonemptyList.toList_injective
  exact delimiterRun_functional leftRun.toDelimiterRun
    rightRun.toDelimiterRun

/-- Recover the symbol represented by one stack closer. -/
private def DelimiterCloser.symbol : DelimiterCloser → Symbol
  | .rightParen => .rightParen
  | .rightBracket => .rightBracket
  | .rightBrace => .rightBrace

/-- Observe one retained symbol directly from the raw token stream. -/
private def rawSymbolAtBoundary
    (tokens : List Token) (cursor : Boundary tokens)
    (symbol : Symbol) : Prop :=
  ∃ terminalCursor : TerminalCursor tokens,
  ∃ token : Token,
    terminalCursor.beforeBoundary = cursor ∧
      tokens[terminalCursor.val]? = some token ∧
      token.payload = .symbol symbol

/-- Observe a retained symbol together with its exact successor boundary. -/
private def rawImmediatelyAfterSymbol
    (tokens : List Token) (symbol : Symbol)
    (symbolCursor after : Boundary tokens) : Prop :=
  ∃ terminalCursor : TerminalCursor tokens,
  ∃ token : Token,
    terminalCursor.beforeBoundary = symbolCursor ∧
      terminalCursor.afterBoundary = after ∧
      tokens[terminalCursor.val]? = some token ∧
      token.payload = .symbol symbol

/-- A matched pair whose protected interior never consumes its own closer. -/
def MatchingDelimiter
    (tokens : List Token) (openCursor closeCursor : Boundary tokens)
    (opening closing : Symbol) : Prop :=
  match opening with
  | .leftParen =>
    closing = .rightParen ∧
    ∃ interiorStart : Boundary tokens,
      (∃ terminalCursor : TerminalCursor tokens,
       ∃ token : Token,
        terminalCursor.beforeBoundary = openCursor ∧
          terminalCursor.afterBoundary = interiorStart ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol opening) ∧
      (∃ terminalCursor : TerminalCursor tokens,
       ∃ token : Token,
        terminalCursor.beforeBoundary = closeCursor ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol closing) ∧
      ProtectedDelimiterRun tokens
        { head := .rightParen, tail := [] }
        interiorStart closeCursor
        { head := .rightParen, tail := [] }
  | .leftBracket =>
    closing = .rightBracket ∧
    ∃ interiorStart : Boundary tokens,
      (∃ terminalCursor : TerminalCursor tokens,
       ∃ token : Token,
        terminalCursor.beforeBoundary = openCursor ∧
          terminalCursor.afterBoundary = interiorStart ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol opening) ∧
      (∃ terminalCursor : TerminalCursor tokens,
       ∃ token : Token,
        terminalCursor.beforeBoundary = closeCursor ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol closing) ∧
      ProtectedDelimiterRun tokens
        { head := .rightBracket, tail := [] }
        interiorStart closeCursor
        { head := .rightBracket, tail := [] }
  | .leftBrace =>
    closing = .rightBrace ∧
    ∃ interiorStart : Boundary tokens,
      (∃ terminalCursor : TerminalCursor tokens,
       ∃ token : Token,
        terminalCursor.beforeBoundary = openCursor ∧
          terminalCursor.afterBoundary = interiorStart ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol opening) ∧
      (∃ terminalCursor : TerminalCursor tokens,
       ∃ token : Token,
        terminalCursor.beforeBoundary = closeCursor ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol closing) ∧
      ProtectedDelimiterRun tokens
        { head := .rightBrace, tail := [] }
        interiorStart closeCursor
        { head := .rightBrace, tail := [] }
  | _ => False

/-- An exact empty-stack run between two boundaries. -/
def SameDelimiterDepth
    (tokens : List Token) (start finish : Boundary tokens) : Prop :=
  DelimiterRun tokens [] start finish []

/-- The first allowed symbol reached again at the starting delimiter depth. -/
def NextSameDepthDelimiter
    (tokens : List Token) (start cursor : Boundary tokens)
    (allowed : NonemptyList Symbol) : Prop :=
  SameDelimiterDepth tokens start cursor ∧
    (∃ symbol : Symbol,
      (symbol = allowed.head ∨ symbol ∈ allowed.tail) ∧
      ∃ terminalCursor : TerminalCursor tokens,
      ∃ token : Token,
        terminalCursor.beforeBoundary = cursor ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol symbol) ∧
    ∀ earlier : Boundary tokens,
      start.val ≤ earlier.val →
      earlier.val < cursor.val →
      SameDelimiterDepth tokens start earlier →
      ¬ ∃ symbol : Symbol,
        (symbol = allowed.head ∨ symbol ∈ allowed.tail) ∧
        ∃ terminalCursor : TerminalCursor tokens,
        ∃ token : Token,
          terminalCursor.beforeBoundary = earlier ∧
            tokens[terminalCursor.val]? = some token ∧
            token.payload = .symbol symbol

/-- A retained symbol token at one exact grammar boundary. -/
def SymbolAtBoundary
    (file : WorkspaceFile) (tokens : List Token)
    (cursor : Boundary tokens) (symbol : Symbol) : Prop :=
  ∃ terminalCursor : TerminalCursor tokens,
  ∃ token : Token,
    terminalCursor.beforeBoundary = cursor ∧
      TerminalAt file tokens terminalCursor (.retained token) token.span ∧
      token.payload = .symbol symbol

/-- A retained symbol token together with its exact successor boundary. -/
def ImmediatelyAfterSymbol
    (file : WorkspaceFile) (tokens : List Token) (symbol : Symbol)
    (symbolCursor after : Boundary tokens) : Prop :=
  ∃ terminalCursor : TerminalCursor tokens,
  ∃ token : Token,
    terminalCursor.beforeBoundary = symbolCursor ∧
      terminalCursor.afterBoundary = after ∧
      TerminalAt file tokens terminalCursor (.retained token) token.span ∧
      token.payload = .symbol symbol

/-- A raw symbol observation has a unique successor boundary. -/
private theorem rawImmediatelyAfterSymbol_functional
    {tokens : List Token} {symbol : Symbol}
    {symbolCursor left right : Boundary tokens}
    (leftAfter :
      rawImmediatelyAfterSymbol tokens symbol symbolCursor left)
    (rightAfter :
      rawImmediatelyAfterSymbol tokens symbol symbolCursor right) :
    left = right := by
  rcases leftAfter with
    ⟨leftCursor, leftToken, leftBefore, leftBoundary, leftLookup, leftPayload⟩
  rcases rightAfter with
    ⟨rightCursor, rightToken, rightBefore, rightBoundary, rightLookup,
      rightPayload⟩
  have cursorEq : leftCursor = rightCursor := by
    apply Fin.ext
    exact congrArg (fun value : Boundary tokens => value.val)
      (leftBefore.trans rightBefore.symm)
  exact leftBoundary.symm.trans
    ((congrArg TerminalCursor.afterBoundary cursorEq).trans rightBoundary)

/-- Two protected runs cannot encounter their bottom closer at different ends. -/
private theorem protectedDelimiterRun_close_functional
    {tokens : List Token} {closer : DelimiterCloser}
    {before : NonemptyList DelimiterCloser}
    {start left right : Boundary tokens}
    {leftFinal rightFinal : NonemptyList DelimiterCloser}
    (leftRun : ProtectedDelimiterRun tokens before start left leftFinal)
    (leftFinalEq : leftFinal = { head := closer, tail := [] })
    (leftClose : rawSymbolAtBoundary tokens left closer.symbol)
    (rightRun : ProtectedDelimiterRun tokens before start right rightFinal)
    (rightFinalEq : rightFinal = { head := closer, tail := [] })
    (rightClose : rawSymbolAtBoundary tokens right closer.symbol) :
    left = right := by
  induction leftRun generalizing closer right rightFinal with
  | nil stack cursor =>
      subst stack
      cases rightRun with
      | nil => rfl
      | cons before after finish stepCursor stepStart endCursor token atStart
          lookup step rest =>
          rcases leftClose with
            ⟨closeCursor, closeToken, closeBefore, closeLookup, closePayload⟩
          have cursorEq : stepCursor = closeCursor := by
            apply Fin.ext
            exact congrArg (fun value : Boundary tokens => value.val)
              (atStart.trans closeBefore.symm)
          subst closeCursor
          have tokenEq : token = closeToken :=
            Option.some.inj (lookup.symm.trans closeLookup)
          subst closeToken
          rw [closePayload] at step
          cases closer <;>
            simp [DelimiterStep, DelimiterCloser.symbol] at step
  | cons before after finish cursor stepStart endCursor token atStart lookup
      step rest induction =>
      cases rightRun with
      | nil =>
          rcases rightClose with
            ⟨closeCursor, closeToken, closeBefore, closeLookup, closePayload⟩
          have cursorEq : cursor = closeCursor := by
            apply Fin.ext
            exact congrArg (fun value : Boundary tokens => value.val)
              (atStart.trans closeBefore.symm)
          subst closeCursor
          have tokenEq : token = closeToken :=
            Option.some.inj (lookup.symm.trans closeLookup)
          subst closeToken
          rw [rightFinalEq, closePayload] at step
          cases closer <;>
            simp [DelimiterStep, DelimiterCloser.symbol] at step
      | cons _ rightAfter rightFinish rightCursor _ _ rightToken rightAtStart
          rightLookup rightStep rightRest =>
          have cursorEq : cursor = rightCursor := by
            apply Fin.ext
            exact congrArg (fun value : Boundary tokens => value.val)
              (atStart.trans rightAtStart.symm)
          subst rightCursor
          have tokenEq : token = rightToken :=
            Option.some.inj (lookup.symm.trans rightLookup)
          subst rightToken
          have afterListEq : after.toList = rightAfter.toList :=
            delimiterStep_functional step rightStep
          have afterEq : after = rightAfter :=
            NonemptyList.toList_injective afterListEq
          subst rightAfter
          exact induction leftFinalEq leftClose rightRest rightFinalEq
            rightClose

/-- A fixed opening delimiter has exactly one matching closing boundary. -/
theorem matchingDelimiter_functional
    {tokens : List Token}
    {openCursor left right : Boundary tokens}
    {opening closing : Symbol}
    (leftMatch :
      MatchingDelimiter tokens openCursor left opening closing)
    (rightMatch :
      MatchingDelimiter tokens openCursor right opening closing) :
    left = right := by
  cases opening <;> simp only [MatchingDelimiter] at leftMatch rightMatch
  all_goals
    rcases leftMatch with
      ⟨leftClosing, leftStart, leftOpen, leftClose, leftRun⟩
    rcases rightMatch with
      ⟨rightClosing, rightStart, rightOpen, rightClose, rightRun⟩
    change rawImmediatelyAfterSymbol tokens _ openCursor leftStart at leftOpen
    change rawImmediatelyAfterSymbol tokens _ openCursor rightStart at rightOpen
    change rawSymbolAtBoundary tokens left closing at leftClose
    change rawSymbolAtBoundary tokens right closing at rightClose
    have startEq : leftStart = rightStart :=
      rawImmediatelyAfterSymbol_functional leftOpen rightOpen
    subst rightStart
    rw [leftClosing] at leftClose rightClose
    exact protectedDelimiterRun_close_functional
      leftRun rfl leftClose rightRun rfl rightClose

end Solcore.Surface.Multi
