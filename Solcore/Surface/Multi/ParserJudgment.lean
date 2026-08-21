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

/-- Every relation closed under the four unguarded rules contains its reach. -/
theorem unguardedReach_least
    {file : WorkspaceFile} {tokens : List Token}
    (relation : DottedItem tokens → Prop)
    (seed : ∀ (production : ProductionId) (cursor : Boundary tokens),
      relation {
        production := production
        dot := ⟨0, Nat.zero_lt_succ _⟩
        origin := cursor
        current := cursor
      })
    (predict : ∀ (waiting : DottedItem tokens)
        (predicted : ProductionId),
      relation waiting →
      NextSymbol waiting (.nonterminal predicted.lhs) →
      relation {
        production := predicted
        dot := ⟨0, Nat.zero_lt_succ _⟩
        origin := waiting.current
        current := waiting.current
      })
    (scan : ∀ (before after : DottedItem tokens)
        (cursor : TerminalCursor tokens)
        (terminal : TerminalSymbol)
        (value : TerminalStreamValue)
        (span : SourceSpan),
      relation before →
      NextSymbol before (.terminal terminal) →
      cursor.beforeBoundary = before.current →
      TerminalAt file tokens cursor value span →
      TerminalMatches terminal value →
      AdvanceItem before cursor.afterBoundary after →
      relation after)
    (complete : ∀ (waiting finished after : DottedItem tokens),
      relation waiting →
      relation finished →
      NextSymbol waiting (.nonterminal finished.production.lhs) →
      CompleteItem finished →
      waiting.current = finished.origin →
      AdvanceItem waiting finished.current after →
      relation after)
    {item : DottedItem tokens}
    (reached : UnguardedReach file tokens item) :
    relation item := by
  induction reached with
  | seed production cursor => exact seed production cursor
  | predict waiting predicted _ next waitingInduction =>
      exact predict waiting predicted waitingInduction next
  | scan before after cursor terminal value span _ next atCurrent terminalAt
      terminalMatches advance beforeInduction =>
      exact scan before after cursor terminal value span beforeInduction next
        atCurrent terminalAt terminalMatches advance
  | complete waiting finished after _ _ next finishedComplete sameCursor advance
      waitingInduction finishedInduction =>
      exact complete waiting finished after waitingInduction finishedInduction
        next finishedComplete sameCursor advance

/-- Unguarded recognition is exactly one reached complete matching item. -/
theorem unguardedRecognizes_exact
    {file : WorkspaceFile} {tokens : List Token}
    {symbol : NonterminalSymbol}
    {start finish : Boundary tokens} :
    UnguardedRecognizes file tokens symbol start finish ↔
      ∃ item : DottedItem tokens,
        UnguardedReach file tokens item ∧
          CompleteItem item ∧
          item.production.lhs = symbol ∧
          item.origin = start ∧
          item.current = finish := by
  rfl

/-- An exact slice is precisely its retained, class-matched cursor sequence. -/
theorem exactSlice_exact
    {file : WorkspaceFile} {tokens : List Token}
    {start finish : Boundary tokens}
    {classes : List TerminalSymbol} :
    ExactSlice file tokens start finish classes ↔
      finish.val = start.val + classes.length ∧
        ∀ index : Fin classes.length,
          ∃ cursor : TerminalCursor tokens,
          ∃ token : Token,
            cursor.beforeBoundary.val = start.val + index.val ∧
              TerminalAt file tokens cursor (.retained token) token.span ∧
              TerminalMatches (classes.get index) (.retained token) := by
  rfl

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

/-- A same-frame match-arm header whose pattern reaches its next fat arrow. -/
def ArmHeaderAt
    (file : WorkspaceFile) (tokens : List Token)
    (regionStart cursor : Boundary tokens) : Prop :=
  regionStart.val ≤ cursor.val ∧
    SameDelimiterDepth tokens regionStart cursor ∧
    SymbolAtBoundary file tokens cursor .pipe ∧
    ∃ patternStart arrowCursor : Boundary tokens,
      ImmediatelyAfterSymbol file tokens .pipe cursor patternStart ∧
        NextSameDepthDelimiter tokens patternStart arrowCursor
          { head := .fatArrow, tail := [] } ∧
        GreatestUnguardedEnd file tokens
          (.aux Grammar.matchArmPatternListSite.site)
          patternStart arrowCursor arrowCursor

/-- A brace pair strictly containing one cursor. -/
def ContainingBraceFrame
    (tokens : List Token) (cursor openCursor closeCursor : Boundary tokens) :
    Prop :=
  openCursor.val < cursor.val ∧
    cursor.val < closeCursor.val ∧
    MatchingDelimiter tokens openCursor closeCursor .leftBrace .rightBrace

/-- The containing brace frame with the greatest opening cursor. -/
def InnermostContainingBraceFrame
    (tokens : List Token) (cursor openCursor closeCursor : Boundary tokens) :
    Prop :=
  ContainingBraceFrame tokens cursor openCursor closeCursor ∧
    ∀ otherOpen otherClose : Boundary tokens,
      ContainingBraceFrame tokens cursor otherOpen otherClose →
      otherOpen.val ≤ openCursor.val

/-- The first same-frame next-arm header or the containing close brace. -/
def NextArmOrClose
    (file : WorkspaceFile) (tokens : List Token)
    (regionStart closeCursor regionEnd : Boundary tokens) : Prop :=
  regionStart.val ≤ regionEnd.val ∧
    regionEnd.val ≤ closeCursor.val ∧
    SameDelimiterDepth tokens regionStart regionEnd ∧
    (regionEnd = closeCursor ∨
      ArmHeaderAt file tokens regionStart regionEnd) ∧
    ∀ earlier : Boundary tokens,
      regionStart.val ≤ earlier.val →
      earlier.val < regionEnd.val →
      SameDelimiterDepth tokens regionStart earlier →
      ¬ (earlier = closeCursor ∨
        ArmHeaderAt file tokens regionStart earlier)

/-- The exact nearest braced-body or match-arm statement region. -/
def NearestStatementRegion
    (file : WorkspaceFile) (tokens : List Token)
    (regionStart regionEnd : Boundary tokens) : Prop :=
  (∃ openCursor : Boundary tokens,
    ImmediatelyAfterSymbol file tokens .leftBrace openCursor regionStart ∧
      MatchingDelimiter tokens openCursor regionEnd .leftBrace .rightBrace) ∨
  (∃ arrowCursor openCursor closeCursor : Boundary tokens,
    ImmediatelyAfterSymbol file tokens .fatArrow arrowCursor regionStart ∧
      InnermostContainingBraceFrame tokens arrowCursor openCursor closeCursor ∧
      NextArmOrClose file tokens regionStart closeCursor regionEnd)

/-- Every match-arm header is at the delimiter depth of its region start. -/
theorem armHeaderAt_same_frame
    {file : WorkspaceFile} {tokens : List Token}
    {regionStart cursor : Boundary tokens}
    (header : ArmHeaderAt file tokens regionStart cursor) :
    SameDelimiterDepth tokens regionStart cursor :=
  header.2.1

/-- Recover the retained token lookup from one terminal observation. -/
private theorem terminalAt_retained_lookup
    {file : WorkspaceFile} {tokens : List Token}
    {cursor : TerminalCursor tokens} {token : Token} {span : SourceSpan}
    (terminalAt : TerminalAt file tokens cursor (.retained token) span) :
    tokens[cursor.val]? = some token := by
  cases terminalAt
  assumption

/-- A shared successor fixes both the observed symbol and its boundary. -/
private theorem immediatelyAfterSymbol_cursor_symbol_functional
    {file : WorkspaceFile} {tokens : List Token}
    {leftSymbol rightSymbol : Symbol}
    {leftCursor rightCursor after : Boundary tokens}
    (leftAfter : ImmediatelyAfterSymbol file tokens leftSymbol
      leftCursor after)
    (rightAfter : ImmediatelyAfterSymbol file tokens rightSymbol
      rightCursor after) :
    leftCursor = rightCursor ∧ leftSymbol = rightSymbol := by
  rcases leftAfter with
    ⟨leftTerminal, leftToken, leftBefore, leftAfter, leftAt, leftPayload⟩
  rcases rightAfter with
    ⟨rightTerminal, rightToken, rightBefore, rightAfter, rightAt,
      rightPayload⟩
  have terminalEq : leftTerminal = rightTerminal := by
    apply Fin.ext
    have leftValue : leftTerminal.afterBoundary.val = leftTerminal.val + 1 := rfl
    have rightValue : rightTerminal.afterBoundary.val = rightTerminal.val + 1 := rfl
    have afterEq : leftTerminal.afterBoundary = rightTerminal.afterBoundary :=
      leftAfter.trans rightAfter.symm
    have afterValueEq := congrArg
      (fun value : Boundary tokens => value.val) afterEq
    omega
  have cursorEq : leftCursor = rightCursor := by
    exact leftBefore.symm.trans
      ((congrArg TerminalCursor.beforeBoundary terminalEq).trans rightBefore)
  subst rightTerminal
  have tokenEq : leftToken = rightToken := by
    exact Option.some.inj
      ((terminalAt_retained_lookup leftAt).symm.trans
        (terminalAt_retained_lookup rightAt))
  have symbolEq : leftSymbol = rightSymbol := by
    have payloadEq : TokenKind.symbol leftSymbol =
        TokenKind.symbol rightSymbol := by
      exact leftPayload.symm.trans
        ((congrArg Located.payload tokenEq).trans rightPayload)
    exact TokenKind.symbol.inj payloadEq
  exact ⟨cursorEq, symbolEq⟩

/-- The innermost frame around a fixed cursor is unique. -/
private theorem innermostContainingBraceFrame_functional
    {tokens : List Token} {cursor : Boundary tokens}
    {leftOpen leftClose rightOpen rightClose : Boundary tokens}
    (leftFrame : InnermostContainingBraceFrame tokens cursor
      leftOpen leftClose)
    (rightFrame : InnermostContainingBraceFrame tokens cursor
      rightOpen rightClose) :
    leftOpen = rightOpen ∧ leftClose = rightClose := by
  have openEq : leftOpen = rightOpen := by
    apply Fin.ext
    exact Nat.le_antisymm
      (rightFrame.2 leftOpen leftClose leftFrame.1)
      (leftFrame.2 rightOpen rightClose rightFrame.1)
  subst rightOpen
  have closeEq : leftClose = rightClose :=
    matchingDelimiter_functional leftFrame.1.2.2 rightFrame.1.2.2
  exact ⟨rfl, closeEq⟩

/-- A fixed frame has at most one least next arm-or-close endpoint. -/
private theorem nextArmOrClose_functional
    {file : WorkspaceFile} {tokens : List Token}
    {regionStart closeCursor left right : Boundary tokens}
    (leftNext : NextArmOrClose file tokens regionStart closeCursor left)
    (rightNext : NextArmOrClose file tokens regionStart closeCursor right) :
    left = right := by
  apply Fin.ext
  apply Nat.le_antisymm
  · exact Nat.le_of_not_gt fun rightLtLeft =>
      leftNext.2.2.2.2 right rightNext.1 rightLtLeft
        rightNext.2.2.1 rightNext.2.2.2.1
  · exact Nat.le_of_not_gt fun leftLtRight =>
      rightNext.2.2.2.2 left leftNext.1 leftLtRight
        leftNext.2.2.1 leftNext.2.2.2.1

/-- A region start determines at most one nearest statement-region end. -/
theorem nearest_statement_region_functional
    {file : WorkspaceFile} {tokens : List Token}
    {regionStart left right : Boundary tokens}
    (leftRegion : NearestStatementRegion file tokens regionStart left)
    (rightRegion : NearestStatementRegion file tokens regionStart right) :
    left = right := by
  rcases leftRegion with leftBlock | leftArm
  · rcases leftBlock with ⟨leftOpen, leftAfter, leftMatch⟩
    rcases rightRegion with rightBlock | rightArm
    · rcases rightBlock with ⟨rightOpen, rightAfter, rightMatch⟩
      have openEq :=
        (immediatelyAfterSymbol_cursor_symbol_functional
          leftAfter rightAfter).1
      subst rightOpen
      exact matchingDelimiter_functional leftMatch rightMatch
    · rcases rightArm with
        ⟨rightArrow, rightOpen, rightClose, rightAfter, rightFrame,
          rightNext⟩
      have impossible :=
        (immediatelyAfterSymbol_cursor_symbol_functional
          leftAfter rightAfter).2
      cases impossible
  · rcases leftArm with
      ⟨leftArrow, leftOpen, leftClose, leftAfter, leftFrame, leftNext⟩
    rcases rightRegion with rightBlock | rightArm
    · rcases rightBlock with ⟨rightOpen, rightAfter, rightMatch⟩
      have impossible :=
        (immediatelyAfterSymbol_cursor_symbol_functional
          leftAfter rightAfter).2
      cases impossible
    · rcases rightArm with
        ⟨rightArrow, rightOpen, rightClose, rightAfter, rightFrame,
          rightNext⟩
      have arrowEq :=
        (immediatelyAfterSymbol_cursor_symbol_functional
          leftAfter rightAfter).1
      subst rightArrow
      rcases innermostContainingBraceFrame_functional leftFrame rightFrame with
        ⟨openEq, closeEq⟩
      subst rightOpen
      subst rightClose
      exact nextArmOrClose_functional leftNext rightNext

/-- The exact declarative guard-decision relation. -/
def GuardEvidence
    (file : WorkspaceFile) (tokens : List Token)
    (key : GuardInstanceKey tokens) (decision : GuardDecision) : Prop :=
  let terminalAtBoundary := fun
      (terminal : TerminalSymbol) (boundary : Boundary tokens) =>
    ∃ matched : MatchedTerminal file tokens terminal,
      matched.cursor.beforeBoundary = boundary
  let immediatelyAfterTerminal := fun
      (terminal : TerminalSymbol)
      (boundary after : Boundary tokens) =>
    ∃ matched : MatchedTerminal file tokens terminal,
      matched.cursor.beforeBoundary = boundary ∧
        matched.cursor.afterBoundary = after
  let statementIf :=
    ∃ openCursor expressionStart closeCursor afterClose : Boundary tokens,
      immediatelyAfterTerminal (.hardKeyword .ifKw)
        key.siteCursor openCursor ∧
      immediatelyAfterTerminal (.symbol .leftParen)
        openCursor expressionStart ∧
      MatchingDelimiter tokens openCursor closeCursor
        .leftParen .rightParen ∧
      UnguardedRecognizes file tokens (.rule .expression)
        expressionStart closeCursor ∧
      immediatelyAfterTerminal (.symbol .rightParen)
        closeCursor afterClose ∧
      terminalAtBoundary (.symbol .leftBrace) afterClose
  let armHeader :=
    ArmHeaderAt file tokens key.contextStart key.siteCursor
  let pipeAtSite :=
    SymbolAtBoundary file tokens key.siteCursor .pipe
  let comptimeAtSite :=
    terminalAtBoundary (.contextualKeyword .comptimeKw) key.siteCursor
  let patternComptime :=
    ∃ expressionStart limit : Boundary tokens,
      immediatelyAfterTerminal (.contextualKeyword .comptimeKw)
        key.siteCursor expressionStart ∧
      NextSameDepthDelimiter tokens expressionStart limit {
        head := .comma
        tail := [.rightParen, .fatArrow]
      } ∧
      GreatestUnguardedEnd file tokens (.rule .expression)
        expressionStart limit limit
  let leadingDotArguments :=
    ExactSlice file tokens key.contextStart key.siteCursor [
      .symbol .dot,
      .category .identifier
    ] ∧
    SymbolAtBoundary file tokens key.siteCursor .leftParen
  let terminalExpression :=
    ∃ regionEnd : Boundary tokens,
      NearestStatementRegion file tokens key.contextStart regionEnd ∧
      GreatestUnguardedEnd file tokens (.rule .expression)
        key.siteCursor regionEnd regionEnd
  let genericContext :=
    ∃ arrowCursor : Boundary tokens,
      SymbolAtBoundary file tokens arrowCursor .fatArrow ∧
      GreatestUnguardedEnd file tokens (.rule .predicateList)
        key.siteCursor arrowCursor arrowCursor
  TokensOwnedBy file tokens ∧
    match key.guard with
    | .G01_statementIf =>
      match decision with
      | .positive => statementIf
      | .negative => ¬ statementIf
      | .neutral => False
    | .G02_matchArmBoundary =>
      match decision with
      | .positive => armHeader
      | .negative => pipeAtSite ∧ ¬ armHeader
      | .neutral => ¬ pipeAtSite
    | .G03_parameterComptime =>
      match decision with
      | .positive => comptimeAtSite
      | .negative => ¬ comptimeAtSite
      | .neutral => False
    | .G04_letComptime =>
      match decision with
      | .positive => comptimeAtSite
      | .negative => ¬ comptimeAtSite
      | .neutral => False
    | .G05_typeComptime =>
      match decision with
      | .positive => comptimeAtSite
      | .negative => ¬ comptimeAtSite
      | .neutral => False
    | .G06_patternComptime =>
      match decision with
      | .positive => patternComptime
      | .negative => ¬ patternComptime
      | .neutral => False
    | .G07_leadingDotArguments =>
      match decision with
      | .positive => leadingDotArguments
      | .negative => ¬ leadingDotArguments
      | .neutral => False
    | .G08_terminalExpression =>
      match decision with
      | .positive => terminalExpression
      | .negative => ¬ terminalExpression
      | .neutral => False
    | .G09_genericContext =>
      match decision with
      | .positive => genericContext
      | .negative => ¬ genericContext
      | .neutral => False

private theorem binaryGuardDecision_functional
    (positive : Prop)
    {left right : GuardDecision}
    (leftEvidence :
      match left with
      | .positive => positive
      | .negative => ¬ positive
      | .neutral => False)
    (rightEvidence :
      match right with
      | .positive => positive
      | .negative => ¬ positive
      | .neutral => False) :
    left = right := by
  cases left <;> cases right <;> simp_all

private theorem matchArmGuardDecision_functional
    (header pipeAtSite : Prop)
    (headerPipe : header → pipeAtSite)
    {left right : GuardDecision}
    (leftEvidence :
      match left with
      | .positive => header
      | .negative => pipeAtSite ∧ ¬ header
      | .neutral => ¬ pipeAtSite)
    (rightEvidence :
      match right with
      | .positive => header
      | .negative => pipeAtSite ∧ ¬ header
      | .neutral => ¬ pipeAtSite) :
    left = right := by
  cases left <;> cases right <;> simp_all

/-- One guard instance has at most one declarative decision. -/
theorem GuardEvidence.functional
    {file : WorkspaceFile} {tokens : List Token}
    {key : GuardInstanceKey tokens} {left right : GuardDecision}
    (leftEvidence : GuardEvidence file tokens key left)
    (rightEvidence : GuardEvidence file tokens key right) :
    left = right := by
  cases key with
  | mk guard contextStart siteCursor ordered =>
      unfold GuardEvidence at leftEvidence rightEvidence
      rcases leftEvidence with ⟨leftOwned, leftEvidence⟩
      rcases rightEvidence with ⟨rightOwned, rightEvidence⟩
      cases guard <;> simp only at leftEvidence rightEvidence
      case G01_statementIf =>
        exact binaryGuardDecision_functional _ leftEvidence rightEvidence
      case G02_matchArmBoundary =>
        apply matchArmGuardDecision_functional _ _ _
          leftEvidence rightEvidence
        intro header
        exact header.2.2.1
      case G03_parameterComptime =>
        exact binaryGuardDecision_functional _ leftEvidence rightEvidence
      case G04_letComptime =>
        exact binaryGuardDecision_functional _ leftEvidence rightEvidence
      case G05_typeComptime =>
        exact binaryGuardDecision_functional _ leftEvidence rightEvidence
      case G06_patternComptime =>
        exact binaryGuardDecision_functional _ leftEvidence rightEvidence
      case G07_leadingDotArguments =>
        exact binaryGuardDecision_functional _ leftEvidence rightEvidence
      case G08_terminalExpression =>
        exact binaryGuardDecision_functional _ leftEvidence rightEvidence
      case G09_genericContext =>
        exact binaryGuardDecision_functional _ leftEvidence rightEvidence

/-- Exact agreement between one final Phase-B table and guard evidence. -/
def PhaseBCorrect
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens) : Prop :=
  ∀ key decision,
    memo key = .final decision ↔ GuardEvidence file tokens key decision

/-- One accepted decision for one checked guarded-production cell. -/
def GuardWitness
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (_correct : PhaseBCorrect file tokens memo)
    (_allFinal : AllGuardsFinal memo)
    (key : GuardWitnessKey tokens) : Prop :=
  ∃ decision : GuardDecision,
    memo key.guardInstance = .final decision ∧
      GuardEvidence file tokens key.guardInstance decision ∧
      decision.allows key.polarity = true

/-- Every guard cell of one production instance accepts its exact polarity. -/
def EnabledProductionInstance
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (allFinal : AllGuardsFinal memo)
    (productionInstance : ProductionInstanceKey tokens) : Prop :=
  ∀ guard polarity,
    (guard, polarity) ∈ guardOf productionInstance.production →
      ∃ witnessKey : GuardWitnessKey tokens,
        witnessKey.productionInstance = productionInstance ∧
          witnessKey.guardInstance.guard = guard ∧
          witnessKey.polarity = polarity ∧
          GuardWitness file tokens memo correct allFinal witnessKey

/-- The least Phase-C reachability relation after all guards are finalized. -/
inductive ContextualReach
    (file : WorkspaceFile)
    (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) :
    ContextualItemKey tokens → Prop where
  | root :
      ContextualReach file tokens memo correct final {
        raw := {
          production := .root .module
          dot := ⟨0, Nat.zero_lt_succ _⟩
          origin := Boundary.start tokens
          current := Boundary.start tokens
        }
        context := .plain
      }
  | predict
      (waiting : ContextualItemKey tokens)
      (predicted : ProductionId)
      (reached : ContextualReach file tokens memo correct final waiting)
      (next : NextSymbol waiting.raw
        (GrammarSymbol.nonterminal predicted.lhs))
      (enabled : EnabledProductionInstance file tokens memo correct final {
        production := predicted
        origin := waiting.raw.current
        context := descendContext waiting predicted
      }) :
      ContextualReach file tokens memo correct final {
        raw := {
          production := predicted
          dot := ⟨0, Nat.zero_lt_succ _⟩
          origin := waiting.raw.current
          current := waiting.raw.current
        }
        context := descendContext waiting predicted
      }
  | scan
      (before after : ContextualItemKey tokens)
      (cursor : TerminalCursor tokens)
      (reached : ContextualReach file tokens memo correct final before)
      (structural : ContextualPackedEdgeKey.StructurallyValid file tokens
        (.scanned before after cursor)) :
      ContextualReach file tokens memo correct final after
  | complete
      (waiting finished after : ContextualItemKey tokens)
      (shared : Boundary tokens)
      (waitingReached :
        ContextualReach file tokens memo correct final waiting)
      (finishedReached :
        ContextualReach file tokens memo correct final finished)
      (structural : ContextualPackedEdgeKey.StructurallyValid file tokens
        (.completed waiting finished after shared)) :
      ContextualReach file tokens memo correct final after

/-- Any contextual Phase-C reach derivation carries a correct Phase-B memo. -/
theorem contextualReach_requires_phaseBCorrect
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {item : ContextualItemKey tokens}
    (reached :
      ∃ (correct : PhaseBCorrect file tokens memo)
          (final : AllGuardsFinal memo),
        ContextualReach file tokens memo correct final item) :
    PhaseBCorrect file tokens memo := by
  rcases reached with ⟨correct, _final, _reached⟩
  exact correct

/-- Any contextual Phase-C reach derivation carries a fully finalized memo. -/
theorem contextualReach_requires_allGuardsFinal
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {item : ContextualItemKey tokens}
    (reached :
      ∃ (correct : PhaseBCorrect file tokens memo)
          (final : AllGuardsFinal memo),
        ContextualReach file tokens memo correct final item) :
    AllGuardsFinal memo := by
  rcases reached with ⟨_correct, final, _reached⟩
  exact final

/-- Contextual reach is the least relation containing the root and closed
under exact guarded prediction, scanning, and completion. -/
theorem contextual_predict_scan_complete_closed
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (relation : ContextualItemKey tokens → Prop)
    (root : relation {
      raw := {
        production := .root .module
        dot := ⟨0, Nat.zero_lt_succ _⟩
        origin := Boundary.start tokens
        current := Boundary.start tokens
      }
      context := .plain
    })
    (predict : ∀ (waiting : ContextualItemKey tokens)
        (predicted : ProductionId),
      relation waiting →
      NextSymbol waiting.raw (.nonterminal predicted.lhs) →
      EnabledProductionInstance file tokens memo correct final {
        production := predicted
        origin := waiting.raw.current
        context := descendContext waiting predicted
      } →
      relation {
        raw := {
          production := predicted
          dot := ⟨0, Nat.zero_lt_succ _⟩
          origin := waiting.raw.current
          current := waiting.raw.current
        }
        context := descendContext waiting predicted
      })
    (scan : ∀ (before after : ContextualItemKey tokens)
        (cursor : TerminalCursor tokens),
      relation before →
      ContextualPackedEdgeKey.StructurallyValid file tokens
        (.scanned before after cursor) →
      relation after)
    (complete : ∀ (waiting finished after : ContextualItemKey tokens)
        (shared : Boundary tokens),
      relation waiting →
      relation finished →
      ContextualPackedEdgeKey.StructurallyValid file tokens
        (.completed waiting finished after shared) →
      relation after)
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item) :
    relation item := by
  induction reached with
  | root => exact root
  | predict waiting predicted _ next enabled waitingInduction =>
      exact predict waiting predicted waitingInduction next enabled
  | scan before after cursor _ structural beforeInduction =>
      exact scan before after cursor beforeInduction structural
  | complete waiting finished after shared _ _ structural
      waitingInduction finishedInduction =>
      exact complete waiting finished after shared waitingInduction
        finishedInduction structural

/-- Structural validity plus reachability of every endpoint of one edge. -/
def ContextualEdgeReach
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (key : ContextualPackedEdgeKey tokens) : Prop :=
  ContextualPackedEdgeKey.StructurallyValid file tokens key ∧
    match key with
    | .scanned before after _ =>
        ContextualReach file tokens memo correct final before ∧
          ContextualReach file tokens memo correct final after
    | .completed waiting finished after _ =>
        ContextualReach file tokens memo correct final waiting ∧
          ContextualReach file tokens memo correct final finished ∧
          ContextualReach file tokens memo correct final after

/-- A contextual edge is retained exactly when it is structural and all of
its constructor-specific endpoints are reached. -/
theorem contextualEdgeReach_endpoints_reached
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {key : ContextualPackedEdgeKey tokens} :
    ContextualEdgeReach file tokens memo correct final key ↔
      ContextualPackedEdgeKey.StructurallyValid file tokens key ∧
        match key with
        | .scanned before after _ =>
            ContextualReach file tokens memo correct final before ∧
              ContextualReach file tokens memo correct final after
        | .completed waiting finished after _ =>
            ContextualReach file tokens memo correct final waiting ∧
              ContextualReach file tokens memo correct final finished ∧
              ContextualReach file tokens memo correct final after := by
  rfl

/-- Raw projection of a reached edge never discards the contextual equations
needed to keep scan and completion anchors coherent. -/
theorem contextual_projection_no_anchor_mixing
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} :
    (∀ (before after : ContextualItemKey tokens)
        (cursor : TerminalCursor tokens),
      ContextualEdgeReach file tokens memo correct final
          (.scanned before after cursor) →
        before.context = after.context) ∧
      ∀ (waiting finished after : ContextualItemKey tokens)
          (shared : Boundary tokens),
        ContextualEdgeReach file tokens memo correct final
            (.completed waiting finished after shared) →
          finished.context =
              descendContext waiting finished.raw.production ∧
            after.context = waiting.context := by
  constructor
  · intro before after cursor edge
    exact edge.1.2
  · intro waiting finished after shared edge
    exact edge.1.2

/-- Every reached contextual item spans an ordered boundary interval. -/
theorem contextualReach_ordered
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item) :
    item.raw.origin.val ≤ item.raw.current.val := by
  induction reached with
  | root => exact Nat.le_refl _
  | predict => exact Nat.le_refl _
  | scan before after cursor reached structural ordered =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      rcases advance with
        ⟨productionEq, dotEq, originEq, currentEq⟩
      rw [originEq, currentEq]
      calc
        before.raw.origin.val ≤ before.raw.current.val := ordered
        _ = cursor.val := by rw [← atCurrent]; rfl
        _ ≤ cursor.val + 1 := Nat.le_succ _
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingOrdered finishedOrdered =>
      rcases structural.1 with
        ⟨symbol, next, complete, lhsEq, waitingAtShared,
          finishedAtShared, advance⟩
      rcases advance with
        ⟨productionEq, dotEq, originEq, currentEq⟩
      rw [originEq, currentEq]
      calc
        waiting.raw.origin.val ≤ waiting.raw.current.val := waitingOrdered
        _ = shared.val := congrArg Fin.val waitingAtShared
        _ = finished.raw.origin.val :=
          (congrArg Fin.val finishedAtShared).symm
        _ ≤ finished.raw.current.val := finishedOrdered

/-- Preconditions shared by all reductions of one source grammar rule. -/
def RuleReductionReady
    (file : WorkspaceFile) (tokens : List Token)
    (rule : GrammarRuleId) (origin finish : Boundary tokens) : Prop :=
  TokensOwnedBy file tokens ∧
    origin.val ≤ finish.val ∧
    (rule = .module →
      origin = Boundary.start tokens ∧
        finish = Boundary.afterLogicalEOF tokens)

/-- Root actions inherit source-rule readiness; all auxiliary actions are ready. -/
def ActionReductionReady
    (file : WorkspaceFile) (tokens : List Token)
    (action : ActionId) (origin finish : Boundary tokens) : Prop :=
  match action.production with
  | .root rule => RuleReductionReady file tokens rule origin finish
  | _ => True

namespace RuleReduction

/-- One matched terminal aligned with its spelling and parsed semantic value. -/
structure SpelledTerminalData
    (file : WorkspaceFile) (tokens : List Token)
    (terminal : TerminalSymbol) (parsedType : Type) where
  matched : MatchedTerminal file tokens terminal
  spelling : String
  parsed : parsedType

/-- Pair an explicit payload with the exact span of one matched terminal. -/
def terminalLoc
    {alpha : Type}
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    (payload : alpha) : Located alpha := {
  span := matched.span
  payload := payload
}

/-- Locate a payload between the first start and last end byte. -/
def between {alpha : Type}
    (file : WorkspaceFile)
    (firstSpan lastSpan : SourceSpan)
    (payload : alpha) : Located alpha := {
  span := {
    source := file.id
    startByte := firstSpan.startByte
    endByte := lastSpan.endByte
  }
  payload := payload
}

/-- Locate the complete module payload over the whole source file. -/
def moduleLoc
    (file : WorkspaceFile)
    (payload : ParsedModuleV1Payload) : ParsedModuleV1 := {
  span := {
    source := file.id
    startByte := 0
    endByte := file.content.utf8ByteSize
  }
  payload := payload
}

/-- Locate a body payload at one empty UTF-8 byte boundary. -/
def emptyAt
    (file : WorkspaceFile)
    (byte : Nat)
    (payload : BodyPayload) : Body := {
  span := { source := file.id, startByte := byte, endByte := byte }
  payload := payload
}

/-- Convert a first/rest nonempty list to ordinary source order. -/
def firstRest {alpha : Type} (values : NonemptyList alpha) : List alpha :=
  values.head :: values.tail

/-- Discard matched argument delimiters while preserving presence. -/
def arguments
    {file : WorkspaceFile} {tokens : List Token}
    {alpha : Type} :
    Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (alpha ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))) →
      Option alpha
  | none => none
  | some (_, values, _, ()) => some values

/-- Fold source-ordered postfix pieces over their receiver. -/
def foldPostfix
    (file : WorkspaceFile) : Expression → List PostfixPartValue → Expression
  | receiver, [] => receiver
  | receiver, part :: rest =>
      let next := match part with
        | .call _ arguments closeParen =>
            between file receiver.span closeParen (.call receiver arguments)
        | .select _ field =>
            between file receiver.span field.span (.select receiver field)
        | .index _ index closeBracket =>
            between file receiver.span closeBracket (.index receiver index)
      foldPostfix file next rest

/-- Fold source-ordered infix operations left-associatively. -/
def foldInfixLeft
    (file : WorkspaceFile) :
    Expression → List (Located InfixOperator × Expression) → Expression
  | left, [] => left
  | left, (operator, right) :: rest =>
      foldInfixLeft file
        (between file left.span right.span (.infix operator left right))
        rest

/-- Construct the exact empty or nonempty body of one match arm. -/
def armBody
    {file : WorkspaceFile} {tokens : List Token}
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow)) :
    List Statement → Body
  | [] =>
      emptyAt file fatArrow.span.endByte {
        origin := .matchArm fatArrow.span
        statements := []
      }
  | first :: rest =>
      let last := rest.getLastD first
      between file first.span last.span {
        origin := .matchArm fatArrow.span
        statements := first :: rest
      }

/-- The exact retained terminal/kind pairs that construct syntax markers. -/
inductive MarkerProjects
    (file : WorkspaceFile) (tokens : List Token) :
    {terminal : TerminalSymbol} →
      MatchedTerminal file tokens terminal → SyntaxMarker → Prop where
  | libraryRoot
      (terminal : MatchedTerminal file tokens (.category .pathComponent))
      (parsed : PathSegment)
      (projects : PathSegmentProjects terminal "lib" parsed) :
      MarkerProjects file tokens terminal .libraryRoot
  | standardRoot
      (terminal : MatchedTerminal file tokens (.category .pathComponent))
      (parsed : PathSegment)
      (projects : PathSegmentProjects terminal "std" parsed) :
      MarkerProjects file tokens terminal .standardRoot
  | externalSigil
      (terminal : MatchedTerminal file tokens (.symbol .at)) :
      MarkerProjects file tokens terminal .externalSigil
  | wildcardStar
      (terminal : MatchedTerminal file tokens (.symbol .star)) :
      MarkerProjects file tokens terminal .wildcard
  | wildcardUnderscore
      (terminal : MatchedTerminal file tokens (.symbol .underscore)) :
      MarkerProjects file tokens terminal .wildcard
  | fallbackName
      (terminal : MatchedTerminal file tokens (.hardKeyword .fallbackKw)) :
      MarkerProjects file tokens terminal .fallbackName
  | contractConstructorName
      (terminal : MatchedTerminal file tokens
        (.hardKeyword .constructorKw)) :
      MarkerProjects file tokens terminal .contractConstructorName
  | publicModifier
      (terminal : MatchedTerminal file tokens (.hardKeyword .publicKw)) :
      MarkerProjects file tokens terminal .publicModifier
  | payableModifier
      (terminal : MatchedTerminal file tokens (.hardKeyword .payableKw)) :
      MarkerProjects file tokens terminal .payableModifier
  | comptimeModifier
      (terminal : MatchedTerminal file tokens
        (.contextualKeyword .comptimeKw)) :
      MarkerProjects file tokens terminal .comptimeModifier
  | defaultModifier
      (terminal : MatchedTerminal file tokens (.hardKeyword .defaultKw)) :
      MarkerProjects file tokens terminal .defaultModifier

namespace MarkerProjects

/-- One matched terminal projects to at most one syntax-marker kind. -/
theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    {matched : MatchedTerminal file tokens terminal}
    {left right : SyntaxMarker}
    (leftProjects : RuleReduction.MarkerProjects
      file tokens matched left)
    (rightProjects : RuleReduction.MarkerProjects
      file tokens matched right) :
    left = right := by
  cases leftProjects <;> cases rightProjects
  all_goals try rfl
  all_goals
    rename_i leftParsed leftProjection rightParsed rightProjection
    have spellingEq :=
      (PathSegmentProjects.functional leftProjection rightProjection).1
    contradiction

end MarkerProjects

/-- Locate one explicitly indexed syntax marker at its exact terminal span. -/
def marker
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol} {kind : SyntaxMarker}
    (matched : MatchedTerminal file tokens terminal)
    (_projects : MarkerProjects file tokens matched kind) : Marker :=
  terminalLoc matched kind

/-- Locate the sole prefix operator at its exact bang-token span. -/
def prefixOperator
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.symbol .bang)) :
    Located PrefixOperator :=
  terminalLoc terminal .logicalNot

/-- The exact retained terminal/operator pairs for all infix operators. -/
inductive InfixOperatorProjects
    (file : WorkspaceFile) (tokens : List Token) :
    {terminal : TerminalSymbol} →
      MatchedTerminal file tokens terminal → InfixOperator → Prop where
  | multiply (terminal : MatchedTerminal file tokens (.symbol .star)) :
      InfixOperatorProjects file tokens terminal .multiply
  | divide (terminal : MatchedTerminal file tokens (.symbol .slash)) :
      InfixOperatorProjects file tokens terminal .divide
  | modulo (terminal : MatchedTerminal file tokens (.symbol .percent)) :
      InfixOperatorProjects file tokens terminal .modulo
  | add (terminal : MatchedTerminal file tokens (.symbol .plus)) :
      InfixOperatorProjects file tokens terminal .add
  | subtract (terminal : MatchedTerminal file tokens (.symbol .minus)) :
      InfixOperatorProjects file tokens terminal .subtract
  | bitAnd (terminal : MatchedTerminal file tokens (.symbol .amp)) :
      InfixOperatorProjects file tokens terminal .bitAnd
  | bitXor (terminal : MatchedTerminal file tokens (.symbol .caret)) :
      InfixOperatorProjects file tokens terminal .bitXor
  | bitOr (terminal : MatchedTerminal file tokens (.symbol .pipe)) :
      InfixOperatorProjects file tokens terminal .bitOr
  | less (terminal : MatchedTerminal file tokens (.symbol .less)) :
      InfixOperatorProjects file tokens terminal .less
  | greater (terminal : MatchedTerminal file tokens (.symbol .greater)) :
      InfixOperatorProjects file tokens terminal .greater
  | lessEqual
      (terminal : MatchedTerminal file tokens (.symbol .lessEqual)) :
      InfixOperatorProjects file tokens terminal .lessEqual
  | greaterEqual
      (terminal : MatchedTerminal file tokens (.symbol .greaterEqual)) :
      InfixOperatorProjects file tokens terminal .greaterEqual
  | equal (terminal : MatchedTerminal file tokens (.symbol .equalEqual)) :
      InfixOperatorProjects file tokens terminal .equal
  | notEqual (terminal : MatchedTerminal file tokens (.symbol .notEqual)) :
      InfixOperatorProjects file tokens terminal .notEqual
  | logicalAnd
      (terminal : MatchedTerminal file tokens (.symbol .logicalAnd)) :
      InfixOperatorProjects file tokens terminal .logicalAnd
  | logicalOr
      (terminal : MatchedTerminal file tokens (.symbol .logicalOr)) :
      InfixOperatorProjects file tokens terminal .logicalOr

/-- Locate one explicitly indexed infix operator at its exact terminal span. -/
def infixOperator
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol} {operator : InfixOperator}
    (matched : MatchedTerminal file tokens terminal)
    (_projects : InfixOperatorProjects file tokens matched operator) :
    Located InfixOperator :=
  terminalLoc matched operator

/-- The exact retained terminal/operator pairs for assignment operators. -/
inductive AssignmentOperatorProjects
    (file : WorkspaceFile) (tokens : List Token) :
    {terminal : TerminalSymbol} →
      MatchedTerminal file tokens terminal → AssignmentOperator → Prop where
  | equal (terminal : MatchedTerminal file tokens (.symbol .equal)) :
      AssignmentOperatorProjects file tokens terminal .equal
  | addEqual (terminal : MatchedTerminal file tokens (.symbol .plusEqual)) :
      AssignmentOperatorProjects file tokens terminal .addEqual
  | subtractEqual
      (terminal : MatchedTerminal file tokens (.symbol .minusEqual)) :
      AssignmentOperatorProjects file tokens terminal .subtractEqual
  | bitXorEqual
      (terminal : MatchedTerminal file tokens (.symbol .caretEqual)) :
      AssignmentOperatorProjects file tokens terminal .bitXorEqual
  | bitAndEqual
      (terminal : MatchedTerminal file tokens (.symbol .ampEqual)) :
      AssignmentOperatorProjects file tokens terminal .bitAndEqual
  | bitOrEqual
      (terminal : MatchedTerminal file tokens (.symbol .pipeEqual)) :
      AssignmentOperatorProjects file tokens terminal .bitOrEqual
  | moduloEqual
      (terminal : MatchedTerminal file tokens (.symbol .percentEqual)) :
      AssignmentOperatorProjects file tokens terminal .moduloEqual

/-- Locate one explicitly indexed assignment operator at its terminal span. -/
def assignmentOperator
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol} {operator : AssignmentOperator}
    (matched : MatchedTerminal file tokens terminal)
    (_projects : AssignmentOperatorProjects file tokens matched operator) :
    Located AssignmentOperator :=
  terminalLoc matched operator

end RuleReduction


local syntax "rrEvs![" term,* "]" : term

local macro "rrEvs![" values:term,* "]" : term => do
  let mut result ← `(EbnfValues.nil)
  for value in values.getElems.reverse do
    result ← `(EbnfValues.cons _ _ $value $result)
  return result

local syntax "rrRoot![" term "]" : term
local macro_rules
  | `(rrRoot![$value:term]) => `(EbnfValue.transport (by rfl) $value)

local syntax "rrTerm![" term "," term "]" : term
local macro_rules
  | `(rrTerm![$terminal:term, $matched:term]) =>
      `(EbnfValue.terminalAtom $terminal $matched)

local syntax "rrRule![" term "," term "]" : term
local macro_rules
  | `(rrRule![$rule:term, $value:term]) =>
      `(EbnfValue.ruleAtom $rule $value)

local syntax "rrSeq![" term "|" term,* "]" : term
local macro "rrSeq![" children:term "|" values:term,* "]" : term => do
  `(EbnfValue.sequence $children rrEvs![$values,*])

local syntax "rrChoice![" term "|" term "," term "]" : term
local macro_rules
  | `(rrChoice![$branches:term | $branch:term, $value:term]) =>
      `(EbnfValue.choice $branches ⟨$branch, $value⟩)

local syntax "rrGroup![" term "," term "]" : term
local macro_rules
  | `(rrGroup![$child:term, $value:term]) =>
      `(EbnfValue.group $child $value)

local syntax "rrOpt![" term "," term "]" : term
local macro_rules
  | `(rrOpt![$child:term, $value:term]) =>
      `(EbnfValue.optional $child $value)

local syntax "rrStar![" term "," term "]" : term
local macro_rules
  | `(rrStar![$child:term, $value:term]) =>
      `(EbnfValue.star $child $value)

local syntax "rrList0![" term "," term "]" : term
local macro_rules
  | `(rrList0![$child:term, $value:term]) =>
      `(EbnfValue.list0 $child $value)

local syntax "rrList1![" term "," term "]" : term
local macro_rules
  | `(rrList1![$child:term, $value:term]) =>
      `(EbnfValue.list1 $child $value)

local syntax "rrTopItemInput![" term "," term "]" : term
local macro_rules
  | `(rrTopItemInput![$branch:term, $value:term]) =>
      `(rrRoot![rrChoice![[
        .atom (.nonterminal .importDecl),
        .atom (.nonterminal .exportDecl),
        .atom (.nonterminal .pragmaDecl),
        .atom (.nonterminal .dataDecl),
        .atom (.nonterminal .typeAliasDecl),
        .atom (.nonterminal .classDecl),
        .atom (.nonterminal .instanceDecl),
        .atom (.nonterminal .contractDecl),
        .atom (.nonterminal .functionDecl)
      ] | $branch, $value]])

local syntax "rrModuleRefInput![" term "," term "]" : term
local macro_rules
  | `(rrModuleRefInput![$branch:term, $value:term]) =>
      `(rrRoot![rrChoice![[
        .sequence [
          .atom (.terminal (.symbol .at)),
          .atom (.terminal (.category .pathComponent)),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.category .pathComponent)),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]))
        ],
        .sequence [
          .atom (.terminal (.category .pathComponent)),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]))
        ]
      ] | $branch, $value]])

local syntax "rrExportDeclInput![" term "," term "]" : term
local macro_rules
  | `(rrExportDeclInput![$branch:term, $value:term]) =>
      `(rrRoot![rrChoice![[
        .sequence [
          .atom (.terminal (.hardKeyword .exportKw)),
          .atom (.terminal (.symbol .leftBrace)),
          .list0 (.atom (.nonterminal .localExportEntry)),
          .atom (.terminal (.symbol .rightBrace)),
          .atom (.terminal (.symbol .semicolon))
        ],
        .sequence [
          .atom (.terminal (.hardKeyword .exportKw)),
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .semicolon))
        ],
        .sequence [
          .atom (.terminal (.hardKeyword .exportKw)),
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.hardKeyword .asKw)),
          .atom (.terminal (.category .identifier)),
          .atom (.terminal (.symbol .semicolon))
        ],
        .sequence [
          .atom (.terminal (.hardKeyword .exportKw)),
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.symbol .star)),
          .atom (.terminal (.symbol .semicolon))
        ],
        .sequence [
          .atom (.terminal (.hardKeyword .exportKw)),
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.symbol .leftBrace)),
          .list0 (.atom (.nonterminal .remoteExportEntry)),
          .atom (.terminal (.symbol .rightBrace)),
          .atom (.terminal (.symbol .semicolon))
        ]
      ] | $branch, $value]])

local syntax "rrLocalExportEntryInput![" term "," term "]" : term
local macro_rules
  | `(rrLocalExportEntryInput![$branch:term, $value:term]) =>
      `(rrRoot![rrChoice![[
        .atom (.terminal (.symbol .star)),
        .atom (.nonterminal .exportItem),
        .sequence [
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.symbol .star))
        ]
      ] | $branch, $value]])

local syntax "rrRemoteExportEntryInput![" term "," term "]" : term
local macro_rules
  | `(rrRemoteExportEntryInput![$branch:term, $value:term]) =>
      `(rrRoot![rrChoice![[
        .atom (.terminal (.symbol .star)),
        .atom (.nonterminal .exportItem)
      ] | $branch, $value]])

local syntax "rrPragmaDeclInput![" term "," term "]" : term
local macro_rules
  | `(rrPragmaDeclInput![$branch:term, $value:term]) =>
      `(rrRoot![rrChoice![[
        .sequence [
          .atom (.terminal (.hardKeyword .pragmaKw)),
          .atom (.terminal (.pragmaName .noCoverageCondition)),
          .optional (.list1 (.atom (.terminal (.category .identifier)))),
          .atom (.terminal (.symbol .semicolon))
        ],
        .sequence [
          .atom (.terminal (.hardKeyword .pragmaKw)),
          .atom (.terminal (.pragmaName .noPattersonCondition)),
          .optional (.list1 (.atom (.terminal (.category .identifier)))),
          .atom (.terminal (.symbol .semicolon))
        ],
        .sequence [
          .atom (.terminal (.hardKeyword .pragmaKw)),
          .atom (.terminal (.pragmaName .noBoundedVariableCondition)),
          .optional (.list1 (.atom (.terminal (.category .identifier)))),
          .atom (.terminal (.symbol .semicolon))
        ],
        .sequence [
          .atom (.terminal (.hardKeyword .pragmaKw)),
          .atom (.terminal (.pragmaName .noGenericInstanceFor)),
          .optional (.list1 (.atom (.terminal (.category .identifier)))),
          .atom (.terminal (.symbol .semicolon))
        ]
      ] | $branch, $value]])

local syntax "rrContractMemberInput![" term "," term "]" : term
local macro_rules
  | `(rrContractMemberInput![$branch:term, $value:term]) =>
      `(rrRoot![rrChoice![[
        .atom (.nonterminal .dataDecl),
        .atom (.nonterminal .typeAliasDecl),
        .atom (.nonterminal .fieldDecl),
        .atom (.nonterminal .functionDecl),
        .atom (.nonterminal .fallbackDecl),
        .atom (.nonterminal .contractConstructorDecl)
      ] | $branch, $value]])

local syntax "rrTypeInput![" term "," term "]" : term
local macro_rules
  | `(rrTypeInput![$branch:term, $value:term]) =>
      `(rrRoot![rrChoice![[
        .sequence [
          .atom (.terminal (.contextualKeyword .comptimeKw)),
          .atom (.nonterminal .type)
        ],
        .sequence [
          .atom (.nonterminal .typeAtom),
          .optional (.sequence [
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)
          ])
        ]
      ] | $branch, $value]])

local syntax "rrTypeAtomInput![" term "," term "]" : term
local macro_rules
  | `(rrTypeAtomInput![$branch:term, $value:term]) =>
      `(rrRoot![rrChoice![[
        .sequence [
          .atom (.terminal (.symbol .at)),
          .atom (.nonterminal .typeAtom)
        ],
        .sequence [
          .atom (.nonterminal .qualifiedName),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ])
        ],
        .sequence [
          .atom (.terminal (.symbol .leftParen)),
          .atom (.terminal (.symbol .rightParen))
        ],
        .sequence [
          .atom (.terminal (.symbol .leftParen)),
          .atom (.nonterminal .type),
          .atom (.terminal (.symbol .rightParen))
        ],
        .sequence [
          .atom (.terminal (.symbol .leftParen)),
          .atom (.nonterminal .type),
          .atom (.terminal (.symbol .comma)),
          .atom (.nonterminal .type),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .comma)),
            .atom (.nonterminal .type)
          ])),
          .atom (.terminal (.symbol .rightParen))
        ]
      ] | $branch, $value]])

local syntax "rrNil" : term
local macro_rules
  | `(rrNil) => `(EbnfValues.nil)

local syntax "rrCons" : term
local macro_rules
  | `(rrCons) => `(EbnfValues.cons _ _)

local syntax "rrTerminalExpr![" term "]" : term
local macro_rules
  | `(rrTerminalExpr![$terminal:term]) =>
      `(.atom (.terminal $terminal))

local syntax "rrRuleExpr![" term "]" : term
local macro_rules
  | `(rrRuleExpr![$rule:term]) =>
      `(.atom (.nonterminal $rule))

local syntax "rrExprSeq![" term,* "]" : term
local macro_rules
  | `(rrExprSeq![$children:term,*]) => `(.sequence [$children,*])

local syntax "rrExprChoice![" term,* "]" : term
local macro_rules
  | `(rrExprChoice![$branches:term,*]) => `(.choice [$branches,*])

local syntax "rrExprGroup![" term "]" : term
local macro_rules
  | `(rrExprGroup![$child:term]) => `(.group $child)

local syntax "rrExprOpt![" term "]" : term
local macro_rules
  | `(rrExprOpt![$child:term]) => `(.optional $child)

local syntax "rrExprStar![" term "]" : term
local macro_rules
  | `(rrExprStar![$child:term]) => `(.star $child)

local syntax "rrExprPlus![" term "]" : term
local macro_rules
  | `(rrExprPlus![$child:term]) => `(.plus $child)

local syntax "rrExprList0![" term "]" : term
local macro_rules
  | `(rrExprList0![$child:term]) => `(.list0 $child)

local syntax "rrExprList1![" term "]" : term
local macro_rules
  | `(rrExprList1![$child:term]) => `(.list1 $child)

local syntax "rrPublicRhs![" term "]" : term
local macro_rules
  | `(rrPublicRhs![.statement]) => `(rrExprChoice![
      rrRuleExpr![.letStatement],
      rrRuleExpr![.returnStatement],
      rrRuleExpr![.matchStatement],
      rrRuleExpr![.ifStatement],
      rrRuleExpr![.forStatement],
      rrRuleExpr![.assemblyStatement],
      rrRuleExpr![.blockStatement],
      rrRuleExpr![.breakStatement],
      rrRuleExpr![.continueStatement],
      rrRuleExpr![.assignmentStatement],
      rrRuleExpr![.expressionStatement]
    ])
  | `(rrPublicRhs![.letStatement]) => `(rrExprSeq![
      rrRuleExpr![.letBinding],
      rrTerminalExpr![.symbol .semicolon]
    ])
  | `(rrPublicRhs![.letBinding]) => `(rrExprSeq![
      rrTerminalExpr![.hardKeyword .letKw],
      rrTerminalExpr![.category .identifier],
      rrExprOpt![rrExprSeq![
        rrTerminalExpr![.symbol .colon],
        rrExprOpt![rrTerminalExpr![.contextualKeyword .comptimeKw]],
        rrRuleExpr![.type]
      ]],
      rrExprOpt![rrExprSeq![
        rrTerminalExpr![.symbol .equal],
        rrRuleExpr![.expression]
      ]]
    ])
  | `(rrPublicRhs![.returnStatement]) => `(rrExprSeq![
      rrTerminalExpr![.hardKeyword .returnKw],
      rrExprOpt![rrRuleExpr![.expression]],
      rrTerminalExpr![.symbol .semicolon]
    ])
  | `(rrPublicRhs![.blockStatement]) => `(rrRuleExpr![.body])
  | `(rrPublicRhs![.breakStatement]) => `(rrExprSeq![
      rrTerminalExpr![.hardKeyword .breakKw],
      rrTerminalExpr![.symbol .semicolon]
    ])
  | `(rrPublicRhs![.continueStatement]) => `(rrExprSeq![
      rrTerminalExpr![.hardKeyword .continueKw],
      rrTerminalExpr![.symbol .semicolon]
    ])
  | `(rrPublicRhs![.assemblyStatement]) => `(rrExprSeq![
      rrTerminalExpr![.hardKeyword .assemblyKw],
      rrTerminalExpr![.category .assemblyBlock]
    ])
  | `(rrPublicRhs![.ifStatement]) => `(rrExprSeq![
      rrTerminalExpr![.hardKeyword .ifKw],
      rrTerminalExpr![.symbol .leftParen],
      rrRuleExpr![.expression],
      rrTerminalExpr![.symbol .rightParen],
      rrRuleExpr![.body],
      rrExprOpt![rrExprSeq![
        rrTerminalExpr![.hardKeyword .elseKw],
        rrRuleExpr![.body]
      ]]
    ])
  | `(rrPublicRhs![.forStatement]) => `(rrExprSeq![
      rrTerminalExpr![.hardKeyword .forKw],
      rrTerminalExpr![.symbol .leftParen],
      rrExprList0![rrRuleExpr![.forInitItem]],
      rrTerminalExpr![.symbol .semicolon],
      rrRuleExpr![.expression],
      rrTerminalExpr![.symbol .semicolon],
      rrExprList0![rrRuleExpr![.forPostItem]],
      rrTerminalExpr![.symbol .rightParen],
      rrRuleExpr![.body]
    ])
  | `(rrPublicRhs![.forInitItem]) => `(rrExprChoice![
      rrRuleExpr![.letBinding],
      rrExprSeq![
        rrRuleExpr![.expression],
        rrRuleExpr![.assignmentOperator],
        rrRuleExpr![.expression]
      ],
      rrRuleExpr![.expression]
    ])
  | `(rrPublicRhs![.forPostItem]) => `(rrExprChoice![
      rrExprSeq![
        rrRuleExpr![.expression],
        rrRuleExpr![.assignmentOperator],
        rrRuleExpr![.expression]
      ],
      rrRuleExpr![.expression]
    ])
  | `(rrPublicRhs![.matchStatement]) => `(rrExprSeq![
      rrTerminalExpr![.hardKeyword .matchKw],
      rrExprList1![rrRuleExpr![.expression]],
      rrTerminalExpr![.symbol .leftBrace],
      rrExprPlus![rrRuleExpr![.matchArm]],
      rrTerminalExpr![.symbol .rightBrace],
      rrExprOpt![rrTerminalExpr![.symbol .semicolon]]
    ])
  | `(rrPublicRhs![.matchArm]) => `(rrExprSeq![
      rrTerminalExpr![.symbol .pipe],
      rrExprList1![rrRuleExpr![.pattern]],
      rrTerminalExpr![.symbol .fatArrow],
      rrExprStar![rrRuleExpr![.armStatement]]
    ])
  | `(rrPublicRhs![.armStatement]) => `(rrRuleExpr![.statement])
  | `(rrPublicRhs![.assignmentStatement]) => `(rrExprSeq![
      rrRuleExpr![.expression],
      rrRuleExpr![.assignmentOperator],
      rrRuleExpr![.expression],
      rrTerminalExpr![.symbol .semicolon]
    ])
  | `(rrPublicRhs![.assignmentOperator]) => `(rrExprChoice![
      rrTerminalExpr![.symbol .equal],
      rrTerminalExpr![.symbol .plusEqual],
      rrTerminalExpr![.symbol .minusEqual],
      rrTerminalExpr![.symbol .caretEqual],
      rrTerminalExpr![.symbol .ampEqual],
      rrTerminalExpr![.symbol .pipeEqual],
      rrTerminalExpr![.symbol .percentEqual]
    ])
  | `(rrPublicRhs![.expressionStatement]) => `(rrExprChoice![
      rrExprSeq![
        rrRuleExpr![.expression],
        rrTerminalExpr![.symbol .semicolon]
      ],
      rrRuleExpr![.terminalExpression]
    ])
  | `(rrPublicRhs![.terminalExpression]) => `(rrRuleExpr![.expression])
  | `(rrPublicRhs![.pattern]) => `(rrExprChoice![
      rrTerminalExpr![.symbol .underscore],
      rrRuleExpr![.literal],
      rrExprSeq![
        rrTerminalExpr![.symbol .dot],
        rrTerminalExpr![.category .identifier],
        rrExprOpt![rrExprSeq![
          rrTerminalExpr![.symbol .leftParen],
          rrExprList1![rrRuleExpr![.pattern]],
          rrTerminalExpr![.symbol .rightParen]
        ]]
      ],
      rrExprSeq![
        rrTerminalExpr![.contextualKeyword .comptimeKw],
        rrRuleExpr![.expression]
      ],
      rrExprSeq![
        rrRuleExpr![.qualifiedName],
        rrExprOpt![rrExprSeq![
          rrTerminalExpr![.symbol .leftParen],
          rrExprList1![rrRuleExpr![.pattern]],
          rrTerminalExpr![.symbol .rightParen]
        ]]
      ],
      rrExprSeq![
        rrTerminalExpr![.symbol .leftParen],
        rrTerminalExpr![.symbol .rightParen]
      ],
      rrExprSeq![
        rrTerminalExpr![.symbol .leftParen],
        rrRuleExpr![.pattern],
        rrTerminalExpr![.symbol .rightParen]
      ],
      rrExprSeq![
        rrTerminalExpr![.symbol .leftParen],
        rrRuleExpr![.pattern],
        rrTerminalExpr![.symbol .comma],
        rrRuleExpr![.pattern],
        rrExprStar![rrExprGroup![rrExprSeq![
          rrTerminalExpr![.symbol .comma],
          rrRuleExpr![.pattern]
        ]]],
        rrTerminalExpr![.symbol .rightParen]
      ]
    ])
  | `(rrPublicRhs![.expression]) => `(rrRuleExpr![.annotation])
  | `(rrPublicRhs![.annotation]) => `(rrExprSeq![
      rrRuleExpr![.conditional],
      rrExprOpt![rrExprSeq![
        rrTerminalExpr![.symbol .colon],
        rrRuleExpr![.type]
      ]]
    ])
  | `(rrPublicRhs![.conditional]) => `(rrExprChoice![
      rrExprSeq![
        rrTerminalExpr![.hardKeyword .ifKw],
        rrRuleExpr![.conditional],
        rrTerminalExpr![.contextualKeyword .thenKw],
        rrRuleExpr![.conditional],
        rrTerminalExpr![.hardKeyword .elseKw],
        rrRuleExpr![.conditional]
      ],
      rrExprSeq![
        rrRuleExpr![.logicalOr],
        rrExprOpt![rrExprSeq![
          rrTerminalExpr![.symbol .question],
          rrRuleExpr![.conditional],
          rrTerminalExpr![.symbol .colon],
          rrRuleExpr![.conditional]
        ]]
      ]
    ])
  | `(rrPublicRhs![.logicalOr]) => `(rrExprSeq![
      rrRuleExpr![.logicalAnd],
      rrExprStar![rrExprGroup![rrExprSeq![
        rrTerminalExpr![.symbol .logicalOr],
        rrRuleExpr![.logicalAnd]
      ]]]
    ])
  | `(rrPublicRhs![.logicalAnd]) => `(rrExprSeq![
      rrRuleExpr![.equality],
      rrExprStar![rrExprGroup![rrExprSeq![
        rrTerminalExpr![.symbol .logicalAnd],
        rrRuleExpr![.equality]
      ]]]
    ])
  | `(rrPublicRhs![.equality]) => `(rrExprSeq![
      rrRuleExpr![.relational],
      rrExprOpt![rrExprSeq![
        rrExprGroup![rrExprChoice![
          rrTerminalExpr![.symbol .equalEqual],
          rrTerminalExpr![.symbol .notEqual]
        ]],
        rrRuleExpr![.relational]
      ]]
    ])
  | `(rrPublicRhs![.relational]) => `(rrExprSeq![
      rrRuleExpr![.bitOr],
      rrExprOpt![rrExprSeq![
        rrExprGroup![rrExprChoice![
          rrTerminalExpr![.symbol .less],
          rrTerminalExpr![.symbol .greater],
          rrTerminalExpr![.symbol .lessEqual],
          rrTerminalExpr![.symbol .greaterEqual]
        ]],
        rrRuleExpr![.bitOr]
      ]]
    ])
  | `(rrPublicRhs![.bitOr]) => `(rrExprSeq![
      rrRuleExpr![.bitXor],
      rrExprStar![rrExprGroup![rrExprSeq![
        rrTerminalExpr![.symbol .pipe],
        rrRuleExpr![.bitXor]
      ]]]
    ])
  | `(rrPublicRhs![.bitXor]) => `(rrExprSeq![
      rrRuleExpr![.bitAnd],
      rrExprStar![rrExprGroup![rrExprSeq![
        rrTerminalExpr![.symbol .caret],
        rrRuleExpr![.bitAnd]
      ]]]
    ])
  | `(rrPublicRhs![.bitAnd]) => `(rrExprSeq![
      rrRuleExpr![.additive],
      rrExprStar![rrExprGroup![rrExprSeq![
        rrTerminalExpr![.symbol .amp],
        rrRuleExpr![.additive]
      ]]]
    ])
  | `(rrPublicRhs![.additive]) => `(rrExprSeq![
      rrRuleExpr![.multiplicative],
      rrExprStar![rrExprGroup![rrExprSeq![
        rrExprGroup![rrExprChoice![
          rrTerminalExpr![.symbol .plus],
          rrTerminalExpr![.symbol .minus]
        ]],
        rrRuleExpr![.multiplicative]
      ]]]
    ])
  | `(rrPublicRhs![.multiplicative]) => `(rrExprSeq![
      rrRuleExpr![.prefix],
      rrExprStar![rrExprGroup![rrExprSeq![
        rrExprGroup![rrExprChoice![
          rrTerminalExpr![.symbol .star],
          rrTerminalExpr![.symbol .slash],
          rrTerminalExpr![.symbol .percent]
        ]],
        rrRuleExpr![.prefix]
      ]]]
    ])
  | `(rrPublicRhs![.prefix]) => `(rrExprChoice![
      rrExprSeq![
        rrTerminalExpr![.symbol .bang],
        rrRuleExpr![.prefix]
      ],
      rrRuleExpr![.postfix]
    ])
  | `(rrPublicRhs![.postfix]) => `(rrExprSeq![
      rrRuleExpr![.atom],
      rrExprStar![rrRuleExpr![.postfixPart]]
    ])
  | `(rrPublicRhs![.postfixPart]) => `(rrExprChoice![
      rrExprSeq![
        rrTerminalExpr![.symbol .leftParen],
        rrExprList0![rrRuleExpr![.expression]],
        rrTerminalExpr![.symbol .rightParen]
      ],
      rrExprSeq![
        rrTerminalExpr![.symbol .dot],
        rrTerminalExpr![.category .identifier]
      ],
      rrExprSeq![
        rrTerminalExpr![.symbol .leftBracket],
        rrRuleExpr![.expression],
        rrTerminalExpr![.symbol .rightBracket]
      ]
    ])
  | `(rrPublicRhs![.atom]) => `(rrExprChoice![
      rrRuleExpr![.literal],
      rrTerminalExpr![.category .identifier],
      rrExprSeq![
        rrTerminalExpr![.symbol .dot],
        rrTerminalExpr![.category .identifier],
        rrExprOpt![rrExprSeq![
          rrTerminalExpr![.symbol .leftParen],
          rrExprList0![rrRuleExpr![.expression]],
          rrTerminalExpr![.symbol .rightParen]
        ]]
      ],
      rrExprSeq![
        rrTerminalExpr![.symbol .at],
        rrRuleExpr![.typeAtom]
      ],
      rrRuleExpr![.lambda],
      rrExprSeq![
        rrTerminalExpr![.symbol .leftParen],
        rrTerminalExpr![.symbol .rightParen]
      ],
      rrExprSeq![
        rrTerminalExpr![.symbol .leftParen],
        rrRuleExpr![.expression],
        rrTerminalExpr![.symbol .rightParen]
      ],
      rrExprSeq![
        rrTerminalExpr![.symbol .leftParen],
        rrRuleExpr![.expression],
        rrTerminalExpr![.symbol .comma],
        rrRuleExpr![.expression],
        rrExprStar![rrExprGroup![rrExprSeq![
          rrTerminalExpr![.symbol .comma],
          rrRuleExpr![.expression]
        ]]],
        rrTerminalExpr![.symbol .rightParen]
      ]
    ])
  | `(rrPublicRhs![.lambda]) => `(rrExprSeq![
      rrTerminalExpr![.hardKeyword .lamKw],
      rrTerminalExpr![.symbol .leftParen],
      rrExprList0![rrRuleExpr![.parameter]],
      rrTerminalExpr![.symbol .rightParen],
      rrExprOpt![rrExprSeq![
        rrTerminalExpr![.symbol .arrow],
        rrRuleExpr![.type]
      ]],
      rrRuleExpr![.body]
    ])
  | `(rrPublicRhs![.literal]) => `(rrExprChoice![
      rrTerminalExpr![.category .decimalLiteral],
      rrTerminalExpr![.category .hexadecimalLiteral],
      rrTerminalExpr![.category .stringLiteral]
    ])

local syntax "rrChoiceRoot![" term "]" term : term
local macro_rules
  | `(rrChoiceRoot![$rule:term] $payload:term) =>
      `(EbnfValue.choice (EbnfExpr.children (rrPublicRhs![$rule])) $payload)

local syntax "rrSequenceRoot![" term "]" term : term
local macro_rules
  | `(rrSequenceRoot![$rule:term] $values:term) =>
      `(EbnfValue.sequence (EbnfExpr.children (rrPublicRhs![$rule])) $values)

/-- Exact source-rule reduction for every grammar rule. -/
inductive RuleReduction
    (file : WorkspaceFile) (tokens : List Token) :
    (rule : GrammarRuleId) →
      (origin finish : Boundary tokens) →
      EbnfValue file tokens (m2cV1.rhs rule) →
      RuleValue rule → Prop where
  | module
      (origin finish : Boundary tokens)
      (items : List TopItem)
      (eof : MatchedTerminal file tokens .endOfFile)
      (originEq : origin = Boundary.start tokens)
      (finishEq : finish = Boundary.afterLogicalEOF tokens)
      (eofValue : eof.value = .endOfFile) :
      RuleReduction file tokens .module origin finish
        rrRoot![rrSeq![[
            .star (.atom (.nonterminal .topItem)),
            .atom (.terminal .endOfFile)
          ] |
            rrStar![.atom (.nonterminal .topItem),
              items.map (EbnfValue.ruleAtom .topItem)],
            rrTerm![.endOfFile, eof]
          ]]
        (RuleReduction.moduleLoc file { source := file.id, items })
  | topItemImport
      (origin finish : Boundary tokens)
      (declaration : ImportDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .topItem origin finish
        rrTopItemInput![0, rrRule![.importDecl, declaration]]
        (sourceLoc witness (.importDecl declaration))
  | topItemExport
      (origin finish : Boundary tokens)
      (declaration : ExportDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .topItem origin finish
        rrTopItemInput![1, rrRule![.exportDecl, declaration]]
        (sourceLoc witness (.exportDecl declaration))
  | topItemPragma
      (origin finish : Boundary tokens)
      (declaration : PragmaDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .topItem origin finish
        rrTopItemInput![2, rrRule![.pragmaDecl, declaration]]
        (sourceLoc witness (.pragmaDecl declaration))
  | topItemData
      (origin finish : Boundary tokens)
      (declaration : DataDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .topItem origin finish
        rrTopItemInput![3, rrRule![.dataDecl, declaration]]
        (sourceLoc witness (.dataDecl declaration))
  | topItemTypeAlias
      (origin finish : Boundary tokens)
      (declaration : TypeAliasDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .topItem origin finish
        rrTopItemInput![4, rrRule![.typeAliasDecl, declaration]]
        (sourceLoc witness (.typeAliasDecl declaration))
  | topItemClass
      (origin finish : Boundary tokens)
      (declaration : ClassDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .topItem origin finish
        rrTopItemInput![5, rrRule![.classDecl, declaration]]
        (sourceLoc witness (.classDecl declaration))
  | topItemInstance
      (origin finish : Boundary tokens)
      (declaration : InstanceDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .topItem origin finish
        rrTopItemInput![6, rrRule![.instanceDecl, declaration]]
        (sourceLoc witness (.instanceDecl declaration))
  | topItemContract
      (origin finish : Boundary tokens)
      (declaration : ContractDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .topItem origin finish
        rrTopItemInput![7, rrRule![.contractDecl, declaration]]
        (sourceLoc witness (.contractDecl declaration))
  | topItemFunction
      (origin finish : Boundary tokens)
      (declaration : FunctionDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .topItem origin finish
        rrTopItemInput![8, rrRule![.functionDecl, declaration]]
        (sourceLoc witness (.functionDecl declaration))
  | moduleRefExternal
      (origin finish : Boundary tokens)
      (atToken : MatchedTerminal file tokens (.symbol .at))
      (library : RuleReduction.SpelledTerminalData file tokens
        (.category .pathComponent) ExternalLibraryName)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (next : RuleReduction.SpelledTerminalData file tokens
        (.category .pathComponent) PathSegment)
      (rest : List
        (MatchedTerminal file tokens (.symbol .dot) ×
          RuleReduction.SpelledTerminalData file tokens
            (.category .pathComponent) PathSegment))
      (atMarker : RuleReduction.MarkerProjects file tokens
        atToken .externalSigil)
      (libraryProjects : ExternalLibraryProjects library.matched
        library.spelling library.parsed)
      (nextProjects : PathSegmentProjects next.matched
        next.spelling next.parsed)
      (restProjects : ∀ entry, entry ∈ rest →
        PathSegmentProjects entry.2.matched
          entry.2.spelling entry.2.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .moduleRef origin finish
        rrModuleRefInput![0, rrSeq![[
          .atom (.terminal (.symbol .at)),
          .atom (.terminal (.category .pathComponent)),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.category .pathComponent)),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]))
        ] |
          rrTerm![.symbol .at, atToken],
          rrTerm![.category .pathComponent, library.matched],
          rrTerm![.symbol .dot, dot],
          rrTerm![.category .pathComponent, next.matched],
          rrStar![.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]), rest.map fun entry =>
            rrGroup![.sequence [
              .atom (.terminal (.symbol .dot)),
              .atom (.terminal (.category .pathComponent))
            ], rrSeq![[
              .atom (.terminal (.symbol .dot)),
              .atom (.terminal (.category .pathComponent))
            ] |
              rrTerm![.symbol .dot, entry.1],
              rrTerm![.category .pathComponent, entry.2.matched]
            ]]
          ]
        ]]
        (sourceLoc witness (.external
          (RuleReduction.marker atToken atMarker)
          (RuleReduction.terminalLoc library.matched library.parsed)
          { head := RuleReduction.terminalLoc next.matched next.parsed
            tail := rest.map fun entry =>
              RuleReduction.terminalLoc entry.2.matched entry.2.parsed }))
  | moduleRefStandard
      (origin finish : Boundary tokens)
      (first : MatchedTerminal file tokens (.category .pathComponent))
      (rest : List
        (MatchedTerminal file tokens (.symbol .dot) ×
          RuleReduction.SpelledTerminalData file tokens
            (.category .pathComponent) PathSegment))
      (rootMarker : RuleReduction.MarkerProjects file tokens
        first .standardRoot)
      (restProjects : ∀ entry, entry ∈ rest →
        PathSegmentProjects entry.2.matched
          entry.2.spelling entry.2.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .moduleRef origin finish
        rrModuleRefInput![1, rrSeq![[
          .atom (.terminal (.category .pathComponent)),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]))
        ] |
          rrTerm![.category .pathComponent, first],
          rrStar![.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]), rest.map fun entry =>
            rrGroup![.sequence [
              .atom (.terminal (.symbol .dot)),
              .atom (.terminal (.category .pathComponent))
            ], rrSeq![[
              .atom (.terminal (.symbol .dot)),
              .atom (.terminal (.category .pathComponent))
            ] |
              rrTerm![.symbol .dot, entry.1],
              rrTerm![.category .pathComponent, entry.2.matched]
            ]]
          ]
        ]]
        (sourceLoc witness (.standard
          (RuleReduction.marker first rootMarker)
          (rest.map fun entry =>
            RuleReduction.terminalLoc entry.2.matched entry.2.parsed)))
  | moduleRefLibraryRoot
      (origin finish : Boundary tokens)
      (first : MatchedTerminal file tokens (.category .pathComponent))
      (nextDot : MatchedTerminal file tokens (.symbol .dot))
      (next : RuleReduction.SpelledTerminalData file tokens
        (.category .pathComponent) PathSegment)
      (remaining : List
        (MatchedTerminal file tokens (.symbol .dot) ×
          RuleReduction.SpelledTerminalData file tokens
            (.category .pathComponent) PathSegment))
      (rootMarker : RuleReduction.MarkerProjects file tokens
        first .libraryRoot)
      (nextProjects : PathSegmentProjects next.matched
        next.spelling next.parsed)
      (remainingProjects : ∀ entry, entry ∈ remaining →
        PathSegmentProjects entry.2.matched
          entry.2.spelling entry.2.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .moduleRef origin finish
        rrModuleRefInput![1, rrSeq![[
          .atom (.terminal (.category .pathComponent)),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]))
        ] |
          rrTerm![.category .pathComponent, first],
          rrStar![.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]),
            rrGroup![.sequence [
              .atom (.terminal (.symbol .dot)),
              .atom (.terminal (.category .pathComponent))
            ], rrSeq![[
              .atom (.terminal (.symbol .dot)),
              .atom (.terminal (.category .pathComponent))
            ] |
              rrTerm![.symbol .dot, nextDot],
              rrTerm![.category .pathComponent, next.matched]
            ]] :: remaining.map fun entry =>
              rrGroup![.sequence [
                .atom (.terminal (.symbol .dot)),
                .atom (.terminal (.category .pathComponent))
              ], rrSeq![[
                .atom (.terminal (.symbol .dot)),
                .atom (.terminal (.category .pathComponent))
              ] |
                rrTerm![.symbol .dot, entry.1],
                rrTerm![.category .pathComponent, entry.2.matched]
              ]]
          ]
        ]]
        (sourceLoc witness (.libraryRoot
          (RuleReduction.marker first rootMarker)
          { head := RuleReduction.terminalLoc next.matched next.parsed
            tail := remaining.map fun entry =>
              RuleReduction.terminalLoc entry.2.matched entry.2.parsed }))
  | moduleRefRelativeLibraryEmpty
      (origin finish : Boundary tokens)
      (first : RuleReduction.SpelledTerminalData file tokens
        (.category .pathComponent) PathSegment)
      (firstProjects : PathSegmentProjects first.matched
        first.spelling first.parsed)
      (libraryMarker : RuleReduction.MarkerProjects file tokens
        first.matched .libraryRoot)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .moduleRef origin finish
        rrModuleRefInput![1, rrSeq![[
          .atom (.terminal (.category .pathComponent)),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]))
        ] |
          rrTerm![.category .pathComponent, first.matched],
          rrStar![.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]), []]
        ]]
        (sourceLoc witness (.relative {
          head := RuleReduction.terminalLoc first.matched first.parsed
          tail := []
        }))
  | moduleRefRelativeOther
      (origin finish : Boundary tokens)
      (first : RuleReduction.SpelledTerminalData file tokens
        (.category .pathComponent) PathSegment)
      (rest : List
        (MatchedTerminal file tokens (.symbol .dot) ×
          RuleReduction.SpelledTerminalData file tokens
            (.category .pathComponent) PathSegment))
      (firstProjects : PathSegmentProjects first.matched
        first.spelling first.parsed)
      (restProjects : ∀ entry, entry ∈ rest →
        PathSegmentProjects entry.2.matched
          entry.2.spelling entry.2.parsed)
      (notStandard : first.spelling ≠ "std")
      (notLibrary : first.spelling ≠ "lib")
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .moduleRef origin finish
        rrModuleRefInput![1, rrSeq![[
          .atom (.terminal (.category .pathComponent)),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]))
        ] |
          rrTerm![.category .pathComponent, first.matched],
          rrStar![.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .pathComponent))
          ]), rest.map fun entry =>
            rrGroup![.sequence [
              .atom (.terminal (.symbol .dot)),
              .atom (.terminal (.category .pathComponent))
            ], rrSeq![[
              .atom (.terminal (.symbol .dot)),
              .atom (.terminal (.category .pathComponent))
            ] |
              rrTerm![.symbol .dot, entry.1],
              rrTerm![.category .pathComponent, entry.2.matched]
            ]]
          ]
        ]]
        (sourceLoc witness (.relative {
          head := RuleReduction.terminalLoc first.matched first.parsed
          tail := rest.map fun entry =>
            RuleReduction.terminalLoc entry.2.matched entry.2.parsed
        }))
  | importDeclModule
      (origin finish : Boundary tokens)
      (importKw : MatchedTerminal file tokens
        (.hardKeyword .importKw))
      (reference : ModuleReference)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .importDecl origin finish
        rrRoot![rrChoice![[
          .sequence [
            .atom (.terminal (.hardKeyword .importKw)),
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.symbol .semicolon))
          ],
          .sequence [
            .atom (.terminal (.hardKeyword .importKw)),
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.hardKeyword .asKw)),
            .atom (.terminal (.category .identifier)),
            .atom (.terminal (.symbol .semicolon))
          ],
          .sequence [
            .atom (.terminal (.hardKeyword .importKw)),
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.symbol .leftBrace)),
            .list0 (.atom (.nonterminal .importEntry)),
            .atom (.terminal (.symbol .rightBrace)),
            .optional (.atom (.nonterminal .hidingClause)),
            .atom (.terminal (.symbol .semicolon))
          ]
        ] | 0, rrSeq![[
          .atom (.terminal (.hardKeyword .importKw)),
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .importKw, importKw],
          rrRule![.moduleRef, reference],
          rrTerm![.symbol .semicolon, semicolon]
        ]]]
        (sourceLoc witness {
          moduleRef := reference
          mode := .module none
        })
  | importDeclAliased
      (origin finish : Boundary tokens)
      (importKw : MatchedTerminal file tokens
        (.hardKeyword .importKw))
      (reference : ModuleReference)
      (asKw : MatchedTerminal file tokens (.hardKeyword .asKw))
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .importDecl origin finish
        rrRoot![rrChoice![[
          .sequence [
            .atom (.terminal (.hardKeyword .importKw)),
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.symbol .semicolon))
          ],
          .sequence [
            .atom (.terminal (.hardKeyword .importKw)),
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.hardKeyword .asKw)),
            .atom (.terminal (.category .identifier)),
            .atom (.terminal (.symbol .semicolon))
          ],
          .sequence [
            .atom (.terminal (.hardKeyword .importKw)),
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.symbol .leftBrace)),
            .list0 (.atom (.nonterminal .importEntry)),
            .atom (.terminal (.symbol .rightBrace)),
            .optional (.atom (.nonterminal .hidingClause)),
            .atom (.terminal (.symbol .semicolon))
          ]
        ] | 1, rrSeq![[
          .atom (.terminal (.hardKeyword .importKw)),
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.hardKeyword .asKw)),
          .atom (.terminal (.category .identifier)),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .importKw, importKw],
          rrRule![.moduleRef, reference],
          rrTerm![.hardKeyword .asKw, asKw],
          rrTerm![.category .identifier, name.matched],
          rrTerm![.symbol .semicolon, semicolon]
        ]]]
        (sourceLoc witness {
          moduleRef := reference
          mode := .module (some
            (RuleReduction.terminalLoc name.matched name.parsed))
        })
  | importDeclItems
      (origin finish : Boundary tokens)
      (importKw : MatchedTerminal file tokens
        (.hardKeyword .importKw))
      (reference : ModuleReference)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (entries : List ImportSelectorEntry)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (hidingValue : Option HidingClause)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .importDecl origin finish
        rrRoot![rrChoice![[
          .sequence [
            .atom (.terminal (.hardKeyword .importKw)),
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.symbol .semicolon))
          ],
          .sequence [
            .atom (.terminal (.hardKeyword .importKw)),
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.hardKeyword .asKw)),
            .atom (.terminal (.category .identifier)),
            .atom (.terminal (.symbol .semicolon))
          ],
          .sequence [
            .atom (.terminal (.hardKeyword .importKw)),
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.symbol .leftBrace)),
            .list0 (.atom (.nonterminal .importEntry)),
            .atom (.terminal (.symbol .rightBrace)),
            .optional (.atom (.nonterminal .hidingClause)),
            .atom (.terminal (.symbol .semicolon))
          ]
        ] | 2, rrSeq![[
          .atom (.terminal (.hardKeyword .importKw)),
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.symbol .leftBrace)),
          .list0 (.atom (.nonterminal .importEntry)),
          .atom (.terminal (.symbol .rightBrace)),
          .optional (.atom (.nonterminal .hidingClause)),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .importKw, importKw],
          rrRule![.moduleRef, reference],
          rrTerm![.symbol .dot, dot],
          rrTerm![.symbol .leftBrace, openBrace],
          rrList0![.atom (.nonterminal .importEntry),
            entries.map (EbnfValue.ruleAtom .importEntry)],
          rrTerm![.symbol .rightBrace, closeBrace],
          rrOpt![.atom (.nonterminal .hidingClause),
            hidingValue.map (EbnfValue.ruleAtom .hidingClause)],
          rrTerm![.symbol .semicolon, semicolon]
        ]]]
        (sourceLoc witness {
          moduleRef := reference
          mode := .items
            (RuleReduction.between file openBrace.span closeBrace.span {
              entries := entries
            }) hidingValue
        })
  | importEntryWildcard
      (origin finish : Boundary tokens)
      (star : MatchedTerminal file tokens (.symbol .star))
      (starMarker : RuleReduction.MarkerProjects file tokens
        star .wildcard)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .importEntry origin finish
        rrRoot![rrChoice![[
          .atom (.terminal (.symbol .star)),
          .sequence [
            .atom (.terminal (.category .identifier)),
            .optional (.sequence [
              .atom (.terminal (.hardKeyword .asKw)),
              .atom (.terminal (.category .identifier))
            ])
          ]
        ] | 0, rrTerm![.symbol .star, star]]]
        (sourceLoc witness (.wildcard
          (RuleReduction.marker star starMarker)))
  | importEntryNamed
      (origin finish : Boundary tokens)
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .importEntry origin finish
        rrRoot![rrChoice![[
          .atom (.terminal (.symbol .star)),
          .sequence [
            .atom (.terminal (.category .identifier)),
            .optional (.sequence [
              .atom (.terminal (.hardKeyword .asKw)),
              .atom (.terminal (.category .identifier))
            ])
          ]
        ] | 1, rrSeq![[
          .atom (.terminal (.category .identifier)),
          .optional (.sequence [
            .atom (.terminal (.hardKeyword .asKw)),
            .atom (.terminal (.category .identifier))
          ])
        ] |
          rrTerm![.category .identifier, name.matched],
          rrOpt![.sequence [
            .atom (.terminal (.hardKeyword .asKw)),
            .atom (.terminal (.category .identifier))
          ], none]
        ]]]
        (sourceLoc witness (.named
          (RuleReduction.terminalLoc name.matched name.parsed) none))
  | importEntryAliased
      (origin finish : Boundary tokens)
      (name alias : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (asKw : MatchedTerminal file tokens (.hardKeyword .asKw))
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (aliasProjects : IdentifierProjects alias.matched
        alias.spelling alias.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .importEntry origin finish
        rrRoot![rrChoice![[
          .atom (.terminal (.symbol .star)),
          .sequence [
            .atom (.terminal (.category .identifier)),
            .optional (.sequence [
              .atom (.terminal (.hardKeyword .asKw)),
              .atom (.terminal (.category .identifier))
            ])
          ]
        ] | 1, rrSeq![[
          .atom (.terminal (.category .identifier)),
          .optional (.sequence [
            .atom (.terminal (.hardKeyword .asKw)),
            .atom (.terminal (.category .identifier))
          ])
        ] |
          rrTerm![.category .identifier, name.matched],
          rrOpt![.sequence [
            .atom (.terminal (.hardKeyword .asKw)),
            .atom (.terminal (.category .identifier))
          ], some (rrSeq![[
            .atom (.terminal (.hardKeyword .asKw)),
            .atom (.terminal (.category .identifier))
          ] |
            rrTerm![.hardKeyword .asKw, asKw],
            rrTerm![.category .identifier, alias.matched]
          ])]
        ]]]
        (sourceLoc witness (.named
          (RuleReduction.terminalLoc name.matched name.parsed)
          (some (RuleReduction.terminalLoc alias.matched alias.parsed))))
  | hidingClause
      (origin finish : Boundary tokens)
      (hidingKw : MatchedTerminal file tokens
        (.hardKeyword .hidingKw))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (names : List (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier))
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (nameProjects : ∀ name, name ∈ names →
        IdentifierProjects name.matched name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .hidingClause origin finish
        rrRoot![rrSeq![[
          .atom (.terminal (.hardKeyword .hidingKw)),
          .atom (.terminal (.symbol .leftBrace)),
          .list0 (.atom (.terminal (.category .identifier))),
          .atom (.terminal (.symbol .rightBrace))
        ] |
          rrTerm![.hardKeyword .hidingKw, hidingKw],
          rrTerm![.symbol .leftBrace, openBrace],
          rrList0![.atom (.terminal (.category .identifier)),
            names.map fun name =>
              rrTerm![.category .identifier, name.matched]],
          rrTerm![.symbol .rightBrace, closeBrace]
        ]]
        (sourceLoc witness {
          names := names.map fun name =>
            RuleReduction.terminalLoc name.matched name.parsed
        })
  | exportDeclLocal
      (origin finish : Boundary tokens)
      (exportKw : MatchedTerminal file tokens
        (.hardKeyword .exportKw))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (entries : List ExportEntry)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .exportDecl origin finish
        rrExportDeclInput![0, rrSeq![[
          .atom (.terminal (.hardKeyword .exportKw)),
          .atom (.terminal (.symbol .leftBrace)),
          .list0 (.atom (.nonterminal .localExportEntry)),
          .atom (.terminal (.symbol .rightBrace)),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .exportKw, exportKw],
          rrTerm![.symbol .leftBrace, openBrace],
          rrList0![.atom (.nonterminal .localExportEntry),
            entries.map (EbnfValue.ruleAtom .localExportEntry)],
          rrTerm![.symbol .rightBrace, closeBrace],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness (.local
          (RuleReduction.between file openBrace.span closeBrace.span {
            entries := entries
          })))
  | exportDeclModule
      (origin finish : Boundary tokens)
      (exportKw : MatchedTerminal file tokens
        (.hardKeyword .exportKw))
      (reference : ModuleReference)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .exportDecl origin finish
        rrExportDeclInput![1, rrSeq![[
          .atom (.terminal (.hardKeyword .exportKw)),
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .exportKw, exportKw],
          rrRule![.moduleRef, reference],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness (.module reference none))
  | exportDeclAliased
      (origin finish : Boundary tokens)
      (exportKw : MatchedTerminal file tokens
        (.hardKeyword .exportKw))
      (reference : ModuleReference)
      (asKw : MatchedTerminal file tokens (.hardKeyword .asKw))
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .exportDecl origin finish
        rrExportDeclInput![2, rrSeq![[
          .atom (.terminal (.hardKeyword .exportKw)),
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.hardKeyword .asKw)),
          .atom (.terminal (.category .identifier)),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .exportKw, exportKw],
          rrRule![.moduleRef, reference],
          rrTerm![.hardKeyword .asKw, asKw],
          rrTerm![.category .identifier, name.matched],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness (.module reference
          (some (RuleReduction.terminalLoc name.matched name.parsed))))
  | exportDeclWildcard
      (origin finish : Boundary tokens)
      (exportKw : MatchedTerminal file tokens
        (.hardKeyword .exportKw))
      (reference : ModuleReference)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (star : MatchedTerminal file tokens (.symbol .star))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (starMarker : RuleReduction.MarkerProjects file tokens
        star .wildcard)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .exportDecl origin finish
        rrExportDeclInput![3, rrSeq![[
          .atom (.terminal (.hardKeyword .exportKw)),
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.symbol .star)),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .exportKw, exportKw],
          rrRule![.moduleRef, reference],
          rrTerm![.symbol .dot, dot],
          rrTerm![.symbol .star, star],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness (.from reference
          (RuleReduction.between file dot.span star.span
            (.dotWildcard (RuleReduction.marker star starMarker)))))
  | exportDeclBraced
      (origin finish : Boundary tokens)
      (exportKw : MatchedTerminal file tokens
        (.hardKeyword .exportKw))
      (reference : ModuleReference)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (entries : List RemoteExportEntry)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .exportDecl origin finish
        rrExportDeclInput![4, rrSeq![[
          .atom (.terminal (.hardKeyword .exportKw)),
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.symbol .leftBrace)),
          .list0 (.atom (.nonterminal .remoteExportEntry)),
          .atom (.terminal (.symbol .rightBrace)),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .exportKw, exportKw],
          rrRule![.moduleRef, reference],
          rrTerm![.symbol .dot, dot],
          rrTerm![.symbol .leftBrace, openBrace],
          rrList0![.atom (.nonterminal .remoteExportEntry),
            entries.map (EbnfValue.ruleAtom .remoteExportEntry)],
          rrTerm![.symbol .rightBrace, closeBrace],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness (.from reference
          (RuleReduction.between file openBrace.span closeBrace.span
            (.braced entries))))
  | localExportEntryWildcard
      (origin finish : Boundary tokens)
      (star : MatchedTerminal file tokens (.symbol .star))
      (starMarker : RuleReduction.MarkerProjects file tokens
        star .wildcard)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .localExportEntry origin finish
        rrLocalExportEntryInput![0, rrTerm![.symbol .star, star]]
        (sourceLoc witness (.wildcard
          (RuleReduction.marker star starMarker)))
  | localExportEntryItem
      (origin finish : Boundary tokens)
      (item : ExportItem)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .localExportEntry origin finish
        rrLocalExportEntryInput![1, rrRule![.exportItem, item]]
        (sourceLoc witness (.item item))
  | localExportEntryAllFrom
      (origin finish : Boundary tokens)
      (reference : ModuleReference)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (star : MatchedTerminal file tokens (.symbol .star))
      (starMarker : RuleReduction.MarkerProjects file tokens
        star .wildcard)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .localExportEntry origin finish
        rrLocalExportEntryInput![2, rrSeq![[
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.symbol .star))
        ] |
          rrRule![.moduleRef, reference],
          rrTerm![.symbol .dot, dot],
          rrTerm![.symbol .star, star]
        ]]
        (sourceLoc witness (.allFrom reference
          (RuleReduction.marker star starMarker)))
  | remoteExportEntryWildcard
      (origin finish : Boundary tokens)
      (star : MatchedTerminal file tokens (.symbol .star))
      (starMarker : RuleReduction.MarkerProjects file tokens
        star .wildcard)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .remoteExportEntry origin finish
        rrRemoteExportEntryInput![0, rrTerm![.symbol .star, star]]
        (sourceLoc witness (.wildcard
          (RuleReduction.marker star starMarker)))
  | remoteExportEntryItem
      (origin finish : Boundary tokens)
      (item : ExportItem)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .remoteExportEntry origin finish
        rrRemoteExportEntryInput![1, rrRule![.exportItem, item]]
        (sourceLoc witness (.item item))
  | exportItem
      (origin finish : Boundary tokens)
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (selection : Option ConstructorSelection)
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .exportItem origin finish
        rrRoot![rrSeq![[
          .atom (.terminal (.category .identifier)),
          .optional (.atom (.nonterminal .constructorSelection))
        ] |
          rrTerm![.category .identifier, name.matched],
          rrOpt![.atom (.nonterminal .constructorSelection),
            selection.map (EbnfValue.ruleAtom .constructorSelection)]
        ]]
        (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          constructors := selection
        })
  | constructorSelectionAll
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (star : MatchedTerminal file tokens (.symbol .star))
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (starMarker : RuleReduction.MarkerProjects file tokens
        star .wildcard)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .constructorSelection origin finish
        rrRoot![rrChoice![[
          .sequence [
            .atom (.terminal (.symbol .leftParen)),
            .atom (.terminal (.symbol .star)),
            .atom (.terminal (.symbol .rightParen))
          ],
          .sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.terminal (.category .identifier))),
            .atom (.terminal (.symbol .rightParen))
          ]
        ] | 0, rrSeq![[
          .atom (.terminal (.symbol .leftParen)),
          .atom (.terminal (.symbol .star)),
          .atom (.terminal (.symbol .rightParen))
        ] |
          rrTerm![.symbol .leftParen, openParen],
          rrTerm![.symbol .star, star],
          rrTerm![.symbol .rightParen, closeParen]
        ]]]
        (sourceLoc witness (.all
          (RuleReduction.marker star starMarker)))
  | constructorSelectionNamed
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (names : NonemptyList (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier))
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (headProjects : IdentifierProjects names.head.matched
        names.head.spelling names.head.parsed)
      (tailProjects : ∀ name, name ∈ names.tail →
        IdentifierProjects name.matched name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .constructorSelection origin finish
        rrRoot![rrChoice![[
          .sequence [
            .atom (.terminal (.symbol .leftParen)),
            .atom (.terminal (.symbol .star)),
            .atom (.terminal (.symbol .rightParen))
          ],
          .sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.terminal (.category .identifier))),
            .atom (.terminal (.symbol .rightParen))
          ]
        ] | 1, rrSeq![[
          .atom (.terminal (.symbol .leftParen)),
          .list1 (.atom (.terminal (.category .identifier))),
          .atom (.terminal (.symbol .rightParen))
        ] |
          rrTerm![.symbol .leftParen, openParen],
          rrList1![.atom (.terminal (.category .identifier)), {
            head := rrTerm![.category .identifier, names.head.matched]
            tail := names.tail.map fun name =>
              rrTerm![.category .identifier, name.matched]
          }],
          rrTerm![.symbol .rightParen, closeParen]
        ]]]
        (sourceLoc witness (.named
          (names.map fun name =>
            RuleReduction.terminalLoc name.matched name.parsed)))
  | pragmaDeclNoCoverageCondition
      (origin finish : Boundary tokens)
      (pragmaKw : MatchedTerminal file tokens
        (.hardKeyword .pragmaKw))
      (kindToken : MatchedTerminal file tokens
        (.pragmaName .noCoverageCondition))
      (targets : Option (NonemptyList
        (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier)))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (targetProjects : ∀ values, targets = some values →
        IdentifierProjects values.head.matched
          values.head.spelling values.head.parsed ∧
        ∀ name, name ∈ values.tail →
          IdentifierProjects name.matched name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pragmaDecl origin finish
        rrPragmaDeclInput![0, rrSeq![[
          .atom (.terminal (.hardKeyword .pragmaKw)),
          .atom (.terminal (.pragmaName .noCoverageCondition)),
          .optional (.list1 (.atom (.terminal (.category .identifier)))),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .pragmaKw, pragmaKw],
          rrTerm![.pragmaName .noCoverageCondition, kindToken],
          rrOpt![.list1 (.atom (.terminal (.category .identifier))),
            targets.map fun values =>
              rrList1![.atom (.terminal (.category .identifier)), {
                head := rrTerm![.category .identifier, values.head.matched]
                tail := values.tail.map fun name =>
                  rrTerm![.category .identifier, name.matched]
              }]],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness {
          kind := RuleReduction.terminalLoc kindToken
            .noCoverageCondition
          targets := targets.elim [] fun values =>
            RuleReduction.firstRest (values.map fun name =>
              RuleReduction.terminalLoc name.matched name.parsed)
        })
  | pragmaDeclNoPattersonCondition
      (origin finish : Boundary tokens)
      (pragmaKw : MatchedTerminal file tokens
        (.hardKeyword .pragmaKw))
      (kindToken : MatchedTerminal file tokens
        (.pragmaName .noPattersonCondition))
      (targets : Option (NonemptyList
        (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier)))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (targetProjects : ∀ values, targets = some values →
        IdentifierProjects values.head.matched
          values.head.spelling values.head.parsed ∧
        ∀ name, name ∈ values.tail →
          IdentifierProjects name.matched name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pragmaDecl origin finish
        rrPragmaDeclInput![1, rrSeq![[
          .atom (.terminal (.hardKeyword .pragmaKw)),
          .atom (.terminal (.pragmaName .noPattersonCondition)),
          .optional (.list1 (.atom (.terminal (.category .identifier)))),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .pragmaKw, pragmaKw],
          rrTerm![.pragmaName .noPattersonCondition, kindToken],
          rrOpt![.list1 (.atom (.terminal (.category .identifier))),
            targets.map fun values =>
              rrList1![.atom (.terminal (.category .identifier)), {
                head := rrTerm![.category .identifier, values.head.matched]
                tail := values.tail.map fun name =>
                  rrTerm![.category .identifier, name.matched]
              }]],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness {
          kind := RuleReduction.terminalLoc kindToken
            .noPattersonCondition
          targets := targets.elim [] fun values =>
            RuleReduction.firstRest (values.map fun name =>
              RuleReduction.terminalLoc name.matched name.parsed)
        })
  | pragmaDeclNoBoundedVariableCondition
      (origin finish : Boundary tokens)
      (pragmaKw : MatchedTerminal file tokens
        (.hardKeyword .pragmaKw))
      (kindToken : MatchedTerminal file tokens
        (.pragmaName .noBoundedVariableCondition))
      (targets : Option (NonemptyList
        (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier)))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (targetProjects : ∀ values, targets = some values →
        IdentifierProjects values.head.matched
          values.head.spelling values.head.parsed ∧
        ∀ name, name ∈ values.tail →
          IdentifierProjects name.matched name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pragmaDecl origin finish
        rrPragmaDeclInput![2, rrSeq![[
          .atom (.terminal (.hardKeyword .pragmaKw)),
          .atom (.terminal (.pragmaName .noBoundedVariableCondition)),
          .optional (.list1 (.atom (.terminal (.category .identifier)))),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .pragmaKw, pragmaKw],
          rrTerm![.pragmaName .noBoundedVariableCondition, kindToken],
          rrOpt![.list1 (.atom (.terminal (.category .identifier))),
            targets.map fun values =>
              rrList1![.atom (.terminal (.category .identifier)), {
                head := rrTerm![.category .identifier, values.head.matched]
                tail := values.tail.map fun name =>
                  rrTerm![.category .identifier, name.matched]
              }]],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness {
          kind := RuleReduction.terminalLoc kindToken
            .noBoundedVariableCondition
          targets := targets.elim [] fun values =>
            RuleReduction.firstRest (values.map fun name =>
              RuleReduction.terminalLoc name.matched name.parsed)
        })
  | pragmaDeclNoGenericInstanceFor
      (origin finish : Boundary tokens)
      (pragmaKw : MatchedTerminal file tokens
        (.hardKeyword .pragmaKw))
      (kindToken : MatchedTerminal file tokens
        (.pragmaName .noGenericInstanceFor))
      (targets : Option (NonemptyList
        (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier)))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (targetProjects : ∀ values, targets = some values →
        IdentifierProjects values.head.matched
          values.head.spelling values.head.parsed ∧
        ∀ name, name ∈ values.tail →
          IdentifierProjects name.matched name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pragmaDecl origin finish
        rrPragmaDeclInput![3, rrSeq![[
          .atom (.terminal (.hardKeyword .pragmaKw)),
          .atom (.terminal (.pragmaName .noGenericInstanceFor)),
          .optional (.list1 (.atom (.terminal (.category .identifier)))),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .pragmaKw, pragmaKw],
          rrTerm![.pragmaName .noGenericInstanceFor, kindToken],
          rrOpt![.list1 (.atom (.terminal (.category .identifier))),
            targets.map fun values =>
              rrList1![.atom (.terminal (.category .identifier)), {
                head := rrTerm![.category .identifier, values.head.matched]
                tail := values.tail.map fun name =>
                  rrTerm![.category .identifier, name.matched]
              }]],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness {
          kind := RuleReduction.terminalLoc kindToken
            .noGenericInstanceFor
          targets := targets.elim [] fun values =>
            RuleReduction.firstRest (values.map fun name =>
              RuleReduction.terminalLoc name.matched name.parsed)
        })
  | genericPrefixBare
      (origin finish : Boundary tokens)
      (forallClause : ForallClause)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .genericPrefix origin finish
        rrRoot![rrSeq![[
          .atom (.nonterminal .forallClause),
          .optional (.sequence [
            .atom (.nonterminal .predicateList),
            .atom (.terminal (.symbol .fatArrow))
          ])
        ] |
          rrRule![.forallClause, forallClause],
          rrOpt![.sequence [
            .atom (.nonterminal .predicateList),
            .atom (.terminal (.symbol .fatArrow))
          ], none]
        ]]
        (sourceLoc witness {
          forallClause := forallClause
          context := none
        })
  | genericPrefixContext
      (origin finish : Boundary tokens)
      (forallClause : ForallClause)
      (predicates : NonemptyList Predicate)
      (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .genericPrefix origin finish
        rrRoot![rrSeq![[
          .atom (.nonterminal .forallClause),
          .optional (.sequence [
            .atom (.nonterminal .predicateList),
            .atom (.terminal (.symbol .fatArrow))
          ])
        ] |
          rrRule![.forallClause, forallClause],
          rrOpt![.sequence [
            .atom (.nonterminal .predicateList),
            .atom (.terminal (.symbol .fatArrow))
          ], some (rrSeq![[
            .atom (.nonterminal .predicateList),
            .atom (.terminal (.symbol .fatArrow))
          ] |
            rrRule![.predicateList, predicates],
            rrTerm![.symbol .fatArrow, fatArrow]
          ])]
        ]]
        (sourceLoc witness {
          forallClause := forallClause
          context := some predicates
        })
  | forallClause
      (origin finish : Boundary tokens)
      (forallKw : MatchedTerminal file tokens
        (.hardKeyword .forallKw))
      (first : ForallBinder)
      (rest : List (OptionalCommaValue × ForallBinder))
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .forallClause origin finish
        rrRoot![rrSeq![[
          .atom (.terminal (.hardKeyword .forallKw)),
          .atom (.nonterminal .forallBinder),
          .star (.group (.sequence [
            .atom (.nonterminal .optionalComma),
            .atom (.nonterminal .forallBinder)
          ])),
          .atom (.terminal (.symbol .dot))
        ] |
          rrTerm![.hardKeyword .forallKw, forallKw],
          rrRule![.forallBinder, first],
          rrStar![.group (.sequence [
            .atom (.nonterminal .optionalComma),
            .atom (.nonterminal .forallBinder)
          ]), rest.map fun entry =>
            rrGroup![.sequence [
              .atom (.nonterminal .optionalComma),
              .atom (.nonterminal .forallBinder)
            ], rrSeq![[
              .atom (.nonterminal .optionalComma),
              .atom (.nonterminal .forallBinder)
            ] |
              rrRule![.optionalComma, entry.1],
              rrRule![.forallBinder, entry.2]
            ]]
          ],
          rrTerm![.symbol .dot, dot]
        ]]
        (sourceLoc witness {
          binders := {
            head := first
            tail := rest.map Prod.snd
          }
        })
  | forallBinderBare
      (origin finish : Boundary tokens)
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .forallBinder origin finish
        rrRoot![rrChoice![[
          .atom (.terminal (.category .identifier)),
          .sequence [
            .atom (.terminal (.category .identifier)),
            .atom (.terminal (.symbol .colon)),
            .atom (.nonterminal .qualifiedName),
            .optional (.sequence [
              .atom (.terminal (.symbol .leftParen)),
              .list1 (.atom (.nonterminal .type)),
              .atom (.terminal (.symbol .rightParen))
            ])
          ]
        ] | 0, rrTerm![.category .identifier, name.matched]]]
        (sourceLoc witness (.bare
          (RuleReduction.terminalLoc name.matched name.parsed)))
  | forallBinderBoundedWithoutArguments
      (origin finish : Boundary tokens)
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (colon : MatchedTerminal file tokens (.symbol .colon))
      (className : QualifiedName)
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .forallBinder origin finish
        rrRoot![rrChoice![[
          .atom (.terminal (.category .identifier)),
          .sequence [
            .atom (.terminal (.category .identifier)),
            .atom (.terminal (.symbol .colon)),
            .atom (.nonterminal .qualifiedName),
            .optional (.sequence [
              .atom (.terminal (.symbol .leftParen)),
              .list1 (.atom (.nonterminal .type)),
              .atom (.terminal (.symbol .rightParen))
            ])
          ]
        ] | 1, rrSeq![[
          .atom (.terminal (.category .identifier)),
          .atom (.terminal (.symbol .colon)),
          .atom (.nonterminal .qualifiedName),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ])
        ] |
          rrTerm![.category .identifier, name.matched],
          rrTerm![.symbol .colon, colon],
          rrRule![.qualifiedName, className],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ], none]
        ]]]
        (sourceLoc witness (.bounded
          (RuleReduction.terminalLoc name.matched name.parsed)
          className none))
  | forallBinderBoundedWithArguments
      (origin finish : Boundary tokens)
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (colon : MatchedTerminal file tokens (.symbol .colon))
      (className : QualifiedName)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (arguments : NonemptyList TypeExpr)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .forallBinder origin finish
        rrRoot![rrChoice![[
          .atom (.terminal (.category .identifier)),
          .sequence [
            .atom (.terminal (.category .identifier)),
            .atom (.terminal (.symbol .colon)),
            .atom (.nonterminal .qualifiedName),
            .optional (.sequence [
              .atom (.terminal (.symbol .leftParen)),
              .list1 (.atom (.nonterminal .type)),
              .atom (.terminal (.symbol .rightParen))
            ])
          ]
        ] | 1, rrSeq![[
          .atom (.terminal (.category .identifier)),
          .atom (.terminal (.symbol .colon)),
          .atom (.nonterminal .qualifiedName),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ])
        ] |
          rrTerm![.category .identifier, name.matched],
          rrTerm![.symbol .colon, colon],
          rrRule![.qualifiedName, className],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ], some (rrSeq![[
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ] |
            rrTerm![.symbol .leftParen, openParen],
            rrList1![.atom (.nonterminal .type),
              arguments.map (EbnfValue.ruleAtom .type)],
            rrTerm![.symbol .rightParen, closeParen]
          ])]
        ]]]
        (sourceLoc witness (.bounded
          (RuleReduction.terminalLoc name.matched name.parsed)
          className (RuleReduction.arguments
            (some (openParen, arguments, closeParen, ())))))
  | optionalCommaAbsent
      (origin finish : Boundary tokens) :
      RuleReduction file tokens .optionalComma origin finish
        rrRoot![rrOpt![.atom (.terminal (.symbol .comma)), none]]
        .absent
  | optionalCommaPresent
      (origin finish : Boundary tokens)
      (comma : MatchedTerminal file tokens (.symbol .comma)) :
      RuleReduction file tokens .optionalComma origin finish
        rrRoot![rrOpt![.atom (.terminal (.symbol .comma)),
          some (rrTerm![.symbol .comma, comma])]]
        (.present comma.span)
  | predicateList
      (origin finish : Boundary tokens)
      (predicates : NonemptyList Predicate) :
      RuleReduction file tokens .predicateList origin finish
        rrRoot![rrList1![.atom (.nonterminal .predicate),
          predicates.map (EbnfValue.ruleAtom .predicate)]]
        predicates
  | predicateWithoutArguments
      (origin finish : Boundary tokens)
      (main : TypeExpr)
      (colon : MatchedTerminal file tokens (.symbol .colon))
      (className : QualifiedName)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .predicate origin finish
        rrRoot![rrSeq![[
          .atom (.nonterminal .typeAtom),
          .atom (.terminal (.symbol .colon)),
          .atom (.nonterminal .qualifiedName),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ])
        ] |
          rrRule![.typeAtom, main],
          rrTerm![.symbol .colon, colon],
          rrRule![.qualifiedName, className],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ], none]
        ]]
        (sourceLoc witness {
          main := main
          className := className
          parameters := none
        })
  | predicateWithArguments
      (origin finish : Boundary tokens)
      (main : TypeExpr)
      (colon : MatchedTerminal file tokens (.symbol .colon))
      (className : QualifiedName)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (parameters : NonemptyList TypeExpr)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .predicate origin finish
        rrRoot![rrSeq![[
          .atom (.nonterminal .typeAtom),
          .atom (.terminal (.symbol .colon)),
          .atom (.nonterminal .qualifiedName),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ])
        ] |
          rrRule![.typeAtom, main],
          rrTerm![.symbol .colon, colon],
          rrRule![.qualifiedName, className],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ], some (rrSeq![[
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ] |
            rrTerm![.symbol .leftParen, openParen],
            rrList1![.atom (.nonterminal .type),
              parameters.map (EbnfValue.ruleAtom .type)],
            rrTerm![.symbol .rightParen, closeParen]
          ])]
        ]]
        (sourceLoc witness {
          main := main
          className := className
          parameters := RuleReduction.arguments
            (some (openParen, parameters, closeParen, ()))
        })
  | functionSignature
      (origin finish : Boundary tokens)
      (genericPrefix : Option GenericPrefix)
      (publicToken : Option (MatchedTerminal file tokens
        (.hardKeyword .publicKw)))
      (payableToken : Option (MatchedTerminal file tokens
        (.hardKeyword .payableKw)))
      (functionKw : MatchedTerminal file tokens
        (.hardKeyword .functionKw))
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (parameters : List Parameter)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (returnValue : Option
        (MatchedTerminal file tokens (.symbol .arrow) ×
          (TypeExpr × Unit)))
      (publicProjects : ∀ terminal, publicToken = some terminal →
        RuleReduction.MarkerProjects file tokens terminal .publicModifier)
      (payableProjects : ∀ terminal, payableToken = some terminal →
        RuleReduction.MarkerProjects file tokens terminal .payableModifier)
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .functionSignature origin finish
        rrRoot![rrSeq![[
          .optional (.atom (.nonterminal .genericPrefix)),
          .optional (.atom (.terminal (.hardKeyword .publicKw))),
          .optional (.atom (.terminal (.hardKeyword .payableKw))),
          .atom (.terminal (.hardKeyword .functionKw)),
          .atom (.terminal (.category .identifier)),
          .atom (.terminal (.symbol .leftParen)),
          .list0 (.atom (.nonterminal .parameter)),
          .atom (.terminal (.symbol .rightParen)),
          .optional (.sequence [
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)
          ])
        ] |
          rrOpt![.atom (.nonterminal .genericPrefix),
            genericPrefix.map (EbnfValue.ruleAtom .genericPrefix)],
          rrOpt![.atom (.terminal (.hardKeyword .publicKw)),
            publicToken.map fun terminal =>
              rrTerm![.hardKeyword .publicKw, terminal]],
          rrOpt![.atom (.terminal (.hardKeyword .payableKw)),
            payableToken.map fun terminal =>
              rrTerm![.hardKeyword .payableKw, terminal]],
          rrTerm![.hardKeyword .functionKw, functionKw],
          rrTerm![.category .identifier, name.matched],
          rrTerm![.symbol .leftParen, openParen],
          rrList0![.atom (.nonterminal .parameter),
            parameters.map (EbnfValue.ruleAtom .parameter)],
          rrTerm![.symbol .rightParen, closeParen],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)
          ], returnValue.map fun value =>
            rrSeq![[
              .atom (.terminal (.symbol .arrow)),
              .atom (.nonterminal .type)
            ] |
              rrTerm![.symbol .arrow, value.1],
              rrRule![.type, value.2.1]
            ]]
        ]]
        (sourceLoc witness {
          genericPrefix := genericPrefix
          «public» := match publicToken with
            | none => none
            | some terminal => some (RuleReduction.marker terminal
                (publicProjects terminal rfl))
          payable := match payableToken with
            | none => none
            | some terminal => some (RuleReduction.marker terminal
                (payableProjects terminal rfl))
          name := RuleReduction.terminalLoc name.matched name.parsed
          parameters := parameters
          returnType := returnValue.map fun value => value.2.1
        })
  | functionDecl
      (origin finish : Boundary tokens)
      (signature : FunctionSignature)
      (body : Body)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .functionDecl origin finish
        rrRoot![rrSeq![[
          .atom (.nonterminal .functionSignature),
          .atom (.nonterminal .body)
        ] |
          rrRule![.functionSignature, signature],
          rrRule![.body, body]
        ]]
        (sourceLoc witness {
          signature := signature
          body := body
        })
  | classMethod
      (origin finish : Boundary tokens)
      (signature : FunctionSignature)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .classMethod origin finish
        rrRoot![rrSeq![[
          .atom (.nonterminal .functionSignature),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrRule![.functionSignature, signature],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness {
          signature := signature
          terminator := semicolon.span
        })
  | dataDecl
      (origin finish : Boundary tokens)
      (dataKw : MatchedTerminal file tokens (.hardKeyword .dataKw))
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (parameters : Option
        (MatchedTerminal file tokens (.symbol .leftParen) ×
          (NonemptyList (RuleReduction.SpelledTerminalData file tokens
            (.category .identifier) Identifier) ×
            (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
      (constructors : Option
        (MatchedTerminal file tokens (.symbol .equal) ×
          (DataConstructor ×
            (List
              (MatchedTerminal file tokens (.symbol .pipe) ×
                DataConstructor) × Unit))))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (parameterProjects : ∀ value, parameters = some value →
        IdentifierProjects value.2.1.head.matched
          value.2.1.head.spelling value.2.1.head.parsed ∧
        ∀ parameter, parameter ∈ value.2.1.tail →
          IdentifierProjects parameter.matched
            parameter.spelling parameter.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .dataDecl origin finish
        rrRoot![rrSeq![[
          .atom (.terminal (.hardKeyword .dataKw)),
          .atom (.terminal (.category .identifier)),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.terminal (.category .identifier))),
            .atom (.terminal (.symbol .rightParen))
          ]),
          .optional (.sequence [
            .atom (.terminal (.symbol .equal)),
            .atom (.nonterminal .dataConstructor),
            .star (.group (.sequence [
              .atom (.terminal (.symbol .pipe)),
              .atom (.nonterminal .dataConstructor)
            ]))
          ]),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .dataKw, dataKw],
          rrTerm![.category .identifier, name.matched],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.terminal (.category .identifier))),
            .atom (.terminal (.symbol .rightParen))
          ], parameters.map fun value =>
            rrSeq![[
              .atom (.terminal (.symbol .leftParen)),
              .list1 (.atom (.terminal (.category .identifier))),
              .atom (.terminal (.symbol .rightParen))
            ] |
              rrTerm![.symbol .leftParen, value.1],
              rrList1![.atom (.terminal (.category .identifier)), {
                head := rrTerm![.category .identifier,
                  value.2.1.head.matched]
                tail := value.2.1.tail.map fun parameter =>
                  rrTerm![.category .identifier, parameter.matched]
              }],
              rrTerm![.symbol .rightParen, value.2.2.1]
            ]],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .equal)),
            .atom (.nonterminal .dataConstructor),
            .star (.group (.sequence [
              .atom (.terminal (.symbol .pipe)),
              .atom (.nonterminal .dataConstructor)
            ]))
          ], constructors.map fun value =>
            rrSeq![[
              .atom (.terminal (.symbol .equal)),
              .atom (.nonterminal .dataConstructor),
              .star (.group (.sequence [
                .atom (.terminal (.symbol .pipe)),
                .atom (.nonterminal .dataConstructor)
              ]))
            ] |
              rrTerm![.symbol .equal, value.1],
              rrRule![.dataConstructor, value.2.1],
              rrStar![.group (.sequence [
                .atom (.terminal (.symbol .pipe)),
                .atom (.nonterminal .dataConstructor)
              ]), value.2.2.1.map fun entry =>
                rrGroup![.sequence [
                  .atom (.terminal (.symbol .pipe)),
                  .atom (.nonterminal .dataConstructor)
                ], rrSeq![[
                  .atom (.terminal (.symbol .pipe)),
                  .atom (.nonterminal .dataConstructor)
                ] |
                  rrTerm![.symbol .pipe, entry.1],
                  rrRule![.dataConstructor, entry.2]
                ]]
              ]
            ]],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          parameters := parameters.map fun value =>
            value.2.1.map fun parameter =>
              RuleReduction.terminalLoc
                parameter.matched parameter.parsed
          constructors := constructors.map fun value => {
            head := value.2.1
            tail := value.2.2.1.map Prod.snd
          }
        })
  | dataConstructorWithoutArguments
      (origin finish : Boundary tokens)
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .dataConstructor origin finish
        rrRoot![rrSeq![[
          .atom (.terminal (.category .identifier)),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ])
        ] |
          rrTerm![.category .identifier, name.matched],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ], none]
        ]]
        (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          fields := none
        })
  | dataConstructorWithArguments
      (origin finish : Boundary tokens)
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (fields : NonemptyList TypeExpr)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .dataConstructor origin finish
        rrRoot![rrSeq![[
          .atom (.terminal (.category .identifier)),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ])
        ] |
          rrTerm![.category .identifier, name.matched],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ], some (rrSeq![[
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ] |
            rrTerm![.symbol .leftParen, openParen],
            rrList1![.atom (.nonterminal .type),
              fields.map (EbnfValue.ruleAtom .type)],
            rrTerm![.symbol .rightParen, closeParen]
          ])]
        ]]
        (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          fields := RuleReduction.arguments
            (some (openParen, fields, closeParen, ()))
        })
  | typeAliasDecl
      (origin finish : Boundary tokens)
      (typeKw : MatchedTerminal file tokens (.hardKeyword .typeKw))
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (parameters : Option
        (MatchedTerminal file tokens (.symbol .leftParen) ×
          (NonemptyList (RuleReduction.SpelledTerminalData file tokens
            (.category .identifier) Identifier) ×
            (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
      (equal : MatchedTerminal file tokens (.symbol .equal))
      (body : TypeExpr)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (parameterProjects : ∀ value, parameters = some value →
        IdentifierProjects value.2.1.head.matched
          value.2.1.head.spelling value.2.1.head.parsed ∧
        ∀ parameter, parameter ∈ value.2.1.tail →
          IdentifierProjects parameter.matched
            parameter.spelling parameter.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .typeAliasDecl origin finish
        rrRoot![rrSeq![[
          .atom (.terminal (.hardKeyword .typeKw)),
          .atom (.terminal (.category .identifier)),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.terminal (.category .identifier))),
            .atom (.terminal (.symbol .rightParen))
          ]),
          .atom (.terminal (.symbol .equal)),
          .atom (.nonterminal .type),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.hardKeyword .typeKw, typeKw],
          rrTerm![.category .identifier, name.matched],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.terminal (.category .identifier))),
            .atom (.terminal (.symbol .rightParen))
          ], parameters.map fun value =>
            rrSeq![[
              .atom (.terminal (.symbol .leftParen)),
              .list1 (.atom (.terminal (.category .identifier))),
              .atom (.terminal (.symbol .rightParen))
            ] |
              rrTerm![.symbol .leftParen, value.1],
              rrList1![.atom (.terminal (.category .identifier)), {
                head := rrTerm![.category .identifier,
                  value.2.1.head.matched]
                tail := value.2.1.tail.map fun parameter =>
                  rrTerm![.category .identifier, parameter.matched]
              }],
              rrTerm![.symbol .rightParen, value.2.2.1]
            ]],
          rrTerm![.symbol .equal, equal],
          rrRule![.type, body],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          parameters := parameters.map fun value =>
            value.2.1.map fun parameter =>
              RuleReduction.terminalLoc
                parameter.matched parameter.parsed
          body := body
        })
  | classDecl
      (origin finish : Boundary tokens)
      (genericPrefix : Option GenericPrefix)
      (classKw : MatchedTerminal file tokens (.hardKeyword .classKw))
      (main : TypeExpr)
      (colon : MatchedTerminal file tokens (.symbol .colon))
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (parameters : Option
        (MatchedTerminal file tokens (.symbol .leftParen) ×
          (NonemptyList TypeExpr ×
            (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (methods : List ClassMethodDecl)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .classDecl origin finish
        rrRoot![rrSeq![[
          .optional (.atom (.nonterminal .genericPrefix)),
          .atom (.terminal (.hardKeyword .classKw)),
          .atom (.nonterminal .typeAtom),
          .atom (.terminal (.symbol .colon)),
          .atom (.terminal (.category .identifier)),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ]),
          .atom (.terminal (.symbol .leftBrace)),
          .star (.atom (.nonterminal .classMethod)),
          .atom (.terminal (.symbol .rightBrace))
        ] |
          rrOpt![.atom (.nonterminal .genericPrefix),
            genericPrefix.map (EbnfValue.ruleAtom .genericPrefix)],
          rrTerm![.hardKeyword .classKw, classKw],
          rrRule![.typeAtom, main],
          rrTerm![.symbol .colon, colon],
          rrTerm![.category .identifier, name.matched],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ], parameters.map fun value =>
            rrSeq![[
              .atom (.terminal (.symbol .leftParen)),
              .list1 (.atom (.nonterminal .type)),
              .atom (.terminal (.symbol .rightParen))
            ] |
              rrTerm![.symbol .leftParen, value.1],
              rrList1![.atom (.nonterminal .type),
                value.2.1.map (EbnfValue.ruleAtom .type)],
              rrTerm![.symbol .rightParen, value.2.2.1]
            ]],
          rrTerm![.symbol .leftBrace, openBrace],
          rrStar![.atom (.nonterminal .classMethod),
            methods.map (EbnfValue.ruleAtom .classMethod)],
          rrTerm![.symbol .rightBrace, closeBrace]
        ]]
        (sourceLoc witness {
          genericPrefix := genericPrefix
          main := main
          className := RuleReduction.terminalLoc name.matched name.parsed
          parameters := RuleReduction.arguments parameters
          methods := methods
        })
  | instanceDecl
      (origin finish : Boundary tokens)
      (genericPrefix : Option GenericPrefix)
      (defaultToken : Option (MatchedTerminal file tokens
        (.hardKeyword .defaultKw)))
      (instanceKw : MatchedTerminal file tokens
        (.hardKeyword .instanceKw))
      (main : TypeExpr)
      (colon : MatchedTerminal file tokens (.symbol .colon))
      (className : QualifiedName)
      (parameters : Option
        (MatchedTerminal file tokens (.symbol .leftParen) ×
          (NonemptyList TypeExpr ×
            (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (methods : List FunctionDecl)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (defaultProjects : ∀ terminal, defaultToken = some terminal →
        RuleReduction.MarkerProjects file tokens terminal .defaultModifier)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .instanceDecl origin finish
        rrRoot![rrSeq![[
          .optional (.atom (.nonterminal .genericPrefix)),
          .optional (.atom (.terminal (.hardKeyword .defaultKw))),
          .atom (.terminal (.hardKeyword .instanceKw)),
          .atom (.nonterminal .typeAtom),
          .atom (.terminal (.symbol .colon)),
          .atom (.nonterminal .qualifiedName),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ]),
          .atom (.terminal (.symbol .leftBrace)),
          .star (.atom (.nonterminal .instanceMethod)),
          .atom (.terminal (.symbol .rightBrace))
        ] |
          rrOpt![.atom (.nonterminal .genericPrefix),
            genericPrefix.map (EbnfValue.ruleAtom .genericPrefix)],
          rrOpt![.atom (.terminal (.hardKeyword .defaultKw)),
            defaultToken.map fun terminal =>
              rrTerm![.hardKeyword .defaultKw, terminal]],
          rrTerm![.hardKeyword .instanceKw, instanceKw],
          rrRule![.typeAtom, main],
          rrTerm![.symbol .colon, colon],
          rrRule![.qualifiedName, className],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ], parameters.map fun value =>
            rrSeq![[
              .atom (.terminal (.symbol .leftParen)),
              .list1 (.atom (.nonterminal .type)),
              .atom (.terminal (.symbol .rightParen))
            ] |
              rrTerm![.symbol .leftParen, value.1],
              rrList1![.atom (.nonterminal .type),
                value.2.1.map (EbnfValue.ruleAtom .type)],
              rrTerm![.symbol .rightParen, value.2.2.1]
            ]],
          rrTerm![.symbol .leftBrace, openBrace],
          rrStar![.atom (.nonterminal .instanceMethod),
            methods.map (EbnfValue.ruleAtom .instanceMethod)],
          rrTerm![.symbol .rightBrace, closeBrace]
        ]]
        (sourceLoc witness {
          genericPrefix := genericPrefix
          default := match defaultToken with
            | none => none
            | some terminal => some (RuleReduction.marker terminal
                (defaultProjects terminal rfl))
          main := main
          className := className
          parameters := RuleReduction.arguments parameters
          methods := methods
        })
  | instanceMethod
      (origin finish : Boundary tokens)
      (functionValue : FunctionDecl) :
      RuleReduction file tokens .instanceMethod origin finish
        rrRoot![rrRule![.functionDecl, functionValue]]
        functionValue
  | contractDecl
      (origin finish : Boundary tokens)
      (contractKw : MatchedTerminal file tokens
        (.hardKeyword .contractKw))
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (parameters : Option
        (MatchedTerminal file tokens (.symbol .leftParen) ×
          (NonemptyList (RuleReduction.SpelledTerminalData file tokens
            (.category .identifier) Identifier) ×
            (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (members : List ContractMember)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (parameterProjects : ∀ value, parameters = some value →
        IdentifierProjects value.2.1.head.matched
          value.2.1.head.spelling value.2.1.head.parsed ∧
        ∀ parameter, parameter ∈ value.2.1.tail →
          IdentifierProjects parameter.matched
            parameter.spelling parameter.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .contractDecl origin finish
        rrRoot![rrSeq![[
          .atom (.terminal (.hardKeyword .contractKw)),
          .atom (.terminal (.category .identifier)),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.terminal (.category .identifier))),
            .atom (.terminal (.symbol .rightParen))
          ]),
          .atom (.terminal (.symbol .leftBrace)),
          .star (.atom (.nonterminal .contractMember)),
          .atom (.terminal (.symbol .rightBrace))
        ] |
          rrTerm![.hardKeyword .contractKw, contractKw],
          rrTerm![.category .identifier, name.matched],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.terminal (.category .identifier))),
            .atom (.terminal (.symbol .rightParen))
          ], parameters.map fun value =>
            rrSeq![[
              .atom (.terminal (.symbol .leftParen)),
              .list1 (.atom (.terminal (.category .identifier))),
              .atom (.terminal (.symbol .rightParen))
            ] |
              rrTerm![.symbol .leftParen, value.1],
              rrList1![.atom (.terminal (.category .identifier)), {
                head := rrTerm![.category .identifier,
                  value.2.1.head.matched]
                tail := value.2.1.tail.map fun parameter =>
                  rrTerm![.category .identifier, parameter.matched]
              }],
              rrTerm![.symbol .rightParen, value.2.2.1]
            ]],
          rrTerm![.symbol .leftBrace, openBrace],
          rrStar![.atom (.nonterminal .contractMember),
            members.map (EbnfValue.ruleAtom .contractMember)],
          rrTerm![.symbol .rightBrace, closeBrace]
        ]]
        (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          parameters := parameters.map fun value =>
            value.2.1.map fun parameter =>
              RuleReduction.terminalLoc
                parameter.matched parameter.parsed
          members := members
        })
  | contractMemberData
      (origin finish : Boundary tokens)
      (declaration : DataDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .contractMember origin finish
        rrContractMemberInput![0, rrRule![.dataDecl, declaration]]
        (sourceLoc witness (.dataDecl declaration))
  | contractMemberTypeAlias
      (origin finish : Boundary tokens)
      (declaration : TypeAliasDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .contractMember origin finish
        rrContractMemberInput![1, rrRule![.typeAliasDecl, declaration]]
        (sourceLoc witness (.typeAlias declaration))
  | contractMemberField
      (origin finish : Boundary tokens)
      (declaration : FieldDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .contractMember origin finish
        rrContractMemberInput![2, rrRule![.fieldDecl, declaration]]
        (sourceLoc witness (.field declaration))
  | contractMemberFunction
      (origin finish : Boundary tokens)
      (declaration : FunctionDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .contractMember origin finish
        rrContractMemberInput![3, rrRule![.functionDecl, declaration]]
        (sourceLoc witness (.function declaration))
  | contractMemberFallback
      (origin finish : Boundary tokens)
      (declaration : FallbackDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .contractMember origin finish
        rrContractMemberInput![4, rrRule![.fallbackDecl, declaration]]
        (sourceLoc witness (.fallback declaration))
  | contractMemberConstructor
      (origin finish : Boundary tokens)
      (declaration : ContractConstructorDecl)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .contractMember origin finish
        rrContractMemberInput![5,
          rrRule![.contractConstructorDecl, declaration]]
        (sourceLoc witness (.constructor declaration))
  | fieldDecl
      (origin finish : Boundary tokens)
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (colon : MatchedTerminal file tokens (.symbol .colon))
      (typeValue : TypeExpr)
      (initializer : Option
        (MatchedTerminal file tokens (.symbol .equal) ×
          (Expression × Unit)))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .fieldDecl origin finish
        rrRoot![rrSeq![[
          .atom (.terminal (.category .identifier)),
          .atom (.terminal (.symbol .colon)),
          .atom (.nonterminal .type),
          .optional (.sequence [
            .atom (.terminal (.symbol .equal)),
            .atom (.nonterminal .expression)
          ]),
          .atom (.terminal (.symbol .semicolon))
        ] |
          rrTerm![.category .identifier, name.matched],
          rrTerm![.symbol .colon, colon],
          rrRule![.type, typeValue],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .equal)),
            .atom (.nonterminal .expression)
          ], initializer.map fun value =>
            rrSeq![[
              .atom (.terminal (.symbol .equal)),
              .atom (.nonterminal .expression)
            ] |
              rrTerm![.symbol .equal, value.1],
              rrRule![.expression, value.2.1]
            ]],
          rrTerm![.symbol .semicolon, semicolon]
        ]]
        (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          type := typeValue
          initializer := initializer.map fun value => value.2.1
        })
  | fallbackDecl
      (origin finish : Boundary tokens)
      (genericPrefix : Option GenericPrefix)
      (publicToken : Option (MatchedTerminal file tokens
        (.hardKeyword .publicKw)))
      (payableToken : Option (MatchedTerminal file tokens
        (.hardKeyword .payableKw)))
      (fallbackKw : MatchedTerminal file tokens
        (.hardKeyword .fallbackKw))
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (parameters : List Parameter)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (returnValue : Option
        (MatchedTerminal file tokens (.symbol .arrow) ×
          (TypeExpr × Unit)))
      (body : Body)
      (publicProjects : ∀ terminal, publicToken = some terminal →
        RuleReduction.MarkerProjects file tokens terminal .publicModifier)
      (payableProjects : ∀ terminal, payableToken = some terminal →
        RuleReduction.MarkerProjects file tokens terminal .payableModifier)
      (fallbackProjects : RuleReduction.MarkerProjects file tokens
        fallbackKw .fallbackName)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .fallbackDecl origin finish
        rrRoot![rrSeq![[
          .optional (.atom (.nonterminal .genericPrefix)),
          .optional (.atom (.terminal (.hardKeyword .publicKw))),
          .optional (.atom (.terminal (.hardKeyword .payableKw))),
          .atom (.terminal (.hardKeyword .fallbackKw)),
          .atom (.terminal (.symbol .leftParen)),
          .list0 (.atom (.nonterminal .parameter)),
          .atom (.terminal (.symbol .rightParen)),
          .optional (.sequence [
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)
          ]),
          .atom (.nonterminal .body)
        ] |
          rrOpt![.atom (.nonterminal .genericPrefix),
            genericPrefix.map (EbnfValue.ruleAtom .genericPrefix)],
          rrOpt![.atom (.terminal (.hardKeyword .publicKw)),
            publicToken.map fun terminal =>
              rrTerm![.hardKeyword .publicKw, terminal]],
          rrOpt![.atom (.terminal (.hardKeyword .payableKw)),
            payableToken.map fun terminal =>
              rrTerm![.hardKeyword .payableKw, terminal]],
          rrTerm![.hardKeyword .fallbackKw, fallbackKw],
          rrTerm![.symbol .leftParen, openParen],
          rrList0![.atom (.nonterminal .parameter),
            parameters.map (EbnfValue.ruleAtom .parameter)],
          rrTerm![.symbol .rightParen, closeParen],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)
          ], returnValue.map fun value =>
            rrSeq![[
              .atom (.terminal (.symbol .arrow)),
              .atom (.nonterminal .type)
            ] |
              rrTerm![.symbol .arrow, value.1],
              rrRule![.type, value.2.1]
            ]],
          rrRule![.body, body]
        ]]
        (sourceLoc witness {
          genericPrefix := genericPrefix
          «public» := match publicToken with
            | none => none
            | some terminal => some (RuleReduction.marker terminal
                (publicProjects terminal rfl))
          payable := match payableToken with
            | none => none
            | some terminal => some (RuleReduction.marker terminal
                (payableProjects terminal rfl))
          marker := RuleReduction.marker fallbackKw fallbackProjects
          parameters := parameters
          returnType := returnValue.map fun value => value.2.1
          body := body
        })
  | contractConstructorDecl
      (origin finish : Boundary tokens)
      (publicToken : Option (MatchedTerminal file tokens
        (.hardKeyword .publicKw)))
      (payableToken : Option (MatchedTerminal file tokens
        (.hardKeyword .payableKw)))
      (constructorKw : MatchedTerminal file tokens
        (.hardKeyword .constructorKw))
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (parameters : List Parameter)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (body : Body)
      (publicProjects : ∀ terminal, publicToken = some terminal →
        RuleReduction.MarkerProjects file tokens terminal .publicModifier)
      (payableProjects : ∀ terminal, payableToken = some terminal →
        RuleReduction.MarkerProjects file tokens terminal .payableModifier)
      (constructorProjects : RuleReduction.MarkerProjects file tokens
        constructorKw .contractConstructorName)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .contractConstructorDecl origin finish
        rrRoot![rrSeq![[
          .optional (.atom (.terminal (.hardKeyword .publicKw))),
          .optional (.atom (.terminal (.hardKeyword .payableKw))),
          .atom (.terminal (.hardKeyword .constructorKw)),
          .atom (.terminal (.symbol .leftParen)),
          .list0 (.atom (.nonterminal .parameter)),
          .atom (.terminal (.symbol .rightParen)),
          .atom (.nonterminal .body)
        ] |
          rrOpt![.atom (.terminal (.hardKeyword .publicKw)),
            publicToken.map fun terminal =>
              rrTerm![.hardKeyword .publicKw, terminal]],
          rrOpt![.atom (.terminal (.hardKeyword .payableKw)),
            payableToken.map fun terminal =>
              rrTerm![.hardKeyword .payableKw, terminal]],
          rrTerm![.hardKeyword .constructorKw, constructorKw],
          rrTerm![.symbol .leftParen, openParen],
          rrList0![.atom (.nonterminal .parameter),
            parameters.map (EbnfValue.ruleAtom .parameter)],
          rrTerm![.symbol .rightParen, closeParen],
          rrRule![.body, body]
        ]]
        (sourceLoc witness {
          «public» := match publicToken with
            | none => none
            | some terminal => some (RuleReduction.marker terminal
                (publicProjects terminal rfl))
          payable := match payableToken with
            | none => none
            | some terminal => some (RuleReduction.marker terminal
                (payableProjects terminal rfl))
          marker := RuleReduction.marker constructorKw constructorProjects
          parameters := parameters
          body := body
        })
  | parameter
      (origin finish : Boundary tokens)
      (comptimeToken : Option (MatchedTerminal file tokens
        (.contextualKeyword .comptimeKw)))
      (name : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (typeValue : Option
        (MatchedTerminal file tokens (.symbol .colon) ×
          (TypeExpr × Unit)))
      (comptimeProjects : ∀ terminal, comptimeToken = some terminal →
        RuleReduction.MarkerProjects file tokens terminal .comptimeModifier)
      (nameProjects : IdentifierProjects name.matched
        name.spelling name.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .parameter origin finish
        rrRoot![rrSeq![[
          .optional (.atom (.terminal
            (.contextualKeyword .comptimeKw))),
          .atom (.terminal (.category .identifier)),
          .optional (.sequence [
            .atom (.terminal (.symbol .colon)),
            .atom (.nonterminal .type)
          ])
        ] |
          rrOpt![.atom (.terminal (.contextualKeyword .comptimeKw)),
            comptimeToken.map fun terminal =>
              rrTerm![.contextualKeyword .comptimeKw, terminal]],
          rrTerm![.category .identifier, name.matched],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .colon)),
            .atom (.nonterminal .type)
          ], typeValue.map fun value =>
            rrSeq![[
              .atom (.terminal (.symbol .colon)),
              .atom (.nonterminal .type)
            ] |
              rrTerm![.symbol .colon, value.1],
              rrRule![.type, value.2.1]
            ]]
        ]]
        (sourceLoc witness {
          comptime := match comptimeToken with
            | none => none
            | some terminal => some (RuleReduction.marker terminal
                (comptimeProjects terminal rfl))
          name := RuleReduction.terminalLoc name.matched name.parsed
          type := typeValue.map fun value => value.2.1
        })
  | body
      (origin finish : Boundary tokens)
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (statements : List Statement)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .body origin finish
        rrRoot![rrSeq![[
          .atom (.terminal (.symbol .leftBrace)),
          .star (.atom (.nonterminal .statement)),
          .atom (.terminal (.symbol .rightBrace))
        ] |
          rrTerm![.symbol .leftBrace, openBrace],
          rrStar![.atom (.nonterminal .statement),
            statements.map (EbnfValue.ruleAtom .statement)],
          rrTerm![.symbol .rightBrace, closeBrace]
        ]]
        (sourceLoc witness {
          origin := .braced openBrace.span closeBrace.span
          statements := statements
        })
  | typeComptime
      (origin finish : Boundary tokens)
      (comptimeToken : MatchedTerminal file tokens
        (.contextualKeyword .comptimeKw))
      (inner : TypeExpr)
      (comptimeProjects : RuleReduction.MarkerProjects file tokens
        comptimeToken .comptimeModifier)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .type origin finish
        rrTypeInput![0, rrSeq![[
          .atom (.terminal (.contextualKeyword .comptimeKw)),
          .atom (.nonterminal .type)
        ] |
          rrTerm![.contextualKeyword .comptimeKw, comptimeToken],
          rrRule![.type, inner]
        ]]
        (sourceLoc witness (.comptime
          (RuleReduction.marker comptimeToken comptimeProjects) inner))
  | typeAtomOnly
      (origin finish : Boundary tokens)
      (atom : TypeExpr) :
      RuleReduction file tokens .type origin finish
        rrTypeInput![1, rrSeq![[
          .atom (.nonterminal .typeAtom),
          .optional (.sequence [
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)
          ])
        ] |
          rrRule![.typeAtom, atom],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)
          ], none]
        ]]
        atom
  | typeFunction
      (origin finish : Boundary tokens)
      (domain : TypeExpr)
      (arrow : MatchedTerminal file tokens (.symbol .arrow))
      (codomain : TypeExpr)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .type origin finish
        rrTypeInput![1, rrSeq![[
          .atom (.nonterminal .typeAtom),
          .optional (.sequence [
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)
          ])
        ] |
          rrRule![.typeAtom, domain],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)
          ], some (rrSeq![[
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)
          ] |
            rrTerm![.symbol .arrow, arrow],
            rrRule![.type, codomain]
          ])]
        ]]
        (sourceLoc witness (.function domain codomain))
  | typeAtomProxy
      (origin finish : Boundary tokens)
      (atToken : MatchedTerminal file tokens (.symbol .at))
      (inner : TypeExpr)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .typeAtom origin finish
        rrTypeAtomInput![0, rrSeq![[
          .atom (.terminal (.symbol .at)),
          .atom (.nonterminal .typeAtom)
        ] |
          rrTerm![.symbol .at, atToken],
          rrRule![.typeAtom, inner]
        ]]
        (sourceLoc witness (.proxy
          (RuleReduction.terminalLoc atToken ()) inner))
  | typeAtomNamedWithoutArguments
      (origin finish : Boundary tokens)
      (name : QualifiedName)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .typeAtom origin finish
        rrTypeAtomInput![1, rrSeq![[
          .atom (.nonterminal .qualifiedName),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ])
        ] |
          rrRule![.qualifiedName, name],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ], none]
        ]]
        (sourceLoc witness (.named name none))
  | typeAtomNamedWithArguments
      (origin finish : Boundary tokens)
      (name : QualifiedName)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (arguments : NonemptyList TypeExpr)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .typeAtom origin finish
        rrTypeAtomInput![1, rrSeq![[
          .atom (.nonterminal .qualifiedName),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ])
        ] |
          rrRule![.qualifiedName, name],
          rrOpt![.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ], some (rrSeq![[
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))
          ] |
            rrTerm![.symbol .leftParen, openParen],
            rrList1![.atom (.nonterminal .type),
              arguments.map (EbnfValue.ruleAtom .type)],
            rrTerm![.symbol .rightParen, closeParen]
          ])]
        ]]
        (sourceLoc witness (.named name
          (RuleReduction.arguments
            (some (openParen, arguments, closeParen, ())))))
  | typeAtomEmptyTuple
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .typeAtom origin finish
        rrTypeAtomInput![2, rrSeq![[
          .atom (.terminal (.symbol .leftParen)),
          .atom (.terminal (.symbol .rightParen))
        ] |
          rrTerm![.symbol .leftParen, openParen],
          rrTerm![.symbol .rightParen, closeParen]
        ]]
        (sourceLoc witness (.tuple []))
  | typeAtomGroup
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (inner : TypeExpr)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .typeAtom origin finish
        rrTypeAtomInput![3, rrSeq![[
          .atom (.terminal (.symbol .leftParen)),
          .atom (.nonterminal .type),
          .atom (.terminal (.symbol .rightParen))
        ] |
          rrTerm![.symbol .leftParen, openParen],
          rrRule![.type, inner],
          rrTerm![.symbol .rightParen, closeParen]
        ]]
        (sourceLoc witness (.group inner))
  | typeAtomTuple
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (first : TypeExpr)
      (comma : MatchedTerminal file tokens (.symbol .comma))
      (second : TypeExpr)
      (rest : List
        (MatchedTerminal file tokens (.symbol .comma) × TypeExpr))
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .typeAtom origin finish
        rrTypeAtomInput![4, rrSeq![[
          .atom (.terminal (.symbol .leftParen)),
          .atom (.nonterminal .type),
          .atom (.terminal (.symbol .comma)),
          .atom (.nonterminal .type),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .comma)),
            .atom (.nonterminal .type)
          ])),
          .atom (.terminal (.symbol .rightParen))
        ] |
          rrTerm![.symbol .leftParen, openParen],
          rrRule![.type, first],
          rrTerm![.symbol .comma, comma],
          rrRule![.type, second],
          rrStar![.group (.sequence [
            .atom (.terminal (.symbol .comma)),
            .atom (.nonterminal .type)
          ]), rest.map fun entry =>
            rrGroup![.sequence [
              .atom (.terminal (.symbol .comma)),
              .atom (.nonterminal .type)
            ], rrSeq![[
              .atom (.terminal (.symbol .comma)),
              .atom (.nonterminal .type)
            ] |
              rrTerm![.symbol .comma, entry.1],
              rrRule![.type, entry.2]
            ]]
          ],
          rrTerm![.symbol .rightParen, closeParen]
        ]]
        (sourceLoc witness
          (.tuple (first :: second :: rest.map Prod.snd)))
  | qualifiedName
      (origin finish : Boundary tokens)
      (first : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
      (rest : List
        (MatchedTerminal file tokens (.symbol .dot) ×
          RuleReduction.SpelledTerminalData file tokens
            (.category .identifier) Identifier))
      (firstProjects : IdentifierProjects first.matched
        first.spelling first.parsed)
      (restProjects : ∀ entry, entry ∈ rest →
        IdentifierProjects entry.2.matched
          entry.2.spelling entry.2.parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .qualifiedName origin finish
        rrRoot![rrSeq![[
          .atom (.terminal (.category .identifier)),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .identifier))
          ]))
        ] |
          rrTerm![.category .identifier, first.matched],
          rrStar![.group (.sequence [
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.category .identifier))
          ]), rest.map fun entry =>
            rrGroup![.sequence [
              .atom (.terminal (.symbol .dot)),
              .atom (.terminal (.category .identifier))
            ], rrSeq![[
              .atom (.terminal (.symbol .dot)),
              .atom (.terminal (.category .identifier))
            ] |
              rrTerm![.symbol .dot, entry.1],
              rrTerm![.category .identifier, entry.2.matched]
            ]]
          ]
        ]]
        (sourceLoc witness {
          components := {
            head := RuleReduction.terminalLoc
              first.matched first.parsed
            tail := rest.map fun entry =>
              RuleReduction.terminalLoc
                entry.2.matched entry.2.parsed
          }
        })
  | statementLet
      (origin finish : Boundary tokens)
      (value : Statement) :
      RuleReduction file tokens .statement origin finish
        (rrChoiceRoot![.statement]
          ⟨⟨0, by decide⟩, EbnfValue.ruleAtom .letStatement value⟩)
        value
  | statementReturn
      (origin finish : Boundary tokens)
      (value : Statement) :
      RuleReduction file tokens .statement origin finish
        (rrChoiceRoot![.statement]
          ⟨⟨1, by decide⟩, EbnfValue.ruleAtom .returnStatement value⟩)
        value
  | statementMatch
      (origin finish : Boundary tokens)
      (value : Statement) :
      RuleReduction file tokens .statement origin finish
        (rrChoiceRoot![.statement]
          ⟨⟨2, by decide⟩, EbnfValue.ruleAtom .matchStatement value⟩)
        value
  | statementIf
      (origin finish : Boundary tokens)
      (value : Statement) :
      RuleReduction file tokens .statement origin finish
        (rrChoiceRoot![.statement]
          ⟨⟨3, by decide⟩, EbnfValue.ruleAtom .ifStatement value⟩)
        value
  | statementFor
      (origin finish : Boundary tokens)
      (value : Statement) :
      RuleReduction file tokens .statement origin finish
        (rrChoiceRoot![.statement]
          ⟨⟨4, by decide⟩, EbnfValue.ruleAtom .forStatement value⟩)
        value
  | statementAssembly
      (origin finish : Boundary tokens)
      (value : Statement) :
      RuleReduction file tokens .statement origin finish
        (rrChoiceRoot![.statement]
          ⟨⟨5, by decide⟩, EbnfValue.ruleAtom .assemblyStatement value⟩)
        value
  | statementBlock
      (origin finish : Boundary tokens)
      (value : Statement) :
      RuleReduction file tokens .statement origin finish
        (rrChoiceRoot![.statement]
          ⟨⟨6, by decide⟩, EbnfValue.ruleAtom .blockStatement value⟩)
        value
  | statementBreak
      (origin finish : Boundary tokens)
      (value : Statement) :
      RuleReduction file tokens .statement origin finish
        (rrChoiceRoot![.statement]
          ⟨⟨7, by decide⟩, EbnfValue.ruleAtom .breakStatement value⟩)
        value
  | statementContinue
      (origin finish : Boundary tokens)
      (value : Statement) :
      RuleReduction file tokens .statement origin finish
        (rrChoiceRoot![.statement]
          ⟨⟨8, by decide⟩, EbnfValue.ruleAtom .continueStatement value⟩)
        value
  | statementAssignment
      (origin finish : Boundary tokens)
      (value : Statement) :
      RuleReduction file tokens .statement origin finish
        (rrChoiceRoot![.statement]
          ⟨⟨9, by decide⟩, EbnfValue.ruleAtom .assignmentStatement value⟩)
        value
  | statementExpression
      (origin finish : Boundary tokens)
      (value : Statement) :
      RuleReduction file tokens .statement origin finish
        (rrChoiceRoot![.statement]
          ⟨⟨10, by decide⟩, EbnfValue.ruleAtom .expressionStatement value⟩)
        value
  | letStatement
      (origin finish : Boundary tokens)
      (binding : LetBinding)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .letStatement origin finish
        (rrSequenceRoot![.letStatement]
          (rrCons (EbnfValue.ruleAtom .letBinding binding)
            (rrCons (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
              rrNil)))
        (sourceLoc witness (.letBinding binding))
  | letBindingUntyped
      (origin finish : Boundary tokens)
      (letKeyword : MatchedTerminal file tokens (.hardKeyword .letKw))
      (name : MatchedTerminal file tokens (.category .identifier))
      (spelling : String)
      (parsed : Identifier)
      (nameProjects : IdentifierProjects name spelling parsed)
      (initializer : Option
        (MatchedTerminal file tokens (.symbol .equal) × Expression))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .letBinding origin finish
        (rrSequenceRoot![.letBinding]
          (rrCons (EbnfValue.terminalAtom (.hardKeyword .letKw) letKeyword)
            (rrCons (EbnfValue.terminalAtom (.category .identifier) name)
              (rrCons (EbnfValue.optional _ none)
                (rrCons
                  (EbnfValue.optional _
                    (initializer.map fun value =>
                      EbnfValue.sequence _
                        (rrCons
                          (EbnfValue.terminalAtom (.symbol .equal) value.1)
                          (rrCons (EbnfValue.ruleAtom .expression value.2) rrNil))))
                  rrNil)))))
        (sourceLoc witness {
          comptime := none
          name := RuleReduction.terminalLoc name parsed
          type := none
          initializer := initializer.map Prod.snd
        })
  | letBindingTyped
      (origin finish : Boundary tokens)
      (letKeyword : MatchedTerminal file tokens (.hardKeyword .letKw))
      (name : MatchedTerminal file tokens (.category .identifier))
      (spelling : String)
      (parsed : Identifier)
      (nameProjects : IdentifierProjects name spelling parsed)
      (colon : MatchedTerminal file tokens (.symbol .colon))
      (typeValue : TypeExpr)
      (initializer : Option
        (MatchedTerminal file tokens (.symbol .equal) × Expression))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .letBinding origin finish
        (rrSequenceRoot![.letBinding]
          (rrCons (EbnfValue.terminalAtom (.hardKeyword .letKw) letKeyword)
            (rrCons (EbnfValue.terminalAtom (.category .identifier) name)
              (rrCons
                (EbnfValue.optional _ (some
                  (EbnfValue.sequence _
                    (rrCons (EbnfValue.terminalAtom (.symbol .colon) colon)
                      (rrCons (EbnfValue.optional _ none)
                        (rrCons (EbnfValue.ruleAtom .type typeValue) rrNil))))))
                (rrCons
                  (EbnfValue.optional _
                    (initializer.map fun value =>
                      EbnfValue.sequence _
                        (rrCons
                          (EbnfValue.terminalAtom (.symbol .equal) value.1)
                          (rrCons (EbnfValue.ruleAtom .expression value.2) rrNil))))
                  rrNil)))))
        (sourceLoc witness {
          comptime := none
          name := RuleReduction.terminalLoc name parsed
          type := some typeValue
          initializer := initializer.map Prod.snd
        })
  | letBindingComptime
      (origin finish : Boundary tokens)
      (letKeyword : MatchedTerminal file tokens (.hardKeyword .letKw))
      (name : MatchedTerminal file tokens (.category .identifier))
      (spelling : String)
      (parsed : Identifier)
      (nameProjects : IdentifierProjects name spelling parsed)
      (colon : MatchedTerminal file tokens (.symbol .colon))
      (comptime : MatchedTerminal file tokens
        (.contextualKeyword .comptimeKw))
      (typeValue : TypeExpr)
      (initializer : Option
        (MatchedTerminal file tokens (.symbol .equal) × Expression))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .letBinding origin finish
        (rrSequenceRoot![.letBinding]
          (rrCons (EbnfValue.terminalAtom (.hardKeyword .letKw) letKeyword)
            (rrCons (EbnfValue.terminalAtom (.category .identifier) name)
              (rrCons
                (EbnfValue.optional _ (some
                  (EbnfValue.sequence _
                    (rrCons (EbnfValue.terminalAtom (.symbol .colon) colon)
                      (rrCons
                        (EbnfValue.optional _ (some
                          (EbnfValue.terminalAtom
                            (.contextualKeyword .comptimeKw) comptime)))
                        (rrCons (EbnfValue.ruleAtom .type typeValue) rrNil))))))
                (rrCons
                  (EbnfValue.optional _
                    (initializer.map fun value =>
                      EbnfValue.sequence _
                        (rrCons
                          (EbnfValue.terminalAtom (.symbol .equal) value.1)
                          (rrCons (EbnfValue.ruleAtom .expression value.2) rrNil))))
                  rrNil)))))
        (sourceLoc witness {
          comptime := some
            (RuleReduction.marker comptime (.comptimeModifier comptime))
          name := RuleReduction.terminalLoc name parsed
          type := some typeValue
          initializer := initializer.map Prod.snd
        })
  | returnStatement
      (origin finish : Boundary tokens)
      (returnKeyword : MatchedTerminal file tokens (.hardKeyword .returnKw))
      (value : Option Expression)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .returnStatement origin finish
        (rrSequenceRoot![.returnStatement]
          (rrCons
            (EbnfValue.terminalAtom (.hardKeyword .returnKw) returnKeyword)
            (rrCons
              (EbnfValue.optional _ (value.map (EbnfValue.ruleAtom .expression)))
              (rrCons (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
                rrNil))))
        (sourceLoc witness (.return value semicolon.span))
  | blockStatement
      (origin finish : Boundary tokens)
      (body : Body)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .blockStatement origin finish
        (EbnfValue.ruleAtom .body body)
        (sourceLoc witness (.block body))
  | breakStatement
      (origin finish : Boundary tokens)
      (breakKeyword : MatchedTerminal file tokens (.hardKeyword .breakKw))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .breakStatement origin finish
        (rrSequenceRoot![.breakStatement]
          (rrCons (EbnfValue.terminalAtom (.hardKeyword .breakKw) breakKeyword)
            (rrCons (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
              rrNil)))
        (sourceLoc witness (.break semicolon.span))
  | continueStatement
      (origin finish : Boundary tokens)
      (continueKeyword : MatchedTerminal file tokens
        (.hardKeyword .continueKw))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .continueStatement origin finish
        (rrSequenceRoot![.continueStatement]
          (rrCons
            (EbnfValue.terminalAtom
              (.hardKeyword .continueKw) continueKeyword)
            (rrCons (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
              rrNil)))
        (sourceLoc witness (.continue semicolon.span))
  | assemblyStatement
      (origin finish : Boundary tokens)
      (assemblyKeyword : MatchedTerminal file tokens
        (.hardKeyword .assemblyKw))
      (assemblyToken : MatchedTerminal file tokens
        (.category .assemblyBlock))
      (slice : AssemblySlice)
      (projects : AssemblySliceProjects assemblyToken slice)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .assemblyStatement origin finish
        (rrSequenceRoot![.assemblyStatement]
          (rrCons
            (EbnfValue.terminalAtom
              (.hardKeyword .assemblyKw) assemblyKeyword)
            (rrCons
              (EbnfValue.terminalAtom
                (.category .assemblyBlock) assemblyToken)
              rrNil)))
        (sourceLoc witness (.assembly slice))
  | ifStatementWithoutElse
      (origin finish : Boundary tokens)
      (ifKeyword : MatchedTerminal file tokens (.hardKeyword .ifKw))
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (condition : Expression)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (thenBody : Body)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .ifStatement origin finish
        (rrSequenceRoot![.ifStatement]
          (rrCons (EbnfValue.terminalAtom (.hardKeyword .ifKw) ifKeyword)
            (rrCons
              (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
              (rrCons (EbnfValue.ruleAtom .expression condition)
                (rrCons
                  (EbnfValue.terminalAtom (.symbol .rightParen) closeParen)
                  (rrCons (EbnfValue.ruleAtom .body thenBody)
                    (rrCons (EbnfValue.optional _ none) rrNil)))))))
        (sourceLoc witness (.ifThenElse condition thenBody none))
  | ifStatementWithElse
      (origin finish : Boundary tokens)
      (ifKeyword : MatchedTerminal file tokens (.hardKeyword .ifKw))
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (condition : Expression)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (thenBody : Body)
      (elseKeyword : MatchedTerminal file tokens (.hardKeyword .elseKw))
      (elseBody : Body)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .ifStatement origin finish
        (rrSequenceRoot![.ifStatement]
          (rrCons (EbnfValue.terminalAtom (.hardKeyword .ifKw) ifKeyword)
            (rrCons
              (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
              (rrCons (EbnfValue.ruleAtom .expression condition)
                (rrCons
                  (EbnfValue.terminalAtom (.symbol .rightParen) closeParen)
                  (rrCons (EbnfValue.ruleAtom .body thenBody)
                    (rrCons
                      (EbnfValue.optional _ (some
                        (EbnfValue.sequence _
                          (rrCons
                            (EbnfValue.terminalAtom
                              (.hardKeyword .elseKw) elseKeyword)
                            (rrCons (EbnfValue.ruleAtom .body elseBody) rrNil)))))
                      rrNil)))))))
        (sourceLoc witness
          (.ifThenElse condition thenBody (some elseBody)))
  | forStatement
      (origin finish : Boundary tokens)
      (forKeyword : MatchedTerminal file tokens (.hardKeyword .forKw))
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (initializers : List ForInitItem)
      (firstSemicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (condition : Expression)
      (secondSemicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (post : List ForPostItem)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (body : Body)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .forStatement origin finish
        (rrSequenceRoot![.forStatement]
          (rrCons (EbnfValue.terminalAtom (.hardKeyword .forKw) forKeyword)
            (rrCons (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
              (rrCons
                (EbnfValue.list0 _
                  (initializers.map (EbnfValue.ruleAtom .forInitItem)))
                (rrCons
                  (EbnfValue.terminalAtom
                    (.symbol .semicolon) firstSemicolon)
                  (rrCons (EbnfValue.ruleAtom .expression condition)
                    (rrCons
                      (EbnfValue.terminalAtom
                        (.symbol .semicolon) secondSemicolon)
                      (rrCons
                        (EbnfValue.list0 _
                          (post.map (EbnfValue.ruleAtom .forPostItem)))
                        (rrCons
                          (EbnfValue.terminalAtom
                            (.symbol .rightParen) closeParen)
                          (rrCons (EbnfValue.ruleAtom .body body) rrNil))))))))))
        (sourceLoc witness (.forLoop initializers condition post body))
  | forInitItemLet
      (origin finish : Boundary tokens)
      (binding : LetBinding)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .forInitItem origin finish
        (rrChoiceRoot![.forInitItem]
          ⟨⟨0, by decide⟩, EbnfValue.ruleAtom .letBinding binding⟩)
        (sourceLoc witness (.letBinding binding))
  | forInitItemAssignment
      (origin finish : Boundary tokens)
      (left : Expression)
      (operator : Located AssignmentOperator)
      (right : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .forInitItem origin finish
        (rrChoiceRoot![.forInitItem]
          ⟨⟨1, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.ruleAtom .expression left)
                (rrCons
                  (EbnfValue.ruleAtom .assignmentOperator operator)
                  (rrCons (EbnfValue.ruleAtom .expression right) rrNil)))⟩)
        (sourceLoc witness (.assignment operator left right))
  | forInitItemExpression
      (origin finish : Boundary tokens)
      (expression : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .forInitItem origin finish
        (rrChoiceRoot![.forInitItem]
          ⟨⟨2, by decide⟩, EbnfValue.ruleAtom .expression expression⟩)
        (sourceLoc witness (.expression expression))
  | forPostItemAssignment
      (origin finish : Boundary tokens)
      (left : Expression)
      (operator : Located AssignmentOperator)
      (right : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .forPostItem origin finish
        (rrChoiceRoot![.forPostItem]
          ⟨⟨0, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.ruleAtom .expression left)
                (rrCons
                  (EbnfValue.ruleAtom .assignmentOperator operator)
                  (rrCons (EbnfValue.ruleAtom .expression right) rrNil)))⟩)
        (sourceLoc witness (.assignment operator left right))
  | forPostItemExpression
      (origin finish : Boundary tokens)
      (expression : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .forPostItem origin finish
        (rrChoiceRoot![.forPostItem]
          ⟨⟨1, by decide⟩, EbnfValue.ruleAtom .expression expression⟩)
        (sourceLoc witness (.expression expression))
  | matchStatement
      (origin finish : Boundary tokens)
      (matchKeyword : MatchedTerminal file tokens (.hardKeyword .matchKw))
      (scrutinees : NonemptyList Expression)
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (arms : NonemptyList MatchArm)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (terminator : Option
        (MatchedTerminal file tokens (.symbol .semicolon)))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .matchStatement origin finish
        (rrSequenceRoot![.matchStatement]
          (rrCons
            (EbnfValue.terminalAtom (.hardKeyword .matchKw) matchKeyword)
            (rrCons
              (EbnfValue.list1 _
                (scrutinees.map (EbnfValue.ruleAtom .expression)))
              (rrCons
                (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace)
                (rrCons
                  (EbnfValue.plus _
                    (arms.map (EbnfValue.ruleAtom .matchArm)))
                  (rrCons
                    (EbnfValue.terminalAtom (.symbol .rightBrace) closeBrace)
                    (rrCons
                      (EbnfValue.optional _
                        (terminator.map
                          (EbnfValue.terminalAtom (.symbol .semicolon))))
                      rrNil)))))))
        (sourceLoc witness
          (.match scrutinees arms (terminator.map MatchedTerminal.span)))
  | matchArm
      (origin finish : Boundary tokens)
      (pipe : MatchedTerminal file tokens (.symbol .pipe))
      (patterns : NonemptyList Pattern)
      (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
      (statements : List Statement)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .matchArm origin finish
        (rrSequenceRoot![.matchArm]
          (rrCons (EbnfValue.terminalAtom (.symbol .pipe) pipe)
            (rrCons
              (EbnfValue.list1 _
                (patterns.map (EbnfValue.ruleAtom .pattern)))
              (rrCons
                (EbnfValue.terminalAtom (.symbol .fatArrow) fatArrow)
                (rrCons
                  (EbnfValue.star _
                    (statements.map (EbnfValue.ruleAtom .armStatement)))
                  rrNil)))))
        (sourceLoc witness {
          patterns := patterns
          body := RuleReduction.armBody fatArrow statements
        })
  | armStatement
      (origin finish : Boundary tokens)
      (statement : Statement) :
      RuleReduction file tokens .armStatement origin finish
        (EbnfValue.ruleAtom .statement statement)
        statement
  | assignmentStatement
      (origin finish : Boundary tokens)
      (left : Expression)
      (operator : Located AssignmentOperator)
      (right : Expression)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .assignmentStatement origin finish
        (rrSequenceRoot![.assignmentStatement]
          (rrCons (EbnfValue.ruleAtom .expression left)
            (rrCons (EbnfValue.ruleAtom .assignmentOperator operator)
              (rrCons (EbnfValue.ruleAtom .expression right)
                (rrCons
                  (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
                  rrNil)))))
        (sourceLoc witness (.assignment operator left right))
  | assignmentOperatorEqual
      (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .equal)) :
      RuleReduction file tokens .assignmentOperator origin finish
        (rrChoiceRoot![.assignmentOperator]
          ⟨⟨0, by decide⟩,
            EbnfValue.terminalAtom (.symbol .equal) terminal⟩)
        (RuleReduction.assignmentOperator terminal (.equal terminal))
  | assignmentOperatorAddEqual
      (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .plusEqual)) :
      RuleReduction file tokens .assignmentOperator origin finish
        (rrChoiceRoot![.assignmentOperator]
          ⟨⟨1, by decide⟩,
            EbnfValue.terminalAtom (.symbol .plusEqual) terminal⟩)
        (RuleReduction.assignmentOperator terminal (.addEqual terminal))
  | assignmentOperatorSubtractEqual
      (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .minusEqual)) :
      RuleReduction file tokens .assignmentOperator origin finish
        (rrChoiceRoot![.assignmentOperator]
          ⟨⟨2, by decide⟩,
            EbnfValue.terminalAtom (.symbol .minusEqual) terminal⟩)
        (RuleReduction.assignmentOperator terminal (.subtractEqual terminal))
  | assignmentOperatorBitXorEqual
      (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .caretEqual)) :
      RuleReduction file tokens .assignmentOperator origin finish
        (rrChoiceRoot![.assignmentOperator]
          ⟨⟨3, by decide⟩,
            EbnfValue.terminalAtom (.symbol .caretEqual) terminal⟩)
        (RuleReduction.assignmentOperator terminal (.bitXorEqual terminal))
  | assignmentOperatorBitAndEqual
      (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .ampEqual)) :
      RuleReduction file tokens .assignmentOperator origin finish
        (rrChoiceRoot![.assignmentOperator]
          ⟨⟨4, by decide⟩,
            EbnfValue.terminalAtom (.symbol .ampEqual) terminal⟩)
        (RuleReduction.assignmentOperator terminal (.bitAndEqual terminal))
  | assignmentOperatorBitOrEqual
      (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .pipeEqual)) :
      RuleReduction file tokens .assignmentOperator origin finish
        (rrChoiceRoot![.assignmentOperator]
          ⟨⟨5, by decide⟩,
            EbnfValue.terminalAtom (.symbol .pipeEqual) terminal⟩)
        (RuleReduction.assignmentOperator terminal (.bitOrEqual terminal))
  | assignmentOperatorModuloEqual
      (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .percentEqual)) :
      RuleReduction file tokens .assignmentOperator origin finish
        (rrChoiceRoot![.assignmentOperator]
          ⟨⟨6, by decide⟩,
            EbnfValue.terminalAtom (.symbol .percentEqual) terminal⟩)
        (RuleReduction.assignmentOperator terminal (.moduloEqual terminal))
  | expressionStatementTerminated
      (origin finish : Boundary tokens)
      (expression : Expression)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .expressionStatement origin finish
        (rrChoiceRoot![.expressionStatement]
          ⟨⟨0, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.ruleAtom .expression expression)
                (rrCons
                  (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
                  rrNil))⟩)
        (sourceLoc witness (.expression expression (some semicolon.span)))
  | expressionStatementTerminal
      (origin finish : Boundary tokens)
      (expression : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .expressionStatement origin finish
        (rrChoiceRoot![.expressionStatement]
          ⟨⟨1, by decide⟩,
            EbnfValue.ruleAtom .terminalExpression expression⟩)
        (sourceLoc witness (.expression expression none))
  | terminalExpression
      (origin finish : Boundary tokens)
      (expression : Expression) :
      RuleReduction file tokens .terminalExpression origin finish
        (EbnfValue.ruleAtom .expression expression)
        expression
  | patternWildcard
      (origin finish : Boundary tokens)
      (underscore : MatchedTerminal file tokens (.symbol .underscore))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pattern origin finish
        (rrChoiceRoot![.pattern]
          ⟨⟨0, by decide⟩,
            EbnfValue.terminalAtom (.symbol .underscore) underscore⟩)
        (sourceLoc witness
          (.wildcard
            (RuleReduction.marker underscore (.wildcardUnderscore underscore))))
  | patternLiteral
      (origin finish : Boundary tokens)
      (literal : Literal)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pattern origin finish
        (rrChoiceRoot![.pattern]
          ⟨⟨1, by decide⟩, EbnfValue.ruleAtom .literal literal⟩)
        (sourceLoc witness (.literal literal))
  | patternDotConstructorWithoutArguments
      (origin finish : Boundary tokens)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (name : MatchedTerminal file tokens (.category .identifier))
      (spelling : String)
      (parsed : Identifier)
      (projects : IdentifierProjects name spelling parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pattern origin finish
        (rrChoiceRoot![.pattern]
          ⟨⟨2, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.terminalAtom (.symbol .dot) dot)
                (rrCons (EbnfValue.terminalAtom (.category .identifier) name)
                  (rrCons (EbnfValue.optional _ none) rrNil)))⟩)
        (sourceLoc witness
          (.dotConstructor
            (RuleReduction.terminalLoc dot ())
            (RuleReduction.terminalLoc name parsed)
            none))
  | patternDotConstructorWithArguments
      (origin finish : Boundary tokens)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (name : MatchedTerminal file tokens (.category .identifier))
      (spelling : String)
      (parsed : Identifier)
      (projects : IdentifierProjects name spelling parsed)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (arguments : NonemptyList Pattern)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pattern origin finish
        (rrChoiceRoot![.pattern]
          ⟨⟨2, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.terminalAtom (.symbol .dot) dot)
                (rrCons (EbnfValue.terminalAtom (.category .identifier) name)
                  (rrCons
                    (EbnfValue.optional _ (some
                      (EbnfValue.sequence _
                        (rrCons
                          (EbnfValue.terminalAtom
                            (.symbol .leftParen) openParen)
                          (rrCons
                            (EbnfValue.list1 _
                              (arguments.map
                                (EbnfValue.ruleAtom .pattern)))
                            (rrCons
                              (EbnfValue.terminalAtom
                                (.symbol .rightParen) closeParen)
                              rrNil))))))
                    rrNil)))⟩)
        (sourceLoc witness
          (.dotConstructor
            (RuleReduction.terminalLoc dot ())
            (RuleReduction.terminalLoc name parsed)
            (some arguments)))
  | patternComptime
      (origin finish : Boundary tokens)
      (comptime : MatchedTerminal file tokens
        (.contextualKeyword .comptimeKw))
      (expression : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pattern origin finish
        (rrChoiceRoot![.pattern]
          ⟨⟨3, by decide⟩,
            EbnfValue.sequence _
              (rrCons
                (EbnfValue.terminalAtom
                  (.contextualKeyword .comptimeKw) comptime)
                (rrCons (EbnfValue.ruleAtom .expression expression) rrNil))⟩)
        (sourceLoc witness
          (.comptime
            (RuleReduction.marker comptime (.comptimeModifier comptime))
            expression))
  | patternNamedWithoutArguments
      (origin finish : Boundary tokens)
      (name : QualifiedName)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pattern origin finish
        (rrChoiceRoot![.pattern]
          ⟨⟨4, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.ruleAtom .qualifiedName name)
                (rrCons (EbnfValue.optional _ none) rrNil))⟩)
        (sourceLoc witness (.named name none))
  | patternNamedWithArguments
      (origin finish : Boundary tokens)
      (name : QualifiedName)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (arguments : NonemptyList Pattern)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pattern origin finish
        (rrChoiceRoot![.pattern]
          ⟨⟨4, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.ruleAtom .qualifiedName name)
                (rrCons
                  (EbnfValue.optional _ (some
                    (EbnfValue.sequence _
                      (rrCons
                        (EbnfValue.terminalAtom
                          (.symbol .leftParen) openParen)
                        (rrCons
                          (EbnfValue.list1 _
                            (arguments.map (EbnfValue.ruleAtom .pattern)))
                          (rrCons
                            (EbnfValue.terminalAtom
                              (.symbol .rightParen) closeParen)
                            rrNil))))))
                  rrNil))⟩)
        (sourceLoc witness (.named name (some arguments)))
  | patternEmptyTuple
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pattern origin finish
        (rrChoiceRoot![.pattern]
          ⟨⟨5, by decide⟩,
            EbnfValue.sequence _
              (rrCons
                (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
                (rrCons
                  (EbnfValue.terminalAtom (.symbol .rightParen) closeParen)
                  rrNil))⟩)
        (sourceLoc witness (.tuple []))
  | patternGroup
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (inner : Pattern)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pattern origin finish
        (rrChoiceRoot![.pattern]
          ⟨⟨6, by decide⟩,
            EbnfValue.sequence _
              (rrCons
                (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
                (rrCons (EbnfValue.ruleAtom .pattern inner)
                  (rrCons
                    (EbnfValue.terminalAtom
                      (.symbol .rightParen) closeParen)
                    rrNil)))⟩)
        (sourceLoc witness (.group inner))
  | patternTuple
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (first : Pattern)
      (comma : MatchedTerminal file tokens (.symbol .comma))
      (second : Pattern)
      (rest : List
        (MatchedTerminal file tokens (.symbol .comma) × Pattern))
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .pattern origin finish
        (rrChoiceRoot![.pattern]
          ⟨⟨7, by decide⟩,
            EbnfValue.sequence _
              (rrCons
                (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
                (rrCons (EbnfValue.ruleAtom .pattern first)
                  (rrCons (EbnfValue.terminalAtom (.symbol .comma) comma)
                    (rrCons (EbnfValue.ruleAtom .pattern second)
                      (rrCons
                        (EbnfValue.star _
                          (rest.map fun value =>
                            EbnfValue.group _
                              (EbnfValue.sequence _
                                (rrCons
                                  (EbnfValue.terminalAtom
                                    (.symbol .comma) value.1)
                                  (rrCons
                                    (EbnfValue.ruleAtom .pattern value.2)
                                    rrNil)))))
                        (rrCons
                          (EbnfValue.terminalAtom
                            (.symbol .rightParen) closeParen)
                          rrNil))))))⟩)
        (sourceLoc witness
          (.tuple (first :: second :: rest.map Prod.snd)))
  | expression
      (origin finish : Boundary tokens)
      (expression : Expression) :
      RuleReduction file tokens .expression origin finish
        (EbnfValue.ruleAtom .annotation expression)
        expression
  | annotationNone
      (origin finish : Boundary tokens)
      (expression : Expression) :
      RuleReduction file tokens .annotation origin finish
        (rrSequenceRoot![.annotation]
          (rrCons (EbnfValue.ruleAtom .conditional expression)
            (rrCons (EbnfValue.optional _ none) rrNil)))
        expression
  | annotationSome
      (origin finish : Boundary tokens)
      (expression : Expression)
      (colon : MatchedTerminal file tokens (.symbol .colon))
      (typeValue : TypeExpr)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .annotation origin finish
        (rrSequenceRoot![.annotation]
          (rrCons (EbnfValue.ruleAtom .conditional expression)
            (rrCons
              (EbnfValue.optional _ (some
                (EbnfValue.sequence _
                  (rrCons (EbnfValue.terminalAtom (.symbol .colon) colon)
                    (rrCons (EbnfValue.ruleAtom .type typeValue) rrNil)))))
              rrNil)))
        (sourceLoc witness (.annotation expression typeValue))
  | conditionalKeyword
      (origin finish : Boundary tokens)
      (ifKeyword : MatchedTerminal file tokens (.hardKeyword .ifKw))
      (condition : Expression)
      (thenKeyword : MatchedTerminal file tokens
        (.contextualKeyword .thenKw))
      (thenBranch : Expression)
      (elseKeyword : MatchedTerminal file tokens (.hardKeyword .elseKw))
      (elseBranch : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .conditional origin finish
        (rrChoiceRoot![.conditional]
          ⟨⟨0, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.terminalAtom (.hardKeyword .ifKw) ifKeyword)
                (rrCons (EbnfValue.ruleAtom .conditional condition)
                  (rrCons
                    (EbnfValue.terminalAtom
                      (.contextualKeyword .thenKw) thenKeyword)
                    (rrCons (EbnfValue.ruleAtom .conditional thenBranch)
                      (rrCons
                        (EbnfValue.terminalAtom
                          (.hardKeyword .elseKw) elseKeyword)
                        (rrCons
                          (EbnfValue.ruleAtom .conditional elseBranch)
                          rrNil))))))⟩)
        (sourceLoc witness
          (.keywordConditional condition thenBranch elseBranch))
  | conditionalLogical
      (origin finish : Boundary tokens)
      (condition : Expression) :
      RuleReduction file tokens .conditional origin finish
        (rrChoiceRoot![.conditional]
          ⟨⟨1, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.ruleAtom .logicalOr condition)
                (rrCons (EbnfValue.optional _ none) rrNil))⟩)
        condition
  | conditionalTernary
      (origin finish : Boundary tokens)
      (condition : Expression)
      (question : MatchedTerminal file tokens (.symbol .question))
      (thenBranch : Expression)
      (colon : MatchedTerminal file tokens (.symbol .colon))
      (elseBranch : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .conditional origin finish
        (rrChoiceRoot![.conditional]
          ⟨⟨1, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.ruleAtom .logicalOr condition)
                (rrCons
                  (EbnfValue.optional _ (some
                    (EbnfValue.sequence _
                      (rrCons
                        (EbnfValue.terminalAtom
                          (.symbol .question) question)
                        (rrCons
                          (EbnfValue.ruleAtom .conditional thenBranch)
                          (rrCons
                            (EbnfValue.terminalAtom (.symbol .colon) colon)
                            (rrCons
                              (EbnfValue.ruleAtom
                                .conditional elseBranch)
                              rrNil)))))))
                  rrNil))⟩)
        (sourceLoc witness
          (.ternaryConditional condition thenBranch elseBranch))
  | logicalOr
      (origin finish : Boundary tokens)
      (left : Expression)
      (rest : List
        (MatchedTerminal file tokens (.symbol .logicalOr) × Expression)) :
      RuleReduction file tokens .logicalOr origin finish
        (rrSequenceRoot![.logicalOr]
          (rrCons (EbnfValue.ruleAtom .logicalAnd left)
            (rrCons
              (EbnfValue.star _
                (rest.map fun value =>
                  EbnfValue.group _
                    (EbnfValue.sequence _
                      (rrCons
                        (EbnfValue.terminalAtom
                          (.symbol .logicalOr) value.1)
                        (rrCons
                          (EbnfValue.ruleAtom .logicalAnd value.2)
                          rrNil)))))
              rrNil)))
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.logicalOr value.1),
              value.2)))
  | logicalAnd
      (origin finish : Boundary tokens)
      (left : Expression)
      (rest : List
        (MatchedTerminal file tokens (.symbol .logicalAnd) × Expression)) :
      RuleReduction file tokens .logicalAnd origin finish
        (rrSequenceRoot![.logicalAnd]
          (rrCons (EbnfValue.ruleAtom .equality left)
            (rrCons
              (EbnfValue.star _
                (rest.map fun value =>
                  EbnfValue.group _
                    (EbnfValue.sequence _
                      (rrCons
                        (EbnfValue.terminalAtom
                          (.symbol .logicalAnd) value.1)
                        (rrCons (EbnfValue.ruleAtom .equality value.2) rrNil)))))
              rrNil)))
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.logicalAnd value.1),
              value.2)))
  | equalityNone
      (origin finish : Boundary tokens)
      (left : Expression) :
      RuleReduction file tokens .equality origin finish
        (rrSequenceRoot![.equality]
          (rrCons (EbnfValue.ruleAtom .relational left)
            (rrCons (EbnfValue.optional _ none) rrNil)))
        left
  | equalityEqual
      (origin finish : Boundary tokens)
      (left : Expression)
      (operator : MatchedTerminal file tokens (.symbol .equalEqual))
      (right : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .equality origin finish
        (rrSequenceRoot![.equality]
          (rrCons (EbnfValue.ruleAtom .relational left)
            (rrCons
              (EbnfValue.optional _ (some
                (EbnfValue.sequence _
                  (rrCons
                    (EbnfValue.group _
                      (EbnfValue.choice _
                        ⟨⟨0, by decide⟩,
                          EbnfValue.terminalAtom
                            (.symbol .equalEqual) operator⟩))
                    (rrCons (EbnfValue.ruleAtom .relational right) rrNil)))))
              rrNil)))
        (sourceLoc witness
          (.infix
            (RuleReduction.infixOperator operator (.equal operator))
            left right))
  | equalityNotEqual
      (origin finish : Boundary tokens)
      (left : Expression)
      (operator : MatchedTerminal file tokens (.symbol .notEqual))
      (right : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .equality origin finish
        (rrSequenceRoot![.equality]
          (rrCons (EbnfValue.ruleAtom .relational left)
            (rrCons
              (EbnfValue.optional _ (some
                (EbnfValue.sequence _
                  (rrCons
                    (EbnfValue.group _
                      (EbnfValue.choice _
                        ⟨⟨1, by decide⟩,
                          EbnfValue.terminalAtom
                            (.symbol .notEqual) operator⟩))
                    (rrCons (EbnfValue.ruleAtom .relational right) rrNil)))))
              rrNil)))
        (sourceLoc witness
          (.infix
            (RuleReduction.infixOperator operator (.notEqual operator))
            left right))
  | relationalNone
      (origin finish : Boundary tokens)
      (left : Expression) :
      RuleReduction file tokens .relational origin finish
        (rrSequenceRoot![.relational]
          (rrCons (EbnfValue.ruleAtom .bitOr left)
            (rrCons (EbnfValue.optional _ none) rrNil)))
        left
  | relationalLess
      (origin finish : Boundary tokens)
      (left : Expression)
      (operator : MatchedTerminal file tokens (.symbol .less))
      (right : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .relational origin finish
        (rrSequenceRoot![.relational]
          (rrCons (EbnfValue.ruleAtom .bitOr left)
            (rrCons
              (EbnfValue.optional _ (some
                (EbnfValue.sequence _
                  (rrCons
                    (EbnfValue.group _
                      (EbnfValue.choice _
                        ⟨⟨0, by decide⟩,
                          EbnfValue.terminalAtom (.symbol .less) operator⟩))
                    (rrCons (EbnfValue.ruleAtom .bitOr right) rrNil)))))
              rrNil)))
        (sourceLoc witness
          (.infix (RuleReduction.infixOperator operator (.less operator))
            left right))
  | relationalGreater
      (origin finish : Boundary tokens)
      (left : Expression)
      (operator : MatchedTerminal file tokens (.symbol .greater))
      (right : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .relational origin finish
        (rrSequenceRoot![.relational]
          (rrCons (EbnfValue.ruleAtom .bitOr left)
            (rrCons
              (EbnfValue.optional _ (some
                (EbnfValue.sequence _
                  (rrCons
                    (EbnfValue.group _
                      (EbnfValue.choice _
                        ⟨⟨1, by decide⟩,
                          EbnfValue.terminalAtom
                            (.symbol .greater) operator⟩))
                    (rrCons (EbnfValue.ruleAtom .bitOr right) rrNil)))))
              rrNil)))
        (sourceLoc witness
          (.infix (RuleReduction.infixOperator operator (.greater operator))
            left right))
  | relationalLessEqual
      (origin finish : Boundary tokens)
      (left : Expression)
      (operator : MatchedTerminal file tokens (.symbol .lessEqual))
      (right : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .relational origin finish
        (rrSequenceRoot![.relational]
          (rrCons (EbnfValue.ruleAtom .bitOr left)
            (rrCons
              (EbnfValue.optional _ (some
                (EbnfValue.sequence _
                  (rrCons
                    (EbnfValue.group _
                      (EbnfValue.choice _
                        ⟨⟨2, by decide⟩,
                          EbnfValue.terminalAtom
                            (.symbol .lessEqual) operator⟩))
                    (rrCons (EbnfValue.ruleAtom .bitOr right) rrNil)))))
              rrNil)))
        (sourceLoc witness
          (.infix
            (RuleReduction.infixOperator operator (.lessEqual operator))
            left right))
  | relationalGreaterEqual
      (origin finish : Boundary tokens)
      (left : Expression)
      (operator : MatchedTerminal file tokens (.symbol .greaterEqual))
      (right : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .relational origin finish
        (rrSequenceRoot![.relational]
          (rrCons (EbnfValue.ruleAtom .bitOr left)
            (rrCons
              (EbnfValue.optional _ (some
                (EbnfValue.sequence _
                  (rrCons
                    (EbnfValue.group _
                      (EbnfValue.choice _
                        ⟨⟨3, by decide⟩,
                          EbnfValue.terminalAtom
                            (.symbol .greaterEqual) operator⟩))
                    (rrCons (EbnfValue.ruleAtom .bitOr right) rrNil)))))
              rrNil)))
        (sourceLoc witness
          (.infix
            (RuleReduction.infixOperator operator (.greaterEqual operator))
            left right))
  | bitOr
      (origin finish : Boundary tokens)
      (left : Expression)
      (rest : List
        (MatchedTerminal file tokens (.symbol .pipe) × Expression)) :
      RuleReduction file tokens .bitOr origin finish
        (rrSequenceRoot![.bitOr]
          (rrCons (EbnfValue.ruleAtom .bitXor left)
            (rrCons
              (EbnfValue.star _
                (rest.map fun value =>
                  EbnfValue.group _
                    (EbnfValue.sequence _
                      (rrCons
                        (EbnfValue.terminalAtom (.symbol .pipe) value.1)
                        (rrCons (EbnfValue.ruleAtom .bitXor value.2) rrNil)))))
              rrNil)))
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.bitOr value.1), value.2)))
  | bitXor
      (origin finish : Boundary tokens)
      (left : Expression)
      (rest : List
        (MatchedTerminal file tokens (.symbol .caret) × Expression)) :
      RuleReduction file tokens .bitXor origin finish
        (rrSequenceRoot![.bitXor]
          (rrCons (EbnfValue.ruleAtom .bitAnd left)
            (rrCons
              (EbnfValue.star _
                (rest.map fun value =>
                  EbnfValue.group _
                    (EbnfValue.sequence _
                      (rrCons
                        (EbnfValue.terminalAtom (.symbol .caret) value.1)
                        (rrCons (EbnfValue.ruleAtom .bitAnd value.2) rrNil)))))
              rrNil)))
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.bitXor value.1), value.2)))
  | bitAnd
      (origin finish : Boundary tokens)
      (left : Expression)
      (rest : List
        (MatchedTerminal file tokens (.symbol .amp) × Expression)) :
      RuleReduction file tokens .bitAnd origin finish
        (rrSequenceRoot![.bitAnd]
          (rrCons (EbnfValue.ruleAtom .additive left)
            (rrCons
              (EbnfValue.star _
                (rest.map fun value =>
                  EbnfValue.group _
                    (EbnfValue.sequence _
                      (rrCons
                        (EbnfValue.terminalAtom (.symbol .amp) value.1)
                        (rrCons (EbnfValue.ruleAtom .additive value.2) rrNil)))))
              rrNil)))
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.bitAnd value.1), value.2)))
  | additive
      (origin finish : Boundary tokens)
      (left : Expression)
      (rest : List
        (Sum
          (MatchedTerminal file tokens (.symbol .plus))
          (MatchedTerminal file tokens (.symbol .minus)) × Expression)) :
      RuleReduction file tokens .additive origin finish
        (rrSequenceRoot![.additive]
          (rrCons (EbnfValue.ruleAtom .multiplicative left)
            (rrCons
              (EbnfValue.star _
                (rest.map fun value =>
                  EbnfValue.group _
                    (EbnfValue.sequence _
                      (rrCons
                        (EbnfValue.group _
                          (match value.1 with
                          | .inl plus =>
                              EbnfValue.choice _
                                ⟨⟨0, by decide⟩,
                                  EbnfValue.terminalAtom
                                    (.symbol .plus) plus⟩
                          | .inr minus =>
                              EbnfValue.choice _
                                ⟨⟨1, by decide⟩,
                                  EbnfValue.terminalAtom
                                    (.symbol .minus) minus⟩))
                        (rrCons
                          (EbnfValue.ruleAtom .multiplicative value.2)
                          rrNil)))))
              rrNil)))
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (match value.1 with
              | .inl plus =>
                  RuleReduction.infixOperator plus (.add plus)
              | .inr minus =>
                  RuleReduction.infixOperator minus (.subtract minus),
              value.2)))
  | multiplicative
      (origin finish : Boundary tokens)
      (left : Expression)
      (rest : List
        (Sum
          (MatchedTerminal file tokens (.symbol .star))
          (Sum
            (MatchedTerminal file tokens (.symbol .slash))
            (MatchedTerminal file tokens (.symbol .percent))) × Expression)) :
      RuleReduction file tokens .multiplicative origin finish
        (rrSequenceRoot![.multiplicative]
          (rrCons (EbnfValue.ruleAtom .prefix left)
            (rrCons
              (EbnfValue.star _
                (rest.map fun value =>
                  EbnfValue.group _
                    (EbnfValue.sequence _
                      (rrCons
                        (EbnfValue.group _
                          (match value.1 with
                          | .inl star =>
                              EbnfValue.choice _
                                ⟨⟨0, by decide⟩,
                                  EbnfValue.terminalAtom
                                    (.symbol .star) star⟩
                          | .inr (.inl slash) =>
                              EbnfValue.choice _
                                ⟨⟨1, by decide⟩,
                                  EbnfValue.terminalAtom
                                    (.symbol .slash) slash⟩
                          | .inr (.inr percent) =>
                              EbnfValue.choice _
                                ⟨⟨2, by decide⟩,
                                  EbnfValue.terminalAtom
                                    (.symbol .percent) percent⟩))
                        (rrCons (EbnfValue.ruleAtom .prefix value.2) rrNil)))))
              rrNil)))
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (match value.1 with
              | .inl star =>
                  RuleReduction.infixOperator star (.multiply star)
              | .inr (.inl slash) =>
                  RuleReduction.infixOperator slash (.divide slash)
              | .inr (.inr percent) =>
                  RuleReduction.infixOperator percent (.modulo percent),
              value.2)))
  | prefixLogicalNot
      (origin finish : Boundary tokens)
      (bang : MatchedTerminal file tokens (.symbol .bang))
      (operand : Expression)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .prefix origin finish
        (rrChoiceRoot![.prefix]
          ⟨⟨0, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.terminalAtom (.symbol .bang) bang)
                (rrCons (EbnfValue.ruleAtom .prefix operand) rrNil))⟩)
        (sourceLoc witness
          (.prefix (RuleReduction.prefixOperator bang) operand))
  | prefixPostfix
      (origin finish : Boundary tokens)
      (expression : Expression) :
      RuleReduction file tokens .prefix origin finish
        (rrChoiceRoot![.prefix]
          ⟨⟨1, by decide⟩, EbnfValue.ruleAtom .postfix expression⟩)
        expression
  | postfix
      (origin finish : Boundary tokens)
      (atom : Expression)
      (parts : List PostfixPartValue) :
      RuleReduction file tokens .postfix origin finish
        (rrSequenceRoot![.postfix]
          (rrCons (EbnfValue.ruleAtom .atom atom)
            (rrCons
              (EbnfValue.star _
                (parts.map (EbnfValue.ruleAtom .postfixPart)))
              rrNil)))
        (RuleReduction.foldPostfix file atom parts)
  | postfixPartCall
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (arguments : List Expression)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen)) :
      RuleReduction file tokens .postfixPart origin finish
        (rrChoiceRoot![.postfixPart]
          ⟨⟨0, by decide⟩,
            EbnfValue.sequence _
              (rrCons
                (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
                (rrCons
                  (EbnfValue.list0 _
                    (arguments.map (EbnfValue.ruleAtom .expression)))
                  (rrCons
                    (EbnfValue.terminalAtom
                      (.symbol .rightParen) closeParen)
                    rrNil)))⟩)
        (.call openParen.span arguments closeParen.span)
  | postfixPartSelect
      (origin finish : Boundary tokens)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (field : MatchedTerminal file tokens (.category .identifier))
      (spelling : String)
      (parsed : Identifier)
      (projects : IdentifierProjects field spelling parsed) :
      RuleReduction file tokens .postfixPart origin finish
        (rrChoiceRoot![.postfixPart]
          ⟨⟨1, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.terminalAtom (.symbol .dot) dot)
                (rrCons
                  (EbnfValue.terminalAtom (.category .identifier) field)
                  rrNil))⟩)
        (.select dot.span (RuleReduction.terminalLoc field parsed))
  | postfixPartIndex
      (origin finish : Boundary tokens)
      (openBracket : MatchedTerminal file tokens (.symbol .leftBracket))
      (index : Expression)
      (closeBracket : MatchedTerminal file tokens (.symbol .rightBracket)) :
      RuleReduction file tokens .postfixPart origin finish
        (rrChoiceRoot![.postfixPart]
          ⟨⟨2, by decide⟩,
            EbnfValue.sequence _
              (rrCons
                (EbnfValue.terminalAtom
                  (.symbol .leftBracket) openBracket)
                (rrCons (EbnfValue.ruleAtom .expression index)
                  (rrCons
                    (EbnfValue.terminalAtom
                      (.symbol .rightBracket) closeBracket)
                    rrNil)))⟩)
        (.index openBracket.span index closeBracket.span)
  | atomLiteral
      (origin finish : Boundary tokens)
      (literal : Literal)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .atom origin finish
        (rrChoiceRoot![.atom]
          ⟨⟨0, by decide⟩, EbnfValue.ruleAtom .literal literal⟩)
        (sourceLoc witness (.literal literal))
  | atomName
      (origin finish : Boundary tokens)
      (name : MatchedTerminal file tokens (.category .identifier))
      (spelling : String)
      (parsed : Identifier)
      (projects : IdentifierProjects name spelling parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .atom origin finish
        (rrChoiceRoot![.atom]
          ⟨⟨1, by decide⟩,
            EbnfValue.terminalAtom (.category .identifier) name⟩)
        (sourceLoc witness
          (.name (RuleReduction.terminalLoc name parsed)))
  | atomDotConstructorWithoutArguments
      (origin finish : Boundary tokens)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (name : MatchedTerminal file tokens (.category .identifier))
      (spelling : String)
      (parsed : Identifier)
      (projects : IdentifierProjects name spelling parsed)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .atom origin finish
        (rrChoiceRoot![.atom]
          ⟨⟨2, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.terminalAtom (.symbol .dot) dot)
                (rrCons (EbnfValue.terminalAtom (.category .identifier) name)
                  (rrCons (EbnfValue.optional _ none) rrNil)))⟩)
        (sourceLoc witness
          (.dotConstructor
            (RuleReduction.terminalLoc dot ())
            (RuleReduction.terminalLoc name parsed)
            none))
  | atomDotConstructorWithArguments
      (origin finish : Boundary tokens)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (name : MatchedTerminal file tokens (.category .identifier))
      (spelling : String)
      (parsed : Identifier)
      (projects : IdentifierProjects name spelling parsed)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (arguments : List Expression)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .atom origin finish
        (rrChoiceRoot![.atom]
          ⟨⟨2, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.terminalAtom (.symbol .dot) dot)
                (rrCons (EbnfValue.terminalAtom (.category .identifier) name)
                  (rrCons
                    (EbnfValue.optional _ (some
                      (EbnfValue.sequence _
                        (rrCons
                          (EbnfValue.terminalAtom
                            (.symbol .leftParen) openParen)
                          (rrCons
                            (EbnfValue.list0 _
                              (arguments.map
                                (EbnfValue.ruleAtom .expression)))
                            (rrCons
                              (EbnfValue.terminalAtom
                                (.symbol .rightParen) closeParen)
                              rrNil))))))
                    rrNil)))⟩)
        (sourceLoc witness
          (.dotConstructor
            (RuleReduction.terminalLoc dot ())
            (RuleReduction.terminalLoc name parsed)
            (some arguments)))
  | atomProxy
      (origin finish : Boundary tokens)
      (atTerminal : MatchedTerminal file tokens (.symbol .at))
      (typeValue : TypeExpr)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .atom origin finish
        (rrChoiceRoot![.atom]
          ⟨⟨3, by decide⟩,
            EbnfValue.sequence _
              (rrCons (EbnfValue.terminalAtom (.symbol .at) atTerminal)
                (rrCons (EbnfValue.ruleAtom .typeAtom typeValue) rrNil))⟩)
        (sourceLoc witness
          (.proxy (RuleReduction.terminalLoc atTerminal ()) typeValue))
  | atomLambda
      (origin finish : Boundary tokens)
      (lambda : Expression) :
      RuleReduction file tokens .atom origin finish
        (rrChoiceRoot![.atom]
          ⟨⟨4, by decide⟩, EbnfValue.ruleAtom .lambda lambda⟩)
        lambda
  | atomEmptyTuple
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .atom origin finish
        (rrChoiceRoot![.atom]
          ⟨⟨5, by decide⟩,
            EbnfValue.sequence _
              (rrCons
                (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
                (rrCons
                  (EbnfValue.terminalAtom (.symbol .rightParen) closeParen)
                  rrNil))⟩)
        (sourceLoc witness (.tuple []))
  | atomGroup
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (inner : Expression)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .atom origin finish
        (rrChoiceRoot![.atom]
          ⟨⟨6, by decide⟩,
            EbnfValue.sequence _
              (rrCons
                (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
                (rrCons (EbnfValue.ruleAtom .expression inner)
                  (rrCons
                    (EbnfValue.terminalAtom
                      (.symbol .rightParen) closeParen)
                    rrNil)))⟩)
        (sourceLoc witness (.group inner))
  | atomTuple
      (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (first : Expression)
      (comma : MatchedTerminal file tokens (.symbol .comma))
      (second : Expression)
      (rest : List
        (MatchedTerminal file tokens (.symbol .comma) × Expression))
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .atom origin finish
        (rrChoiceRoot![.atom]
          ⟨⟨7, by decide⟩,
            EbnfValue.sequence _
              (rrCons
                (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
                (rrCons (EbnfValue.ruleAtom .expression first)
                  (rrCons (EbnfValue.terminalAtom (.symbol .comma) comma)
                    (rrCons (EbnfValue.ruleAtom .expression second)
                      (rrCons
                        (EbnfValue.star _
                          (rest.map fun value =>
                            EbnfValue.group _
                              (EbnfValue.sequence _
                                (rrCons
                                  (EbnfValue.terminalAtom
                                    (.symbol .comma) value.1)
                                  (rrCons
                                    (EbnfValue.ruleAtom
                                      .expression value.2)
                                    rrNil)))))
                        (rrCons
                          (EbnfValue.terminalAtom
                            (.symbol .rightParen) closeParen)
                          rrNil))))))⟩)
        (sourceLoc witness
          (.tuple (first :: second :: rest.map Prod.snd)))
  | lambda
      (origin finish : Boundary tokens)
      (lambdaKeyword : MatchedTerminal file tokens (.hardKeyword .lamKw))
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (parameters : List Parameter)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
      (returnType : Option
        (MatchedTerminal file tokens (.symbol .arrow) × TypeExpr))
      (body : Body)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      RuleReduction file tokens .lambda origin finish
        (rrSequenceRoot![.lambda]
          (rrCons
            (EbnfValue.terminalAtom (.hardKeyword .lamKw) lambdaKeyword)
            (rrCons
              (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
              (rrCons
                (EbnfValue.list0 _
                  (parameters.map (EbnfValue.ruleAtom .parameter)))
                (rrCons
                  (EbnfValue.terminalAtom
                    (.symbol .rightParen) closeParen)
                  (rrCons
                    (EbnfValue.optional _
                      (returnType.map fun value =>
                        EbnfValue.sequence _
                          (rrCons
                            (EbnfValue.terminalAtom
                              (.symbol .arrow) value.1)
                            (rrCons (EbnfValue.ruleAtom .type value.2) rrNil))))
                    (rrCons (EbnfValue.ruleAtom .body body) rrNil)))))))
        (sourceLoc witness
          (.lambda parameters (returnType.map Prod.snd) body))
  | literalDecimal
      (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.category .decimalLiteral))
      (payload : LiteralPayload)
      (projects : LiteralProjects terminal payload) :
      RuleReduction file tokens .literal origin finish
        (rrChoiceRoot![.literal]
          ⟨⟨0, by decide⟩,
            EbnfValue.terminalAtom (.category .decimalLiteral) terminal⟩)
        (RuleReduction.terminalLoc terminal payload)
  | literalHexadecimal
      (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens
        (.category .hexadecimalLiteral))
      (payload : LiteralPayload)
      (projects : LiteralProjects terminal payload) :
      RuleReduction file tokens .literal origin finish
        (rrChoiceRoot![.literal]
          ⟨⟨1, by decide⟩,
            EbnfValue.terminalAtom
              (.category .hexadecimalLiteral) terminal⟩)
        (RuleReduction.terminalLoc terminal payload)
  | literalString
      (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.category .stringLiteral))
      (payload : LiteralPayload)
      (projects : LiteralProjects terminal payload) :
      RuleReduction file tokens .literal origin finish
        (rrChoiceRoot![.literal]
          ⟨⟨2, by decide⟩,
            EbnfValue.terminalAtom (.category .stringLiteral) terminal⟩)
        (RuleReduction.terminalLoc terminal payload)

private theorem transport_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {left right : EbnfExpr} (indexEq : left = right)
    {first second : EbnfValue file tokens left} :
    EbnfValue.transport indexEq first = EbnfValue.transport indexEq second ↔
      first = second :=
  (EbnfValue.transport_injective indexEq).eq_iff

private theorem terminalAtom_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    {first second : MatchedTerminal file tokens terminal} :
    EbnfValue.terminalAtom terminal first =
        EbnfValue.terminalAtom terminal second ↔ first = second :=
  (EbnfValue.terminalAtom_injective terminal).eq_iff

private theorem ruleAtom_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {first second : RuleValue rule} :
    EbnfValue.ruleAtom (file := file) (tokens := tokens) rule first =
        EbnfValue.ruleAtom rule second ↔ first = second :=
  (EbnfValue.ruleAtom_injective rule).eq_iff

private theorem sequence_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {children : List EbnfExpr}
    {first second : EbnfValues file tokens children} :
    EbnfValue.sequence children first = EbnfValue.sequence children second ↔
      first = second :=
  (EbnfValue.sequence_injective children).eq_iff

private theorem group_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {first second : EbnfValue file tokens child} :
    EbnfValue.group child first = EbnfValue.group child second ↔ first = second :=
  (EbnfValue.group_injective child).eq_iff

private theorem choice_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {branches : List EbnfExpr}
    {first second : (branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch)} :
    EbnfValue.choice branches first = EbnfValue.choice branches second ↔
      first = second :=
  (EbnfValue.choice_injective branches).eq_iff

private theorem optional_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr}
    {first second : Option (EbnfValue file tokens child)} :
    EbnfValue.optional child first = EbnfValue.optional child second ↔
      first = second :=
  (EbnfValue.optional_injective child).eq_iff

private theorem star_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr}
    {first second : List (EbnfValue file tokens child)} :
    EbnfValue.star child first = EbnfValue.star child second ↔ first = second :=
  (EbnfValue.star_injective child).eq_iff

private theorem plus_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr}
    {first second : NonemptyList (EbnfValue file tokens child)} :
    EbnfValue.plus child first = EbnfValue.plus child second ↔ first = second :=
  (EbnfValue.plus_injective child).eq_iff

private theorem list0_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr}
    {first second : List (EbnfValue file tokens child)} :
    EbnfValue.list0 child first = EbnfValue.list0 child second ↔ first = second :=
  (EbnfValue.list0_injective child).eq_iff

private theorem list1_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr}
    {first second : NonemptyList (EbnfValue file tokens child)} :
    EbnfValue.list1 child first = EbnfValue.list1 child second ↔ first = second :=
  (EbnfValue.list1_injective child).eq_iff

private theorem cons_inj_iff
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {rest : List EbnfExpr}
    {firstHead secondHead : EbnfValue file tokens child}
    {firstTail secondTail : EbnfValues file tokens rest} :
    EbnfValues.cons child rest firstHead firstTail =
        EbnfValues.cons child rest secondHead secondTail ↔
      firstHead = secondHead ∧ firstTail = secondTail := by
  constructor
  · exact EbnfValues.cons_injective child rest
  · rintro ⟨rfl, rfl⟩
    rfl

attribute [local simp] transport_inj_iff terminalAtom_inj_iff
  ruleAtom_inj_iff sequence_inj_iff group_inj_iff choice_inj_iff
  optional_inj_iff star_inj_iff plus_inj_iff list0_inj_iff
  list1_inj_iff cons_inj_iff

universe u v w

private theorem listMap_injective_of_injective
    {alpha : Type u} {beta : Type v} {function : alpha → beta}
    (injective : Function.Injective function) :
    Function.Injective (List.map function) := by
  intro left right inputEq
  induction left generalizing right with
  | nil => simpa using inputEq
  | cons head tail ih =>
      cases right with
      | nil => simp at inputEq
      | cons otherHead otherTail =>
          simp only [List.map_cons, List.cons.injEq] at inputEq
          rw [injective inputEq.1, ih inputEq.2]
private theorem nonemptyListMap_injective_of_injective
    {alpha beta : Type} {function : alpha → beta}
    (injective : Function.Injective function) :
    Function.Injective (NonemptyList.map function) := by
  rintro ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩ inputEq
  have headEq := congrArg NonemptyList.head inputEq
  have tailEq := congrArg NonemptyList.tail inputEq
  simp only [NonemptyList.map] at headEq tailEq
  have := injective headEq
  have := listMap_injective_of_injective injective tailEq
  subst_vars
  rfl
private theorem listMap_output_functional
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    {key : alpha → beta} {output : alpha → gamma}
    {projects : alpha → Prop} {left right : List alpha}
    (leftProjects : ∀ value, value ∈ left → projects value)
    (rightProjects : ∀ value, value ∈ right → projects value)
    (pointwise : ∀ {leftValue rightValue},
      projects leftValue → projects rightValue →
        key leftValue = key rightValue →
          output leftValue = output rightValue)
    (keyEq : left.map key = right.map key) :
    left.map output = right.map output := by
  induction left generalizing right with
  | nil => simpa using keyEq
  | cons head tail ih =>
      cases right with
      | nil => simp at keyEq
      | cons otherHead otherTail =>
          simp only [List.map_cons, List.cons.injEq] at keyEq ⊢
          refine ⟨pointwise
            (leftProjects head (by simp))
            (rightProjects otherHead (by simp)) keyEq.1, ?_⟩
          exact ih
            (fun value member => leftProjects value (by simp [member]))
            (fun value member => rightProjects value (by simp [member]))
            keyEq.2
private theorem nonemptyListMap_output_functional
    {alpha beta gamma : Type}
    {key : alpha → beta} {output : alpha → gamma}
    {projects : alpha → Prop} {left right : NonemptyList alpha}
    (leftProjects : projects left.head ∧
      ∀ value, value ∈ left.tail → projects value)
    (rightProjects : projects right.head ∧
      ∀ value, value ∈ right.tail → projects value)
    (pointwise : ∀ {leftValue rightValue},
      projects leftValue → projects rightValue →
        key leftValue = key rightValue →
          output leftValue = output rightValue)
    (keyEq : left.map key = right.map key) :
    left.map output = right.map output := by
  have headKeyEq := congrArg NonemptyList.head keyEq
  have tailKeyEq := congrArg NonemptyList.tail keyEq
  simp only [NonemptyList.map] at headKeyEq tailKeyEq
  have headEq := pointwise leftProjects.1 rightProjects.1 headKeyEq
  have tailEq := listMap_output_functional leftProjects.2 rightProjects.2
    pointwise tailKeyEq
  cases left
  cases right
  simp only [NonemptyList.map] at headEq tailEq ⊢
  simp only [NonemptyList.mk.injEq]
  exact ⟨headEq, tailEq⟩
private theorem spelledTerminalLoc_functional
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol} {parsedType : Type}
    (Projects : MatchedTerminal file tokens terminal →
      String → parsedType → Prop)
    (projectsFunctional : ∀ {matched leftSpelling rightSpelling
        leftParsed rightParsed},
      Projects matched leftSpelling leftParsed →
        Projects matched rightSpelling rightParsed →
          leftParsed = rightParsed)
    {left right : RuleReduction.SpelledTerminalData file tokens
      terminal parsedType}
    (leftProjects : Projects left.matched left.spelling left.parsed)
    (rightProjects : Projects right.matched right.spelling right.parsed)
    (matchedEq : left.matched = right.matched) :
    RuleReduction.terminalLoc left.matched left.parsed =
      RuleReduction.terminalLoc right.matched right.parsed := by
  cases left with
  | mk leftMatched leftSpelling leftParsed =>
      cases right with
      | mk rightMatched rightSpelling rightParsed =>
          cases matchedEq
          have parsedEq : leftParsed = rightParsed := by
            simpa using projectsFunctional leftProjects rightProjects
          cases parsedEq
          rfl
private theorem identifierTerminalLoc_functional
    {file : WorkspaceFile} {tokens : List Token}
    {left right : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier}
    (leftProjects : IdentifierProjects left.matched left.spelling left.parsed)
    (rightProjects : IdentifierProjects right.matched right.spelling right.parsed)
    (matchedEq : left.matched = right.matched) :
    RuleReduction.terminalLoc left.matched left.parsed =
      RuleReduction.terminalLoc right.matched right.parsed :=
  spelledTerminalLoc_functional IdentifierProjects
    (fun left right => (IdentifierProjects.functional left right).2)
    leftProjects rightProjects matchedEq
private theorem pathTerminalLoc_functional
    {file : WorkspaceFile} {tokens : List Token}
    {left right : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment}
    (leftProjects : PathSegmentProjects left.matched left.spelling left.parsed)
    (rightProjects : PathSegmentProjects right.matched right.spelling right.parsed)
    (matchedEq : left.matched = right.matched) :
    RuleReduction.terminalLoc left.matched left.parsed =
      RuleReduction.terminalLoc right.matched right.parsed :=
  spelledTerminalLoc_functional PathSegmentProjects
    (fun left right => (PathSegmentProjects.functional left right).2)
    leftProjects rightProjects matchedEq
private theorem externalTerminalLoc_functional
    {file : WorkspaceFile} {tokens : List Token}
    {left right : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName}
    (leftProjects : ExternalLibraryProjects
      left.matched left.spelling left.parsed)
    (rightProjects : ExternalLibraryProjects
      right.matched right.spelling right.parsed)
    (matchedEq : left.matched = right.matched) :
    RuleReduction.terminalLoc left.matched left.parsed =
      RuleReduction.terminalLoc right.matched right.parsed :=
  spelledTerminalLoc_functional ExternalLibraryProjects
    (fun left right => (ExternalLibraryProjects.functional left right).2)
    leftProjects rightProjects matchedEq
private theorem identifierListLocated_functional
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List (RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)}
    (leftProjects : ∀ value, value ∈ left →
      IdentifierProjects value.matched value.spelling value.parsed)
    (rightProjects : ∀ value, value ∈ right →
      IdentifierProjects value.matched value.spelling value.parsed)
    (matchedEq : left.map (fun value => value.matched) =
      right.map (fun value => value.matched)) :
    left.map (fun value => RuleReduction.terminalLoc
      value.matched value.parsed) =
      right.map (fun value => RuleReduction.terminalLoc
        value.matched value.parsed) :=
  listMap_output_functional leftProjects rightProjects
    identifierTerminalLoc_functional matchedEq

private theorem identifierNonemptyLocated_functional
    {file : WorkspaceFile} {tokens : List Token}
    {left right : NonemptyList (RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)}
    (leftProjects : IdentifierProjects left.head.matched
      left.head.spelling left.head.parsed ∧
      ∀ value, value ∈ left.tail →
        IdentifierProjects value.matched value.spelling value.parsed)
    (rightProjects : IdentifierProjects right.head.matched
      right.head.spelling right.head.parsed ∧
      ∀ value, value ∈ right.tail →
        IdentifierProjects value.matched value.spelling value.parsed)
    (matchedEq : left.map (fun value => value.matched) =
      right.map (fun value => value.matched)) :
    left.map (fun value => RuleReduction.terminalLoc
      value.matched value.parsed) =
      right.map (fun value => RuleReduction.terminalLoc
        value.matched value.parsed) :=
  nonemptyListMap_output_functional leftProjects rightProjects
    identifierTerminalLoc_functional matchedEq
private def dotTailInput
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol} {parsedType : Type}
    (value : MatchedTerminal file tokens (.symbol .dot) ×
      RuleReduction.SpelledTerminalData file tokens terminal parsedType) :
    EbnfValue file tokens (.group (.sequence [
      .atom (.terminal (.symbol .dot)), .atom (.terminal terminal)])) :=
  EbnfValue.group _ (EbnfValue.sequence _
    (EbnfValues.cons _ _ (EbnfValue.terminalAtom _ value.1)
      (EbnfValues.cons _ _ (EbnfValue.terminalAtom _ value.2.matched)
        EbnfValues.nil)))

private theorem dotTailInput_matched_functional
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol} {parsedType : Type}
    {left right : MatchedTerminal file tokens (.symbol .dot) ×
      RuleReduction.SpelledTerminalData file tokens terminal parsedType}
    (inputEq : dotTailInput left = dotTailInput right) :
    (left.1, left.2.matched) = (right.1, right.2.matched) := by
  have groupEq := EbnfValue.group_injective _ inputEq
  have sequenceEq := EbnfValue.sequence_injective _ groupEq
  have firstEq := EbnfValues.cons_injective _ _ sequenceEq
  have dotEq := EbnfValue.terminalAtom_injective _ firstEq.1
  have secondEq := EbnfValues.cons_injective _ _ firstEq.2
  have terminalEq := EbnfValue.terminalAtom_injective _ secondEq.1
  exact Prod.ext dotEq terminalEq

private theorem identifierDotTailLocated_functional
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List
      (MatchedTerminal file tokens (.symbol .dot) ×
        RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier)}
    (leftProjects : ∀ value, value ∈ left →
      IdentifierProjects value.2.matched value.2.spelling value.2.parsed)
    (rightProjects : ∀ value, value ∈ right →
      IdentifierProjects value.2.matched value.2.spelling value.2.parsed)
    (inputEq : left.map dotTailInput = right.map dotTailInput) :
    left.map (fun value => RuleReduction.terminalLoc
      value.2.matched value.2.parsed) =
      right.map (fun value => RuleReduction.terminalLoc
        value.2.matched value.2.parsed) := by
  apply listMap_output_functional leftProjects rightProjects _ inputEq
  intro leftValue rightValue leftProof rightProof valueEq
  exact identifierTerminalLoc_functional leftProof rightProof
    (congrArg Prod.snd (dotTailInput_matched_functional valueEq))

private theorem pathDotTailLocated_functional
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List
      (MatchedTerminal file tokens (.symbol .dot) ×
        RuleReduction.SpelledTerminalData file tokens
          (.category .pathComponent) PathSegment)}
    (leftProjects : ∀ value, value ∈ left →
      PathSegmentProjects value.2.matched value.2.spelling value.2.parsed)
    (rightProjects : ∀ value, value ∈ right →
      PathSegmentProjects value.2.matched value.2.spelling value.2.parsed)
    (inputEq : left.map dotTailInput = right.map dotTailInput) :
    left.map (fun value => RuleReduction.terminalLoc
      value.2.matched value.2.parsed) =
      right.map (fun value => RuleReduction.terminalLoc
        value.2.matched value.2.parsed) := by
  apply listMap_output_functional leftProjects rightProjects _ inputEq
  intro leftValue rightValue leftProof rightProof valueEq
  exact pathTerminalLoc_functional leftProof rightProof
    (congrArg Prod.snd (dotTailInput_matched_functional valueEq))

private theorem moduleRef_standard_library_exclusive
    {file : WorkspaceFile} {tokens : List Token}
    {left right : MatchedTerminal file tokens (.category .pathComponent)}
    (matchedEq : left = right)
    (standard : RuleReduction.MarkerProjects file tokens left .standardRoot)
    (library : RuleReduction.MarkerProjects file tokens right .libraryRoot) :
    False := by
  subst right
  have kindEq := RuleReduction.MarkerProjects.functional standard library
  contradiction

private theorem moduleRef_standard_relative_exclusive
    {file : WorkspaceFile} {tokens : List Token}
    {root : MatchedTerminal file tokens (.category .pathComponent)}
    {relative : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment}
    (matchedEq : root = relative.matched)
    (standard : RuleReduction.MarkerProjects file tokens root .standardRoot)
    (relativeProjects : PathSegmentProjects relative.matched
      relative.spelling relative.parsed)
    (notStandard : relative.spelling ≠ "std") : False := by
  subst root
  cases standard with
  | standardRoot _ parsed standardProjects =>
      exact notStandard
        (PathSegmentProjects.functional relativeProjects standardProjects).1

private theorem moduleRef_library_relative_exclusive
    {file : WorkspaceFile} {tokens : List Token}
    {root : MatchedTerminal file tokens (.category .pathComponent)}
    {relative : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment}
    (matchedEq : root = relative.matched)
    (library : RuleReduction.MarkerProjects file tokens root .libraryRoot)
    (relativeProjects : PathSegmentProjects relative.matched
      relative.spelling relative.parsed)
    (notLibrary : relative.spelling ≠ "lib") : False := by
  subst root
  cases library with
  | libraryRoot _ parsed libraryProjects =>
      exact notLibrary
        (PathSegmentProjects.functional relativeProjects libraryProjects).1

private theorem ruleReduction_topItem_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .topItem)}
    {left right : RuleValue .topItem}
    (leftReduces : RuleReduction file tokens .topItem origin finish input left)
    (rightReduces : RuleReduction file tokens .topItem origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals simp at inputEq
  all_goals first
    | apply (sourceLoc_eq_iff _ _ _ _).2
      exact congrArg _ inputEq
    | apply (sourceLoc_eq_iff _ _ _ _).2
      exact congrArg _ (ruleAtom_inj_iff.mp inputEq)

private theorem ruleReduction_optionalComma_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .optionalComma)}
    {left right : RuleValue .optionalComma}
    (leftReduces : RuleReduction file tokens .optionalComma origin finish input left)
    (rightReduces : RuleReduction file tokens .optionalComma origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals simp at inputEq
  all_goals subst_vars <;> rfl

private theorem ruleReduction_assignmentOperator_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .assignmentOperator)}
    {left right : RuleValue .assignmentOperator}
    (leftReduces : RuleReduction file tokens .assignmentOperator origin finish input left)
    (rightReduces : RuleReduction file tokens .assignmentOperator origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals have choiceEq := EbnfValue.choice_injective _ inputEq
  all_goals have choiceParts := Sigma.ext_iff.mp choiceEq
  all_goals simp at choiceParts
  all_goals have terminalEq :=
    EbnfValue.terminalAtom_injective _ choiceParts
  all_goals cases terminalEq <;> rfl

private theorem ruleReduction_equality_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .equality)}
    {left right : RuleValue .equality}
    (leftReduces : RuleReduction file tokens .equality origin finish input left)
    (rightReduces : RuleReduction file tokens .equality origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals have sequenceEq := EbnfValue.sequence_injective _ inputEq
  all_goals have outerConsEq := EbnfValues.cons_injective _ _ sequenceEq
  all_goals have leftEq :=
    EbnfValue.ruleAtom_injective _ outerConsEq.1
  all_goals have optionConsEq :=
    EbnfValues.cons_injective _ _ outerConsEq.2
  all_goals have optionEq :=
    EbnfValue.optional_injective _ optionConsEq.1
  all_goals try exact leftEq
  all_goals first
    | have innerValueEq := Option.some.inj optionEq
    | cases optionEq
  all_goals have innerSequenceEq :=
    EbnfValue.sequence_injective _ innerValueEq
  all_goals have operatorConsEq :=
    EbnfValues.cons_injective _ _ innerSequenceEq
  all_goals have groupedEq :=
    EbnfValue.group_injective _ operatorConsEq.1
  all_goals have operatorChoiceEq :=
    EbnfValue.choice_injective _ groupedEq
  all_goals have branchEq := congrArg Sigma.fst operatorChoiceEq
  all_goals simp at branchEq
  all_goals have operatorChoiceParts := Sigma.ext_iff.mp operatorChoiceEq
  all_goals have operatorValueEq := eq_of_heq operatorChoiceParts.2
  all_goals have operatorEq :=
    EbnfValue.terminalAtom_injective _ operatorValueEq
  all_goals have rightConsEq :=
    EbnfValues.cons_injective _ _ operatorConsEq.2
  all_goals have rightEq :=
    EbnfValue.ruleAtom_injective _ rightConsEq.1
  all_goals cases leftEq
  all_goals cases operatorEq
  all_goals cases rightEq
  all_goals exact (sourceLoc_eq_iff _ _ _ _).2 rfl

private theorem ruleReduction_relational_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .relational)}
    {left right : RuleValue .relational}
    (leftReduces : RuleReduction file tokens .relational origin finish input left)
    (rightReduces : RuleReduction file tokens .relational origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals have sequenceEq := EbnfValue.sequence_injective _ inputEq
  all_goals have outerConsEq := EbnfValues.cons_injective _ _ sequenceEq
  all_goals have leftEq :=
    EbnfValue.ruleAtom_injective _ outerConsEq.1
  all_goals have optionConsEq :=
    EbnfValues.cons_injective _ _ outerConsEq.2
  all_goals have optionEq :=
    EbnfValue.optional_injective _ optionConsEq.1
  all_goals try exact leftEq
  all_goals first
    | have innerValueEq := Option.some.inj optionEq
    | cases optionEq
  all_goals have innerSequenceEq :=
    EbnfValue.sequence_injective _ innerValueEq
  all_goals have operatorConsEq :=
    EbnfValues.cons_injective _ _ innerSequenceEq
  all_goals have groupedEq :=
    EbnfValue.group_injective _ operatorConsEq.1
  all_goals have operatorChoiceEq :=
    EbnfValue.choice_injective _ groupedEq
  all_goals have branchEq := congrArg Sigma.fst operatorChoiceEq
  all_goals simp at branchEq
  all_goals have operatorChoiceParts := Sigma.ext_iff.mp operatorChoiceEq
  all_goals have operatorValueEq := eq_of_heq operatorChoiceParts.2
  all_goals have operatorEq :=
    EbnfValue.terminalAtom_injective _ operatorValueEq
  all_goals have rightConsEq :=
    EbnfValues.cons_injective _ _ operatorConsEq.2
  all_goals have rightEq :=
    EbnfValue.ruleAtom_injective _ rightConsEq.1
  all_goals cases leftEq
  all_goals cases operatorEq
  all_goals cases rightEq
  all_goals exact (sourceLoc_eq_iff _ _ _ _).2 rfl

private theorem ruleReduction_statement_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .statement)}
    {left right : RuleValue .statement}
    (leftReduces : RuleReduction file tokens .statement origin finish input left)
    (rightReduces : RuleReduction file tokens .statement origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals have choiceEq := EbnfValue.choice_injective _ inputEq
  all_goals have branchEq := congrArg Sigma.fst choiceEq
  all_goals simp at branchEq
  all_goals have choiceParts := Sigma.ext_iff.mp choiceEq
  all_goals have valueEq := eq_of_heq choiceParts.2
  all_goals simp only [List.get_eq_getElem] at valueEq
  all_goals first
    | exact EbnfValue.ruleAtom_injective .letStatement valueEq
    | exact EbnfValue.ruleAtom_injective .returnStatement valueEq
    | exact EbnfValue.ruleAtom_injective .matchStatement valueEq
    | exact EbnfValue.ruleAtom_injective .ifStatement valueEq
    | exact EbnfValue.ruleAtom_injective .forStatement valueEq
    | exact EbnfValue.ruleAtom_injective .assemblyStatement valueEq
    | exact EbnfValue.ruleAtom_injective .blockStatement valueEq
    | exact EbnfValue.ruleAtom_injective .breakStatement valueEq
    | exact EbnfValue.ruleAtom_injective .continueStatement valueEq
    | exact EbnfValue.ruleAtom_injective .assignmentStatement valueEq
    | exact EbnfValue.ruleAtom_injective .expressionStatement valueEq

private theorem ruleReduction_functionDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .functionDecl)}
    {left right : RuleValue .functionDecl}
    (leftReduces : RuleReduction file tokens .functionDecl origin finish input left)
    (rightReduces : RuleReduction file tokens .functionDecl origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  simp at inputEq
  rcases inputEq with ⟨rfl, rfl⟩
  exact (sourceLoc_eq_iff _ _ _ _).2 rfl

private theorem ruleReduction_classMethod_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .classMethod)}
    {left right : RuleValue .classMethod}
    (leftReduces : RuleReduction file tokens .classMethod origin finish input left)
    (rightReduces : RuleReduction file tokens .classMethod origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  simp at inputEq
  rcases inputEq with ⟨rfl, rfl⟩
  exact (sourceLoc_eq_iff _ _ _ _).2 rfl

private theorem ruleReduction_instanceMethod_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .instanceMethod)}
    {left right : RuleValue .instanceMethod}
    (leftReduces : RuleReduction file tokens .instanceMethod origin finish input left)
    (rightReduces : RuleReduction file tokens .instanceMethod origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  have transportedEq := EbnfValue.transport_injective _ inputEq
  have valueEq := EbnfValue.ruleAtom_injective .functionDecl transportedEq
  simpa only [RuleValue] using valueEq

private theorem ruleReduction_contractMember_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .contractMember)}
    {left right : RuleValue .contractMember}
    (leftReduces : RuleReduction file tokens .contractMember origin finish input left)
    (rightReduces : RuleReduction file tokens .contractMember origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals have choiceEq := EbnfValue.choice_injective _ inputEq
  all_goals have branchEq := congrArg Sigma.fst choiceEq
  all_goals simp at branchEq
  all_goals have choiceParts := Sigma.ext_iff.mp choiceEq
  all_goals have valueEq := eq_of_heq choiceParts.2
  all_goals simp only [List.get_eq_getElem] at valueEq
  all_goals apply (sourceLoc_eq_iff _ _ _ _).2
  all_goals first
    | exact congrArg _ (EbnfValue.ruleAtom_injective .dataDecl valueEq)
    | exact congrArg _ (EbnfValue.ruleAtom_injective .typeAliasDecl valueEq)
    | exact congrArg _ (EbnfValue.ruleAtom_injective .fieldDecl valueEq)
    | exact congrArg _ (EbnfValue.ruleAtom_injective .functionDecl valueEq)
    | exact congrArg _ (EbnfValue.ruleAtom_injective .fallbackDecl valueEq)
    | exact congrArg _
        (EbnfValue.ruleAtom_injective .contractConstructorDecl valueEq)

private theorem ruleReduction_letStatement_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .letStatement)}
    {left right : RuleValue .letStatement}
    (leftReduces : RuleReduction file tokens .letStatement origin finish input left)
    (rightReduces : RuleReduction file tokens .letStatement origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have bindingConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have bindingEq := EbnfValue.ruleAtom_injective _ bindingConsEq.1
  exact (sourceLoc_eq_iff _ _ _ _).2 (congrArg _ bindingEq)

private theorem ruleReduction_returnStatement_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .returnStatement)}
    {left right : RuleValue .returnStatement}
    (leftReduces : RuleReduction file tokens .returnStatement origin finish input left)
    (rightReduces : RuleReduction file tokens .returnStatement origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have keywordConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have valueConsEq := EbnfValues.cons_injective _ _ keywordConsEq.2
  have optionalEq := EbnfValue.optional_injective _ valueConsEq.1
  have valueEq := Option.map_injective
    (EbnfValue.ruleAtom_injective .expression) optionalEq
  have semicolonConsEq := EbnfValues.cons_injective _ _ valueConsEq.2
  have semicolonEq :=
    EbnfValue.terminalAtom_injective _ semicolonConsEq.1
  cases valueEq
  cases semicolonEq
  exact (sourceLoc_eq_iff _ _ _ _).2 rfl

private theorem ruleReduction_blockStatement_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .blockStatement)}
    {left right : RuleValue .blockStatement}
    (leftReduces : RuleReduction file tokens .blockStatement origin finish input left)
    (rightReduces : RuleReduction file tokens .blockStatement origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  have bodyEq := EbnfValue.ruleAtom_injective .body inputEq
  exact (sourceLoc_eq_iff _ _ _ _).2 (congrArg _ bodyEq)

private theorem ruleReduction_breakStatement_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .breakStatement)}
    {left right : RuleValue .breakStatement}
    (leftReduces : RuleReduction file tokens .breakStatement origin finish input left)
    (rightReduces : RuleReduction file tokens .breakStatement origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have keywordConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have semicolonConsEq := EbnfValues.cons_injective _ _ keywordConsEq.2
  have semicolonEq :=
    EbnfValue.terminalAtom_injective _ semicolonConsEq.1
  cases semicolonEq
  exact (sourceLoc_eq_iff _ _ _ _).2 rfl

private theorem ruleReduction_continueStatement_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .continueStatement)}
    {left right : RuleValue .continueStatement}
    (leftReduces : RuleReduction file tokens .continueStatement origin finish input left)
    (rightReduces : RuleReduction file tokens .continueStatement origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have keywordConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have semicolonConsEq := EbnfValues.cons_injective _ _ keywordConsEq.2
  have semicolonEq :=
    EbnfValue.terminalAtom_injective _ semicolonConsEq.1
  cases semicolonEq
  exact (sourceLoc_eq_iff _ _ _ _).2 rfl

private theorem ruleReduction_assemblyStatement_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .assemblyStatement)}
    {left right : RuleValue .assemblyStatement}
    (leftReduces : RuleReduction file tokens .assemblyStatement origin finish input left)
    (rightReduces : RuleReduction file tokens .assemblyStatement origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have keywordConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have tokenConsEq := EbnfValues.cons_injective _ _ keywordConsEq.2
  have tokenEq := EbnfValue.terminalAtom_injective _ tokenConsEq.1
  rename_i _ _ leftSlice leftProjects _ _ _ rightSlice rightProjects _
  rw [← tokenEq] at rightProjects
  have sliceEq : leftSlice = rightSlice :=
    AssemblySliceProjects.functional leftProjects rightProjects
  cases sliceEq
  exact (sourceLoc_eq_iff _ _ _ _).2 rfl

private theorem ruleReduction_armStatement_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .armStatement)}
    {left right : RuleValue .armStatement}
    (leftReduces : RuleReduction file tokens .armStatement origin finish input left)
    (rightReduces : RuleReduction file tokens .armStatement origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  exact EbnfValue.ruleAtom_injective .statement inputEq

private theorem ruleReduction_assignmentStatement_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .assignmentStatement)}
    {left right : RuleValue .assignmentStatement}
    (leftReduces : RuleReduction file tokens .assignmentStatement origin finish input left)
    (rightReduces : RuleReduction file tokens .assignmentStatement origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have leftConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have leftEq := EbnfValue.ruleAtom_injective _ leftConsEq.1
  have operatorConsEq := EbnfValues.cons_injective _ _ leftConsEq.2
  have operatorEq := EbnfValue.ruleAtom_injective _ operatorConsEq.1
  have rightConsEq := EbnfValues.cons_injective _ _ operatorConsEq.2
  have rightEq := EbnfValue.ruleAtom_injective _ rightConsEq.1
  cases leftEq
  cases operatorEq
  cases rightEq
  exact (sourceLoc_eq_iff _ _ _ _).2 rfl

private theorem ruleReduction_expressionStatement_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .expressionStatement)}
    {left right : RuleValue .expressionStatement}
    (leftReduces : RuleReduction file tokens .expressionStatement origin finish input left)
    (rightReduces : RuleReduction file tokens .expressionStatement origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals have choiceEq := EbnfValue.choice_injective _ inputEq
  all_goals have branchEq := congrArg Sigma.fst choiceEq
  all_goals simp at branchEq
  all_goals have choiceParts := Sigma.ext_iff.mp choiceEq
  all_goals have valueEq := eq_of_heq choiceParts.2
  all_goals simp only [List.get_eq_getElem] at valueEq
  all_goals apply (sourceLoc_eq_iff _ _ _ _).2
  · have sequenceEq := EbnfValue.sequence_injective _ valueEq
    have expressionConsEq := EbnfValues.cons_injective _ _ sequenceEq
    have expressionEq :=
      EbnfValue.ruleAtom_injective _ expressionConsEq.1
    have semicolonConsEq :=
      EbnfValues.cons_injective _ _ expressionConsEq.2
    have semicolonEq :=
      EbnfValue.terminalAtom_injective _ semicolonConsEq.1
    cases expressionEq
    cases semicolonEq
    rfl
  · have expressionEq := EbnfValue.ruleAtom_injective _ valueEq
    cases expressionEq
    rfl

private theorem ruleReduction_terminalExpression_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .terminalExpression)}
    {left right : RuleValue .terminalExpression}
    (leftReduces : RuleReduction file tokens .terminalExpression origin finish input left)
    (rightReduces : RuleReduction file tokens .terminalExpression origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  exact EbnfValue.ruleAtom_injective .expression inputEq

private theorem ruleReduction_expression_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .expression)}
    {left right : RuleValue .expression}
    (leftReduces : RuleReduction file tokens .expression origin finish input left)
    (rightReduces : RuleReduction file tokens .expression origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  exact EbnfValue.ruleAtom_injective .annotation inputEq

private theorem ruleReduction_literal_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .literal)}
    {left right : RuleValue .literal}
    (leftReduces : RuleReduction file tokens .literal origin finish input left)
    (rightReduces : RuleReduction file tokens .literal origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals have choiceEq := EbnfValue.choice_injective _ inputEq
  all_goals have branchEq := congrArg Sigma.fst choiceEq
  all_goals simp at branchEq
  all_goals have choiceParts := Sigma.ext_iff.mp choiceEq
  all_goals have valueEq := eq_of_heq choiceParts.2
  all_goals simp only [List.get_eq_getElem] at valueEq
  all_goals have terminalEq := EbnfValue.terminalAtom_injective _ valueEq
  all_goals cases terminalEq
  all_goals
    rename_i _ leftPayload leftProjects rightPayload rightProjects
    have payloadEq : leftPayload = rightPayload :=
      LiteralProjects.functional leftProjects rightProjects
    cases payloadEq
    rfl

private theorem ruleReduction_moduleRef_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .moduleRef)}
    {left right : RuleValue .moduleRef}
    (leftReduces : RuleReduction file tokens .moduleRef
      origin finish input left)
    (rightReduces : RuleReduction file tokens .moduleRef
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals
    have rootEq := EbnfValue.transport_injective _ inputEq
    have choiceEq := EbnfValue.choice_injective _ rootEq
    have branchEq := congrArg Sigma.fst choiceEq
    simp at branchEq
  all_goals
    have branchValueEq := eq_of_heq (Sigma.ext_iff.mp choiceEq).2
    have sequenceEq := EbnfValue.sequence_injective _ branchValueEq
    have firstConsEq := EbnfValues.cons_injective _ _ sequenceEq
    have firstMatchedEq := EbnfValue.terminalAtom_injective _ firstConsEq.1
  case moduleRefExternal.moduleRefExternal =>
    rename_i atLeft libraryLeft dotLeft nextLeft restLeft atMarkerLeft
      libraryProjectsLeft nextProjectsLeft restProjectsLeft witnessLeft
      atRight libraryRight dotRight nextRight restRight atMarkerRight
      libraryProjectsRight nextProjectsRight restProjectsRight witnessRight
    have libraryConsEq := EbnfValues.cons_injective _ _ firstConsEq.2
    have libraryMatchedEq :=
      EbnfValue.terminalAtom_injective _ libraryConsEq.1
    have dotConsEq := EbnfValues.cons_injective _ _ libraryConsEq.2
    have nextConsEq := EbnfValues.cons_injective _ _ dotConsEq.2
    have nextMatchedEq := EbnfValue.terminalAtom_injective _ nextConsEq.1
    have starConsEq := EbnfValues.cons_injective _ _ nextConsEq.2
    have restInputEq := EbnfValue.star_injective _ starConsEq.1
    change restLeft.map dotTailInput =
      restRight.map dotTailInput at restInputEq
    have libraryLocEq := externalTerminalLoc_functional
      libraryProjectsLeft libraryProjectsRight libraryMatchedEq
    have nextLocEq := pathTerminalLoc_functional
      nextProjectsLeft nextProjectsRight nextMatchedEq
    have restLocEq := pathDotTailLocated_functional
      restProjectsLeft restProjectsRight restInputEq
    apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
    cases firstMatchedEq
    rw [libraryLocEq, nextLocEq, restLocEq]
  all_goals
    have starConsEq := EbnfValues.cons_injective _ _ firstConsEq.2
    have restInputEq := EbnfValue.star_injective _ starConsEq.1
  all_goals first
    | exact (moduleRef_standard_library_exclusive firstMatchedEq
        (by assumption) (by assumption)).elim
    | exact (moduleRef_standard_library_exclusive firstMatchedEq.symm
        (by assumption) (by assumption)).elim
    | exact (moduleRef_standard_relative_exclusive firstMatchedEq
        (by assumption) (by assumption) (by assumption)).elim
    | exact (moduleRef_standard_relative_exclusive firstMatchedEq.symm
        (by assumption) (by assumption) (by assumption)).elim
    | exact (moduleRef_library_relative_exclusive firstMatchedEq
        (by assumption) (by assumption) (by assumption)).elim
    | exact (moduleRef_library_relative_exclusive firstMatchedEq.symm
        (by assumption) (by assumption) (by assumption)).elim
    | skip
  all_goals try simp only [List.cons.injEq] at restInputEq
  all_goals first
    | exact (List.cons_ne_nil _ _ restInputEq).elim
    | exact (List.cons_ne_nil _ _ restInputEq.symm).elim
    | skip
  case moduleRefStandard.moduleRefStandard =>
    rename_i firstLeft restLeft markerLeft projectsLeft witnessLeft
      firstRight restRight markerRight projectsRight witnessRight
    change restLeft.map dotTailInput =
      restRight.map dotTailInput at restInputEq
    have restLocEq := pathDotTailLocated_functional
      projectsLeft projectsRight restInputEq
    apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
    cases firstMatchedEq
    rw [restLocEq]
  case moduleRefLibraryRoot.moduleRefLibraryRoot =>
    rename_i firstLeft nextDotLeft nextLeft remainingLeft markerLeft
      nextProjectsLeft remainingProjectsLeft witnessLeft
      firstRight nextDotRight nextRight remainingRight markerRight
      nextProjectsRight remainingProjectsRight witnessRight
    change dotTailInput (nextDotLeft, nextLeft) =
        dotTailInput (nextDotRight, nextRight) ∧
      remainingLeft.map dotTailInput =
        remainingRight.map dotTailInput at restInputEq
    have nextMatchedEq := congrArg Prod.snd
      (dotTailInput_matched_functional restInputEq.1)
    have nextLocEq := pathTerminalLoc_functional
      nextProjectsLeft nextProjectsRight nextMatchedEq
    have remainingLocEq := pathDotTailLocated_functional
      remainingProjectsLeft remainingProjectsRight restInputEq.2
    apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
    cases firstMatchedEq
    rw [nextLocEq, remainingLocEq]
  case moduleRefRelativeLibraryEmpty.moduleRefRelativeLibraryEmpty =>
    rename_i firstLeft projectsLeft markerLeft witnessLeft
      firstRight projectsRight markerRight witnessRight
    have firstLocEq := pathTerminalLoc_functional
      projectsLeft projectsRight firstMatchedEq
    apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
    rw [firstLocEq]
  case moduleRefRelativeOther.moduleRefRelativeOther =>
    rename_i firstLeft restLeft firstProjectsLeft restProjectsLeft
      notStandardLeft notLibraryLeft witnessLeft firstRight restRight
      firstProjectsRight restProjectsRight notStandardRight notLibraryRight
      witnessRight
    change restLeft.map dotTailInput =
      restRight.map dotTailInput at restInputEq
    have firstLocEq := pathTerminalLoc_functional
      firstProjectsLeft firstProjectsRight firstMatchedEq
    have restLocEq := pathDotTailLocated_functional
      restProjectsLeft restProjectsRight restInputEq
    apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
    rw [firstLocEq, restLocEq]

private theorem ruleReduction_qualifiedName_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .qualifiedName)}
    {left right : RuleValue .qualifiedName}
    (leftReduces : RuleReduction file tokens .qualifiedName
      origin finish input left)
    (rightReduces : RuleReduction file tokens .qualifiedName
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  rename_i firstLeft restLeft firstProjectsLeft restProjectsLeft witnessLeft
    firstRight restRight firstProjectsRight restProjectsRight witnessRight
  have rootEq := EbnfValue.transport_injective _ inputEq
  have sequenceEq := EbnfValue.sequence_injective _ rootEq
  have firstConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have firstMatchedEq := EbnfValue.terminalAtom_injective _ firstConsEq.1
  have starConsEq := EbnfValues.cons_injective _ _ firstConsEq.2
  have restInputEq := EbnfValue.star_injective _ starConsEq.1
  change restLeft.map dotTailInput =
    restRight.map dotTailInput at restInputEq
  have firstLocEq := identifierTerminalLoc_functional
    firstProjectsLeft firstProjectsRight firstMatchedEq
  have restLocEq := identifierDotTailLocated_functional
    restProjectsLeft restProjectsRight restInputEq
  apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
  rw [firstLocEq, restLocEq]

private theorem ruleReduction_hidingClause_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .hidingClause)}
    {left right : RuleValue .hidingClause}
    (leftReduces : RuleReduction file tokens .hidingClause
      origin finish input left)
    (rightReduces : RuleReduction file tokens .hidingClause
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  rename_i _ _ namesLeft _ projectsLeft witnessLeft
    _ _ namesRight _ projectsRight witnessRight
  have rootEq := EbnfValue.transport_injective _ inputEq
  have sequenceEq := EbnfValue.sequence_injective _ rootEq
  have keywordConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have openConsEq := EbnfValues.cons_injective _ _ keywordConsEq.2
  have namesConsEq := EbnfValues.cons_injective _ _ openConsEq.2
  have namesInputEq := EbnfValue.list0_injective _ namesConsEq.1
  have matchedEq : namesLeft.map (fun value => value.matched) =
      namesRight.map (fun value => value.matched) := by
    apply listMap_injective_of_injective
      (EbnfValue.terminalAtom_injective (.category .identifier))
    simpa [List.map_map, Function.comp_def] using namesInputEq
  have namesLocEq := identifierListLocated_functional
    projectsLeft projectsRight matchedEq
  apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
  rw [namesLocEq]

private theorem ruleReduction_constructorSelection_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .constructorSelection)}
    {left right : RuleValue .constructorSelection}
    (leftReduces : RuleReduction file tokens .constructorSelection
      origin finish input left)
    (rightReduces : RuleReduction file tokens .constructorSelection
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals
    have rootEq := EbnfValue.transport_injective _ inputEq
    have choiceEq := EbnfValue.choice_injective _ rootEq
    have branchEq := congrArg Sigma.fst choiceEq
    simp at branchEq
  all_goals
    have branchValueEq := eq_of_heq (Sigma.ext_iff.mp choiceEq).2
    have sequenceEq := EbnfValue.sequence_injective _ branchValueEq
    have openConsEq := EbnfValues.cons_injective _ _ sequenceEq
  case constructorSelectionAll.constructorSelectionAll =>
    rename_i _ starLeft _ _ witnessLeft _ starRight _ _ witnessRight
    have starConsEq := EbnfValues.cons_injective _ _ openConsEq.2
    have starEq := EbnfValue.terminalAtom_injective _ starConsEq.1
    cases starEq
    exact (sourceLoc_eq_iff witnessLeft witnessRight _ _).2 rfl
  case constructorSelectionNamed.constructorSelectionNamed =>
    rename_i _ namesLeft _ headProjectsLeft tailProjectsLeft witnessLeft
      _ namesRight _ headProjectsRight tailProjectsRight witnessRight
    have namesConsEq := EbnfValues.cons_injective _ _ openConsEq.2
    have namesInputEq := EbnfValue.list1_injective _ namesConsEq.1
    have matchedEq :
        namesLeft.map (fun value => value.matched) =
          namesRight.map (fun value => value.matched) := by
      apply nonemptyListMap_injective_of_injective
        (EbnfValue.terminalAtom_injective (.category .identifier))
      simpa [NonemptyList.map, List.map_map, Function.comp_def]
        using namesInputEq
    have namesLocEq := identifierNonemptyLocated_functional
      ⟨headProjectsLeft, tailProjectsLeft⟩
      ⟨headProjectsRight, tailProjectsRight⟩ matchedEq
    apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
    rw [namesLocEq]

private theorem ruleReduction_pragmaDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .pragmaDecl)}
    {left right : RuleValue .pragmaDecl}
    (leftReduces : RuleReduction file tokens .pragmaDecl
      origin finish input left)
    (rightReduces : RuleReduction file tokens .pragmaDecl
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals
    have rootEq := EbnfValue.transport_injective _ inputEq
    have choiceEq := EbnfValue.choice_injective _ rootEq
    have branchEq := congrArg Sigma.fst choiceEq
    simp at branchEq
  all_goals
    have branchValueEq := eq_of_heq (Sigma.ext_iff.mp choiceEq).2
    have sequenceEq := EbnfValue.sequence_injective _ branchValueEq
    have keywordConsEq := EbnfValues.cons_injective _ _ sequenceEq
    have kindConsEq := EbnfValues.cons_injective _ _ keywordConsEq.2
    have kindEq := EbnfValue.terminalAtom_injective _ kindConsEq.1
    have targetsConsEq := EbnfValues.cons_injective _ _ kindConsEq.2
    have optionalEq := EbnfValue.optional_injective _ targetsConsEq.1
    rename_i _ _ targetsLeft _ projectsLeft witnessLeft
      _ _ targetsRight _ projectsRight witnessRight
    cases kindEq
    apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
    cases targetsLeft with
    | none =>
        cases targetsRight with
        | none => rfl
        | some rightValues => cases optionalEq
    | some leftValues =>
        cases targetsRight with
        | none => cases optionalEq
        | some rightValues =>
            have listValueEq := Option.some.inj optionalEq
            have terminalListEq :=
              EbnfValue.list1_injective _ listValueEq
            have matchedEq :
                leftValues.map (fun value => value.matched) =
                  rightValues.map (fun value => value.matched) := by
              apply nonemptyListMap_injective_of_injective
                (EbnfValue.terminalAtom_injective (.category .identifier))
              simpa [NonemptyList.map, List.map_map, Function.comp_def]
                using terminalListEq
            have locatedEq := identifierNonemptyLocated_functional
              (projectsLeft leftValues rfl)
              (projectsRight rightValues rfl) matchedEq
            congr 1
            exact congrArg RuleReduction.firstRest locatedEq

private theorem ruleReduction_exportItem_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .exportItem)}
    {left right : RuleValue .exportItem}
    (leftReduces : RuleReduction file tokens .exportItem
      origin finish input left)
    (rightReduces : RuleReduction file tokens .exportItem
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  rename_i nameLeft selectionLeft projectsLeft witnessLeft
    nameRight selectionRight projectsRight witnessRight
  have rootEq := EbnfValue.transport_injective _ inputEq
  have sequenceEq := EbnfValue.sequence_injective _ rootEq
  have nameConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have nameMatchedEq := EbnfValue.terminalAtom_injective _ nameConsEq.1
  have selectionConsEq := EbnfValues.cons_injective _ _ nameConsEq.2
  have optionalEq := EbnfValue.optional_injective _ selectionConsEq.1
  have selectionEq := Option.map_injective
    (EbnfValue.ruleAtom_injective .constructorSelection) optionalEq
  have nameLocEq := identifierTerminalLoc_functional
    projectsLeft projectsRight nameMatchedEq
  apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
  cases selectionEq
  rw [nameLocEq]

private theorem ruleReduction_localExportEntry_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .localExportEntry)}
    {left right : RuleValue .localExportEntry}
    (leftReduces : RuleReduction file tokens .localExportEntry
      origin finish input left)
    (rightReduces : RuleReduction file tokens .localExportEntry
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals simp at inputEq
  all_goals apply (sourceLoc_eq_iff _ _ _ _).2
  all_goals simp_all [RuleReduction.marker]

private theorem ruleReduction_remoteExportEntry_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .remoteExportEntry)}
    {left right : RuleValue .remoteExportEntry}
    (leftReduces : RuleReduction file tokens .remoteExportEntry
      origin finish input left)
    (rightReduces : RuleReduction file tokens .remoteExportEntry
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals simp at inputEq
  all_goals apply (sourceLoc_eq_iff _ _ _ _).2
  all_goals simp_all [RuleReduction.marker]

private theorem ruleReduction_importEntry_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .importEntry)}
    {left right : RuleValue .importEntry}
    (leftReduces : RuleReduction file tokens .importEntry
      origin finish input left)
    (rightReduces : RuleReduction file tokens .importEntry
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals simp at inputEq
  all_goals apply (sourceLoc_eq_iff _ _ _ _).2
  case importEntryWildcard.importEntryWildcard =>
    simp_all [RuleReduction.marker]
  case importEntryNamed.importEntryNamed =>
    rename_i nameLeft projectsLeft _ nameRight projectsRight _
    rw [identifierTerminalLoc_functional projectsLeft projectsRight inputEq]
  case importEntryAliased.importEntryAliased =>
    rename_i nameLeft aliasLeft _ nameProjectsLeft aliasProjectsLeft _
      nameRight aliasRight _ nameProjectsRight aliasProjectsRight _
    rw [identifierTerminalLoc_functional
      nameProjectsLeft nameProjectsRight inputEq.1]
    rw [identifierTerminalLoc_functional
      aliasProjectsLeft aliasProjectsRight inputEq.2.2]

private theorem ruleReduction_importDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .importDecl)}
    {left right : RuleValue .importDecl}
    (leftReduces : RuleReduction file tokens .importDecl
      origin finish input left)
    (rightReduces : RuleReduction file tokens .importDecl
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals simp at inputEq
  all_goals apply (sourceLoc_eq_iff _ _ _ _).2
  case importDeclModule.importDeclModule =>
    rcases inputEq with ⟨_, referenceEq, _⟩
    cases referenceEq
    rfl
  case importDeclAliased.importDeclAliased =>
    rename_i _ referenceLeft _ nameLeft _ projectsLeft _
      _ referenceRight _ nameRight _ projectsRight _
    rcases inputEq with ⟨_, referenceEq, _, nameMatchedEq, _⟩
    have nameLocEq := identifierTerminalLoc_functional
      projectsLeft projectsRight nameMatchedEq
    rw [referenceEq, nameLocEq]
  case importDeclItems.importDeclItems =>
    rcases inputEq with ⟨_, referenceEq, _, openEq,
      entriesInputEq, closeEq, hidingInputEq, _⟩
    have entriesEq := listMap_injective_of_injective
      (EbnfValue.ruleAtom_injective .importEntry) entriesInputEq
    have hidingEq := Option.map_injective
      (EbnfValue.ruleAtom_injective .hidingClause) hidingInputEq
    cases referenceEq
    cases openEq
    cases entriesEq
    cases closeEq
    cases hidingEq
    rfl

private theorem ruleReduction_exportDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .exportDecl)}
    {left right : RuleValue .exportDecl}
    (leftReduces : RuleReduction file tokens .exportDecl
      origin finish input left)
    (rightReduces : RuleReduction file tokens .exportDecl
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals
    have rootEq := EbnfValue.transport_injective _ inputEq
    have choiceEq := EbnfValue.choice_injective _ rootEq
    have branchEq := congrArg Sigma.fst choiceEq
    simp at branchEq
  all_goals
    have valueEq := eq_of_heq (Sigma.ext_iff.mp choiceEq).2
    have sequenceEq := EbnfValue.sequence_injective _ valueEq
    simp only [cons_inj_iff, terminalAtom_inj_iff,
      ruleAtom_inj_iff, list0_inj_iff] at sequenceEq
    clear inputEq rootEq choiceEq branchEq valueEq
  all_goals apply (sourceLoc_eq_iff _ _ _ _).2
  case exportDeclLocal.exportDeclLocal =>
    rcases sequenceEq with ⟨_, openEq, entriesInputEq, closeEq, _⟩
    have entriesEq := listMap_injective_of_injective
      (EbnfValue.ruleAtom_injective .localExportEntry) entriesInputEq
    cases openEq
    cases entriesEq
    cases closeEq
    rfl
  case exportDeclModule.exportDeclModule =>
    rcases sequenceEq with ⟨_, referenceEq, _⟩
    cases referenceEq
    rfl
  case exportDeclAliased.exportDeclAliased =>
    rename_i _ referenceLeft _ nameLeft _ projectsLeft _
      _ referenceRight _ nameRight _ projectsRight _
    rcases sequenceEq with ⟨_, referenceEq, _, nameMatchedEq, _⟩
    have nameLocEq := identifierTerminalLoc_functional
      projectsLeft projectsRight nameMatchedEq
    rw [referenceEq, nameLocEq]
  case exportDeclWildcard.exportDeclWildcard =>
    have referenceEq := sequenceEq.2.1
    have dotEq := sequenceEq.2.2.1
    have starEq := sequenceEq.2.2.2.1
    simp [RuleReduction.marker, referenceEq, dotEq, starEq]
  case exportDeclBraced.exportDeclBraced =>
    have referenceEq := sequenceEq.2.1
    have openEq := sequenceEq.2.2.2.1
    have entriesInputEq := sequenceEq.2.2.2.2.1
    have closeEq := sequenceEq.2.2.2.2.2.1
    have entriesEq := listMap_injective_of_injective
      (EbnfValue.ruleAtom_injective .remoteExportEntry) entriesInputEq
    rw [referenceEq, openEq, entriesEq, closeEq]

private theorem ruleReduction_genericPrefix_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .genericPrefix)}
    {left right : RuleValue .genericPrefix}
    (leftReduces : RuleReduction file tokens .genericPrefix
      origin finish input left)
    (rightReduces : RuleReduction file tokens .genericPrefix
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals simp at inputEq
  all_goals apply (sourceLoc_eq_iff _ _ _ _).2
  all_goals simp_all

private theorem ruleReduction_predicateList_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .predicateList)}
    {left right : RuleValue .predicateList}
    (leftReduces : RuleReduction file tokens .predicateList
      origin finish input left)
    (rightReduces : RuleReduction file tokens .predicateList
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  simp at inputEq
  exact nonemptyListMap_injective_of_injective
    (EbnfValue.ruleAtom_injective .predicate) inputEq

private theorem ruleReduction_predicate_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .predicate)}
    {left right : RuleValue .predicate}
    (leftReduces : RuleReduction file tokens .predicate
      origin finish input left)
    (rightReduces : RuleReduction file tokens .predicate
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals simp at inputEq
  all_goals apply (sourceLoc_eq_iff _ _ _ _).2
  case predicateWithoutArguments.predicateWithoutArguments =>
    rcases inputEq with ⟨mainEq, _, classEq⟩
    rw [mainEq, classEq]
  case predicateWithArguments.predicateWithArguments =>
    rcases inputEq with ⟨mainEq, _, classEq, openEq,
      parametersInputEq, closeEq⟩
    have parametersEq := nonemptyListMap_injective_of_injective
      (EbnfValue.ruleAtom_injective .type) parametersInputEq
    rw [mainEq, classEq, openEq, parametersEq, closeEq]

private theorem ruleReduction_forallBinder_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .forallBinder)}
    {left right : RuleValue .forallBinder}
    (leftReduces : RuleReduction file tokens .forallBinder
      origin finish input left)
    (rightReduces : RuleReduction file tokens .forallBinder
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals simp at inputEq
  all_goals apply (sourceLoc_eq_iff _ _ _ _).2
  case forallBinderBare.forallBinderBare =>
    rename_i nameLeft projectsLeft _ nameRight projectsRight _
    rw [identifierTerminalLoc_functional projectsLeft projectsRight inputEq]
  case forallBinderBoundedWithoutArguments.forallBinderBoundedWithoutArguments =>
    rename_i nameLeft _ _ projectsLeft _
      nameRight _ _ projectsRight _
    rcases inputEq with ⟨nameMatchedEq, _, classEq⟩
    have nameLocEq := identifierTerminalLoc_functional
      projectsLeft projectsRight nameMatchedEq
    rw [nameLocEq, classEq]
  case forallBinderBoundedWithArguments.forallBinderBoundedWithArguments =>
    rename_i nameLeft _ _ _ argumentsLeft _ projectsLeft _
      nameRight _ _ _ argumentsRight _ projectsRight _
    rcases inputEq with ⟨nameMatchedEq, _, classEq, openEq,
      argumentsInputEq, closeEq⟩
    have nameLocEq := identifierTerminalLoc_functional
      projectsLeft projectsRight nameMatchedEq
    have argumentsEq := nonemptyListMap_injective_of_injective
      (EbnfValue.ruleAtom_injective .type) argumentsInputEq
    rw [nameLocEq, classEq, openEq, argumentsEq, closeEq]

private theorem ruleReduction_dataConstructor_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .dataConstructor)}
    {left right : RuleValue .dataConstructor}
    (leftReduces : RuleReduction file tokens .dataConstructor
      origin finish input left)
    (rightReduces : RuleReduction file tokens .dataConstructor
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals simp at inputEq
  all_goals apply (sourceLoc_eq_iff _ _ _ _).2
  case dataConstructorWithoutArguments.dataConstructorWithoutArguments =>
    rename_i nameLeft projectsLeft _ nameRight projectsRight _
    rw [identifierTerminalLoc_functional projectsLeft projectsRight inputEq]
  case dataConstructorWithArguments.dataConstructorWithArguments =>
    rename_i nameLeft _ fieldsLeft _ projectsLeft _
      nameRight _ fieldsRight _ projectsRight _
    rcases inputEq with ⟨nameMatchedEq, openEq, fieldsInputEq, closeEq⟩
    have nameLocEq := identifierTerminalLoc_functional
      projectsLeft projectsRight nameMatchedEq
    have fieldsEq := nonemptyListMap_injective_of_injective
      (EbnfValue.ruleAtom_injective .type) fieldsInputEq
    rw [nameLocEq, openEq, fieldsEq, closeEq]

private theorem optionMap_output_functional
    {alpha beta gamma : Type}
    {key : alpha → beta} {output : alpha → gamma}
    {projects : alpha → Prop} {left right : Option alpha}
    (leftProjects : ∀ value, left = some value → projects value)
    (rightProjects : ∀ value, right = some value → projects value)
    (pointwise : ∀ {leftValue rightValue},
      projects leftValue → projects rightValue →
        key leftValue = key rightValue →
          output leftValue = output rightValue)
    (keyEq : left.map key = right.map key) :
    left.map output = right.map output := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some rightValue => simp at keyEq
  | some leftValue =>
      cases right with
      | none => simp at keyEq
      | some rightValue =>
          simp only [Option.map_some, Option.some.injEq] at keyEq ⊢
          exact pointwise (leftProjects leftValue rfl)
            (rightProjects rightValue rfl) keyEq

private theorem ruleReduction_forallClause_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .forallClause)}
    {left right : RuleValue .forallClause}
    (leftReduces : RuleReduction file tokens .forallClause
      origin finish input left)
    (rightReduces : RuleReduction file tokens .forallClause
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  simp at inputEq
  have restEq := listMap_injective_of_injective (by
    intro left right valueEq
    simp at valueEq
    exact Prod.ext valueEq.1 valueEq.2) inputEq.2.2.1
  apply (sourceLoc_eq_iff _ _ _ _).2
  rw [inputEq.2.1, restEq]

private theorem ruleReduction_typeAliasDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .typeAliasDecl)}
    {left right : RuleValue .typeAliasDecl}
    (leftReduces : RuleReduction file tokens .typeAliasDecl
      origin finish input left)
    (rightReduces : RuleReduction file tokens .typeAliasDecl
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  rename_i _ nameLeft parametersLeft _ bodyLeft _ nameProjectsLeft
    parameterProjectsLeft witnessLeft _ nameRight parametersRight _
    bodyRight _ nameProjectsRight parameterProjectsRight witnessRight
  simp at inputEq
  have nameLocEq := identifierTerminalLoc_functional
    nameProjectsLeft nameProjectsRight inputEq.2.1
  have parametersLocEq : parametersLeft.map (fun value =>
      value.2.1.map fun parameter => RuleReduction.terminalLoc
        parameter.matched parameter.parsed) =
      parametersRight.map (fun value =>
        value.2.1.map fun parameter => RuleReduction.terminalLoc
          parameter.matched parameter.parsed) := by
    apply optionMap_output_functional parameterProjectsLeft
      parameterProjectsRight _ inputEq.2.2.1
    intro leftValue rightValue leftProjects rightProjects valueEq
    simp at valueEq
    have encodedEq :
        (leftValue.2.1.map (fun value => value.matched)).map
            (EbnfValue.terminalAtom (.category .identifier)) =
          (rightValue.2.1.map (fun value => value.matched)).map
            (EbnfValue.terminalAtom (.category .identifier)) := by
      simpa [NonemptyList.map, List.map_map, Function.comp_def]
        using valueEq.2.1
    have matchedEq := nonemptyListMap_injective_of_injective
      (EbnfValue.terminalAtom_injective (.category .identifier)) encodedEq
    exact identifierNonemptyLocated_functional
      leftProjects rightProjects matchedEq
  apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
  rw [nameLocEq, parametersLocEq, inputEq.2.2.2.2.1]

private theorem ruleReduction_fieldDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .fieldDecl)}
    {left right : RuleValue .fieldDecl}
    (leftReduces : RuleReduction file tokens .fieldDecl
      origin finish input left)
    (rightReduces : RuleReduction file tokens .fieldDecl
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  rename_i nameLeft _ _ _ _ projectsLeft witnessLeft
    nameRight _ _ _ _ projectsRight witnessRight
  simp at inputEq
  have initializerEq := Option.map_injective (by
    rintro ⟨leftToken, leftValue, _⟩ ⟨rightToken, rightValue, _⟩ valueEq
    simp at valueEq
    cases valueEq.1
    cases valueEq.2
    rfl) inputEq.2.2.2.1
  have nameLocEq := identifierTerminalLoc_functional
    projectsLeft projectsRight inputEq.1
  apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
  rw [nameLocEq, inputEq.2.2.1, initializerEq]

private theorem ruleReduction_parameter_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .parameter)}
    {left right : RuleValue .parameter}
    (leftReduces : RuleReduction file tokens .parameter
      origin finish input left)
    (rightReduces : RuleReduction file tokens .parameter
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  rename_i _ nameLeft _ _ projectsLeft witnessLeft
    _ nameRight _ _ projectsRight witnessRight
  simp at inputEq
  have comptimeEq := Option.map_injective
    (EbnfValue.terminalAtom_injective _) inputEq.1
  have typeEq := Option.map_injective (by
    rintro ⟨leftToken, leftValue, _⟩ ⟨rightToken, rightValue, _⟩ valueEq
    simp at valueEq
    cases valueEq.1
    cases valueEq.2
    rfl) inputEq.2.2
  have nameLocEq := identifierTerminalLoc_functional
    projectsLeft projectsRight inputEq.2.1
  apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
  cases comptimeEq
  rw [nameLocEq, typeEq]

private theorem ruleReduction_functionSignature_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .functionSignature)}
    {left right : RuleValue .functionSignature}
    (leftReduces : RuleReduction file tokens .functionSignature
      origin finish input left)
    (rightReduces : RuleReduction file tokens .functionSignature
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  rename_i _ _ _ _ nameLeft _ _ _ _ _ _ projectsLeft witnessLeft
    _ _ _ _ nameRight _ _ _ _ _ _ projectsRight witnessRight
  simp at inputEq
  have genericEq := Option.map_injective
    (EbnfValue.ruleAtom_injective .genericPrefix) inputEq.1
  have publicEq := Option.map_injective
    (EbnfValue.terminalAtom_injective _) inputEq.2.1
  have payableEq := Option.map_injective
    (EbnfValue.terminalAtom_injective _) inputEq.2.2.1
  have parametersEq := listMap_injective_of_injective
    (EbnfValue.ruleAtom_injective .parameter) inputEq.2.2.2.2.2.2.1
  have returnEq := Option.map_injective (by
    rintro ⟨leftToken, leftValue, _⟩ ⟨rightToken, rightValue, _⟩ valueEq
    simp at valueEq
    cases valueEq.1
    cases valueEq.2
    rfl) inputEq.2.2.2.2.2.2.2.2
  have nameLocEq := identifierTerminalLoc_functional
    projectsLeft projectsRight inputEq.2.2.2.2.1
  apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
  cases genericEq
  cases publicEq
  cases payableEq
  cases parametersEq
  cases returnEq
  rw [nameLocEq]

private theorem ruleReduction_dataDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .dataDecl)}
    {left right : RuleValue .dataDecl}
    (leftReduces : RuleReduction file tokens .dataDecl
      origin finish input left)
    (rightReduces : RuleReduction file tokens .dataDecl
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  rename_i _ nameLeft parametersLeft constructorsLeft _ nameProjectsLeft
    parameterProjectsLeft witnessLeft _ nameRight parametersRight
    constructorsRight _ nameProjectsRight parameterProjectsRight witnessRight
  simp at inputEq
  have nameLocEq := identifierTerminalLoc_functional
    nameProjectsLeft nameProjectsRight inputEq.2.1
  have parametersLocEq : parametersLeft.map (fun value =>
      value.2.1.map fun parameter => RuleReduction.terminalLoc
        parameter.matched parameter.parsed) =
      parametersRight.map (fun value =>
        value.2.1.map fun parameter => RuleReduction.terminalLoc
          parameter.matched parameter.parsed) := by
    apply optionMap_output_functional parameterProjectsLeft
      parameterProjectsRight _ inputEq.2.2.1
    intro leftValue rightValue leftProjects rightProjects valueEq
    simp at valueEq
    have encodedEq :
        (leftValue.2.1.map (fun value => value.matched)).map
            (EbnfValue.terminalAtom (.category .identifier)) =
          (rightValue.2.1.map (fun value => value.matched)).map
            (EbnfValue.terminalAtom (.category .identifier)) := by
      simpa [NonemptyList.map, List.map_map, Function.comp_def]
        using valueEq.2.1
    exact identifierNonemptyLocated_functional leftProjects rightProjects
      (nonemptyListMap_injective_of_injective
        (EbnfValue.terminalAtom_injective _) encodedEq)
  have constructorsEq : constructorsLeft = constructorsRight := by
    apply Option.map_injective _ inputEq.2.2.2.1
    intro leftValue rightValue valueEq
    simp at valueEq
    have restEq := listMap_injective_of_injective (by
      intro left right entryEq
      have groupEq := EbnfValue.group_injective _ entryEq
      have sequenceEq := EbnfValue.sequence_injective _ groupEq
      have firstEq := EbnfValues.cons_injective _ _ sequenceEq
      have pipeEq := EbnfValue.terminalAtom_injective _ firstEq.1
      have secondEq := EbnfValues.cons_injective _ _ firstEq.2
      have constructorEq := EbnfValue.ruleAtom_injective _ secondEq.1
      exact Prod.ext pipeEq constructorEq) valueEq.2.2
    rcases leftValue with ⟨leftToken, leftHead, leftRest, _⟩
    rcases rightValue with ⟨rightToken, rightHead, rightRest, _⟩
    simp_all
  apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
  cases constructorsEq
  rw [nameLocEq, parametersLocEq]

private theorem ruleReduction_contractDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .contractDecl)}
    {left right : RuleValue .contractDecl}
    (leftReduces : RuleReduction file tokens .contractDecl
      origin finish input left)
    (rightReduces : RuleReduction file tokens .contractDecl
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  rename_i _ nameLeft parametersLeft _ _ _ nameProjectsLeft
    parameterProjectsLeft witnessLeft _ nameRight parametersRight _ _ _
    nameProjectsRight parameterProjectsRight witnessRight
  simp at inputEq
  have nameLocEq := identifierTerminalLoc_functional
    nameProjectsLeft nameProjectsRight inputEq.2.1
  have parametersLocEq : parametersLeft.map (fun value =>
      value.2.1.map fun parameter => RuleReduction.terminalLoc
        parameter.matched parameter.parsed) =
      parametersRight.map (fun value =>
        value.2.1.map fun parameter => RuleReduction.terminalLoc
          parameter.matched parameter.parsed) := by
    apply optionMap_output_functional parameterProjectsLeft
      parameterProjectsRight _ inputEq.2.2.1
    intro leftValue rightValue leftProjects rightProjects valueEq
    simp at valueEq
    have encodedEq :
        (leftValue.2.1.map (fun value => value.matched)).map
            (EbnfValue.terminalAtom (.category .identifier)) =
          (rightValue.2.1.map (fun value => value.matched)).map
            (EbnfValue.terminalAtom (.category .identifier)) := by
      simpa [NonemptyList.map, List.map_map, Function.comp_def]
        using valueEq.2.1
    exact identifierNonemptyLocated_functional leftProjects rightProjects
      (nonemptyListMap_injective_of_injective
        (EbnfValue.terminalAtom_injective _) encodedEq)
  have membersEq := listMap_injective_of_injective
    (EbnfValue.ruleAtom_injective .contractMember) inputEq.2.2.2.2.1
  apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
  rw [nameLocEq, parametersLocEq, membersEq]

private def fixedInfixTailInput
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol) (rule : GrammarRuleId)
    (value : MatchedTerminal file tokens terminal × RuleValue rule) :
    EbnfValue file tokens (.group (.sequence [
      .atom (.terminal terminal), .atom (.nonterminal rule)])) :=
  EbnfValue.group _ (EbnfValue.sequence _
    (EbnfValues.cons _ _ (EbnfValue.terminalAtom _ value.1)
      (EbnfValues.cons _ _ (EbnfValue.ruleAtom _ value.2)
        EbnfValues.nil)))

private theorem fixedInfixTailInput_injective
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol) (rule : GrammarRuleId) :
    Function.Injective (@fixedInfixTailInput file tokens terminal rule) := by
  intro left right inputEq
  have groupEq := EbnfValue.group_injective _ inputEq
  have sequenceEq := EbnfValue.sequence_injective _ groupEq
  have terminalConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have terminalEq := EbnfValue.terminalAtom_injective _ terminalConsEq.1
  have ruleConsEq := EbnfValues.cons_injective _ _ terminalConsEq.2
  have ruleEq := EbnfValue.ruleAtom_injective _ ruleConsEq.1
  exact Prod.ext terminalEq ruleEq

private theorem ruleReduction_annotation_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .annotation)}
    {left right : RuleValue .annotation}
    (leftReduces : RuleReduction file tokens .annotation
      origin finish input left)
    (rightReduces : RuleReduction file tokens .annotation
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals have sequenceEq := EbnfValue.sequence_injective _ inputEq
  all_goals have expressionConsEq :=
    EbnfValues.cons_injective _ _ sequenceEq
  all_goals have expressionEq :=
    EbnfValue.ruleAtom_injective _ expressionConsEq.1
  all_goals have optionConsEq :=
    EbnfValues.cons_injective _ _ expressionConsEq.2
  all_goals have optionEq :=
    EbnfValue.optional_injective _ optionConsEq.1
  all_goals try exact expressionEq
  all_goals first
    | have innerValueEq := Option.some.inj optionEq
    | cases optionEq
  all_goals have innerSequenceEq :=
    EbnfValue.sequence_injective _ innerValueEq
  all_goals have colonConsEq :=
    EbnfValues.cons_injective _ _ innerSequenceEq
  all_goals have typeConsEq :=
    EbnfValues.cons_injective _ _ colonConsEq.2
  all_goals have typeEq := EbnfValue.ruleAtom_injective _ typeConsEq.1
  all_goals cases expressionEq
  all_goals cases typeEq
  all_goals exact (sourceLoc_eq_iff _ _ _ _).2 rfl

private theorem ruleReduction_conditional_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .conditional)}
    {left right : RuleValue .conditional}
    (leftReduces : RuleReduction file tokens .conditional
      origin finish input left)
    (rightReduces : RuleReduction file tokens .conditional
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals
    have choiceEq := EbnfValue.choice_injective _ inputEq
    have branchEq := congrArg Sigma.fst choiceEq
    simp at branchEq
  all_goals
    have valueEq := eq_of_heq (Sigma.ext_iff.mp choiceEq).2
    have sequenceEq := EbnfValue.sequence_injective _ valueEq
    simp only [cons_inj_iff, terminalAtom_inj_iff,
      ruleAtom_inj_iff, optional_inj_iff] at sequenceEq
  case conditionalKeyword.conditionalKeyword =>
    apply (sourceLoc_eq_iff _ _ _ _).2
    rw [sequenceEq.2.1, sequenceEq.2.2.2.1,
      sequenceEq.2.2.2.2.2.1]
  case conditionalLogical.conditionalLogical => exact sequenceEq.1
  case conditionalLogical.conditionalTernary => cases sequenceEq.2.1
  case conditionalTernary.conditionalLogical => cases sequenceEq.2.1
  case conditionalTernary.conditionalTernary =>
    have innerValueEq := Option.some.inj sequenceEq.2.1
    have innerSequenceEq := EbnfValue.sequence_injective _ innerValueEq
    simp only [cons_inj_iff, terminalAtom_inj_iff,
      ruleAtom_inj_iff] at innerSequenceEq
    apply (sourceLoc_eq_iff _ _ _ _).2
    rw [sequenceEq.1, innerSequenceEq.2.1,
      innerSequenceEq.2.2.2.1]

private theorem ruleReduction_logicalOr_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .logicalOr)}
    {left right : RuleValue .logicalOr}
    (leftReduces : RuleReduction file tokens .logicalOr
      origin finish input left)
    (rightReduces : RuleReduction file tokens .logicalOr
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have leftConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have leftEq := EbnfValue.ruleAtom_injective _ leftConsEq.1
  have starConsEq := EbnfValues.cons_injective _ _ leftConsEq.2
  have restInputEq := EbnfValue.star_injective _ starConsEq.1
  change List.map (fixedInfixTailInput (.symbol .logicalOr) .logicalAnd) _ =
    List.map (fixedInfixTailInput (.symbol .logicalOr) .logicalAnd) _
      at restInputEq
  have restEq := listMap_injective_of_injective
    (fixedInfixTailInput_injective (.symbol .logicalOr) .logicalAnd)
    restInputEq
  rw [leftEq, restEq]

private theorem ruleReduction_logicalAnd_functional
    {file : WorkspaceFile} {tokens : List Token} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .logicalAnd)}
    {left right : RuleValue .logicalAnd}
    (leftReduces : RuleReduction file tokens .logicalAnd origin finish input left)
    (rightReduces : RuleReduction file tokens .logicalAnd origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have leftConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have leftEq := EbnfValue.ruleAtom_injective _ leftConsEq.1
  have starConsEq := EbnfValues.cons_injective _ _ leftConsEq.2
  have restInputEq := EbnfValue.star_injective _ starConsEq.1
  change List.map (fixedInfixTailInput (.symbol .logicalAnd) .equality) _ =
    List.map (fixedInfixTailInput (.symbol .logicalAnd) .equality) _ at restInputEq
  have restEq := listMap_injective_of_injective
    (fixedInfixTailInput_injective (.symbol .logicalAnd) .equality) restInputEq
  rw [leftEq, restEq]

private theorem ruleReduction_bitOr_functional
    {file : WorkspaceFile} {tokens : List Token} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .bitOr)}
    {left right : RuleValue .bitOr}
    (leftReduces : RuleReduction file tokens .bitOr origin finish input left)
    (rightReduces : RuleReduction file tokens .bitOr origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have leftConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have leftEq := EbnfValue.ruleAtom_injective _ leftConsEq.1
  have starConsEq := EbnfValues.cons_injective _ _ leftConsEq.2
  have restInputEq := EbnfValue.star_injective _ starConsEq.1
  change List.map (fixedInfixTailInput (.symbol .pipe) .bitXor) _ =
    List.map (fixedInfixTailInput (.symbol .pipe) .bitXor) _ at restInputEq
  have restEq := listMap_injective_of_injective
    (fixedInfixTailInput_injective (.symbol .pipe) .bitXor) restInputEq
  rw [leftEq, restEq]

private theorem ruleReduction_bitXor_functional
    {file : WorkspaceFile} {tokens : List Token} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .bitXor)}
    {left right : RuleValue .bitXor}
    (leftReduces : RuleReduction file tokens .bitXor origin finish input left)
    (rightReduces : RuleReduction file tokens .bitXor origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have leftConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have leftEq := EbnfValue.ruleAtom_injective _ leftConsEq.1
  have starConsEq := EbnfValues.cons_injective _ _ leftConsEq.2
  have restInputEq := EbnfValue.star_injective _ starConsEq.1
  change List.map (fixedInfixTailInput (.symbol .caret) .bitAnd) _ =
    List.map (fixedInfixTailInput (.symbol .caret) .bitAnd) _ at restInputEq
  have restEq := listMap_injective_of_injective
    (fixedInfixTailInput_injective (.symbol .caret) .bitAnd) restInputEq
  rw [leftEq, restEq]

private theorem ruleReduction_bitAnd_functional
    {file : WorkspaceFile} {tokens : List Token} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .bitAnd)}
    {left right : RuleValue .bitAnd}
    (leftReduces : RuleReduction file tokens .bitAnd origin finish input left)
    (rightReduces : RuleReduction file tokens .bitAnd origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have leftConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have leftEq := EbnfValue.ruleAtom_injective _ leftConsEq.1
  have starConsEq := EbnfValues.cons_injective _ _ leftConsEq.2
  have restInputEq := EbnfValue.star_injective _ starConsEq.1
  change List.map (fixedInfixTailInput (.symbol .amp) .additive) _ =
    List.map (fixedInfixTailInput (.symbol .amp) .additive) _ at restInputEq
  have restEq := listMap_injective_of_injective
    (fixedInfixTailInput_injective (.symbol .amp) .additive) restInputEq
  rw [leftEq, restEq]

private theorem ruleReduction_prefix_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .prefix)}
    {left right : RuleValue .prefix}
    (leftReduces : RuleReduction file tokens .prefix
      origin finish input left)
    (rightReduces : RuleReduction file tokens .prefix
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals
    have choiceEq := EbnfValue.choice_injective _ inputEq
    have branchEq := congrArg Sigma.fst choiceEq
    simp at branchEq
  all_goals
    have valueEq := eq_of_heq (Sigma.ext_iff.mp choiceEq).2
  case prefixLogicalNot.prefixLogicalNot =>
    have sequenceEq := EbnfValue.sequence_injective _ valueEq
    simp only [cons_inj_iff, terminalAtom_inj_iff,
      ruleAtom_inj_iff] at sequenceEq
    apply (sourceLoc_eq_iff _ _ _ _).2
    rw [sequenceEq.1, sequenceEq.2.1]
  case prefixPostfix.prefixPostfix =>
    change EbnfValue.ruleAtom .postfix left =
      EbnfValue.ruleAtom .postfix right at valueEq
    exact EbnfValue.ruleAtom_injective .postfix valueEq

private theorem ruleReduction_postfix_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .postfix)}
    {left right : RuleValue .postfix}
    (leftReduces : RuleReduction file tokens .postfix
      origin finish input left)
    (rightReduces : RuleReduction file tokens .postfix
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have atomConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have atomEq := EbnfValue.ruleAtom_injective _ atomConsEq.1
  have starConsEq := EbnfValues.cons_injective _ _ atomConsEq.2
  have partsInputEq := EbnfValue.star_injective _ starConsEq.1
  have partsEq := listMap_injective_of_injective
    (EbnfValue.ruleAtom_injective .postfixPart) partsInputEq
  rw [atomEq, partsEq]

private theorem ruleReduction_postfixPart_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .postfixPart)}
    {left right : RuleValue .postfixPart}
    (leftReduces : RuleReduction file tokens .postfixPart
      origin finish input left)
    (rightReduces : RuleReduction file tokens .postfixPart
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals
    have choiceEq := EbnfValue.choice_injective _ inputEq
    have branchEq := congrArg Sigma.fst choiceEq
    simp at branchEq
  all_goals
    have valueEq := eq_of_heq (Sigma.ext_iff.mp choiceEq).2
    have sequenceEq := EbnfValue.sequence_injective _ valueEq
    simp only [cons_inj_iff, terminalAtom_inj_iff,
      ruleAtom_inj_iff, list0_inj_iff] at sequenceEq
  case postfixPartCall.postfixPartCall =>
    have argumentsEq := listMap_injective_of_injective
      (EbnfValue.ruleAtom_injective .expression) sequenceEq.2.1
    rw [sequenceEq.1, argumentsEq, sequenceEq.2.2.1]
  case postfixPartSelect.postfixPartSelect =>
    rename_i _ _ _ parsedLeft projectsLeft _ _ _ parsedRight projectsRight
    cases sequenceEq.2.1
    have parsedEq := (IdentifierProjects.functional
      projectsLeft projectsRight).2
    rw [sequenceEq.1, parsedEq]
  case postfixPartIndex.postfixPartIndex =>
    rw [sequenceEq.1, sequenceEq.2.1, sequenceEq.2.2.1]

private def typeArgumentsInput
    {file : WorkspaceFile} {tokens : List Token}
    (value : MatchedTerminal file tokens (.symbol .leftParen) ×
      (NonemptyList TypeExpr ×
        (MatchedTerminal file tokens (.symbol .rightParen) × Unit))) :
    EbnfValue file tokens (.sequence [
      .atom (.terminal (.symbol .leftParen)),
      .list1 (.atom (.nonterminal .type)),
      .atom (.terminal (.symbol .rightParen))]) :=
  EbnfValue.sequence _
    (EbnfValues.cons _ _ (EbnfValue.terminalAtom _ value.1)
      (EbnfValues.cons _ _ (EbnfValue.list1 _
        (value.2.1.map (EbnfValue.ruleAtom .type)))
        (EbnfValues.cons _ _ (EbnfValue.terminalAtom _ value.2.2.1)
          EbnfValues.nil)))

private theorem typeArgumentsInput_injective
    {file : WorkspaceFile} {tokens : List Token} :
    Function.Injective (@typeArgumentsInput file tokens) := by
  intro left right inputEq
  have sequenceEq := EbnfValue.sequence_injective _ inputEq
  have openConsEq := EbnfValues.cons_injective _ _ sequenceEq
  have openEq := EbnfValue.terminalAtom_injective _ openConsEq.1
  have argumentsConsEq := EbnfValues.cons_injective _ _ openConsEq.2
  have encodedArgumentsEq :=
    EbnfValue.list1_injective _ argumentsConsEq.1
  have argumentsEq := nonemptyListMap_injective_of_injective
    (EbnfValue.ruleAtom_injective .type) encodedArgumentsEq
  have closeConsEq := EbnfValues.cons_injective _ _ argumentsConsEq.2
  have closeEq := EbnfValue.terminalAtom_injective _ closeConsEq.1
  exact Prod.ext openEq (Prod.ext argumentsEq
    (Prod.ext closeEq (Subsingleton.elim _ _)))

private theorem ruleReduction_module_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .module)}
    {left right : RuleValue .module}
    (leftReduces : RuleReduction file tokens .module origin finish input left)
    (rightReduces : RuleReduction file tokens .module origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  simp at inputEq
  have itemsEq := listMap_injective_of_injective
    (EbnfValue.ruleAtom_injective .topItem) inputEq.1
  rw [itemsEq]

private theorem ruleReduction_body_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .body)}
    {left right : RuleValue .body}
    (leftReduces : RuleReduction file tokens .body origin finish input left)
    (rightReduces : RuleReduction file tokens .body origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  simp at inputEq
  have statementsEq := listMap_injective_of_injective
    (EbnfValue.ruleAtom_injective .statement) inputEq.2.1
  apply (sourceLoc_eq_iff _ _ _ _).2
  rw [inputEq.1, statementsEq, inputEq.2.2]

private theorem ruleReduction_classDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .classDecl)}
    {left right : RuleValue .classDecl}
    (leftReduces : RuleReduction file tokens .classDecl
      origin finish input left)
    (rightReduces : RuleReduction file tokens .classDecl
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  rename_i genericLeft _ mainLeft _ nameLeft parametersLeft _ methodsLeft _
    projectsLeft witnessLeft genericRight _ mainRight _ nameRight
    parametersRight _ methodsRight _ projectsRight witnessRight
  simp at inputEq
  have genericEq := Option.map_injective
    (EbnfValue.ruleAtom_injective .genericPrefix) inputEq.1
  have parametersInputEq := inputEq.2.2.2.2.2.1
  change parametersLeft.map typeArgumentsInput =
    parametersRight.map typeArgumentsInput at parametersInputEq
  have parametersEq := Option.map_injective
    typeArgumentsInput_injective parametersInputEq
  have methodsEq := listMap_injective_of_injective
    (EbnfValue.ruleAtom_injective .classMethod)
    inputEq.2.2.2.2.2.2.2.1
  have nameLocEq := identifierTerminalLoc_functional
    projectsLeft projectsRight inputEq.2.2.2.2.1
  apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
  cases genericEq
  cases parametersEq
  cases methodsEq
  rw [inputEq.2.2.1, nameLocEq]

private theorem ruleReduction_instanceDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .instanceDecl)}
    {left right : RuleValue .instanceDecl}
    (leftReduces : RuleReduction file tokens .instanceDecl
      origin finish input left)
    (rightReduces : RuleReduction file tokens .instanceDecl
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  rename_i genericLeft defaultLeft _ mainLeft _ classLeft parametersLeft _
    methodsLeft _ _ witnessLeft genericRight defaultRight _ mainRight _
    classRight parametersRight _ methodsRight _ _ witnessRight
  simp at inputEq
  have genericEq := Option.map_injective
    (EbnfValue.ruleAtom_injective .genericPrefix) inputEq.1
  have defaultEq := Option.map_injective
    (EbnfValue.terminalAtom_injective _) inputEq.2.1
  have parametersInputEq := inputEq.2.2.2.2.2.2.1
  change parametersLeft.map typeArgumentsInput =
    parametersRight.map typeArgumentsInput at parametersInputEq
  have parametersEq := Option.map_injective
    typeArgumentsInput_injective parametersInputEq
  have methodsEq := listMap_injective_of_injective
    (EbnfValue.ruleAtom_injective .instanceMethod)
    inputEq.2.2.2.2.2.2.2.2.1
  apply (sourceLoc_eq_iff witnessLeft witnessRight _ _).2
  cases genericEq
  cases defaultEq
  cases parametersEq
  cases methodsEq
  rw [inputEq.2.2.2.1, inputEq.2.2.2.2.2.1]

private theorem ruleReduction_fallbackDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .fallbackDecl)}
    {left right : RuleValue .fallbackDecl}
    (leftReduces : RuleReduction file tokens .fallbackDecl
      origin finish input left)
    (rightReduces : RuleReduction file tokens .fallbackDecl
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  simp at inputEq
  have genericEq := Option.map_injective
    (EbnfValue.ruleAtom_injective .genericPrefix) inputEq.1
  have publicEq := Option.map_injective
    (EbnfValue.terminalAtom_injective _) inputEq.2.1
  have payableEq := Option.map_injective
    (EbnfValue.terminalAtom_injective _) inputEq.2.2.1
  have parametersEq := listMap_injective_of_injective
    (EbnfValue.ruleAtom_injective .parameter) inputEq.2.2.2.2.2.1
  have returnEq := Option.map_injective (by
    rintro ⟨leftToken, leftValue, _⟩ ⟨rightToken, rightValue, _⟩ valueEq
    simp at valueEq
    cases valueEq.1
    cases valueEq.2
    rfl) inputEq.2.2.2.2.2.2.2.1
  apply (sourceLoc_eq_iff _ _ _ _).2
  cases genericEq
  cases publicEq
  cases payableEq
  cases inputEq.2.2.2.1
  cases parametersEq
  cases returnEq
  cases inputEq.2.2.2.2.2.2.2.2
  rfl

private theorem ruleReduction_contractConstructorDecl_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .contractConstructorDecl)}
    {left right : RuleValue .contractConstructorDecl}
    (leftReduces : RuleReduction file tokens .contractConstructorDecl
      origin finish input left)
    (rightReduces : RuleReduction file tokens .contractConstructorDecl
      origin finish input right) : left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces
  cases rightReduces
  simp at inputEq
  have publicEq := Option.map_injective
    (EbnfValue.terminalAtom_injective _) inputEq.1
  have payableEq := Option.map_injective
    (EbnfValue.terminalAtom_injective _) inputEq.2.1
  have parametersEq := listMap_injective_of_injective
    (EbnfValue.ruleAtom_injective .parameter) inputEq.2.2.2.2.1
  apply (sourceLoc_eq_iff _ _ _ _).2
  cases publicEq
  cases payableEq
  cases inputEq.2.2.1
  cases parametersEq
  cases inputEq.2.2.2.2.2.2
  rfl

private theorem ruleReduction_type_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .type)}
    {left right : RuleValue .type}
    (leftReduces : RuleReduction file tokens .type origin finish input left)
    (rightReduces : RuleReduction file tokens .type origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals
    have choiceEq := EbnfValue.choice_injective _ inputEq
    have branchEq := congrArg Sigma.fst choiceEq
    simp at branchEq
  all_goals
    have valueEq := eq_of_heq (Sigma.ext_iff.mp choiceEq).2
    have sequenceEq := EbnfValue.sequence_injective _ valueEq
    simp only [cons_inj_iff, terminalAtom_inj_iff,
      ruleAtom_inj_iff, optional_inj_iff] at sequenceEq
  case typeComptime.typeComptime =>
    apply (sourceLoc_eq_iff _ _ _ _).2
    cases sequenceEq.1
    cases sequenceEq.2.1
    rfl
  case typeAtomOnly.typeAtomOnly => exact sequenceEq.1
  case typeAtomOnly.typeFunction => cases sequenceEq.2.1
  case typeFunction.typeAtomOnly => cases sequenceEq.2.1
  case typeFunction.typeFunction =>
    have innerValueEq := Option.some.inj sequenceEq.2.1
    have innerSequenceEq := EbnfValue.sequence_injective _ innerValueEq
    simp only [cons_inj_iff, terminalAtom_inj_iff,
      ruleAtom_inj_iff] at innerSequenceEq
    apply (sourceLoc_eq_iff _ _ _ _).2
    rw [sequenceEq.1, innerSequenceEq.2.1]

private theorem ruleReduction_typeAtom_functional
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .typeAtom)}
    {left right : RuleValue .typeAtom}
    (leftReduces : RuleReduction file tokens .typeAtom origin finish input left)
    (rightReduces : RuleReduction file tokens .typeAtom origin finish input right) :
    left = right := by
  generalize inputEq : input = rightInput at rightReduces
  cases leftReduces <;> cases rightReduces
  all_goals
    have choiceEq := EbnfValue.choice_injective _ inputEq
    have branchEq := congrArg Sigma.fst choiceEq
    simp at branchEq
  all_goals
    have valueEq := eq_of_heq (Sigma.ext_iff.mp choiceEq).2
    have sequenceEq := EbnfValue.sequence_injective _ valueEq
    simp only [cons_inj_iff, terminalAtom_inj_iff, ruleAtom_inj_iff,
      optional_inj_iff, star_inj_iff] at sequenceEq
  case typeAtomProxy.typeAtomProxy =>
    apply (sourceLoc_eq_iff _ _ _ _).2
    rw [sequenceEq.1, sequenceEq.2.1]
  case typeAtomNamedWithoutArguments.typeAtomNamedWithoutArguments =>
    apply (sourceLoc_eq_iff _ _ _ _).2
    rw [sequenceEq.1]
  case typeAtomNamedWithoutArguments.typeAtomNamedWithArguments =>
    cases sequenceEq.2.1
  case typeAtomNamedWithArguments.typeAtomNamedWithoutArguments =>
    cases sequenceEq.2.1
  case typeAtomNamedWithArguments.typeAtomNamedWithArguments =>
    have innerValueEq := Option.some.inj sequenceEq.2.1
    have innerSequenceEq := EbnfValue.sequence_injective _ innerValueEq
    simp only [cons_inj_iff, terminalAtom_inj_iff,
      list1_inj_iff] at innerSequenceEq
    have argumentsEq := nonemptyListMap_injective_of_injective
      (EbnfValue.ruleAtom_injective .type) innerSequenceEq.2.1
    apply (sourceLoc_eq_iff _ _ _ _).2
    rw [sequenceEq.1, innerSequenceEq.1, argumentsEq,
      innerSequenceEq.2.2.1]
  case typeAtomEmptyTuple.typeAtomEmptyTuple =>
    exact (sourceLoc_eq_iff _ _ _ _).2 rfl
  case typeAtomGroup.typeAtomGroup =>
    apply (sourceLoc_eq_iff _ _ _ _).2
    rw [sequenceEq.2.1]
  case typeAtomTuple.typeAtomTuple =>
    have restInputEq := sequenceEq.2.2.2.2.1
    change List.map (fixedInfixTailInput (.symbol .comma) .type) _ =
      List.map (fixedInfixTailInput (.symbol .comma) .type) _ at restInputEq
    have restEq := listMap_injective_of_injective
      (fixedInfixTailInput_injective (.symbol .comma) .type) restInputEq
    apply (sourceLoc_eq_iff _ _ _ _).2
    rw [sequenceEq.2.1, sequenceEq.2.2.2.1, restEq]

/-- A module-rule reduction can only produce the full-file, source-owned
module payload from its exact item list. -/
theorem ruleReduction_source_backed
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .module)}
    {output : RuleValue .module}
    (reduces : RuleReduction file tokens .module
      origin finish input output) :
    ∃ items : List TopItem,
      origin = Boundary.start tokens ∧
      finish = Boundary.afterLogicalEOF tokens ∧
      output = RuleReduction.moduleLoc file {
        source := file.id
        items := items
      } := by
  cases reduces with
  | module origin finish items eof originEq finishEq eofValue =>
      exact ⟨items, originEq, finishEq, rfl⟩

/-- Exact semantic reduction for one generated production action. -/
inductive ActionReduces
    (file : WorkspaceFile) (tokens : List Token) :
    (action : ActionId) →
      (origin finish : Boundary tokens) →
      GrammarSymbolValues file tokens action.production.rhs →
      NonterminalValue file tokens action.production.lhs → Prop where
  | root
      (rule : GrammarRuleId)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.root rule).rhs)
      (output : RuleValue rule)
      (reduces : RuleReduction file tokens rule origin finish
        (RootAction.unpack rule input) output) :
      ActionReduces file tokens (.actionFor (.root rule))
        origin finish input output
  | atom
      (site : AtomSite)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.atom site).rhs) :
      ActionReduces file tokens (.actionFor (.atom site))
        origin finish input (AtomSite.pack site input)
  | seq
      (site : SequenceSite)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.seq site).rhs) :
      ActionReduces file tokens (.actionFor (.seq site))
        origin finish input (SequenceSite.pack site input)
  | group
      (site : GroupSite)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.group site).rhs) :
      ActionReduces file tokens (.actionFor (.group site))
        origin finish input (GroupSite.pack site input)
  | choice
      (site : ChoiceSite)
      (branch : Fin site.branchCount)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.choice site branch).rhs) :
      ActionReduces file tokens (.actionFor (.choice site branch))
        origin finish input (ChoiceSite.pack site branch input)
  | opt
      (site : OptionalSite)
      (branch : OptionalBranch)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.opt site branch).rhs) :
      ActionReduces file tokens (.actionFor (.opt site branch))
        origin finish input (OptionalSite.pack site branch input)
  | star
      (site : StarSite)
      (branch : NilConsBranch)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.star site branch).rhs) :
      ActionReduces file tokens (.actionFor (.star site branch))
        origin finish input (StarSite.pack site branch input)
  | plus
      (site : PlusSite)
      (branch : OneConsBranch)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.plus site branch).rhs) :
      ActionReduces file tokens (.actionFor (.plus site branch))
        origin finish input (PlusSite.pack site branch input)
  | list0
      (site : List0Site)
      (branch : NilConsBranch)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.list0 site branch).rhs) :
      ActionReduces file tokens (.actionFor (.list0 site branch))
        origin finish input (List0Site.pack site branch input)
  | list1
      (site : List1Site)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.list1 site).rhs) :
      ActionReduces file tokens (.actionFor (.list1 site))
        origin finish input (List1Site.pack site input)
  | tail
      (site : ListSite)
      (branch : NilConsBranch)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.tail site branch).rhs) :
      ActionReduces file tokens (.actionFor (.tail site branch))
        origin finish input (ListSite.pack site branch input)

/-- The action reduction relation has exactly the eleven production shapes. -/
theorem actionReduces_eleven_shapes_exact
    {file : WorkspaceFile} {tokens : List Token}
    {production : ProductionId}
    {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens production.rhs}
    {output : NonterminalValue file tokens production.lhs} :
    ActionReduces file tokens (.actionFor production)
        origin finish input output ↔
      match production with
      | .root rule =>
          RuleReduction file tokens rule origin finish
            (RootAction.unpack rule input) output
      | .atom site => output = AtomSite.pack site input
      | .seq site => output = SequenceSite.pack site input
      | .group site => output = GroupSite.pack site input
      | .choice site branch =>
          output = ChoiceSite.pack site branch input
      | .opt site branch =>
          output = OptionalSite.pack site branch input
      | .star site branch =>
          output = StarSite.pack site branch input
      | .plus site branch =>
          output = PlusSite.pack site branch input
      | .list0 site branch =>
          output = List0Site.pack site branch input
      | .list1 site => output = List1Site.pack site input
      | .tail site branch =>
          output = ListSite.pack site branch input := by
  constructor
  · intro reduces
    cases reduces with
    | root rule origin finish input output reduces => exact reduces
    | atom => rfl
    | seq => rfl
    | group => rfl
    | choice => rfl
    | opt => rfl
    | star => rfl
    | plus => rfl
    | list0 => rfl
    | list1 => rfl
    | tail => rfl
  · cases production with
    | root rule =>
        intro reduces
        exact .root rule origin finish input output reduces
    | atom site =>
        intro outputEq
        subst output
        exact .atom site origin finish input
    | seq site =>
        intro outputEq
        subst output
        exact .seq site origin finish input
    | group site =>
        intro outputEq
        subst output
        exact .group site origin finish input
    | choice site branch =>
        intro outputEq
        subst output
        exact .choice site branch origin finish input
    | opt site branch =>
        intro outputEq
        subst output
        exact .opt site branch origin finish input
    | star site branch =>
        intro outputEq
        subst output
        exact .star site branch origin finish input
    | plus site branch =>
        intro outputEq
        subst output
        exact .plus site branch origin finish input
    | list0 site branch =>
        intro outputEq
        subst output
        exact .list0 site branch origin finish input
    | list1 site =>
        intro outputEq
        subst output
        exact .list1 site origin finish input
    | tail site branch =>
        intro outputEq
        subst output
        exact .tail site branch origin finish input

mutual

  /-- Values coherent with one reached contextual item's consumed prefix. -/
  inductive CoherentPrefix
      (file : WorkspaceFile) (tokens : List Token)
      (memo : GuardMemo tokens)
      (correct : PhaseBCorrect file tokens memo)
      (final : AllGuardsFinal memo) :
      (item : ContextualItemKey tokens) →
        PrefixValues file tokens item → Prop where
    | zero
        (item : ContextualItemKey tokens)
        (reached : ContextualReach file tokens memo correct final item)
        (zero : item.raw.dot.val = 0) :
        CoherentPrefix file tokens memo correct final item
          (PrefixValues.zeroValue item zero)
    | scan
        (before after : ContextualItemKey tokens)
        (cursor : TerminalCursor tokens)
        (priorValues : PrefixValues file tokens before)
        (witness : ScannedEdgeWitness
          file tokens before.raw after.raw cursor)
        (edge : ContextualEdgeReach file tokens memo correct final
          (.scanned before after cursor))
        (prior : CoherentPrefix file tokens memo correct final
          before priorValues) :
        CoherentPrefix file tokens memo correct final after
          (PrefixValues.scanValue before after witness.terminal
            witness.next witness.matched witness.advance priorValues)
    | complete
        (waiting finished after : ContextualItemKey tokens)
        (shared : Boundary tokens)
        (priorValues : PrefixValues file tokens waiting)
        (childValue : NonterminalValue file tokens
          finished.raw.production.lhs)
        (witness : CompletedEdgeWitness
          tokens waiting.raw finished.raw after.raw shared)
        (edge : ContextualEdgeReach file tokens memo correct final
          (.completed waiting finished after shared))
        (prior : CoherentPrefix file tokens memo correct final
          waiting priorValues)
        (child : CoherentReduction file tokens memo correct final
          finished childValue) :
        CoherentPrefix file tokens memo correct final after
          (PrefixValues.completeValue waiting finished after
            witness.next witness.advance priorValues childValue)

  /-- Completed nonterminal values coherent with one reached contextual item. -/
  inductive CoherentReduction
      (file : WorkspaceFile) (tokens : List Token)
      (memo : GuardMemo tokens)
      (correct : PhaseBCorrect file tokens memo)
      (final : AllGuardsFinal memo) :
      (item : ContextualItemKey tokens) →
        NonterminalValue file tokens item.raw.production.lhs → Prop where
    | reduce
        (item : ContextualItemKey tokens)
        (priorValues : PrefixValues file tokens item)
        (output : NonterminalValue file tokens item.raw.production.lhs)
        (reached : ContextualReach file tokens memo correct final item)
        (complete : CompleteItem item.raw)
        (coherentPrefix : CoherentPrefix file tokens memo correct final
          item priorValues)
        (action : ActionReduces file tokens
          (.actionFor item.raw.production)
          item.raw.origin item.raw.current
          (PrefixValues.fullValue item complete priorValues) output) :
        CoherentReduction file tokens memo correct final item output

end

/-- A coherent prefix is attached to the exact contextual item reached by its
derivation; a raw projection from another context cannot be spliced in. -/
theorem coherentPrefix_no_context_splice
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    (coherent : CoherentPrefix
      file tokens memo correct final item values) :
    ContextualReach file tokens memo correct final item ∧
      (item.raw.dot.val = 0 ∨
        (∃ before : ContextualItemKey tokens,
          ∃ cursor : TerminalCursor tokens,
            ContextualEdgeReach file tokens memo correct final
              (.scanned before item cursor) ∧
            before.context = item.context) ∨
        ∃ waiting finished : ContextualItemKey tokens,
          ∃ shared : Boundary tokens,
            ContextualEdgeReach file tokens memo correct final
              (.completed waiting finished item shared) ∧
            item.context = waiting.context ∧
            finished.context =
              descendContext waiting finished.raw.production) := by
  cases coherent with
  | zero item reached zero => exact ⟨reached, Or.inl zero⟩
  | scan before after cursor priorValues witness edge prior =>
      exact ⟨edge.2.2, Or.inr (Or.inl
        ⟨before, cursor, edge, edge.1.2⟩)⟩
  | complete waiting finished after shared priorValues childValue witness
      edge prior child =>
      exact ⟨edge.2.2.2, Or.inr (Or.inr
        ⟨waiting, finished, shared, edge, edge.1.2.2, edge.1.2.1⟩)⟩

/-- A coherent completed canonical root item for one source rule. -/
def CanonicalCompleteRootReduction
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (rule : GrammarRuleId)
    (origin finish : Boundary tokens)
    (context : GuardContext tokens)
    (value : RuleValue rule) : Prop :=
  ContextualReach file tokens memo correct final
      (CanonicalCompleteRootItem tokens rule origin finish context) ∧
    CompleteItem
      (CanonicalCompleteRootItem tokens rule origin finish context).raw ∧
    CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens rule origin finish context) value

/-- A canonical coherent module-root reduction over the complete token stream. -/
def SourceBackedRoot
    (file : WorkspaceFile) (tokens : List Token)
    (module : ParsedModuleV1) : Prop :=
  ∃ memo : GuardMemo tokens,
    ∃ correct : PhaseBCorrect file tokens memo,
      ∃ allFinal : AllGuardsFinal memo,
        CanonicalCompleteRootReduction
          file tokens memo correct allFinal
          GrammarRuleId.module
          (Boundary.start tokens)
          (Boundary.afterLogicalEOF tokens)
          GuardContext.plain
          module

/-- Expose the exact canonical complete module root carried by success. -/
theorem sourceBackedRoot_exact
    {file : WorkspaceFile} {tokens : List Token}
    {module : ParsedModuleV1} :
    SourceBackedRoot file tokens module ↔
      ∃ memo : GuardMemo tokens,
        ∃ correct : PhaseBCorrect file tokens memo,
          ∃ final : AllGuardsFinal memo,
            CanonicalCompleteRootReduction
              file tokens memo correct final .module
              (Boundary.start tokens)
              (Boundary.afterLogicalEOF tokens)
              .plain module :=
  Iff.rfl

/-- Public successful parsing admits only a source-backed complete module root. -/
inductive Parses : WorkspaceFile → List Token → ParsedModuleV1 → Prop where
  | sourceBackedRoot
      (file : WorkspaceFile)
      (tokens : List Token)
      (module : ParsedModuleV1)
      (owned : TokensOwnedBy file tokens)
      (sourceBacked : SourceBackedRoot file tokens module) :
      Parses file tokens module

/-- The greatest cursor reached by the fully saturated contextual relation. -/
def GreatestReachableCursor
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) : Prop :=
  (∃ item : ContextualItemKey tokens,
    ContextualReach file tokens memo correct final item ∧
      item.raw.current = cursor) ∧
  ∀ item : ContextualItemKey tokens,
    ContextualReach file tokens memo correct final item →
      item.raw.current.val ≤ cursor.val

namespace GreatestReachableCursor

/-- A saturated contextual relation has at most one greatest reached cursor. -/
theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {leftCursor rightCursor : Boundary tokens}
    (leftGreatest : GreatestReachableCursor
      file tokens memo correct final leftCursor)
    (rightGreatest : GreatestReachableCursor
      file tokens memo correct final rightCursor) :
    leftCursor = rightCursor := by
  rcases leftGreatest.1 with ⟨leftItem, leftReach, leftCurrent⟩
  rcases rightGreatest.1 with ⟨rightItem, rightReach, rightCurrent⟩
  apply Fin.ext
  apply Nat.le_antisymm
  · simpa [leftCurrent] using rightGreatest.2 leftItem leftReach
  · simpa [rightCurrent] using leftGreatest.2 rightItem rightReach

end GreatestReachableCursor

/-- One reached contextual item at the greatest cursor. -/
def FrontierReach
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) (item : ContextualItemKey tokens) : Prop :=
  GreatestReachableCursor file tokens memo correct final cursor ∧
    ContextualReach file tokens memo correct final item ∧
    item.raw.current = cursor

/-- One enabled terminal expected by a contextual frontier item. -/
def ExpectedMember
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) (expected : Expected) : Prop :=
  ∃ item : ContextualItemKey tokens,
    ∃ terminal : TerminalSymbol,
      FrontierReach file tokens memo correct final cursor item ∧
      NextSymbol item.raw (.terminal terminal) ∧
      EnabledProductionInstance file tokens memo correct final {
        production := item.raw.production
        origin := item.raw.origin
        context := item.context
      } ∧
      expected = terminal.expected

/-- The unique intended sorted and deduplicated expected frontier list. -/
def CanonicalExpected
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens)
    (values : NonemptyList Expected) : Prop :=
  (∀ expected, expected ∈ (values.head :: values.tail) ↔
      ExpectedMember file tokens memo correct final cursor expected) ∧
    (values.head :: values.tail).Nodup ∧
    (values.head :: values.tail).Pairwise
      (fun left right => Expected.compare left right = .lt)

/-- A sorted, deduplicated canonical expected list is unique. -/
theorem canonicalExpected_sorted_nodup_unique
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens}
    {leftValues rightValues : NonemptyList Expected}
    (leftCanonical : CanonicalExpected
      file tokens memo correct final cursor leftValues)
    (rightCanonical : CanonicalExpected
      file tokens memo correct final cursor rightValues) :
    leftValues = rightValues := by
  rcases leftCanonical with
    ⟨leftMembership, leftNodup, leftSorted⟩
  rcases rightCanonical with
    ⟨rightMembership, rightNodup, rightSorted⟩
  have compareAsymm (first second : Expected)
      (firstSecond : Expected.compare first second = .lt)
      (secondFirst : Expected.compare second first = .lt) : False := by
    unfold Expected.compare at firstSecond secondFirst
    cases primary : compare first.ctorIdx second.ctorIdx with
    | lt =>
        have reverse : compare second.ctorIdx first.ctorIdx = .gt :=
          Std.OrientedCmp.gt_of_lt primary
        simp [reverse] at secondFirst
    | eq =>
        have reverse : compare second.ctorIdx first.ctorIdx = .eq :=
          Std.OrientedCmp.eq_symm primary
        simp [primary] at firstSecond
        simp [reverse] at secondFirst
        have payloadReverse := Std.OrientedCmp.gt_of_lt firstSecond
        simp [payloadReverse] at secondFirst
    | gt =>
        simp [primary] at firstSecond
  have membershipIff (expected : Expected) :
      expected ∈ (leftValues.head :: leftValues.tail) ↔
        expected ∈ (rightValues.head :: rightValues.tail) :=
    (leftMembership expected).trans (rightMembership expected).symm
  letI : BEq Expected := ⟨fun first second => decide (first = second)⟩
  letI : ReflBEq Expected := ⟨by intro value; simp⟩
  letI : LawfulBEq Expected := ⟨by
      intro first second equality
      simpa using of_decide_eq_true equality⟩
  have permutation :
      (leftValues.head :: leftValues.tail).Perm
        (rightValues.head :: rightValues.tail) := by
    apply List.perm_iff_count.mpr
    intro expected
    rw [leftNodup.count, rightNodup.count]
    by_cases leftMember :
        expected ∈ (leftValues.head :: leftValues.tail)
    · have rightMember :
          expected ∈ (rightValues.head :: rightValues.tail) :=
        (membershipIff expected).mp leftMember
      simp [leftMember, rightMember]
    · have rightNotMember :
          expected ∉ (rightValues.head :: rightValues.tail) := by
        exact fun rightMember =>
          leftMember ((membershipIff expected).mpr rightMember)
      simp [leftMember, rightNotMember]
  have listEq :
      leftValues.head :: leftValues.tail =
        rightValues.head :: rightValues.tail :=
    permutation.eq_of_pairwise
      (fun first second _ _ firstSecond secondFirst =>
        False.elim (compareAsymm first second firstSecond secondFirst))
      leftSorted rightSorted
  cases leftValues
  cases rightValues
  simp only at listEq
  cases listEq
  rfl

/-- The retained token or logical EOF observed at one parser boundary. -/
inductive FoundAt
    (file : WorkspaceFile) (tokens : List Token) :
    Boundary tokens → SourceSpan → Found → Prop where
  | retained
      (cursor : TerminalCursor tokens)
      (boundary : Boundary tokens)
      (token : Token)
      (atBoundary : cursor.beforeBoundary = boundary)
      (terminalAt : TerminalAt file tokens cursor (.retained token) token.span) :
      FoundAt file tokens boundary token.span (.token token.payload)
  | endOfFile
      (cursor : TerminalCursor tokens)
      (boundary : Boundary tokens)
      (atBoundary : cursor.beforeBoundary = boundary)
      (atEnd : cursor.val = tokens.length) :
      FoundAt file tokens boundary {
        source := file.id
        startByte := file.content.utf8ByteSize
        endByte := file.content.utf8ByteSize
      } .endOfFile

namespace FoundAt

/-- One parser boundary determines at most one found span and token class. -/
theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {cursor : Boundary tokens}
    {leftSpan rightSpan : SourceSpan}
    {leftFound rightFound : Found}
    (leftAt : FoundAt file tokens cursor leftSpan leftFound)
    (rightAt : FoundAt file tokens cursor rightSpan rightFound) :
    leftSpan = rightSpan ∧ leftFound = rightFound := by
  cases leftAt with
  | retained leftCursor _ leftToken leftBoundary leftTerminalAt =>
      cases rightAt with
      | retained rightCursor _ rightToken rightBoundary rightTerminalAt =>
          have cursorEq : leftCursor = rightCursor := by
            apply Fin.ext
            exact congrArg
              (fun boundary : Boundary tokens => boundary.val)
              (leftBoundary.trans rightBoundary.symm)
          subst rightCursor
          rcases TerminalAt.functional leftTerminalAt rightTerminalAt with
            ⟨valueEq, spanEq⟩
          have tokenEq : leftToken = rightToken :=
            TerminalStreamValue.retained.inj valueEq
          subst rightToken
          exact ⟨rfl, rfl⟩
      | endOfFile rightCursor _ rightBoundary rightAtEnd =>
          have cursorEq : leftCursor = rightCursor := by
            apply Fin.ext
            exact congrArg
              (fun boundary : Boundary tokens => boundary.val)
              (leftBoundary.trans rightBoundary.symm)
          subst rightCursor
          have impossible :
              TerminalStreamValue.retained leftToken =
                TerminalStreamValue.endOfFile :=
            (TerminalAt.functional leftTerminalAt
              (TerminalAt.endOfFile leftCursor rightAtEnd)).1
          contradiction
  | endOfFile leftCursor _ leftBoundary leftAtEnd =>
      cases rightAt with
      | retained rightCursor _ rightToken rightBoundary rightTerminalAt =>
          have cursorEq : leftCursor = rightCursor := by
            apply Fin.ext
            exact congrArg
              (fun boundary : Boundary tokens => boundary.val)
              (leftBoundary.trans rightBoundary.symm)
          subst rightCursor
          have impossible :
              TerminalStreamValue.endOfFile =
                TerminalStreamValue.retained rightToken :=
            (TerminalAt.functional
              (TerminalAt.endOfFile leftCursor leftAtEnd)
              rightTerminalAt).1
          contradiction
      | endOfFile rightCursor _ rightBoundary rightAtEnd =>
          exact ⟨rfl, rfl⟩

end FoundAt

namespace NonAssociativeLevel

/-- The source rule that establishes one nonassociative precedence level. -/
def rule : NonAssociativeLevel → GrammarRuleId
  | .relational => .relational
  | .equality => .equality

end NonAssociativeLevel

/-- A coherent completed level root retained at the diagnostic frontier. -/
structure NonAssociativeFrontierValue
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens)
    (level : NonAssociativeLevel) where
  origin : Boundary tokens
  context : GuardContext tokens
  value : RuleValue level.rule
  frontier : FrontierReach file tokens memo correct final cursor
    (CanonicalCompleteRootItem tokens level.rule origin cursor context)
  root : CanonicalCompleteRootReduction
    file tokens memo correct final level.rule origin cursor context value

/-- A source-level group resets a completed nonassociative operation. -/
def ExplicitGroupBoundary
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {cursor : Boundary tokens} :
    (level : NonAssociativeLevel) →
      NonAssociativeFrontierValue
        file tokens memo correct final cursor level → Prop
  | .relational, candidate => ∃ inner, candidate.value.payload = .group inner
  | .equality, candidate => ∃ inner, candidate.value.payload = .group inner

/-- The first completed operation at one nonassociative precedence level. -/
def CompletedNonAssociative
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {cursor : Boundary tokens} :
    (level : NonAssociativeLevel) →
      (candidate : NonAssociativeFrontierValue
        file tokens memo correct final cursor level) →
      Located InfixOperator → Prop
  | .relational, candidate, first =>
      ∃ left right,
        candidate.value.payload = .infix first left right ∧
        first.payload ∈ [.less, .greater, .lessEqual, .greaterEqual]
  | .equality, candidate, first =>
      ∃ left right,
        candidate.value.payload = .infix first left right ∧
        first.payload ∈ [.equal, .notEqual]

/-- An explicitly grouped level value cannot simultaneously expose an
ungrouped completed nonassociative operation at that same level root. -/
theorem explicit_group_resets_nonassociative_level
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens}
    {level : NonAssociativeLevel}
    (candidate : NonAssociativeFrontierValue
      file tokens memo correct final cursor level)
    (grouped : ExplicitGroupBoundary level candidate) :
    ∀ first : Located InfixOperator,
      ¬ CompletedNonAssociative level candidate first := by
  intro first completed
  cases level <;>
    rcases grouped with ⟨inner, grouped⟩ <;>
    rcases completed with ⟨left, right, completed, firstAllowed⟩ <;>
    cases grouped.symm.trans completed

/-- One exact nonassociative operator beginning at the frontier cursor. -/
inductive FoundNonAssociativeOperatorAt
    (file : WorkspaceFile) (tokens : List Token) :
    Boundary tokens → NonAssociativeLevel → Located InfixOperator → Prop where
  | less
      {cursor : Boundary tokens}
      (terminal : MatchedTerminal file tokens (.symbol .less))
      (atCursor : terminal.cursor.beforeBoundary = cursor) :
      FoundNonAssociativeOperatorAt file tokens cursor .relational
        (RuleReduction.terminalLoc terminal .less)
  | greater
      {cursor : Boundary tokens}
      (terminal : MatchedTerminal file tokens (.symbol .greater))
      (atCursor : terminal.cursor.beforeBoundary = cursor) :
      FoundNonAssociativeOperatorAt file tokens cursor .relational
        (RuleReduction.terminalLoc terminal .greater)
  | lessEqual
      {cursor : Boundary tokens}
      (terminal : MatchedTerminal file tokens (.symbol .lessEqual))
      (atCursor : terminal.cursor.beforeBoundary = cursor) :
      FoundNonAssociativeOperatorAt file tokens cursor .relational
        (RuleReduction.terminalLoc terminal .lessEqual)
  | greaterEqual
      {cursor : Boundary tokens}
      (terminal : MatchedTerminal file tokens (.symbol .greaterEqual))
      (atCursor : terminal.cursor.beforeBoundary = cursor) :
      FoundNonAssociativeOperatorAt file tokens cursor .relational
        (RuleReduction.terminalLoc terminal .greaterEqual)
  | equal
      {cursor : Boundary tokens}
      (terminal : MatchedTerminal file tokens (.symbol .equalEqual))
      (atCursor : terminal.cursor.beforeBoundary = cursor) :
      FoundNonAssociativeOperatorAt file tokens cursor .equality
        (RuleReduction.terminalLoc terminal .equal)
  | notEqual
      {cursor : Boundary tokens}
      (terminal : MatchedTerminal file tokens (.symbol .notEqual))
      (atCursor : terminal.cursor.beforeBoundary = cursor) :
      FoundNonAssociativeOperatorAt file tokens cursor .equality
        (RuleReduction.terminalLoc terminal .notEqual)

namespace FoundNonAssociativeOperatorAt

/-- One frontier determines at most one nonassociative level and operator. -/
theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {cursor : Boundary tokens}
    {leftLevel rightLevel : NonAssociativeLevel}
    {leftOperator rightOperator : Located InfixOperator}
    (leftFound : FoundNonAssociativeOperatorAt
      file tokens cursor leftLevel leftOperator)
    (rightFound : FoundNonAssociativeOperatorAt
      file tokens cursor rightLevel rightOperator) :
    leftLevel = rightLevel ∧ leftOperator = rightOperator := by
  have symbolSpan
      {leftSymbol rightSymbol : Symbol}
      (leftTerminal : MatchedTerminal file tokens (.symbol leftSymbol))
      (leftAtCursor : leftTerminal.cursor.beforeBoundary = cursor)
      (rightTerminal : MatchedTerminal file tokens (.symbol rightSymbol))
      (rightAtCursor : rightTerminal.cursor.beforeBoundary = cursor) :
      leftSymbol = rightSymbol ∧ leftTerminal.span = rightTerminal.span := by
    have cursorEq : leftTerminal.cursor = rightTerminal.cursor := by
      apply Fin.ext
      exact congrArg
        (fun boundary : Boundary tokens => boundary.val)
        (leftAtCursor.trans rightAtCursor.symm)
    cases leftTerminal with
    | mk leftCursor leftValue leftSpan leftAt leftMatches =>
        cases rightTerminal with
        | mk rightCursor rightValue rightSpan rightAt rightMatches =>
            simp only at cursorEq
            subst rightCursor
            rcases TerminalAt.functional leftAt rightAt with
              ⟨valueEq, spanEq⟩
            subst rightValue
            cases leftValue with
            | retained token =>
                simp only [TerminalMatches] at leftMatches rightMatches
                have payloadEq := leftMatches.symm.trans rightMatches
                have symbolEq : leftSymbol = rightSymbol :=
                  TokenKind.symbol.inj payloadEq
                exact ⟨symbolEq, spanEq⟩
            | endOfFile =>
                simp [TerminalMatches] at leftMatches
  cases leftFound <;> cases rightFound <;>
    rename_i leftTerminal leftAtCursor rightTerminal rightAtCursor <;>
    rcases symbolSpan leftTerminal leftAtCursor rightTerminal rightAtCursor with
      ⟨symbolEq, spanEq⟩ <;>
    cases symbolEq <;>
    constructor <;>
    first
    | rfl
    | simpa only [RuleReduction.terminalLoc] using
        congrArg
          (fun span => ({ span := span, payload := _ } : Located InfixOperator))
          spanEq

end FoundNonAssociativeOperatorAt

/-- A second same-level operator following an ungrouped completed operation. -/
def RepeatedNonAssociativeAt
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) (level : NonAssociativeLevel)
    (operator : Located InfixOperator) : Prop :=
  ∃ candidate : NonAssociativeFrontierValue
      file tokens memo correct final cursor level,
    ∃ first : Located InfixOperator,
      CompletedNonAssociative level candidate first ∧
      ¬ ExplicitGroupBoundary level candidate ∧
      FoundNonAssociativeOperatorAt file tokens cursor level operator

/-- Every repeated-nonassociative witness retains the same coherent,
greatest-frontier level root inspected by its completed and grouping tests. -/
theorem repeatedNonAssociative_coherent
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens}
    {level : NonAssociativeLevel}
    {operator : Located InfixOperator}
    (repeated : RepeatedNonAssociativeAt
      file tokens memo correct final cursor level operator) :
    ∃ candidate : NonAssociativeFrontierValue
        file tokens memo correct final cursor level,
      ∃ first : Located InfixOperator,
        FrontierReach file tokens memo correct final cursor
          (CanonicalCompleteRootItem tokens level.rule
            candidate.origin cursor candidate.context) ∧
        CanonicalCompleteRootReduction
          file tokens memo correct final level.rule
          candidate.origin cursor candidate.context candidate.value ∧
        CompletedNonAssociative level candidate first ∧
        ¬ ExplicitGroupBoundary level candidate ∧
        FoundNonAssociativeOperatorAt
          file tokens cursor level operator := by
  rcases repeated with
    ⟨candidate, first, completed, ungrouped, found⟩
  exact ⟨candidate, first, candidate.frontier, candidate.root,
    completed, ungrouped, found⟩

namespace ParseDiagnostic

/-- Exact declarative applicability of one closed parser diagnostic. -/
inductive Applies : WorkspaceFile → List Token → ParseDiagnostic → Prop where
  | unexpected
      (file : WorkspaceFile)
      (tokens : List Token)
      (memo : GuardMemo tokens)
      (correct : PhaseBCorrect file tokens memo)
      (final : AllGuardsFinal memo)
      (cursor : Boundary tokens)
      (span : SourceSpan)
      (found : Found)
      (expected : NonemptyList Expected)
      (noRoot : ¬ ∃ module, SourceBackedRoot file tokens module)
      (greatest : GreatestReachableCursor
        file tokens memo correct final cursor)
      (canonical : CanonicalExpected
        file tokens memo correct final cursor expected)
      (foundAt : FoundAt file tokens cursor span found)
      (notRepeated : ∀ level operator,
        ¬ RepeatedNonAssociativeAt file tokens memo correct final
          cursor level operator) :
      Applies file tokens (.unexpected span found expected)
  | repeatedNonAssociative
      (file : WorkspaceFile)
      (tokens : List Token)
      (memo : GuardMemo tokens)
      (correct : PhaseBCorrect file tokens memo)
      (final : AllGuardsFinal memo)
      (cursor : Boundary tokens)
      (level : NonAssociativeLevel)
      (operator : Located InfixOperator)
      (noRoot : ¬ ∃ module, SourceBackedRoot file tokens module)
      (greatest : GreatestReachableCursor
        file tokens memo correct final cursor)
      (repeated : RepeatedNonAssociativeAt
        file tokens memo correct final cursor level operator) :
      Applies file tokens
        (.repeatedNonAssociative operator.span level operator)

end ParseDiagnostic

private theorem finalPhaseBMemo_functional
    {file : WorkspaceFile} {tokens : List Token}
    {leftMemo rightMemo : GuardMemo tokens}
    (leftCorrect : PhaseBCorrect file tokens leftMemo)
    (leftFinal : AllGuardsFinal leftMemo)
    (rightCorrect : PhaseBCorrect file tokens rightMemo)
    (rightFinal : AllGuardsFinal rightMemo) :
    leftMemo = rightMemo := by
  funext key
  rcases leftFinal key with ⟨leftDecision, leftState⟩
  rcases rightFinal key with ⟨rightDecision, rightState⟩
  have leftEvidence : GuardEvidence file tokens key leftDecision :=
    (leftCorrect key leftDecision).mp leftState
  have rightEvidence : GuardEvidence file tokens key rightDecision :=
    (rightCorrect key rightDecision).mp rightState
  have decisionEq : leftDecision = rightDecision :=
    GuardEvidence.functional leftEvidence rightEvidence
  subst rightDecision
  exact leftState.trans rightState.symm

namespace ParseDiagnostic.Applies

theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {left right : ParseDiagnostic}
    (leftApplies : ParseDiagnostic.Applies file tokens left)
    (rightApplies : ParseDiagnostic.Applies file tokens right) :
    left = right := by
  cases leftApplies with
  | unexpected leftMemo leftCorrect leftFinal leftCursor leftSpan
      leftFound leftExpected _ leftGreatest leftCanonical leftFoundAt
      leftNotRepeated =>
      cases rightApplies with
      | unexpected rightMemo rightCorrect rightFinal rightCursor rightSpan
          rightFound rightExpected _ rightGreatest rightCanonical rightFoundAt
          rightNotRepeated =>
          have memoEq : leftMemo = rightMemo :=
            finalPhaseBMemo_functional
              leftCorrect leftFinal rightCorrect rightFinal
          subst rightMemo
          have correctEq : leftCorrect = rightCorrect := Subsingleton.elim _ _
          subst rightCorrect
          have finalEq : leftFinal = rightFinal := Subsingleton.elim _ _
          subst rightFinal
          have cursorEq : leftCursor = rightCursor :=
            GreatestReachableCursor.functional leftGreatest rightGreatest
          subst rightCursor
          have expectedEq : leftExpected = rightExpected :=
            canonicalExpected_sorted_nodup_unique
              leftCanonical rightCanonical
          subst rightExpected
          rcases FoundAt.functional leftFoundAt rightFoundAt with
            ⟨spanEq, foundEq⟩
          subst rightSpan
          subst rightFound
          rfl
      | repeatedNonAssociative rightMemo rightCorrect rightFinal
          rightCursor rightLevel rightOperator _ rightGreatest rightRepeated =>
          have memoEq : leftMemo = rightMemo :=
            finalPhaseBMemo_functional
              leftCorrect leftFinal rightCorrect rightFinal
          subst rightMemo
          have correctEq : leftCorrect = rightCorrect := Subsingleton.elim _ _
          subst rightCorrect
          have finalEq : leftFinal = rightFinal := Subsingleton.elim _ _
          subst rightFinal
          have cursorEq : leftCursor = rightCursor :=
            GreatestReachableCursor.functional leftGreatest rightGreatest
          subst rightCursor
          exact (leftNotRepeated rightLevel rightOperator rightRepeated).elim
  | repeatedNonAssociative leftMemo leftCorrect leftFinal leftCursor
      leftLevel leftOperator _ leftGreatest leftRepeated =>
      cases rightApplies with
      | unexpected rightMemo rightCorrect rightFinal rightCursor _ _ _ _
          rightGreatest _ _ rightNotRepeated =>
          have memoEq : leftMemo = rightMemo :=
            finalPhaseBMemo_functional
              leftCorrect leftFinal rightCorrect rightFinal
          subst rightMemo
          have correctEq : leftCorrect = rightCorrect := Subsingleton.elim _ _
          subst rightCorrect
          have finalEq : leftFinal = rightFinal := Subsingleton.elim _ _
          subst rightFinal
          have cursorEq : leftCursor = rightCursor :=
            GreatestReachableCursor.functional leftGreatest rightGreatest
          subst rightCursor
          exact (rightNotRepeated leftLevel leftOperator leftRepeated).elim
      | repeatedNonAssociative rightMemo rightCorrect rightFinal
          rightCursor rightLevel rightOperator _ rightGreatest rightRepeated =>
          have memoEq : leftMemo = rightMemo :=
            finalPhaseBMemo_functional
              leftCorrect leftFinal rightCorrect rightFinal
          subst rightMemo
          have correctEq : leftCorrect = rightCorrect := Subsingleton.elim _ _
          subst rightCorrect
          have finalEq : leftFinal = rightFinal := Subsingleton.elim _ _
          subst rightFinal
          have cursorEq : leftCursor = rightCursor :=
            GreatestReachableCursor.functional leftGreatest rightGreatest
          subst rightCursor
          rcases leftRepeated with
            ⟨leftCandidate, leftFirst, leftCompleted, leftUngrouped,
              leftFoundOperator⟩
          rcases rightRepeated with
            ⟨rightCandidate, rightFirst, rightCompleted, rightUngrouped,
              rightFoundOperator⟩
          rcases FoundNonAssociativeOperatorAt.functional
              leftFoundOperator rightFoundOperator with
            ⟨levelEq, operatorEq⟩
          subst rightLevel
          subst rightOperator
          rfl

end ParseDiagnostic.Applies

/-- Unexpected-token and repeated-nonassociative diagnostics are exclusive. -/
theorem parse_diagnostic_constructors_exclusive
    {file : WorkspaceFile} {tokens : List Token}
    {unexpectedSpan repeatedSpan : SourceSpan}
    {found : Found} {expected : NonemptyList Expected}
    {level : NonAssociativeLevel}
    {operator : Located InfixOperator}
    (unexpected : ParseDiagnostic.Applies file tokens
      (.unexpected unexpectedSpan found expected))
    (repeated : ParseDiagnostic.Applies file tokens
      (.repeatedNonAssociative repeatedSpan level operator)) :
    False := by
  have impossible :
      ParseDiagnostic.unexpected unexpectedSpan found expected =
        ParseDiagnostic.repeatedNonAssociative repeatedSpan level operator :=
    ParseDiagnostic.Applies.functional unexpected repeated
  contradiction

end Solcore.Surface.Multi
