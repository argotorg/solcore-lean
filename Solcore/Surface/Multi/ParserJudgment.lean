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

end Solcore.Surface.Multi
