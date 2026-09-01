import Solcore.Syntax.DeclarativeYulNameOutcomeGrammar

/-!
Functionality, exclusivity, and clean-grammar embeddings for ordinary Yul-name
outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Every ordinary name exposes a current token admitted by the exact Yul-name
decision. -/
theorem YulNameOrdinaryParses.startsAt {input output : Remainder}
    {name : Syntax.YulIdentifier}
    (parsed : YulNameOrdinaryParses input name output) :
    ∃ token,
      TokenAt input.tokens input.endIndex input.cursor token ∧
        tokenKindStartsOrdinaryYulName token.value = true := by
  cases parsed with
  | marked token => exact ⟨_, token, rfl⟩
  | underscore token => exact ⟨_, token, rfl⟩
  | fallbackKeyword token => exact ⟨_, token, rfl⟩
  | identifier parsed => exact ⟨_, parsed.1, rfl⟩

/-- Every ordinary Yul name consumes exactly its current token. -/
theorem YulNameOrdinaryParses.output_eq {input output : Remainder}
    {name : Syntax.YulIdentifier}
    (parsed : YulNameOrdinaryParses input name output) :
    output = { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | marked | underscore | fallbackKeyword => rfl
  | identifier parsed =>
      rcases parsed with ⟨token, tokensEq, endIndexEq, cursorEq⟩
      cases input
      cases output
      simp_all

/-- The ordinary Yul-name output remainder is functional. -/
theorem YulNameOrdinaryParses.output_unique {input : Remainder}
    {left right : Syntax.YulIdentifier} {afterLeft afterRight : Remainder}
    (leftParsed : YulNameOrdinaryParses input left afterLeft)
    (rightParsed : YulNameOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  rw [leftParsed.output_eq, rightParsed.output_eq]

/-- Ordinary Yul-name rejection excludes ordinary success. -/
theorem YulNameRejects.disjoint {input rejected : Remainder}
    (rejection : YulNameRejects input rejected) :
    ¬ ∃ name output, YulNameOrdinaryParses input name output := by
  cases rejection with
  | absent noSuccess => exact noSuccess

/-- Every strict clean Yul name is an ordinary success. -/
theorem YulNameParses.toOrdinary {input output : Remainder}
    {name : Syntax.YulIdentifier} (parsed : YulNameParses input name output) :
    YulNameOrdinaryParses input name output := by
  cases parsed with
  | marked token => exact .marked token
  | underscore token => exact .underscore token
  | fallbackKeyword token => exact .fallbackKeyword token
  | identifier hyphenAbsent parsed => exact .identifier parsed

/-- Ordinary name outcomes form the deterministic contract used by
transactional callers. -/
theorem yulNameDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulNameOrdinaryParses YulNameRejects where
  successOutputUnique := YulNameOrdinaryParses.output_unique
  successRejectDisjoint := YulNameRejects.disjoint

/-- Finishing an ordinary sequence fixes its value and leaves input unchanged. -/
theorem FinishYulNamesOrdinaryParses.output_eq
    {first last : Syntax.YulIdentifier} {tailRev : List Syntax.YulIdentifier}
    {input output : Remainder} {value : YulNamesOrdinaryValue}
    (derivation : FinishYulNamesOrdinaryParses first last tailRev input value
      output) : output = input := by
  cases derivation
  rfl

/-- The ordinary tail output depends only on the current remainder. -/
theorem YulNamesTailOrdinaryParses.output_unique :
    ∀ {leftFirst rightFirst : Syntax.YulIdentifier}
      {input : Remainder} {leftLast rightLast : Syntax.YulIdentifier}
      {leftRev rightRev : List Syntax.YulIdentifier}
      {leftValue rightValue : YulNamesOrdinaryValue}
      {leftOutput rightOutput : Remainder},
      YulNamesTailOrdinaryParses leftFirst input leftLast leftRev leftValue
          leftOutput →
      YulNamesTailOrdinaryParses rightFirst input rightLast rightRev rightValue
          rightOutput →
      leftOutput = rightOutput := by
  intro leftFirst rightFirst input leftLast rightLast leftRev rightRev
    leftValue rightValue leftOutput rightOutput leftParsed
  induction leftParsed generalizing rightFirst rightLast rightRev rightValue
      rightOutput with
  | done leftCommaAbsent leftFinished =>
      intro rightParsed
      cases rightParsed with
      | done rightCommaAbsent rightFinished =>
          rw [leftFinished.output_eq, rightFinished.output_eq]
      | next commaSpan commaToken nameParsed tail =>
          exact False.elim (absent_conflicts_token leftCommaAbsent commaToken)
  | next commaSpan commaToken leftNameParsed leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | done rightCommaAbsent rightFinished =>
          exact False.elim (absent_conflicts_token rightCommaAbsent commaToken)
      | next rightCommaSpan rightCommaToken rightNameParsed rightTail =>
          have afterNameEq := leftNameParsed.output_unique rightNameParsed
          subst afterNameEq
          exact inductionHypothesis rightTail

/-- A tail rejection cannot overlap an ordinary tail success at the same
remainder, independently of the accumulated names. -/
theorem YulNamesTailRejects.disjointOrdinary :
    ∀ {rejectedFirst successfulFirst : Syntax.YulIdentifier}
      {input : Remainder}
      {rejectedLast successfulLast : Syntax.YulIdentifier}
      {rejectedRev successfulRev : List Syntax.YulIdentifier}
      {rejectedOutput successfulOutput : Remainder}
      {successfulValue : YulNamesOrdinaryValue},
      YulNamesTailRejects rejectedFirst input rejectedLast rejectedRev
          rejectedOutput →
      YulNamesTailOrdinaryParses successfulFirst input successfulLast
          successfulRev successfulValue successfulOutput →
      False := by
  intro rejectedFirst successfulFirst input rejectedLast successfulLast
    rejectedRev successfulRev rejectedOutput successfulOutput successfulValue
    rejected
  induction rejected generalizing successfulFirst successfulLast successfulRev
      successfulOutput successfulValue with
  | commaNameRejected commaSpan commaToken nameRejected =>
      intro successful
      cases successful with
      | done commaAbsent finished =>
          exact absent_conflicts_token commaAbsent commaToken
      | next otherCommaSpan otherCommaToken nameParsed tail =>
          exact nameRejected.disjoint ⟨_, _, nameParsed⟩
  | laterRejected commaSpan commaToken rejectedNameParsed tailRejected
        inductionHypothesis =>
      intro successful
      cases successful with
      | done commaAbsent finished =>
          exact absent_conflicts_token commaAbsent commaToken
      | next otherCommaSpan otherCommaToken successfulNameParsed tail =>
          have afterNameEq :=
            rejectedNameParsed.output_unique successfulNameParsed
          subst afterNameEq
          exact inductionHypothesis tail

/-- The public ordinary nonempty sequence has a unique output remainder. -/
theorem YulNamesOrdinaryParses.output_unique {input : Remainder}
    {left right : YulNamesOrdinaryValue}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulNamesOrdinaryParses input left afterLeft)
    (rightParsed : YulNamesOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftFirstParsed leftTail =>
      cases rightParsed with
      | parsed rightFirstParsed rightTail =>
          have afterFirstEq := leftFirstParsed.output_unique rightFirstParsed
          subst afterFirstEq
          exact leftTail.output_unique rightTail

/-- Public name-sequence rejection excludes every ordinary success. -/
theorem YulNamesRejects.disjoint {input rejected : Remainder}
    (rejection : YulNamesRejects input rejected) :
    ¬ ∃ value output, YulNamesOrdinaryParses input value output := by
  intro successful
  rcases successful with ⟨value, output, successful⟩
  cases rejection with
  | firstRejected firstRejected =>
      cases successful with
      | parsed firstParsed tail =>
          exact firstRejected.disjoint ⟨_, _, firstParsed⟩
  | tailRejected rejectedFirstParsed tailRejected =>
      cases successful with
      | parsed successfulFirstParsed successfulTail =>
          have afterFirstEq :=
            rejectedFirstParsed.output_unique successfulFirstParsed
          subst afterFirstEq
          exact tailRejected.disjointOrdinary successfulTail

/-- Clean finishing embeds into ordinary non-consuming assembly. -/
theorem FinishYulNamesParses.toOrdinary
    {first last : Syntax.YulIdentifier} {tailRev : List Syntax.YulIdentifier}
    {input output : Remainder} {span : SourceSpan}
    {names : NonemptyList Syntax.YulIdentifier}
    (derivation : FinishYulNamesParses first last tailRev input span names
      output) :
    FinishYulNamesOrdinaryParses first last tailRev input { span, names }
      output := by
  cases derivation
  exact .parsed

/-- Every clean tail success is an ordinary tail success. -/
theorem YulNamesTailParses.toOrdinary {first : Syntax.YulIdentifier}
    {input output : Remainder} {last : Syntax.YulIdentifier}
    {tailRev : List Syntax.YulIdentifier} {span : SourceSpan}
    {names : NonemptyList Syntax.YulIdentifier}
    (parsed : YulNamesTailParses first input last tailRev span names output) :
    YulNamesTailOrdinaryParses first input last tailRev { span, names }
      output := by
  induction parsed with
  | done commaAbsent finished =>
      exact .done commaAbsent finished.toOrdinary
  | next commaSpan commaToken nameParsed progress tail inductionHypothesis =>
      rcases commaToken with ⟨token, afterCommaEq⟩
      subst afterCommaEq
      exact .next commaSpan token nameParsed.toOrdinary inductionHypothesis

/-- Every clean public name sequence is an ordinary sequence success. -/
theorem YulNamesParses.toOrdinary {input output : Remainder}
    {span : SourceSpan} {names : NonemptyList Syntax.YulIdentifier}
    (parsed : YulNamesParses input span names output) :
    YulNamesOrdinaryParses input { span, names } output := by
  cases parsed with
  | parsed firstParsed progress tail =>
      exact .parsed firstParsed.toOrdinary tail.toOrdinary

/-- Public name-sequence outcomes form a deterministic ordinary contract. -/
theorem yulNamesDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulNamesOrdinaryParses YulNamesRejects where
  successOutputUnique := YulNamesOrdinaryParses.output_unique
  successRejectDisjoint := YulNamesRejects.disjoint

end Solcore.Syntax.DeclarativeGrammar
