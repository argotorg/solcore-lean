import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Grammar.Yul

/-!
Properties of the declarative grammar of Yul names, blocks and terminated statements:
outcomes are deterministic, and successful values and rejection points are unique. Nothing
here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulBlockOutcomeProperties
/-!
Functionality, rejection exclusivity, and clean embedding for ordinary
inline-Yul block outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem exactToken_span_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftSpan = rightSpan := by
  have tokenEq :
      ({ span := leftSpan, value := kind } : Token) =
        { span := rightSpan, value := kind } :=
    Option.some.inj (leftParsed.1.2.symm.trans rightParsed.1.2)
  exact congrArg (fun token : Token => token.span) tokenEq

/-- Ordinary block-item success has a unique final remainder whenever one
ordinary statement has a unique final remainder. -/
theorem YulBlockItemsParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {openingSpan : SourceSpan} {input : Remainder}
    {leftSpan rightSpan : SourceSpan}
    {leftBody rightBody : List Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockItemsParses statementOrdinary openingSpan input
      leftSpan leftBody afterLeft)
    (rightParsed : YulBlockItemsParses statementOrdinary openingSpan input
      rightSpan rightBody afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightSpan rightBody afterRight with
  | close leftClosingSpan leftClosingParsed =>
      cases rightParsed with
      | close rightClosingSpan rightClosingParsed =>
          exact exactToken_output_unique leftClosingParsed rightClosingParsed
      | next rightNotAtEnd rightClosingAbsent rightStatementParsed
            rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosingParsed)
  | next leftNotAtEnd leftClosingAbsent leftStatementParsed leftProgress
        leftTail inductionHypothesis =>
      cases rightParsed with
      | close rightClosingSpan rightClosingParsed =>
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosingParsed)
      | next rightNotAtEnd rightClosingAbsent rightStatementParsed
            rightProgress rightTail =>
          have afterStatementEq := outcomes.successOutputUnique
            leftStatementParsed rightStatementParsed
          subst afterStatementEq
          exact inductionHypothesis rightTail

/-- Ordinary complete block success has a unique final remainder. -/
theorem YulBlockParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftBody rightBody : List Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockOrdinaryParses statementOrdinary input leftSpan
      leftBody afterLeft)
    (rightParsed : YulBlockOrdinaryParses statementOrdinary input rightSpan
      rightBody afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpeningSpan leftOpeningParsed leftItemsParsed =>
      cases rightParsed with
      | parsed rightOpeningSpan rightOpeningParsed rightItemsParsed =>
          have openingSpanEq := exactToken_span_unique leftOpeningParsed
            rightOpeningParsed
          subst openingSpanEq
          have afterOpeningEq := exactToken_output_unique leftOpeningParsed
            rightOpeningParsed
          subst afterOpeningEq
          exact leftItemsParsed.output_unique outcomes rightItemsParsed

/-- An exact block-item rejection excludes every ordinary block-item
success from the same remainder. -/
theorem YulBlockItemsRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : YulBlockItemsRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ openingSpan bodySpan body output,
      YulBlockItemsParses statementOrdinary openingSpan input bodySpan body
        output := by
  induction rejection with
  | missingClose closingAbsent atEnd =>
      rintro ⟨openingSpan, bodySpan, body, output, parsed⟩
      cases parsed with
      | close closingSpan closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next notAtEnd otherClosingAbsent statementParsed progress tail =>
          exact (Nat.not_lt_of_ge atEnd) notAtEnd
  | statementRejected notAtEnd closingAbsent rejectedStatement =>
      rintro ⟨openingSpan, bodySpan, body, output, parsed⟩
      cases parsed with
      | close closingSpan closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next otherNotAtEnd otherClosingAbsent statementParsed progress tail =>
          exact outcomes.successRejectDisjoint rejectedStatement
            ⟨_, _, statementParsed⟩
  | laterRejected notAtEnd closingAbsent rejectedStatementParsed progress
        tailRejected inductionHypothesis =>
      rintro ⟨openingSpan, bodySpan, body, output, parsed⟩
      cases parsed with
      | close closingSpan closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next otherNotAtEnd otherClosingAbsent successfulStatementParsed
            otherProgress successfulTail =>
          have afterStatementEq := outcomes.successOutputUnique
            rejectedStatementParsed successfulStatementParsed
          subst afterStatementEq
          exact inductionHypothesis ⟨_, _, _, _, successfulTail⟩

/-- Exact complete-block rejection excludes ordinary complete-block success. -/
theorem YulBlockRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : YulBlockRejects statementOrdinary statementRejects input
      rejected) :
    ¬ ∃ bodySpan body output,
      YulBlockOrdinaryParses statementOrdinary input bodySpan body output := by
  rintro ⟨bodySpan, body, output, parsed⟩
  cases rejection with
  | openingMissing openingAbsent =>
      cases parsed with
      | parsed openingSpan openingParsed itemsParsed =>
          exact absent_conflicts_exact openingAbsent openingParsed
  | itemsRejected rejectedOpeningSpan rejectedOpeningParsed itemsRejected =>
      cases parsed with
      | parsed openingSpan openingParsed itemsParsed =>
          have afterOpeningEq := exactToken_output_unique
            rejectedOpeningParsed openingParsed
          subst afterOpeningEq
          exact itemsRejected.disjointOrdinary outcomes
            ⟨_, _, _, _, itemsParsed⟩

/-- Ordinary block success and exact block rejection form a deterministic
outcome contract. -/
theorem yulBlockDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects) :
    DeterministicOutcomeSpec
      (YulBlockOutcomeParses statementOrdinary)
      (YulBlockRejects statementOrdinary statementRejects) where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique outcomes rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨block, output, parsed⟩
    exact rejection.disjointOrdinary outcomes
      ⟨block.span, block.body, output, parsed⟩

/-- A clean block-item derivation embeds into an ordinary derivation when
each clean statement embeds into the supplied ordinary statement relation. -/
theorem YulBlockItemsParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {openingSpan bodySpan : SourceSpan} {body : List Syntax.YulStmt}
    {input output : Remainder}
    (parsed : YulBlockItemsParses statementClean openingSpan input bodySpan
      body output) :
    YulBlockItemsParses statementOrdinary openingSpan input bodySpan body
      output := by
  induction parsed with
  | close closingSpan closingParsed => exact .close closingSpan closingParsed
  | next notAtEnd closingAbsent statementParsed progress tail
        inductionHypothesis =>
      exact .next notAtEnd closingAbsent (cleanToOrdinary statementParsed)
        progress inductionHypothesis

/-- A clean complete block derivation embeds into the corresponding ordinary
block derivation without changing its span, body, or remainder. -/
theorem YulBlockParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {bodySpan : SourceSpan}
    {body : List Syntax.YulStmt}
    (parsed : YulBlockParses statementClean input bodySpan body output) :
    YulBlockOrdinaryParses statementOrdinary input bodySpan body output := by
  cases parsed with
  | parsed openingSpan openingParsed bodyParsed =>
      exact .parsed openingSpan openingParsed
        (bodyParsed.toOrdinary cleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulBlockStatementOutcomeProperties
/-! Ordinary outcomes for lifting one parsed Yul block into statement form. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary block-statement success uses ordinary statements recursively. -/
abbrev YulBlockStatementOrdinaryParses
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulBlockStatementParses statementOrdinary

/-- Block-statement rejection is exactly rejection of its underlying block. -/
abbrev YulBlockStatementRejects
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :=
  YulBlockRejects statementOrdinary statementRejects

/-- Ordinary block-statement success has functional output. -/
theorem YulBlockStatementOrdinaryParses.output_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockStatementOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : YulBlockStatementOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftBlock =>
      cases rightParsed with
      | parsed rightBlock => exact leftBlock.output_unique outcomes rightBlock

/-- Underlying block rejection excludes every ordinary block statement. -/
theorem YulBlockStatementRejects.disjointOrdinary
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : YulBlockStatementRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      YulBlockStatementOrdinaryParses statementOrdinary input statement
        output := by
  rintro ⟨statement, output, parsed⟩
  cases parsed with
  | parsed blockParsed =>
      apply YulBlockRejects.disjointOrdinary outcomes rejection
      exact ⟨_, _, output, blockParsed⟩

/-- Construct the lifted block-statement outcome contract. -/
theorem yulBlockStatementDeterministicOutcomeSpec
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects) :
    DeterministicOutcomeSpec
      (YulBlockStatementOrdinaryParses statementOrdinary)
      (YulBlockStatementRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulBlockStatementOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    YulBlockStatementRejects.disjointOrdinary outcomes

/-- Clean block statements embed into ordinary block statements unchanged. -/
theorem YulBlockStatementParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulBlockStatementParses statementClean input statement output) :
    YulBlockStatementOrdinaryParses statementOrdinary input statement
      output := by
  cases parsed with
  | parsed blockParsed => exact .parsed (blockParsed.toOrdinary cleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulNameOutcomeProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementTerminatedOutcomeProperties
/-!
Parser-independent ordinary outcomes for a Yul statement core followed by its
maximal optional semicolon.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary success of a core statement followed by its optional semicolon. -/
abbrev YulStatementTerminatedOrdinaryParses
    (coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulStatementTerminatedParses coreOrdinary

/-- Optional semicolon parsing cannot reject, so a terminated attempt rejects
exactly where its core attempt rejects. -/
abbrev YulStatementTerminatedRejects
    (coreRejects : Remainder → Remainder → Prop) :=
  coreRejects

/-- Maximal optional-semicolon parsing has one output remainder. -/
theorem OptionalYulSemicolonParses.output_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalYulSemicolonParses input left afterLeft)
    (rightParsed : OptionalYulSemicolonParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightToken =>
          exact False.elim (absent_conflicts_exact leftAbsent rightToken)
  | present leftSpan leftToken =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
      | present rightSpan rightToken =>
          rw [leftToken.2, rightToken.2]

/-- Optional termination preserves functional output of the core relation. -/
theorem YulStatementTerminatedOrdinaryParses.output_unique
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementTerminatedOrdinaryParses coreOrdinary input
      left afterLeft)
    (rightParsed : YulStatementTerminatedOrdinaryParses coreOrdinary input
      right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftCore, leftCoreParsed, leftSemicolon⟩
  rcases rightParsed with ⟨rightCore, rightCoreParsed, rightSemicolon⟩
  have coreEq := outcomes.successOutputUnique leftCoreParsed rightCoreParsed
  subst rightCore
  exact leftSemicolon.output_unique rightSemicolon

/-- Core rejection excludes every optionally terminated ordinary success. -/
theorem YulStatementTerminatedRejects.disjointOrdinary
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input rejected : Remainder}
    (rejection : YulStatementTerminatedRejects coreRejects input rejected) :
    ¬ ∃ statement output,
      YulStatementTerminatedOrdinaryParses coreOrdinary input statement
        output := by
  rintro ⟨statement, output, afterCore, coreParsed, semicolonParsed⟩
  exact outcomes.successRejectDisjoint rejection
    ⟨statement, afterCore, coreParsed⟩

/-- Construct the deterministic outcome contract for optional termination. -/
theorem yulStatementTerminatedDeterministicOutcomeSpec
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec coreOrdinary coreRejects) :
    DeterministicOutcomeSpec
      (YulStatementTerminatedOrdinaryParses coreOrdinary)
      (YulStatementTerminatedRejects coreRejects) where
  successOutputUnique :=
    YulStatementTerminatedOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    YulStatementTerminatedRejects.disjointOrdinary outcomes

/-- Clean core success embeds into ordinary optional termination unchanged. -/
theorem YulStatementTerminatedParses.toOrdinary
    {coreClean coreOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      coreClean input statement output →
        coreOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulStatementTerminatedParses coreClean input statement output) :
    YulStatementTerminatedOrdinaryParses coreOrdinary input statement
      output := by
  rcases parsed with ⟨afterCore, coreParsed, semicolonParsed⟩
  exact ⟨afterCore, cleanToOrdinary coreParsed, semicolonParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementOrdinaryRecoveryProperties
/-!
Functionality, boundary exclusion, and clean embedding for the outer
recovering Yul-statement outcome.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- A statement recovery scan has functional output from one remainder. -/
theorem YulStatementRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.YulStmt} {afterLeft afterRight : Remainder},
      YulStatementRecoveryScanParses first leftLast input left afterLeft →
      YulStatementRecoveryScanParses first rightLast input right afterRight →
      afterLeft = afterRight := by
  intro first leftLast rightLast input left right afterLeft afterRight
    leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- One ordinary recovering statement layer has functional output. -/
theorem YulStatementLayerOrdinaryParses.output_unique
    {terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec terminatedOrdinary
      terminatedRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementLayerOrdinaryParses terminatedOrdinary
      terminatedRejects input left afterLeft)
    (rightParsed : YulStatementLayerOrdinaryParses terminatedOrdinary
      terminatedRejects input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | terminated leftTerminated =>
      cases rightParsed with
      | terminated rightTerminated =>
          exact outcomes.successOutputUnique leftTerminated rightTerminated
      | recovered rightRejected rightContinues rightCurrent rightScan =>
          exact False.elim (outcomes.successRejectDisjoint rightRejected
            ⟨_, _, leftTerminated⟩)
  | recovered leftRejected leftContinues leftCurrent leftScan =>
      cases rightParsed with
      | terminated rightTerminated =>
          exact False.elim (outcomes.successRejectDisjoint leftRejected
            ⟨_, _, rightTerminated⟩)
      | recovered rightRejected rightContinues rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every outer statement rejection is non-consuming. -/
theorem YulStatementRejects.output_eq {input rejected : Remainder}
    (rejection : YulStatementRejects input rejected) : rejected = input := by
  cases rejection <;> rfl

/-- Boundary exclusion for terminated successes lifts through recovery. -/
theorem YulStatementRejects.disjointLayerOrdinary
    {terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (terminatedBoundaryDisjoint : ∀ {input rejected},
      YulStatementRejects input rejected →
        ¬ ∃ statement output,
          terminatedOrdinary input statement output)
    {input rejected : Remainder}
    (rejection : YulStatementRejects input rejected) :
    ¬ ∃ statement output,
      YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
        input statement output := by
  rintro ⟨statement, output, parsed⟩
  cases parsed with
  | terminated parsed =>
      exact terminatedBoundaryDisjoint rejection ⟨_, _, parsed⟩
  | recovered terminatedRejected continues current scan =>
      have rejectedEq := rejection.output_eq
      subst rejected
      exact continues rejection

/-- Construct the deterministic outcome contract for one recovering layer. -/
theorem yulStatementLayerDeterministicOutcomeSpec
    {terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec terminatedOrdinary
      terminatedRejects)
    (terminatedBoundaryDisjoint : ∀ {input rejected},
      YulStatementRejects input rejected →
        ¬ ∃ statement output,
          terminatedOrdinary input statement output) :
    DeterministicOutcomeSpec
      (YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects)
      YulStatementRejects where
  successOutputUnique :=
    YulStatementLayerOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    YulStatementRejects.disjointLayerOrdinary terminatedBoundaryDisjoint

/-- A clean terminated success is an ordinary recovering-layer success. -/
theorem YulStatementLayerOrdinaryParses.ofClean
    {cleanTerminated terminatedOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      cleanTerminated input statement output →
        terminatedOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : cleanTerminated input statement output) :
    YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
      input statement output :=
  .terminated (cleanToOrdinary parsed)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementTerminatedBoundaryProperties
/-! Lift Yul recovery-boundary exclusion through optional termination. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A recovery boundary that excludes core success also excludes every
optionally terminated success, since termination begins with that same core
success. -/
theorem YulStatementRejects.disjointTerminatedOrdinary
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    (coreBoundaryDisjoint : ∀ {input rejected},
      YulStatementRejects input rejected →
        ¬ ∃ statement output, coreOrdinary input statement output)
    {input rejected : Remainder}
    (rejection : YulStatementRejects input rejected) :
    ¬ ∃ statement output,
      YulStatementTerminatedOrdinaryParses coreOrdinary input statement
        output := by
  rintro ⟨statement, output, afterCore, coreParsed, semicolonParsed⟩
  exact coreBoundaryDisjoint rejection ⟨statement, afterCore, coreParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end
