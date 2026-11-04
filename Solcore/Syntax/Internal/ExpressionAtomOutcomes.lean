import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Internal.ExpressionOutcomes

/-!
Properties of the declarative grammar of expression atoms and one expression step:
outcomes are deterministic, and successful values and rejection points are unique. Nothing
here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionLambdaOutcomeProperties
/-! Deterministic ordinary outcomes for guarded Core lambda expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- Every ordinary lambda branch exposes its selected leading marker. -/
theorem LambdaExpressionOrdinaryParses.marker_present
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
      blockOrdinary input expression output) :
    ∃ span afterMarker,
      ExactTokenParses (.keyword .lamKw) input span afterMarker := by
  cases parsed with
  | parsed markerSpan markerParsed => exact ⟨markerSpan, _, markerParsed⟩

/-- Every guarded lambda rejection also exposes its selected marker. -/
theorem LambdaExpressionRejects.marker_present
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects blockRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : LambdaExpressionRejects parameterOrdinary parameterRejects
      typeOrdinary typeRejects blockRejects input rejected) :
    ∃ span afterMarker,
      ExactTokenParses (.keyword .lamKw) input span afterMarker := by
  cases rejection with
  | parametersRejected markerSpan markerParsed
  | returnTypeRejected markerSpan markerParsed
  | bodyRejected markerSpan markerParsed =>
      exact ⟨markerSpan, _, markerParsed⟩

/-- Optional lambda returns have the unique output selected by arrow priority
and the supplied type outcome. -/
theorem OptionalLambdaReturnTypeOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Option Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input
      left afterLeft)
    (rightParsed : OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present arrowSpan arrowParsed typeParsed =>
          exact False.elim
            (absent_conflicts_token leftAbsent arrowParsed.1)
  | present leftArrowSpan leftArrow leftType =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (absent_conflicts_token rightAbsent leftArrow.1)
      | present rightArrowSpan rightArrow rightType =>
          have afterArrowEq := exactToken_output_unique leftArrow rightArrow
          subst afterArrowEq
          exact typeOutcomes.successOutputUnique leftType rightType

/-- A committed optional-return rejection excludes both arrow absence and
ordinary nested-type success. -/
theorem OptionalLambdaReturnTypeRejects.disjointOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input rejected : Remainder}
    (rejection : OptionalLambdaReturnTypeRejects typeOrdinary typeRejects
      input rejected) :
    ¬ ∃ returnType output,
      OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input returnType
        output := by
  rintro ⟨returnType, output, successful⟩
  cases rejection with
  | typeRejected rejectedArrowSpan rejectedArrow rejectedType =>
      cases successful with
      | absent arrowAbsent =>
          exact absent_conflicts_token arrowAbsent rejectedArrow.1
      | present successfulArrowSpan successfulArrow successfulType =>
          have afterArrowEq := exactToken_output_unique rejectedArrow
            successfulArrow
          subst afterArrowEq
          exact typeOutcomes.successRejectDisjoint rejectedType
            ⟨_, _, successfulType⟩

/-- Optional lambda return outcomes are deterministic whenever type outcomes
are. -/
theorem optionalLambdaReturnTypeDeterministicOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects) :
    DeterministicOutcomeSpec
      (OptionalLambdaReturnTypeOrdinaryParses typeOrdinary)
      (OptionalLambdaReturnTypeRejects typeOrdinary typeRejects) where
  successOutputUnique :=
    OptionalLambdaReturnTypeOrdinaryParses.output_unique typeOutcomes
  successRejectDisjoint :=
    OptionalLambdaReturnTypeRejects.disjointOrdinary typeOutcomes

/-- The existing clean optional-return grammar embeds through any supplied
clean-to-ordinary type bridge. -/
theorem OptionalLambdaReturnTypeParses.toOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    (typeToOrdinary : ∀ {input type output},
      TypeExprParses input type output → typeOrdinary input type output)
    {input output : Remainder} {returnType : Option Syntax.TypeExpr}
    (parsed : OptionalLambdaReturnTypeParses input returnType output) :
    OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input returnType
      output := by
  cases parsed with
  | absent arrowAbsent => exact .absent arrowAbsent
  | present arrowSpan arrowParsed typeParsed =>
      exact .present arrowSpan arrowParsed (typeToOrdinary typeParsed)

/-- Ordinary lambda success has the unique output selected successively by
parameters, return type, and body. -/
theorem LambdaExpressionOrdinaryParses.output_unique
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (parameterOutcomes : DeterministicOutcomeSpec parameterOrdinary
      parameterRejects)
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaExpressionOrdinaryParses parameterOrdinary
      typeOrdinary blockOrdinary input left afterLeft)
    (rightParsed : LambdaExpressionOrdinaryParses parameterOrdinary
      typeOrdinary blockOrdinary input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftParameters leftReturn leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightParameters rightReturn
            rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterParametersEq := TrailingDelimitedListParses.output_unique
            (opening := .leftParen) (closing := .rightParen)
            (elementParses := parameterOrdinary)
            parameterOutcomes.successOutputUnique leftParameters
              rightParameters
          subst afterParametersEq
          have afterReturnEq :=
            OptionalLambdaReturnTypeOrdinaryParses.output_unique typeOutcomes
              leftReturn rightReturn
          subst afterReturnEq
          exact blockOutcomes.successOutputUnique leftBody rightBody

/-- Exact guarded lambda rejection excludes every ordinary success. -/
theorem LambdaExpressionRejects.disjointOrdinary
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (parameterOutcomes : DeterministicOutcomeSpec parameterOrdinary
      parameterRejects)
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects)
    {input rejected : Remainder}
    (rejection : LambdaExpressionRejects parameterOrdinary parameterRejects
      typeOrdinary typeRejects blockRejects input rejected) :
    ¬ ∃ expression output,
      LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
        blockOrdinary input expression output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | parametersRejected rejectedMarkerSpan rejectedMarker rejectedParameters =>
      cases successful with
      | parsed successfulMarkerSpan successfulMarker successfulParameters
            successfulReturn successfulBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact rejectedParameters.disjointAllowEmptyTrailing
            parameterOutcomes (fun parsed => parsed)
              ⟨_, _, successfulParameters⟩
  | returnTypeRejected rejectedMarkerSpan rejectedMarker rejectedParameters
        rejectedReturn =>
      cases successful with
      | parsed successfulMarkerSpan successfulMarker successfulParameters
            successfulReturn successfulBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterParametersEq := TrailingDelimitedListParses.output_unique
            (opening := .leftParen) (closing := .rightParen)
            (elementParses := parameterOrdinary)
            parameterOutcomes.successOutputUnique rejectedParameters
              successfulParameters
          subst afterParametersEq
          exact rejectedReturn.disjointOrdinary typeOutcomes
            ⟨_, _, successfulReturn⟩
  | bodyRejected rejectedMarkerSpan rejectedMarker rejectedParameters
        rejectedReturn rejectedBody =>
      cases successful with
      | parsed successfulMarkerSpan successfulMarker successfulParameters
            successfulReturn successfulBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterParametersEq := TrailingDelimitedListParses.output_unique
            (opening := .leftParen) (closing := .rightParen)
            (elementParses := parameterOrdinary)
            parameterOutcomes.successOutputUnique rejectedParameters
              successfulParameters
          subst afterParametersEq
          have afterReturnEq :=
            OptionalLambdaReturnTypeOrdinaryParses.output_unique typeOutcomes
              rejectedReturn successfulReturn
          subst afterReturnEq
          exact blockOutcomes.successRejectDisjoint rejectedBody
            ⟨_, _, successfulBody⟩

/-- Lift deterministic subordinate outcomes through the guarded lambda
branch. -/
theorem lambdaExpressionDeterministicOutcomeSpec
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (parameterOutcomes : DeterministicOutcomeSpec parameterOrdinary
      parameterRejects)
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects) :
    DeterministicOutcomeSpec
      (LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
        blockOrdinary)
      (LambdaExpressionRejects parameterOrdinary parameterRejects
        typeOrdinary typeRejects blockRejects) where
  successOutputUnique := LambdaExpressionOrdinaryParses.output_unique
    parameterOutcomes typeOutcomes blockOutcomes
  successRejectDisjoint := LambdaExpressionRejects.disjointOrdinary
    parameterOutcomes typeOutcomes blockOutcomes

/-- The existing clean lambda grammar embeds through supplied subordinate
clean-to-ordinary bridges. -/
theorem LambdaExpressionParses.toOrdinary
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {blockClean blockOrdinary :
      Remainder → Syntax.Block → Remainder → Prop}
    (parameterToOrdinary : ∀ {input parameter output},
      LambdaParameterParses input parameter output →
        parameterOrdinary input parameter output)
    (typeToOrdinary : ∀ {input type output},
      TypeExprParses input type output → typeOrdinary input type output)
    (blockToOrdinary : ∀ {input block output},
      blockClean input block output → blockOrdinary input block output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : LambdaExpressionParses blockClean input expression output) :
    LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
      blockOrdinary input expression output := by
  cases parsed with
  | parsed markerSpan markerParsed parametersParsed returnTypeParsed
        bodyParsed =>
      exact .parsed markerSpan markerParsed
        (parametersParsed.mapElementRelation parameterToOrdinary)
        (returnTypeParsed.toOrdinary typeToOrdinary)
        (blockToOrdinary bodyParsed)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionLambdaExactnessProperties
/-! Exact optional return types and complete Core lambda expression ASTs. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Arrow priority fixes the optional lambda return type and its exact AST. -/
theorem OptionalLambdaReturnTypeOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Option Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input left afterLeft)
    (rightParsed : OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present _ rightArrow _ => exact False.elim (leftAbsent ⟨_, rightArrow.1⟩)
  | present _ leftArrow leftType =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent ⟨_, leftArrow.1⟩)
      | present _ rightArrow rightType =>
          have outputEq := leftArrow.output_unique rightArrow
          subst outputEq
          exact congrArg some (outcomes.successValueUnique leftType rightType)

/-- Exact parameters, types, and bodies fix a lambda's complete AST and spans. -/
theorem LambdaExpressionOrdinaryParses.value_unique
    {parameterOrdinary : Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (parameterOutcomes : ExactDeterministicOutcomeSpec parameterOrdinary parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
      blockOrdinary input left afterLeft)
    (rightParsed : LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
      blockOrdinary input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftParameters leftReturn leftBody =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightParameters rightReturn rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases (trailingDelimitedListExactOutcomeSpec .leftParen .rightParen
            parameterOutcomes).successResultUnique leftParameters rightParameters with
            ⟨parametersEq, parametersOutputEq⟩
          subst parametersEq
          subst parametersOutputEq
          have returnEq := leftReturn.value_unique typeOutcomes rightReturn
          have returnOutputEq := leftReturn.output_unique typeOutcomes.toDeterministicOutcomeSpec rightReturn
          subst returnEq
          subst returnOutputEq
          cases blockOutcomes.successValueUnique leftBody rightBody
          rfl

/-- Exact lambda successes fix both the complete AST and final remainder. -/
theorem LambdaExpressionOrdinaryParses.result_unique
    {parameterOrdinary : Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (parameterOutcomes : ExactDeterministicOutcomeSpec parameterOrdinary parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
      blockOrdinary input left afterLeft)
    (rightParsed : LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
      blockOrdinary input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique parameterOutcomes typeOutcomes blockOutcomes rightParsed,
    leftParsed.output_unique parameterOutcomes.toDeterministicOutcomeSpec
      typeOutcomes.toDeterministicOutcomeSpec blockOutcomes.toDeterministicOutcomeSpec rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomCoreStarterProperties
/-! Starter evidence retained by every ordered Core atom branch outcome. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary literal leaves expose the literal dispatcher guard. -/
theorem LiteralExpressionOrdinaryParses.coreLiteralStartsAt
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : LiteralExpressionOrdinaryParses input expression output) :
    CoreLiteralStartsAt input := by
  cases parsed with
  | parsed literalParsed =>
      cases literalParsed with
      | decimal token => exact Or.inl ⟨_, _, token⟩
      | hexadecimal token => exact Or.inr (Or.inl ⟨_, _, token⟩)
      | string token => exact Or.inr (Or.inr ⟨_, _, token⟩)

/-- Ordinary identifier leaves expose the Boolean-or-identifier guard. -/
theorem IdentifierExpressionOrdinaryParses.expressionNameStartsAt
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : IdentifierExpressionOrdinaryParses input expression output) :
    ExpressionNameStartsAt input := by
  cases parsed with
  | parsed nameParsed =>
      cases nameParsed with
      | boolean booleanParsed =>
          cases booleanParsed with
          | trueKeyword token => exact Or.inl ⟨_, token⟩
          | falseKeyword token => exact Or.inr (Or.inl ⟨_, token⟩)
      | identifier trueAbsent falseAbsent identifierParsed =>
          exact Or.inr (Or.inr ⟨_, _, identifierParsed.1⟩)

/-- Ordinary leading-dot construction exposes its selected marker. -/
theorem DotConstructorOrdinaryParses.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : DotConstructorOrdinaryParses nestedOrdinary input expression
      output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .dot } := by
  cases parsed with
  | parsed dotSpan dotParsed nameParsed argumentsParsed =>
      exact ⟨dotSpan, dotParsed.1⟩

/-- Rejected leading-dot construction retains the same selected marker. -/
theorem DotConstructorRejects.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : DotConstructorRejects nestedOrdinary nestedRejects input
      rejected) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .dot } := by
  cases rejection with
  | nameRejected dotSpan dotParsed nameRejected =>
      exact ⟨dotSpan, dotParsed.1⟩
  | argumentsRejected dotSpan dotParsed nameParsed argumentsRejected =>
      exact ⟨dotSpan, dotParsed.1⟩

/-- Ordinary proxy construction exposes its selected `@`. -/
theorem ProxyExpressionOrdinaryParses.marker_present
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ProxyExpressionOrdinaryParses typeOrdinary input expression
      output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .at } := by
  cases parsed with
  | parsed markerSpan markerParsed typeParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

/-- Rejected proxy construction retains its selected `@`. -/
theorem ProxyExpressionRejects.marker_present
    {typeRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : ProxyExpressionRejects typeRejects input rejected) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .at } := by
  cases rejection with
  | typeRejected markerSpan markerParsed typeRejected =>
      exact ⟨markerSpan, markerParsed.1⟩

/-- Ordinary parenthesized atoms expose their selected opening marker. -/
theorem ParenthesizedExpressionOrdinaryParses.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input
      expression output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftParen } := by
  cases parsed with
  | empty openingSpan closingSpan openingParsed closingParsed =>
      exact ⟨openingSpan, openingParsed.1⟩
  | group openingSpan closingSpan openingParsed closingAbsent elementParsed
        progress commaAbsent closingParsed =>
      exact ⟨openingSpan, openingParsed.1⟩
  | tuple openingSpan closingSpan openingParsed closingAbsent firstParsed
        progress tail =>
      exact ⟨openingSpan, openingParsed.1⟩

/-- Rejected parenthesized atoms retain their selected opening marker. -/
theorem ParenthesizedExpressionRejects.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : ParenthesizedExpressionRejects nestedOrdinary nestedRejects
      input rejected) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftParen } := by
  cases rejection with
  | firstRejected openingSpan openingParsed closingAbsent firstRejected =>
      exact ⟨openingSpan, openingParsed.1⟩
  | closingMissing openingSpan openingParsed closingAbsent firstParsed
        progress commaAbsent closingAbsent =>
      exact ⟨openingSpan, openingParsed.1⟩
  | tailRejected openingSpan openingParsed closingAbsent firstParsed progress
        tailRejected =>
      exact ⟨openingSpan, openingParsed.1⟩

/-- Ordinary arrays expose their selected opening bracket. -/
theorem ArrayLiteralExpressionOrdinaryParses.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input
      expression output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftBracket } := by
  cases parsed with
  | parsed valuesParsed =>
      cases valuesParsed with
      | empty openingSpan closingSpan openingToken closingToken =>
          exact ⟨openingSpan, openingToken⟩
      | nonempty closingAbsent nonemptyParsed =>
          rcases nonemptyParsed with ⟨openingSpan, first, afterFirst, rest,
            closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
            progress, tail, elementsEq, spanEq⟩
          exact ⟨openingSpan, openingToken⟩

/-- Rejected arrays retain their selected opening bracket. -/
theorem ArrayLiteralExpressionRejects.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : ArrayLiteralExpressionRejects nestedOrdinary nestedRejects
      input rejected) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftBracket } := by
  cases rejection with
  | present openingSpan openingToken valuesRejected =>
      exact ⟨openingSpan, openingToken⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomCoreSelectionProperties
/-! Unique branch selection for the ordered Core atom dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The seven successful branches in executable priority order. -/
inductive ExpressionAtomCoreBranch where
  | literal
  | identifier
  | dotConstructor
  | proxy
  | parenthesized
  | array
  | lambda
  deriving DecidableEq

/-- Parser-independent evidence selecting exactly one Core atom branch. -/
inductive ExpressionAtomCoreBranchSelected :
    ExpressionAtomCoreBranch → Remainder → Prop where
  | literal {input : Remainder}
      (starts : CoreLiteralStartsAt input) :
      ExpressionAtomCoreBranchSelected .literal input
  | identifier {input : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (starts : ExpressionNameStartsAt input) :
      ExpressionAtomCoreBranchSelected .identifier input
  | dotConstructor {input : Remainder} (markerSpan : SourceSpan)
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan, value := .symbol .dot }) :
      ExpressionAtomCoreBranchSelected .dotConstructor input
  | proxy {input : Remainder} (markerSpan : SourceSpan)
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan, value := .symbol .at }) :
      ExpressionAtomCoreBranchSelected .proxy input
  | parenthesized {input : Remainder} (markerSpan : SourceSpan)
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan, value := .symbol .leftParen }) :
      ExpressionAtomCoreBranchSelected .parenthesized input
  | array {input : Remainder} (markerSpan : SourceSpan)
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan, value := .symbol .leftBracket }) :
      ExpressionAtomCoreBranchSelected .array input
  | lambda {input : Remainder} (markerSpan : SourceSpan)
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBracket))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan, value := .keyword .lamKw }) :
      ExpressionAtomCoreBranchSelected .lambda input

private theorem absent_conflicts_token_variant {tokens : Array Token}
    {endIndex cursor : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex cursor kind)
    (present : TokenAt tokens endIndex cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Ordered guard evidence selects a unique branch. -/
theorem ExpressionAtomCoreBranchSelected.branch_unique
    {left right : ExpressionAtomCoreBranch} {input : Remainder}
    (leftSelected : ExpressionAtomCoreBranchSelected left input)
    (rightSelected : ExpressionAtomCoreBranchSelected right input) :
    left = right := by
  cases leftSelected with
  | literal leftLiteral =>
      cases rightSelected with
      | literal => rfl
      | identifier rightAbsent _ => exact False.elim (rightAbsent leftLiteral)
      | dotConstructor _ rightAbsent _ _ =>
          exact False.elim (rightAbsent leftLiteral)
      | proxy _ rightAbsent _ _ _ =>
          exact False.elim (rightAbsent leftLiteral)
      | parenthesized _ rightAbsent _ _ _ _ =>
          exact False.elim (rightAbsent leftLiteral)
      | array _ rightAbsent _ _ _ _ _ =>
          exact False.elim (rightAbsent leftLiteral)
      | lambda _ rightAbsent _ _ _ _ _ _ =>
          exact False.elim (rightAbsent leftLiteral)
  | identifier leftLiteralAbsent leftName =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier => rfl
      | dotConstructor _ _ rightNameAbsent _ =>
          exact False.elim (rightNameAbsent leftName)
      | proxy _ _ rightNameAbsent _ _ =>
          exact False.elim (rightNameAbsent leftName)
      | parenthesized _ _ rightNameAbsent _ _ _ =>
          exact False.elim (rightNameAbsent leftName)
      | array _ _ rightNameAbsent _ _ _ _ =>
          exact False.elim (rightNameAbsent leftName)
      | lambda _ _ rightNameAbsent _ _ _ _ _ =>
          exact False.elim (rightNameAbsent leftName)
  | dotConstructor leftSpan leftLiteralAbsent leftNameAbsent leftMarker =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier _ rightName => exact False.elim (leftNameAbsent rightName)
      | dotConstructor => rfl
      | proxy _ _ _ rightDotAbsent _ =>
          exact False.elim (absent_conflicts_token_variant rightDotAbsent leftMarker)
      | parenthesized _ _ _ rightDotAbsent _ _ =>
          exact False.elim (absent_conflicts_token_variant rightDotAbsent leftMarker)
      | array _ _ _ rightDotAbsent _ _ _ =>
          exact False.elim (absent_conflicts_token_variant rightDotAbsent leftMarker)
      | lambda _ _ _ rightDotAbsent _ _ _ _ =>
          exact False.elim (absent_conflicts_token_variant rightDotAbsent leftMarker)
  | proxy leftSpan leftLiteralAbsent leftNameAbsent leftDotAbsent leftMarker =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier _ rightName => exact False.elim (leftNameAbsent rightName)
      | dotConstructor _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token_variant leftDotAbsent rightMarker)
      | proxy => rfl
      | parenthesized _ _ _ _ rightAtAbsent _ =>
          exact False.elim (absent_conflicts_token_variant rightAtAbsent leftMarker)
      | array _ _ _ _ rightAtAbsent _ _ =>
          exact False.elim (absent_conflicts_token_variant rightAtAbsent leftMarker)
      | lambda _ _ _ _ rightAtAbsent _ _ _ =>
          exact False.elim (absent_conflicts_token_variant rightAtAbsent leftMarker)
  | parenthesized leftSpan leftLiteralAbsent leftNameAbsent leftDotAbsent
        leftAtAbsent leftMarker =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier _ rightName => exact False.elim (leftNameAbsent rightName)
      | dotConstructor _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token_variant leftDotAbsent rightMarker)
      | proxy _ _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token_variant leftAtAbsent rightMarker)
      | parenthesized => rfl
      | array _ _ _ _ _ rightParenAbsent _ =>
          exact False.elim
            (absent_conflicts_token_variant rightParenAbsent leftMarker)
      | lambda _ _ _ _ _ rightParenAbsent _ _ =>
          exact False.elim
            (absent_conflicts_token_variant rightParenAbsent leftMarker)
  | array leftSpan leftLiteralAbsent leftNameAbsent leftDotAbsent leftAtAbsent
        leftParenAbsent leftMarker =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier _ rightName => exact False.elim (leftNameAbsent rightName)
      | dotConstructor _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token_variant leftDotAbsent rightMarker)
      | proxy _ _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token_variant leftAtAbsent rightMarker)
      | parenthesized _ _ _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token_variant leftParenAbsent rightMarker)
      | array => rfl
      | lambda _ _ _ _ _ _ rightBracketAbsent _ =>
          exact False.elim
            (absent_conflicts_token_variant rightBracketAbsent leftMarker)
  | lambda leftSpan leftLiteralAbsent leftNameAbsent leftDotAbsent leftAtAbsent
        leftParenAbsent leftBracketAbsent leftMarker =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier _ rightName => exact False.elim (leftNameAbsent rightName)
      | dotConstructor _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token_variant leftDotAbsent rightMarker)
      | proxy _ _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token_variant leftAtAbsent rightMarker)
      | parenthesized _ _ _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token_variant leftParenAbsent rightMarker)
      | array _ _ _ _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token_variant leftBracketAbsent rightMarker)
      | lambda => rfl

/-- Every ordinary Core atom success carries some exact branch-selection
evidence.  The existential target keeps elimination proof-irrelevant. -/
theorem ExpressionAtomCoreOrdinaryParses.exists_branch_selected
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary
      parameterOrdinary typeOrdinary blockOrdinary input expression output) :
    ∃ branch, ExpressionAtomCoreBranchSelected branch input := by
  cases parsed with
  | literal parsed => exact ⟨.literal, .literal parsed.coreLiteralStartsAt⟩
  | identifier literalAbsent parsed =>
      exact ⟨.identifier,
        .identifier literalAbsent parsed.expressionNameStartsAt⟩
  | dotConstructor literalAbsent nameAbsent parsed =>
      rcases parsed.marker_present with ⟨span, marker⟩
      exact ⟨.dotConstructor,
        .dotConstructor span literalAbsent nameAbsent marker⟩
  | proxy literalAbsent nameAbsent dotAbsent parsed =>
      rcases parsed.marker_present with ⟨span, marker⟩
      exact ⟨.proxy,
        .proxy span literalAbsent nameAbsent dotAbsent marker⟩
  | parenthesized literalAbsent nameAbsent dotAbsent atAbsent parsed =>
      rcases parsed.marker_present with ⟨span, marker⟩
      exact ⟨.parenthesized, .parenthesized span literalAbsent nameAbsent
        dotAbsent atAbsent marker⟩
  | array literalAbsent nameAbsent dotAbsent atAbsent leftParenAbsent parsed =>
      rcases parsed.marker_present with ⟨span, marker⟩
      exact ⟨.array, .array span literalAbsent nameAbsent dotAbsent atAbsent
        leftParenAbsent marker⟩
  | lambda literalAbsent nameAbsent dotAbsent atAbsent leftParenAbsent
        leftBracketAbsent parsed =>
      rcases parsed.marker_present with ⟨span, afterMarker, marker⟩
      exact ⟨.lambda, .lambda span literalAbsent nameAbsent dotAbsent atAbsent
        leftParenAbsent leftBracketAbsent marker.1⟩

/-- The final dispatcher rejection excludes every successful branch
selection. -/
theorem ExpressionAtomCoreFinalRejects.disjointBranchSelected
    {input : Remainder} (rejection : ExpressionAtomCoreFinalRejects input) :
    ¬ ∃ branch, ExpressionAtomCoreBranchSelected branch input := by
  rintro ⟨branch, selected⟩
  cases rejection with
  | final literalAbsent nameAbsent dotAbsent atAbsent leftParenAbsent
        leftBracketAbsent lambdaAbsent =>
      cases selected with
      | literal starts => exact literalAbsent starts
      | identifier _ starts => exact nameAbsent starts
      | dotConstructor span _ _ marker =>
          exact absent_conflicts_token_variant dotAbsent marker
      | proxy span _ _ _ marker =>
          exact absent_conflicts_token_variant atAbsent marker
      | parenthesized span _ _ _ _ marker =>
          exact absent_conflicts_token_variant leftParenAbsent marker
      | array span _ _ _ _ _ marker =>
          exact absent_conflicts_token_variant leftBracketAbsent marker
      | lambda span _ _ _ _ _ _ marker =>
          exact absent_conflicts_token_variant lambdaAbsent marker

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomCoreSuccessProperties
/-! Output functionality of the ordered Core atom dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordered Core atom ordinary success has a unique output remainder whenever
all supplied subordinate outcomes do. -/
theorem ExpressionAtomCoreOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (parameterOutcomes : DeterministicOutcomeSpec parameterOrdinary
      parameterRejects)
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary
      parameterOrdinary typeOrdinary blockOrdinary input left afterLeft)
    (rightParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary
      parameterOrdinary typeOrdinary blockOrdinary input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | literal leftBranch =>
      cases rightParsed with
      | literal rightBranch =>
          exact literalExpressionDeterministicOutcomeSpec.successOutputUnique
            leftBranch rightBranch
      | identifier literalAbsent _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
      | dotConstructor literalAbsent _ _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
      | proxy literalAbsent _ _ _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
      | parenthesized literalAbsent _ _ _ _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
      | array literalAbsent _ _ _ _ _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
      | lambda literalAbsent _ _ _ _ _ _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
  | identifier leftLiteralAbsent leftBranch =>
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact identifierExpressionDeterministicOutcomeSpec
            |>.successOutputUnique leftBranch rightBranch
      | dotConstructor _ nameAbsent _ =>
          exact False.elim
            (nameAbsent leftBranch.expressionNameStartsAt)
      | proxy _ nameAbsent _ _ =>
          exact False.elim
            (nameAbsent leftBranch.expressionNameStartsAt)
      | parenthesized _ nameAbsent _ _ _ =>
          exact False.elim
            (nameAbsent leftBranch.expressionNameStartsAt)
      | array _ nameAbsent _ _ _ _ =>
          exact False.elim
            (nameAbsent leftBranch.expressionNameStartsAt)
      | lambda _ nameAbsent _ _ _ _ _ =>
          exact False.elim
            (nameAbsent leftBranch.expressionNameStartsAt)
  | dotConstructor leftLiteralAbsent leftNameAbsent leftBranch =>
      rcases leftBranch.marker_present with ⟨leftSpan, leftMarker⟩
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact False.elim
            (leftNameAbsent rightBranch.expressionNameStartsAt)
      | dotConstructor _ _ rightBranch =>
          exact (dotConstructorDeterministicOutcomeSpec nestedOutcomes)
            |>.successOutputUnique leftBranch rightBranch
      | proxy _ _ dotAbsent _ =>
          exact False.elim (absent_conflicts_token_variant dotAbsent leftMarker)
      | parenthesized _ _ dotAbsent _ _ =>
          exact False.elim (absent_conflicts_token_variant dotAbsent leftMarker)
      | array _ _ dotAbsent _ _ _ =>
          exact False.elim (absent_conflicts_token_variant dotAbsent leftMarker)
      | lambda _ _ dotAbsent _ _ _ _ =>
          exact False.elim (absent_conflicts_token_variant dotAbsent leftMarker)
  | proxy leftLiteralAbsent leftNameAbsent leftDotAbsent leftBranch =>
      rcases leftBranch.marker_present with ⟨leftSpan, leftMarker⟩
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact False.elim
            (leftNameAbsent rightBranch.expressionNameStartsAt)
      | dotConstructor _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token_variant leftDotAbsent rightMarker)
      | proxy _ _ _ rightBranch =>
          exact (proxyExpressionDeterministicOutcomeSpec typeOutcomes)
            |>.successOutputUnique leftBranch rightBranch
      | parenthesized _ _ _ atAbsent _ =>
          exact False.elim (absent_conflicts_token_variant atAbsent leftMarker)
      | array _ _ _ atAbsent _ _ =>
          exact False.elim (absent_conflicts_token_variant atAbsent leftMarker)
      | lambda _ _ _ atAbsent _ _ _ =>
          exact False.elim (absent_conflicts_token_variant atAbsent leftMarker)
  | parenthesized leftLiteralAbsent leftNameAbsent leftDotAbsent leftAtAbsent
        leftBranch =>
      rcases leftBranch.marker_present with ⟨leftSpan, leftMarker⟩
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact False.elim
            (leftNameAbsent rightBranch.expressionNameStartsAt)
      | dotConstructor _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token_variant leftDotAbsent rightMarker)
      | proxy _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token_variant leftAtAbsent rightMarker)
      | parenthesized _ _ _ _ rightBranch =>
          exact (parenthesizedExpressionDeterministicOutcomeSpec
            nestedOutcomes).successOutputUnique leftBranch rightBranch
      | array _ _ _ _ leftParenAbsent _ =>
          exact False.elim
            (absent_conflicts_token_variant leftParenAbsent leftMarker)
      | lambda _ _ _ _ leftParenAbsent _ _ =>
          exact False.elim
            (absent_conflicts_token_variant leftParenAbsent leftMarker)
  | array leftLiteralAbsent leftNameAbsent leftDotAbsent leftAtAbsent
        leftParenAbsent leftBranch =>
      rcases leftBranch.marker_present with ⟨leftSpan, leftMarker⟩
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact False.elim
            (leftNameAbsent rightBranch.expressionNameStartsAt)
      | dotConstructor _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token_variant leftDotAbsent rightMarker)
      | proxy _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token_variant leftAtAbsent rightMarker)
      | parenthesized _ _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token_variant leftParenAbsent rightMarker)
      | array _ _ _ _ _ rightBranch =>
          exact (arrayLiteralExpressionDeterministicOutcomeSpec
            nestedOutcomes).successOutputUnique leftBranch rightBranch
      | lambda _ _ _ _ _ leftBracketAbsent _ =>
          exact False.elim
            (absent_conflicts_token_variant leftBracketAbsent leftMarker)
  | lambda leftLiteralAbsent leftNameAbsent leftDotAbsent leftAtAbsent
        leftParenAbsent leftBracketAbsent leftBranch =>
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact False.elim
            (leftNameAbsent rightBranch.expressionNameStartsAt)
      | dotConstructor _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token_variant leftDotAbsent rightMarker)
      | proxy _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token_variant leftAtAbsent rightMarker)
      | parenthesized _ _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token_variant leftParenAbsent rightMarker)
      | array _ _ _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token_variant leftBracketAbsent rightMarker)
      | lambda _ _ _ _ _ _ rightBranch =>
          exact (lambdaExpressionDeterministicOutcomeSpec parameterOutcomes
            typeOutcomes blockOutcomes).successOutputUnique leftBranch
              rightBranch

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomCoreRejectionProperties
/-! Rejection exclusion for the ordered Core atom dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordered Core atom rejection excludes every ordinary success. -/
theorem ExpressionAtomCoreRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (parameterOutcomes : DeterministicOutcomeSpec parameterOrdinary
      parameterRejects)
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects)
    {input rejected : Remainder}
    (rejection : ExpressionAtomCoreRejects nestedOrdinary nestedRejects
      parameterOrdinary parameterRejects typeOrdinary typeRejects
        blockRejects input rejected) :
    ¬ ∃ expression output,
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | dotConstructor rejectedLiteralAbsent rejectedNameAbsent rejectedBranch =>
      rcases rejectedBranch.marker_present with
        ⟨rejectedSpan, rejectedMarker⟩
      cases successful with
      | literal successfulBranch =>
          exact rejectedLiteralAbsent successfulBranch.coreLiteralStartsAt
      | identifier _ successfulBranch =>
          exact rejectedNameAbsent successfulBranch.expressionNameStartsAt
      | dotConstructor _ _ successfulBranch =>
          exact (dotConstructorDeterministicOutcomeSpec nestedOutcomes)
            |>.successRejectDisjoint rejectedBranch
              ⟨_, _, successfulBranch⟩
      | proxy _ _ dotAbsent _ =>
          exact absent_conflicts_token_variant dotAbsent rejectedMarker
      | parenthesized _ _ dotAbsent _ _ =>
          exact absent_conflicts_token_variant dotAbsent rejectedMarker
      | array _ _ dotAbsent _ _ _ =>
          exact absent_conflicts_token_variant dotAbsent rejectedMarker
      | lambda _ _ dotAbsent _ _ _ _ =>
          exact absent_conflicts_token_variant dotAbsent rejectedMarker
  | proxy rejectedLiteralAbsent rejectedNameAbsent rejectedDotAbsent
        rejectedBranch =>
      rcases rejectedBranch.marker_present with
        ⟨rejectedSpan, rejectedMarker⟩
      cases successful with
      | literal successfulBranch =>
          exact rejectedLiteralAbsent successfulBranch.coreLiteralStartsAt
      | identifier _ successfulBranch =>
          exact rejectedNameAbsent successfulBranch.expressionNameStartsAt
      | dotConstructor _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token_variant rejectedDotAbsent successfulMarker
      | proxy _ _ _ successfulBranch =>
          exact (proxyExpressionDeterministicOutcomeSpec typeOutcomes)
            |>.successRejectDisjoint rejectedBranch
              ⟨_, _, successfulBranch⟩
      | parenthesized _ _ _ atAbsent _ =>
          exact absent_conflicts_token_variant atAbsent rejectedMarker
      | array _ _ _ atAbsent _ _ =>
          exact absent_conflicts_token_variant atAbsent rejectedMarker
      | lambda _ _ _ atAbsent _ _ _ =>
          exact absent_conflicts_token_variant atAbsent rejectedMarker
  | parenthesized rejectedLiteralAbsent rejectedNameAbsent rejectedDotAbsent
        rejectedAtAbsent rejectedBranch =>
      rcases rejectedBranch.marker_present with
        ⟨rejectedSpan, rejectedMarker⟩
      cases successful with
      | literal successfulBranch =>
          exact rejectedLiteralAbsent successfulBranch.coreLiteralStartsAt
      | identifier _ successfulBranch =>
          exact rejectedNameAbsent successfulBranch.expressionNameStartsAt
      | dotConstructor _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token_variant rejectedDotAbsent successfulMarker
      | proxy _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token_variant rejectedAtAbsent successfulMarker
      | parenthesized _ _ _ _ successfulBranch =>
          exact (parenthesizedExpressionDeterministicOutcomeSpec
            nestedOutcomes).successRejectDisjoint rejectedBranch
              ⟨_, _, successfulBranch⟩
      | array _ _ _ _ leftParenAbsent _ =>
          exact absent_conflicts_token_variant leftParenAbsent rejectedMarker
      | lambda _ _ _ _ leftParenAbsent _ _ =>
          exact absent_conflicts_token_variant leftParenAbsent rejectedMarker
  | array rejectedLiteralAbsent rejectedNameAbsent rejectedDotAbsent
        rejectedAtAbsent rejectedLeftParenAbsent rejectedBranch =>
      rcases rejectedBranch.marker_present with
        ⟨rejectedSpan, rejectedMarker⟩
      cases successful with
      | literal successfulBranch =>
          exact rejectedLiteralAbsent successfulBranch.coreLiteralStartsAt
      | identifier _ successfulBranch =>
          exact rejectedNameAbsent successfulBranch.expressionNameStartsAt
      | dotConstructor _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token_variant rejectedDotAbsent successfulMarker
      | proxy _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token_variant rejectedAtAbsent successfulMarker
      | parenthesized _ _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token_variant rejectedLeftParenAbsent
            successfulMarker
      | array _ _ _ _ _ successfulBranch =>
          exact (arrayLiteralExpressionDeterministicOutcomeSpec
            nestedOutcomes).successRejectDisjoint rejectedBranch
              ⟨_, _, successfulBranch⟩
      | lambda _ _ _ _ _ leftBracketAbsent _ =>
          exact absent_conflicts_token_variant leftBracketAbsent rejectedMarker
  | lambda rejectedLiteralAbsent rejectedNameAbsent rejectedDotAbsent
        rejectedAtAbsent rejectedLeftParenAbsent rejectedLeftBracketAbsent
        rejectedBranch =>
      cases successful with
      | literal successfulBranch =>
          exact rejectedLiteralAbsent successfulBranch.coreLiteralStartsAt
      | identifier _ successfulBranch =>
          exact rejectedNameAbsent successfulBranch.expressionNameStartsAt
      | dotConstructor _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token_variant rejectedDotAbsent successfulMarker
      | proxy _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token_variant rejectedAtAbsent successfulMarker
      | parenthesized _ _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token_variant rejectedLeftParenAbsent
            successfulMarker
      | array _ _ _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token_variant rejectedLeftBracketAbsent
            successfulMarker
      | lambda _ _ _ _ _ _ successfulBranch =>
          exact (lambdaExpressionDeterministicOutcomeSpec parameterOutcomes
            typeOutcomes blockOutcomes).successRejectDisjoint rejectedBranch
              ⟨_, _, successfulBranch⟩
  | final finalRejected =>
      exact finalRejected.disjointBranchSelected
        successful.exists_branch_selected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomCoreOutcomeProperties
/-! Deterministic outcome contract for the ordered Core atom dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lift deterministic nested expression, lambda-parameter, type, and block
outcomes through all seven ordered Core atom branches and final rejection. -/
theorem expressionAtomCoreDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (parameterOutcomes : DeterministicOutcomeSpec parameterOrdinary
      parameterRejects)
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects) :
    DeterministicOutcomeSpec
      (ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary)
      (ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects) where
  successOutputUnique := ExpressionAtomCoreOrdinaryParses.output_unique
    nestedOutcomes parameterOutcomes typeOutcomes blockOutcomes
  successRejectDisjoint := ExpressionAtomCoreRejects.disjointOrdinary
    nestedOutcomes parameterOutcomes typeOutcomes blockOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionStepOutcomeProperties
/-! Deterministic outcomes for one complete Core expression step. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Compose subordinate deterministic contracts through atom dispatch,
public recovery, postfix parsing, and the complete operator stack. -/
theorem coreExpressionStepDeterministicOutcomeSpec
    (relations : CoreExpressionStepRelations)
    (nestedOutcomes : DeterministicOutcomeSpec relations.nestedOrdinary
      relations.nestedRejects)
    (parameterOutcomes : DeterministicOutcomeSpec relations.parameterOrdinary
      relations.parameterRejects)
    (typeOutcomes : DeterministicOutcomeSpec relations.typeOrdinary
      relations.typeRejects)
    (blockOutcomes : DeterministicOutcomeSpec relations.blockOrdinary
      relations.blockRejects) :
    DeterministicOutcomeSpec
      (CoreExpressionStepOrdinaryParses relations)
      (CoreExpressionStepRejects relations) := by
  have coreOutcomes : DeterministicOutcomeSpec relations.atomCoreOrdinary
      relations.atomCoreRejects :=
    expressionAtomCoreDeterministicOutcomeSpec nestedOutcomes
      parameterOutcomes typeOutcomes blockOutcomes
  have atomOutcomes : DeterministicOutcomeSpec relations.atomOrdinary
      relations.atomRejects :=
    expressionAtomDeterministicOutcomeSpec coreOutcomes
  have postfixOutcomes : DeterministicOutcomeSpec relations.postfixOrdinary
      relations.postfixRejects :=
    expressionPostfixDeterministicOutcomeSpec atomOutcomes nestedOutcomes
  exact expressionLayerDeterministicOutcomeSpec nestedOutcomes postfixOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionPostfixSuccessExactnessProperties
/-! Exact success values for maximal postfix tails at one fixed base AST. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- At one fixed base, exact nested expressions fix the complete postfix AST
and remainder, including index delimiters, call arguments, and field spans. -/
theorem PostfixTailParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {base left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : PostfixTailParses nestedOrdinary input base left afterLeft)
    (rightParsed : PostfixTailParses nestedOrdinary input base right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | index openingSpan closingSpan openingToken indexParsed closingToken
            tail =>
          exact False.elim (leftAbsent.1 ⟨openingSpan, openingToken.1⟩)
      | call indexAbsent argumentsParsed tail =>
          exact False.elim (leftAbsent.2.1 argumentsParsed.opening_present)
      | field dotSpan indexAbsent callAbsent dotToken nameParsed tail =>
          exact False.elim (leftAbsent.2.2 ⟨dotSpan, dotToken.1⟩)
  | index leftOpeningSpan leftClosingSpan leftOpening leftIndex leftClosing
        leftTail ih =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent.1 ⟨leftOpeningSpan, leftOpening.1⟩)
      | index rightOpeningSpan rightClosingSpan rightOpening rightIndex
            rightClosing rightTail =>
          rcases leftOpening.result_unique rightOpening with
            ⟨openingEq, inputEq⟩
          subst openingEq
          subst inputEq
          rcases nestedOutcomes.successResultUnique leftIndex rightIndex with
            ⟨indexEq, inputEq⟩
          subst indexEq
          subst inputEq
          rcases leftClosing.result_unique rightClosing with
            ⟨closingEq, inputEq⟩
          subst closingEq
          subst inputEq
          exact ih rightTail
      | call rightIndexAbsent argumentsParsed tail =>
          exact False.elim (rightIndexAbsent ⟨leftOpeningSpan, leftOpening.1⟩)
      | field dotSpan rightIndexAbsent callAbsent dotToken nameParsed tail =>
          exact False.elim (rightIndexAbsent ⟨leftOpeningSpan, leftOpening.1⟩)
  | call leftIndexAbsent leftArguments leftTail ih =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent.2.1 leftArguments.opening_present)
      | index openingSpan closingSpan rightOpening indexParsed closingToken
            tail =>
          exact False.elim (leftIndexAbsent ⟨openingSpan, rightOpening.1⟩)
      | call rightIndexAbsent rightArguments rightTail =>
          rcases (noTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
              nestedOutcomes).successResultUnique leftArguments rightArguments
            with ⟨argumentsEq, inputEq⟩
          subst argumentsEq
          subst inputEq
          exact ih rightTail
      | field dotSpan rightIndexAbsent rightCallAbsent dotToken nameParsed
            tail =>
          exact False.elim (rightCallAbsent leftArguments.opening_present)
  | field leftDotSpan leftIndexAbsent leftCallAbsent leftDot leftName leftTail
        ih =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent.2.2 ⟨leftDotSpan, leftDot.1⟩)
      | index openingSpan closingSpan rightOpening indexParsed closingToken
            tail =>
          exact False.elim (leftIndexAbsent ⟨openingSpan, rightOpening.1⟩)
      | call rightIndexAbsent rightArguments tail =>
          exact False.elim (leftCallAbsent rightArguments.opening_present)
      | field rightDotSpan rightIndexAbsent rightCallAbsent rightDot rightName
            rightTail =>
          rcases leftDot.result_unique rightDot with ⟨dotEq, inputEq⟩
          subst dotEq
          subst inputEq
          rcases leftName.result_unique rightName with ⟨nameEq, inputEq⟩
          subst nameEq
          subst inputEq
          exact ih rightTail

/-- A maximal postfix tail at a fixed base has one complete expression AST. -/
theorem PostfixTailParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {base left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : PostfixTailParses nestedOrdinary input base left afterLeft)
    (rightParsed : PostfixTailParses nestedOrdinary input base right afterRight) :
    left = right :=
  (leftParsed.result_unique nestedOutcomes rightParsed).1

/-- Exact atoms and nested expressions fix a complete postfix expression and
its final remainder. -/
theorem ExpressionPostfixOrdinaryParses.result_unique
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : ExactDeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input left afterLeft)
    (rightParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input right afterRight) : left = right ∧ afterLeft = afterRight := by
  rcases leftParsed with ⟨leftBase, leftAfterAtom, leftAtom, leftTail⟩
  rcases rightParsed with ⟨rightBase, rightAfterAtom, rightAtom, rightTail⟩
  rcases atomOutcomes.successResultUnique leftAtom rightAtom with
    ⟨baseEq, inputEq⟩
  subst baseEq
  subst inputEq
  exact leftTail.result_unique nestedOutcomes rightTail

/-- A complete ordinary postfix success fixes its full AST value. -/
theorem ExpressionPostfixOrdinaryParses.value_unique
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : ExactDeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input left afterLeft)
    (rightParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input right afterRight) : left = right :=
  (ExpressionPostfixOrdinaryParses.result_unique atomOutcomes nestedOutcomes
    leftParsed rightParsed).1

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionPostfixRejectionExactnessProperties
/-! Exact postfix rejection endpoints, independent of the accumulated base AST. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem postfix_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem postfix_absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Exact nested outcomes fix every postfix rejection endpoint independently
of the accumulated base, retaining index/call/field selection priority. -/
theorem PostfixTailRejects.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input left right : Remainder} {leftBase rightBase : Syntax.Expr}
    (leftRejected : PostfixTailRejects nestedOrdinary nestedRejects input
      leftBase left)
    (rightRejected : PostfixTailRejects nestedOrdinary nestedRejects input
      rightBase right) : left = right := by
  have argumentsOutcomes := noTrailingDelimitedListExactOutcomeSpec
    .leftParen .rightParen nestedOutcomes
  induction leftRejected generalizing rightBase right <;>
    cases rightRejected <;>
    grind (ematch := 20) [postfix_absent_conflicts_exact,
      postfix_absent_conflicts_token, ExactTokenParses.output_unique,
      nestedOutcomes.successOutputUnique, nestedOutcomes.successRejectDisjoint,
      nestedOutcomes.rejectOutputUnique,
      NoTrailingDelimitedListParses.opening_present,
      argumentsOutcomes.successOutputUnique,
      argumentsOutcomes.successRejectDisjoint,
      argumentsOutcomes.rejectOutputUnique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique]

/-- Exact atom and nested outcomes fix the first rejecting endpoint of the
complete atom-plus-postfix sequence. -/
theorem ExpressionPostfixRejects.output_unique
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : ExactDeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input left right : Remainder}
    (leftRejected : ExpressionPostfixRejects atomOrdinary nestedOrdinary
      atomRejects nestedRejects input left)
    (rightRejected : ExpressionPostfixRejects atomOrdinary nestedOrdinary
      atomRejects nestedRejects input right) : left = right := by
  cases leftRejected with
  | atomRejected leftAtom =>
      cases rightRejected with
      | atomRejected rightAtom =>
          exact atomOutcomes.rejectOutputUnique leftAtom rightAtom
      | tailRejected rightAtom rightTail =>
          exact False.elim
            (atomOutcomes.successRejectDisjoint leftAtom ⟨_, _, rightAtom⟩)
  | tailRejected leftAtom leftTail =>
      cases rightRejected with
      | atomRejected rightAtom =>
          exact False.elim
            (atomOutcomes.successRejectDisjoint rightAtom ⟨_, _, leftAtom⟩)
      | tailRejected rightAtom rightTail =>
          have inputEq := atomOutcomes.successOutputUnique leftAtom rightAtom
          subst inputEq
          exact leftTail.output_unique nestedOutcomes rightTail

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionPostfixExactnessProperties
/-! Exact ordinary outcomes for Core atom-plus-postfix expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- At any fixed base AST, a maximal postfix tail has exact success values,
final remainders, and rejection endpoints. -/
theorem postfixTailExactOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (base : Syntax.Expr) :
    ExactDeterministicOutcomeSpec
      (fun input expression output =>
        PostfixTailOrdinaryParses nestedOrdinary input base expression output)
      (fun input rejected =>
        PostfixTailRejects nestedOrdinary nestedRejects input base rejected) where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique nestedOutcomes.toDeterministicOutcomeSpec
      rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨expression, output, parsed⟩
    exact rejection.disjointOrdinary nestedOutcomes.toDeterministicOutcomeSpec
      ⟨base, expression, output, parsed⟩
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.value_unique nestedOutcomes rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact leftRejected.output_unique nestedOutcomes rightRejected

/-- Exact atom and nested-expression outcomes lift through every maximal
index, call, and field suffix to a complete exact postfix outcome. -/
theorem expressionPostfixExactOutcomeSpec
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : ExactDeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    ExactDeterministicOutcomeSpec
      (ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary)
      (ExpressionPostfixRejects atomOrdinary nestedOrdinary atomRejects
        nestedRejects) where
  toDeterministicOutcomeSpec := expressionPostfixDeterministicOutcomeSpec
    atomOutcomes.toDeterministicOutcomeSpec
    nestedOutcomes.toDeterministicOutcomeSpec
  successValueUnique := ExpressionPostfixOrdinaryParses.value_unique
    atomOutcomes nestedOutcomes
  rejectOutputUnique := ExpressionPostfixRejects.output_unique
    atomOutcomes nestedOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionSimpleAtomExactnessProperties
/-! Exact values of leading-dot, proxy, and array Core expression atoms. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Opening-parenthesis priority fixes the optional constructor arguments. -/
theorem OptionalDotConstructorArgumentsOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Option (DelimitedList Syntax.Expr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalDotConstructorArgumentsOrdinaryParses nestedOrdinary
      input left afterLeft)
    (rightParsed : OptionalDotConstructorArgumentsOrdinaryParses nestedOrdinary
      input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightArguments => exact False.elim (leftAbsent rightArguments.opening_present)
  | present leftArguments =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent leftArguments.opening_present)
      | present rightArguments =>
          exact congrArg some (leftArguments.value_unique outcomes rightArguments)

/-- Leading-dot construction fixes its marker, Boolean-first name, and arguments. -/
theorem DotConstructorOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : DotConstructorOrdinaryParses nestedOrdinary input left afterLeft)
    (rightParsed : DotConstructorOrdinaryParses nestedOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftDot leftName leftArguments =>
      cases rightParsed with
      | parsed rightSpan rightDot rightName rightArguments =>
          rcases leftDot.result_unique rightDot with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases ExpressionNameOrdinaryParses.result_unique leftName rightName with
            ⟨nameEq, nameOutputEq⟩
          subst nameEq
          subst nameOutputEq
          cases OptionalDotConstructorArgumentsOrdinaryParses.value_unique
            outcomes leftArguments rightArguments
          rfl

/-- Leading-dot construction fixes its complete AST and final remainder. -/
theorem DotConstructorOrdinaryParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : DotConstructorOrdinaryParses nestedOrdinary input left afterLeft)
    (rightParsed : DotConstructorOrdinaryParses nestedOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- Exact type outcomes fix the proxy marker, type, and complete covering span. -/
theorem ProxyExpressionOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ProxyExpressionOrdinaryParses typeOrdinary input left afterLeft)
    (rightParsed : ProxyExpressionOrdinaryParses typeOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftType =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightType =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          cases outcomes.successValueUnique leftType rightType
          rfl

/-- Exact no-trailing nested lists fix the complete array AST and span. -/
theorem ArrayLiteralExpressionOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input left afterLeft)
    (rightParsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftValues =>
      cases rightParsed with
      | parsed rightValues =>
          cases leftValues.value_unique outcomes rightValues
          rfl

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomCoreExactnessProperties
/-! Exact successful ASTs of the seven ordered Core expression-atom branches. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordered branch selection and exact subordinates fix the complete atom-core AST. -/
theorem ExpressionAtomCoreOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {parameterOrdinary : Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (parameterOutcomes : ExactDeterministicOutcomeSpec parameterOrdinary parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
      typeOrdinary blockOrdinary input left afterLeft)
    (rightParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
      typeOrdinary blockOrdinary input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind (ematch := 12) [LiteralExpressionOrdinaryParses.value_unique,
      IdentifierExpressionOrdinaryParses.value_unique,
      DotConstructorOrdinaryParses.value_unique nestedOutcomes,
      ProxyExpressionOrdinaryParses.value_unique typeOutcomes,
      ParenthesizedExpressionOrdinaryParses.value_unique nestedOutcomes,
      ArrayLiteralExpressionOrdinaryParses.value_unique nestedOutcomes,
      LambdaExpressionOrdinaryParses.value_unique parameterOutcomes typeOutcomes blockOutcomes,
      LiteralExpressionOrdinaryParses.coreLiteralStartsAt,
      IdentifierExpressionOrdinaryParses.expressionNameStartsAt,
      DotConstructorOrdinaryParses.marker_present,
      ProxyExpressionOrdinaryParses.marker_present,
      ParenthesizedExpressionOrdinaryParses.marker_present,
      ArrayLiteralExpressionOrdinaryParses.marker_present, absent_conflicts_token_variant]

/-- Exact atom-core successes fix the complete AST and final remainder. -/
theorem ExpressionAtomCoreOrdinaryParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {parameterOrdinary : Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (parameterOutcomes : ExactDeterministicOutcomeSpec parameterOrdinary parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
      typeOrdinary blockOrdinary input left afterLeft)
    (rightParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
      typeOrdinary blockOrdinary input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique nestedOutcomes parameterOutcomes typeOutcomes blockOutcomes rightParsed,
    leftParsed.output_unique nestedOutcomes.toDeterministicOutcomeSpec
      parameterOutcomes.toDeterministicOutcomeSpec typeOutcomes.toDeterministicOutcomeSpec
      blockOutcomes.toDeterministicOutcomeSpec rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end
