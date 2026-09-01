import Solcore.Syntax.DeclarativeCoreExpressionLambdaOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedTrailingOutcomeProperties

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
