import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Grammar.Declarations
import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Internal.ParameterOutcomes
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.SignatureOutcomes
import Solcore.Syntax.Internal.DeriveOutcomes

/-!
Properties of the declarative grammar of enums, traits, function declarations and contract members: outcomes are deterministic, and successful values and rejection points are unique. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeEnumConstructorOutcomeProperties
/-! Deterministic exact ordinary outcomes for enum constructors. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem noTrailing_opening_present {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : NoTrailingDelimitedListParses opening closing elementParses input
      values output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol opening } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- The allow-empty, no-trailing constructor-field list inherits the public
Core type outcome. -/
theorem enumConstructorFieldListDeterministicOutcomeSpec :
    DeterministicOutcomeSpec
      (NoTrailingDelimitedListParses .leftParen .rightParen
        TypeExprOrdinaryParses)
      (DelimitedListRejects .leftParen .rightParen true false
        TypeExprOrdinaryParses TypeExprRejects) :=
  noTrailingDelimitedListDeterministicOutcomeSpec .leftParen .rightParen
    typeExprDeterministicOutcomeSpec

/-- Optional constructor fields have one final remainder. -/
theorem OptionalEnumConstructorFieldsOrdinaryParses.output_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.TypeExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalEnumConstructorFieldsOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalEnumConstructorFieldsOrdinaryParses input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightFields =>
          rcases noTrailing_opening_present rightFields with
            ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token leftAbsent openingPresent)
  | present leftFields =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases noTrailing_opening_present leftFields with
            ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token rightAbsent openingPresent)
      | present rightFields =>
          exact enumConstructorFieldListDeterministicOutcomeSpec
            |>.successOutputUnique leftFields rightFields

/-- A committed constructor-field rejection excludes absent and present
ordinary success. -/
theorem OptionalEnumConstructorFieldsRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalEnumConstructorFieldsRejects input rejected) :
    ¬ ∃ fields output,
      OptionalEnumConstructorFieldsOrdinaryParses input fields output := by
  rintro ⟨fields, output, successful⟩
  cases rejection with
  | present openingPresent fieldsRejected =>
      cases successful with
      | absent openingAbsent =>
          rcases openingPresent with ⟨span, openingToken⟩
          exact absent_conflicts_token openingAbsent openingToken
      | present fieldsParsed =>
          exact enumConstructorFieldListDeterministicOutcomeSpec
            |>.successRejectDisjoint fieldsRejected ⟨_, _, fieldsParsed⟩

/-- Optional enum-constructor fields have deterministic and exclusive ordinary
outcomes. -/
theorem optionalEnumConstructorFieldsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalEnumConstructorFieldsOrdinaryParses
      OptionalEnumConstructorFieldsRejects where
  successOutputUnique :=
    OptionalEnumConstructorFieldsOrdinaryParses.output_unique
  successRejectDisjoint :=
    OptionalEnumConstructorFieldsRejects.disjointOrdinary

/-- Ordinary enum-constructor success has one final remainder. -/
theorem EnumConstructorOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumConstructorOrdinaryParses input left afterLeft)
    (rightParsed : EnumConstructorOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftName leftFields =>
      cases rightParsed with
      | parsed rightName rightFields =>
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          exact OptionalEnumConstructorFieldsOrdinaryParses.output_unique
            leftFields rightFields

/-- Exact enum-constructor rejection excludes every ordinary success. -/
theorem EnumConstructorRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : EnumConstructorRejects input rejected) :
    ¬ ∃ constructor output,
      EnumConstructorOrdinaryParses input constructor output := by
  rintro ⟨constructor, output, successful⟩
  cases rejection with
  | nameRejected nameRejected =>
      cases successful with
      | parsed nameParsed fieldsParsed =>
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, nameParsed⟩
  | fieldsRejected rejectedName fieldsRejected =>
      cases successful with
      | parsed successfulName successfulFields =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact optionalEnumConstructorFieldsDeterministicOutcomeSpec
            |>.successRejectDisjoint fieldsRejected
              ⟨_, _, successfulFields⟩

/-- Enum constructors have deterministic and exclusive ordinary outcomes. -/
theorem enumConstructorDeterministicOutcomeSpec :
    DeterministicOutcomeSpec EnumConstructorOrdinaryParses
      EnumConstructorRejects where
  successOutputUnique := EnumConstructorOrdinaryParses.output_unique
  successRejectDisjoint := EnumConstructorRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeEnumBodyOutcomeProperties
/-! Deterministic exact ordinary outcomes for canonical enum bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Possibly-empty, trailing-comma enum bodies have deterministic and
exclusive ordinary outcomes. -/
theorem enumBodyDeterministicOutcomeSpec :
    DeterministicOutcomeSpec EnumBodyOrdinaryOutcomeParses EnumBodyRejects := by
  have outcomes := trailingDelimitedListDeterministicOutcomeSpec
    .leftBrace .rightBrace enumConstructorDeterministicOutcomeSpec
  constructor
  · intro input left right afterLeft afterRight leftParsed rightParsed
    exact outcomes.successOutputUnique leftParsed rightParsed
  · intro input rejected rejection
    rintro ⟨body, output, parsed⟩
    exact outcomes.successRejectDisjoint rejection
      ⟨{ span := body.1, elements := body.2 }, output, parsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeEnumDeclarationOutcomeProperties
/-! Deterministic exact ordinary outcomes for complete enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem enumBody_output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftConstructors rightConstructors : List Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumBodyOrdinaryParses input leftSpan leftConstructors
      afterLeft)
    (rightParsed : EnumBodyOrdinaryParses input rightSpan rightConstructors
      afterRight) : afterLeft = afterRight :=
  enumBodyDeterministicOutcomeSpec.successOutputUnique
    (left := (leftSpan, leftConstructors))
    (right := (rightSpan, rightConstructors)) leftParsed rightParsed

private theorem enumBody_reject_disjoint
    {input rejected : Remainder} (rejection : EnumBodyRejects input rejected) :
    ¬ ∃ span constructors output,
      EnumBodyOrdinaryParses input span constructors output := by
  rintro ⟨span, constructors, output, parsed⟩
  exact enumBodyDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨(span, constructors), output, parsed⟩

/-- Ordinary enum-declaration success has one final remainder. -/
theorem EnumDeclOrdinaryParses.output_unique
    (deriveAttribute : Option Syntax.DeriveAttribute)
    {input : Remainder} {left right : Syntax.EnumDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumDeclOrdinaryParses deriveAttribute input left afterLeft)
    (rightParsed : EnumDeclOrdinaryParses deriveAttribute input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftParameters leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightParameters
            rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterParametersEq := leftParameters.output_unique
            rightParameters
          subst afterParametersEq
          exact enumBody_output_unique leftBody rightBody

/-- Exact enum-declaration rejection excludes every ordinary success. -/
theorem EnumDeclRejects.disjointOrdinary
    (deriveAttribute : Option Syntax.DeriveAttribute)
    {input rejected : Remainder}
    (rejection : EnumDeclRejects input rejected) :
    ¬ ∃ declaration output,
      EnumDeclOrdinaryParses deriveAttribute input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulName
        successfulParameters successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | nameRejected rejectedMarkerSpan rejectedMarker nameRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | parametersRejected rejectedMarkerSpan rejectedMarker rejectedName
            parametersRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact optionalGenericParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint parametersRejected
              ⟨_, _, successfulParameters⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedParameters bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          exact enumBody_reject_disjoint bodyRejected
            ⟨_, _, _, successfulBody⟩

/-- Enum declarations have deterministic and exclusive ordinary outcomes. -/
theorem enumDeclDeterministicOutcomeSpec
    (deriveAttribute : Option Syntax.DeriveAttribute) :
    DeterministicOutcomeSpec (EnumDeclOrdinaryParses deriveAttribute)
      EnumDeclRejects where
  successOutputUnique := EnumDeclOrdinaryParses.output_unique deriveAttribute
  successRejectDisjoint := EnumDeclRejects.disjointOrdinary deriveAttribute

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplHeadArgumentsOutcomeProperties
/-! Deterministic exact outcomes for implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary implementation head arguments have one final remainder. -/
theorem ImplHeadArgumentsOrdinaryParses.output_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplHeadArgumentsOrdinaryParses input left afterLeft)
    (rightParsed : ImplHeadArgumentsOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold ImplHeadArgumentsOrdinaryParses at leftParsed rightParsed
  exact NonemptyTrailingDelimitedListParses.output_unique
    (opening := .less) (closing := .greater)
    (elementParses := TypeExprOrdinaryParses)
    typeExprDeterministicOutcomeSpec.successOutputUnique leftParsed rightParsed

/-- Exact list rejection excludes every ordinary implementation argument
success. -/
theorem ImplHeadArgumentsRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ImplHeadArgumentsRejects input rejected) :
    ¬ ∃ arguments output,
      ImplHeadArgumentsOrdinaryParses input arguments output := by
  intro successful
  rcases successful with ⟨arguments, output, parsed⟩
  exact DelimitedListRejects.disjointNonemptyTrailing
    typeExprDeterministicOutcomeSpec (fun ordinary => ordinary) rejection
      ⟨_, _, parsed⟩

/-- Implementation head arguments have deterministic and exclusive broad
ordinary outcomes. -/
theorem implHeadArgumentsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ImplHeadArgumentsOrdinaryParses
      ImplHeadArgumentsRejects where
  successOutputUnique := ImplHeadArgumentsOrdinaryParses.output_unique
  successRejectDisjoint := ImplHeadArgumentsRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplDefaultMarkerOutcomeProperties
/-! Deterministic exact outcomes for the optional implementation marker. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Optional implementation markers have one final remainder. -/
theorem OptionalImplDefaultMarkerOrdinaryParses.output_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalImplDefaultMarkerOrdinaryParses input left afterLeft)
    (rightParsed : OptionalImplDefaultMarkerOrdinaryParses input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightMarker =>
          exact False.elim (absent_conflicts_exact leftAbsent rightMarker)
  | present leftSpan leftMarker =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftMarker)
      | present rightSpan rightMarker =>
          exact exactToken_output_unique leftMarker rightMarker

/-- The impossible reject relation is disjoint from every ordinary success. -/
theorem OptionalImplDefaultMarkerRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalImplDefaultMarkerRejects input rejected) :
    ¬ ∃ marker output,
      OptionalImplDefaultMarkerOrdinaryParses input marker output := by
  exact False.elim rejection

/-- Optional implementation markers have deterministic ordinary outcomes and
cannot reject. -/
theorem optionalImplDefaultMarkerDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalImplDefaultMarkerOrdinaryParses
      OptionalImplDefaultMarkerRejects where
  successOutputUnique :=
    OptionalImplDefaultMarkerOrdinaryParses.output_unique
  successRejectDisjoint :=
    OptionalImplDefaultMarkerRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplDefaultMarkerExactnessProperties
/-! Exact outcomes for the optional leading `default` implementation marker. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem implDefault_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- The optional implementation marker fixes its absent or present span. -/
theorem OptionalImplDefaultMarkerOrdinaryParses.value_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalImplDefaultMarkerOrdinaryParses input left afterLeft)
    (rightParsed : OptionalImplDefaultMarkerOrdinaryParses input right
      afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightMarker =>
          exact False.elim
            (implDefault_absent_conflicts_exact leftAbsent rightMarker)
  | present leftSpan leftMarker =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (implDefault_absent_conflicts_exact rightAbsent leftMarker)
      | present rightSpan rightMarker =>
          rw [leftMarker.span_unique rightMarker]

/-- The optional implementation marker fixes its value and final remainder. -/
theorem OptionalImplDefaultMarkerOrdinaryParses.result_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalImplDefaultMarkerOrdinaryParses input left afterLeft)
    (rightParsed : OptionalImplDefaultMarkerOrdinaryParses input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The impossible optional-marker rejection has a unique endpoint. -/
theorem OptionalImplDefaultMarkerRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalImplDefaultMarkerRejects input left)
    (_rightRejected : OptionalImplDefaultMarkerRejects input right) :
    left = right :=
  False.elim leftRejected

/-- Optional implementation markers have fully exact outcomes. -/
theorem optionalImplDefaultMarkerExactOutcomeSpec :
    ExactDeterministicOutcomeSpec OptionalImplDefaultMarkerOrdinaryParses
      OptionalImplDefaultMarkerRejects where
  toDeterministicOutcomeSpec :=
    optionalImplDefaultMarkerDeterministicOutcomeSpec
  successValueUnique := OptionalImplDefaultMarkerOrdinaryParses.value_unique
  rejectOutputUnique := OptionalImplDefaultMarkerRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTraitMethodOutcomeProperties
/-! Deterministic exact ordinary outcomes for signature-only trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary trait-method success has one final remainder. -/
theorem TraitMethodOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodOrdinaryParses input left afterLeft)
    (rightParsed : TraitMethodOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftSemicolonSpan leftSignature leftSemicolon =>
      cases rightParsed with
      | parsed rightSemicolonSpan rightSignature rightSemicolon =>
          have afterSignatureEq :=
            functionSignatureDeterministicOutcomeSpec.successOutputUnique
              leftSignature rightSignature
          subst afterSignatureEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact first-stage trait-method rejection excludes every ordinary success. -/
theorem TraitMethodRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : TraitMethodRejects input rejected) :
    ¬ ∃ method output, TraitMethodOrdinaryParses input method output := by
  rintro ⟨method, output, successful⟩
  cases rejection with
  | signatureRejected signatureRejected =>
      cases successful with
      | parsed semicolonSpan signatureParsed semicolonParsed =>
          exact functionSignatureDeterministicOutcomeSpec
            |>.successRejectDisjoint signatureRejected
              ⟨_, _, signatureParsed⟩
  | semicolonMissing rejectedSignature semicolonAbsent =>
      cases successful with
      | parsed semicolonSpan successfulSignature semicolonParsed =>
          have afterSignatureEq :=
            functionSignatureDeterministicOutcomeSpec.successOutputUnique
              rejectedSignature successfulSignature
          subst afterSignatureEq
          exact absent_conflicts_exact semicolonAbsent semicolonParsed

/-- Signature-only trait methods have deterministic and exclusive ordinary
outcomes. -/
theorem traitMethodDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TraitMethodOrdinaryParses TraitMethodRejects where
  successOutputUnique := TraitMethodOrdinaryParses.output_unique
  successRejectDisjoint := TraitMethodRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTraitBodyOutcomeProperties
/-! Deterministic exact ordinary outcomes for prioritized trait bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_present {kind : TokenKind}
    {input : Remainder}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False := by
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

/-- Forward ordinary trait-method tails have one final remainder. -/
theorem TraitMethodTailOrdinaryParses.output_unique
    {input : Remainder}
    {leftMethods rightMethods : List Syntax.TraitMethod}
    {leftClosingSpan rightClosingSpan : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodTailOrdinaryParses input leftMethods
      leftClosingSpan afterLeft)
    (rightParsed : TraitMethodTailOrdinaryParses input rightMethods
      rightClosingSpan afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightMethods rightClosingSpan afterRight with
  | close leftClosingSpan leftClosingParsed =>
      cases rightParsed with
      | close rightClosingSpan rightClosingParsed =>
          exact exactToken_output_unique leftClosingParsed rightClosingParsed
      | next rightClosingAbsent rightFunctionPresent rightMethodParsed
            rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosingParsed)
  | next leftClosingAbsent leftFunctionPresent leftMethodParsed leftProgress
        leftTail inductionHypothesis =>
      cases rightParsed with
      | close rightClosingSpan rightClosingParsed =>
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosingParsed)
      | next rightClosingAbsent rightFunctionPresent rightMethodParsed
            rightProgress rightTail =>
          have afterMethodEq :=
            traitMethodDeterministicOutcomeSpec.successOutputUnique
              leftMethodParsed rightMethodParsed
          subst afterMethodEq
          exact inductionHypothesis rightTail

/-- Exact loop rejection excludes every ordinary trait-method tail. -/
theorem TraitMethodTailRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : TraitMethodTailRejects input rejected) :
    ¬ ∃ methods closingSpan output,
      TraitMethodTailOrdinaryParses input methods closingSpan output := by
  induction rejection with
  | unexpected closingAbsent functionAbsent =>
      rintro ⟨methods, closingSpan, output, parsed⟩
      cases parsed with
      | close successfulClosingSpan successfulClosing =>
          exact absent_conflicts_exact closingAbsent successfulClosing
      | next successfulClosingAbsent successfulFunction successfulMethod
            successfulProgress successfulTail =>
          exact absent_conflicts_present functionAbsent successfulFunction
  | methodRejected closingAbsent functionPresent methodRejected =>
      rintro ⟨methods, closingSpan, output, parsed⟩
      cases parsed with
      | close successfulClosingSpan successfulClosing =>
          exact absent_conflicts_exact closingAbsent successfulClosing
      | next successfulClosingAbsent successfulFunction successfulMethod
            successfulProgress successfulTail =>
          exact traitMethodDeterministicOutcomeSpec.successRejectDisjoint
            methodRejected ⟨_, _, successfulMethod⟩
  | laterRejected closingAbsent functionPresent rejectedMethod rejectedProgress
        tailRejected inductionHypothesis =>
      rintro ⟨methods, closingSpan, output, parsed⟩
      cases parsed with
      | close successfulClosingSpan successfulClosing =>
          exact absent_conflicts_exact closingAbsent successfulClosing
      | next successfulClosingAbsent successfulFunction successfulMethod
            successfulProgress successfulTail =>
          have afterMethodEq :=
            traitMethodDeterministicOutcomeSpec.successOutputUnique
              rejectedMethod successfulMethod
          subst afterMethodEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

/-- Prioritized trait-method tails have deterministic and exclusive ordinary
outcomes. -/
theorem traitMethodTailDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TraitMethodTailOrdinaryOutcomeParses
      TraitMethodTailRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨tail, output, parsed⟩
    exact rejection.disjointOrdinary ⟨tail.2, tail.1, output, parsed⟩

/-- Ordinary complete trait-body success has one final remainder. -/
theorem TraitBodyOrdinaryParses.output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMethods rightMethods : List Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitBodyOrdinaryParses input leftSpan leftMethods afterLeft)
    (rightParsed : TraitBodyOrdinaryParses input rightSpan rightMethods
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpeningSpan leftClosingSpan leftOpening leftMethodsParsed =>
      cases rightParsed with
      | parsed rightOpeningSpan rightClosingSpan rightOpening
            rightMethodsParsed =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact leftMethodsParsed.output_unique rightMethodsParsed

/-- Exact complete trait-body rejection excludes every ordinary success. -/
theorem TraitBodyRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : TraitBodyRejects input rejected) :
    ¬ ∃ bodySpan methods output,
      TraitBodyOrdinaryParses input bodySpan methods output := by
  rintro ⟨bodySpan, methods, output, parsed⟩
  cases rejection with
  | openingMissing openingAbsent =>
      cases parsed with
      | parsed openingSpan closingSpan openingParsed methodsParsed =>
          exact absent_conflicts_exact openingAbsent openingParsed
  | tailRejected rejectedOpeningSpan rejectedOpening tailRejected =>
      cases parsed with
      | parsed openingSpan closingSpan openingParsed methodsParsed =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            openingParsed
          subst afterOpeningEq
          exact tailRejected.disjointOrdinary ⟨_, _, _, methodsParsed⟩

/-- Complete trait bodies have deterministic and exclusive ordinary outcomes. -/
theorem traitBodyDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TraitBodyOrdinaryOutcomeParses
      TraitBodyRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨body, output, parsed⟩
    exact rejection.disjointOrdinary ⟨body.1, body.2, output, parsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTraitDeclarationOutcomeProperties
/-! Deterministic exact ordinary outcomes for complete trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem traitBody_output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMethods rightMethods : List Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitBodyOrdinaryParses input leftSpan leftMethods afterLeft)
    (rightParsed : TraitBodyOrdinaryParses input rightSpan rightMethods
      afterRight) : afterLeft = afterRight :=
  traitBodyDeterministicOutcomeSpec.successOutputUnique
    (left := (leftSpan, leftMethods))
    (right := (rightSpan, rightMethods)) leftParsed rightParsed

private theorem traitBody_reject_disjoint
    {input rejected : Remainder} (rejection : TraitBodyRejects input rejected) :
    ¬ ∃ span methods output,
      TraitBodyOrdinaryParses input span methods output := by
  rintro ⟨span, methods, output, parsed⟩
  exact traitBodyDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨(span, methods), output, parsed⟩

/-- Ordinary trait-declaration success has one final remainder. -/
theorem TraitDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.TraitDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitDeclOrdinaryParses input left afterLeft)
    (rightParsed : TraitDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftGenerics leftWhere
        leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightGenerics rightWhere
            rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterGenericsEq := leftGenerics.output_unique rightGenerics
          subst afterGenericsEq
          have afterWhereEq := leftWhere.output_unique rightWhere
          subst afterWhereEq
          exact traitBody_output_unique leftBody rightBody

/-- Exact trait-declaration rejection excludes every ordinary success. -/
theorem TraitDeclRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : TraitDeclRejects input rejected) :
    ¬ ∃ declaration output,
      TraitDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulName
        successfulGenerics successfulWhere successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | nameRejected rejectedMarkerSpan rejectedMarker nameRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | genericsRejected rejectedMarkerSpan rejectedMarker rejectedName
            genericsRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact genericParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint genericsRejected
              ⟨_, _, successfulGenerics⟩
      | whereRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedGenerics whereRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          exact optionalWhereClauseDeterministicOutcomeSpec
            |>.successRejectDisjoint whereRejected ⟨_, _, successfulWhere⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedGenerics rejectedWhere bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterWhereEq := rejectedWhere.output_unique successfulWhere
          subst afterWhereEq
          exact traitBody_reject_disjoint bodyRejected
            ⟨_, _, _, successfulBody⟩

/-- Trait declarations have deterministic and exclusive ordinary outcomes. -/
theorem traitDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TraitDeclOrdinaryParses TraitDeclRejects where
  successOutputUnique := TraitDeclOrdinaryParses.output_unique
  successRejectDisjoint := TraitDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeProperties
/-!
Functionality and rejection exclusivity for ordinary named-function
declaration outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary function-declaration success has one final remainder. -/
theorem FunctionDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.FunctionDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionDeclOrdinaryParses input left afterLeft)
    (rightParsed : FunctionDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftSignature leftBody =>
      cases rightParsed with
      | parsed rightSignature rightBody =>
          have afterSignatureEq := leftSignature.output_unique rightSignature
          subst afterSignatureEq
          exact (isolatedCoreBlockPublicOutcomeSpec .allow)
            |>.successOutputUnique leftBody rightBody

/-- Exact first-stage declaration rejection excludes every ordinary success. -/
theorem FunctionDeclRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : FunctionDeclRejects input rejected) :
    ¬ ∃ declaration output,
      FunctionDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulSignature successfulBody =>
      cases rejection with
      | signatureRejected signatureRejected =>
          exact functionSignatureDeterministicOutcomeSpec
            |>.successRejectDisjoint signatureRejected
              ⟨_, _, successfulSignature⟩
      | bodyRejected rejectedSignature bodyRejected =>
          have afterSignatureEq := rejectedSignature.output_unique
            successfulSignature
          subst afterSignatureEq
          exact (isolatedCoreBlockPublicOutcomeSpec .allow)
            |>.successRejectDisjoint bodyRejected ⟨_, _, successfulBody⟩

/-- Complete named-function declarations have deterministic and exclusive
ordinary outcomes. -/
theorem functionDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FunctionDeclOrdinaryParses
      FunctionDeclRejects where
  successOutputUnique := FunctionDeclOrdinaryParses.output_unique
  successRejectDisjoint := FunctionDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractMemberCoreRejectionProperties
/-! Rejection exclusion for broad attribute-free contract-member dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_present_variant {kind : TokenKind}
    {input : Remainder}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : ContractMemberCoreTokenPresentAt input kind) : False := by
  exact absent present

/-- Exact selected-branch rejection excludes every broad ordinary success. -/
theorem ContractMemberCoreRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ContractMemberCoreRejects input rejected) :
    ¬ ∃ member output,
      ContractMemberCoreOrdinaryParses input member output := by
  rintro ⟨member, output, successful⟩
  cases rejection with
  | fieldRejected rejectedFieldPresent rejectedField =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact (contractFieldDeterministicOutcomeSpec
            coreExpressionPublicOutcomeSpec).successRejectDisjoint
              rejectedField ⟨_, _, successfulField⟩
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact successfulFieldAbsent rejectedFieldPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact successfulFieldAbsent rejectedFieldPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact successfulFieldAbsent rejectedFieldPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact successfulFieldAbsent rejectedFieldPresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact successfulFieldAbsent rejectedFieldPresent
  | functionRejected rejectedFieldAbsent rejectedFunctionPresent
        rejectedFunction =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact functionDeclDeterministicOutcomeSpec.successRejectDisjoint
            rejectedFunction ⟨_, _, successfulFunction⟩
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact absent_conflicts_present_variant successfulFunctionAbsent
            rejectedFunctionPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact absent_conflicts_present_variant successfulFunctionAbsent
            rejectedFunctionPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact absent_conflicts_present_variant successfulFunctionAbsent
            rejectedFunctionPresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact absent_conflicts_present_variant successfulFunctionAbsent
            rejectedFunctionPresent
  | constructorRejected rejectedFieldAbsent rejectedFunctionAbsent
        rejectedConstructorPresent rejectedConstructor =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact absent_conflicts_present_variant rejectedFunctionAbsent
            successfulFunctionPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact constructorDeclDeterministicOutcomeSpec.successRejectDisjoint
            rejectedConstructor ⟨_, _, successfulConstructor⟩
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact absent_conflicts_present_variant successfulConstructorAbsent
            rejectedConstructorPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact absent_conflicts_present_variant successfulConstructorAbsent
            rejectedConstructorPresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact absent_conflicts_present_variant successfulConstructorAbsent
            rejectedConstructorPresent
  | fallbackRejected rejectedFieldAbsent rejectedFunctionAbsent
        rejectedConstructorAbsent rejectedFallbackPresent rejectedFallback =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact absent_conflicts_present_variant rejectedFunctionAbsent
            successfulFunctionPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact absent_conflicts_present_variant rejectedConstructorAbsent
            successfulConstructorPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact fallbackDeclDeterministicOutcomeSpec.successRejectDisjoint
            rejectedFallback ⟨_, _, successfulFallback⟩
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact absent_conflicts_present_variant successfulFallbackAbsent
            rejectedFallbackPresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact absent_conflicts_present_variant successfulFallbackAbsent
            rejectedFallbackPresent
  | typeAliasRejected rejectedFieldAbsent rejectedFunctionAbsent
        rejectedConstructorAbsent rejectedFallbackAbsent rejectedTypePresent
        rejectedType =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact absent_conflicts_present_variant rejectedFunctionAbsent
            successfulFunctionPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact absent_conflicts_present_variant rejectedConstructorAbsent
            successfulConstructorPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact absent_conflicts_present_variant rejectedFallbackAbsent
            successfulFallbackPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact typeAliasDeclDeterministicOutcomeSpec.successRejectDisjoint
            rejectedType ⟨_, _, successfulType⟩
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact absent_conflicts_present_variant successfulTypeAbsent
            rejectedTypePresent
  | enumRejected rejectedFieldAbsent rejectedFunctionAbsent
        rejectedConstructorAbsent rejectedFallbackAbsent rejectedTypeAbsent
        rejectedEnumPresent rejectedEnum =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact absent_conflicts_present_variant rejectedFunctionAbsent
            successfulFunctionPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact absent_conflicts_present_variant rejectedConstructorAbsent
            successfulConstructorPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact absent_conflicts_present_variant rejectedFallbackAbsent
            successfulFallbackPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact absent_conflicts_present_variant rejectedTypeAbsent
            successfulTypePresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact (enumDeclDeterministicOutcomeSpec none).successRejectDisjoint
            rejectedEnum ⟨_, _, successfulEnum⟩
  | unrecognized rejectedFieldAbsent rejectedFunctionAbsent
        rejectedConstructorAbsent rejectedFallbackAbsent rejectedTypeAbsent
        rejectedEnumAbsent =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact absent_conflicts_present_variant rejectedFunctionAbsent
            successfulFunctionPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact absent_conflicts_present_variant rejectedConstructorAbsent
            successfulConstructorPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact absent_conflicts_present_variant rejectedFallbackAbsent
            successfulFallbackPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact absent_conflicts_present_variant rejectedTypeAbsent
            successfulTypePresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact absent_conflicts_present_variant rejectedEnumAbsent
            successfulEnumPresent

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractMemberCoreSuccessProperties
/-! Output functionality for broad attribute-free contract-member success. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem present_conflicts_absent
    {input : Remainder} {kind : TokenKind}
    (present : ContractMemberCoreTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False := by
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

/-- Broad attribute-free contract-member success has one final remainder. -/
theorem ContractMemberCoreOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberCoreOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberCoreOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | field leftFieldPresent leftFieldParsed =>
      cases rightParsed with
      | field rightFieldPresent rightFieldParsed =>
          exact (contractFieldDeterministicOutcomeSpec
            coreExpressionPublicOutcomeSpec).successOutputUnique
              leftFieldParsed rightFieldParsed
      | function rightFieldAbsent _ _ =>
          exact False.elim (rightFieldAbsent leftFieldPresent)
      | constructor rightFieldAbsent _ _ _ =>
          exact False.elim (rightFieldAbsent leftFieldPresent)
      | fallback rightFieldAbsent _ _ _ _ =>
          exact False.elim (rightFieldAbsent leftFieldPresent)
      | typeAlias rightFieldAbsent _ _ _ _ _ =>
          exact False.elim (rightFieldAbsent leftFieldPresent)
      | enum rightFieldAbsent _ _ _ _ _ _ =>
          exact False.elim (rightFieldAbsent leftFieldPresent)
  | function leftFieldAbsent leftFunctionPresent leftFunctionParsed =>
      cases rightParsed with
      | field rightFieldPresent _ =>
          exact False.elim (leftFieldAbsent rightFieldPresent)
      | function _ _ rightFunctionParsed =>
          exact functionDeclDeterministicOutcomeSpec.successOutputUnique
            leftFunctionParsed rightFunctionParsed
      | constructor _ rightFunctionAbsent _ _ =>
          exact False.elim
            (present_conflicts_absent leftFunctionPresent rightFunctionAbsent)
      | fallback _ rightFunctionAbsent _ _ _ =>
          exact False.elim
            (present_conflicts_absent leftFunctionPresent rightFunctionAbsent)
      | typeAlias _ rightFunctionAbsent _ _ _ _ =>
          exact False.elim
            (present_conflicts_absent leftFunctionPresent rightFunctionAbsent)
      | enum _ rightFunctionAbsent _ _ _ _ _ =>
          exact False.elim
            (present_conflicts_absent leftFunctionPresent rightFunctionAbsent)
  | constructor leftFieldAbsent leftFunctionAbsent leftConstructorPresent
        leftConstructorParsed =>
      cases rightParsed with
      | field rightFieldPresent _ =>
          exact False.elim (leftFieldAbsent rightFieldPresent)
      | function _ rightFunctionPresent _ =>
          exact False.elim
            (present_conflicts_absent rightFunctionPresent leftFunctionAbsent)
      | constructor _ _ _ rightConstructorParsed =>
          exact constructorDeclDeterministicOutcomeSpec.successOutputUnique
            leftConstructorParsed rightConstructorParsed
      | fallback _ _ rightConstructorAbsent _ _ =>
          exact False.elim (present_conflicts_absent leftConstructorPresent
            rightConstructorAbsent)
      | typeAlias _ _ rightConstructorAbsent _ _ _ =>
          exact False.elim (present_conflicts_absent leftConstructorPresent
            rightConstructorAbsent)
      | enum _ _ rightConstructorAbsent _ _ _ _ =>
          exact False.elim (present_conflicts_absent leftConstructorPresent
            rightConstructorAbsent)
  | fallback leftFieldAbsent leftFunctionAbsent leftConstructorAbsent
        leftFallbackPresent leftFallbackParsed =>
      cases rightParsed with
      | field rightFieldPresent _ =>
          exact False.elim (leftFieldAbsent rightFieldPresent)
      | function _ rightFunctionPresent _ =>
          exact False.elim
            (present_conflicts_absent rightFunctionPresent leftFunctionAbsent)
      | constructor _ _ rightConstructorPresent _ =>
          exact False.elim (present_conflicts_absent rightConstructorPresent
            leftConstructorAbsent)
      | fallback _ _ _ _ rightFallbackParsed =>
          exact fallbackDeclDeterministicOutcomeSpec.successOutputUnique
            leftFallbackParsed rightFallbackParsed
      | typeAlias _ _ _ rightFallbackAbsent _ _ =>
          exact False.elim (present_conflicts_absent leftFallbackPresent
            rightFallbackAbsent)
      | enum _ _ _ rightFallbackAbsent _ _ _ =>
          exact False.elim (present_conflicts_absent leftFallbackPresent
            rightFallbackAbsent)
  | typeAlias leftFieldAbsent leftFunctionAbsent leftConstructorAbsent
        leftFallbackAbsent leftTypePresent leftTypeParsed =>
      cases rightParsed with
      | field rightFieldPresent _ =>
          exact False.elim (leftFieldAbsent rightFieldPresent)
      | function _ rightFunctionPresent _ =>
          exact False.elim
            (present_conflicts_absent rightFunctionPresent leftFunctionAbsent)
      | constructor _ _ rightConstructorPresent _ =>
          exact False.elim (present_conflicts_absent rightConstructorPresent
            leftConstructorAbsent)
      | fallback _ _ _ rightFallbackPresent _ =>
          exact False.elim (present_conflicts_absent rightFallbackPresent
            leftFallbackAbsent)
      | typeAlias _ _ _ _ _ rightTypeParsed =>
          exact typeAliasDeclDeterministicOutcomeSpec.successOutputUnique
            leftTypeParsed rightTypeParsed
      | enum _ _ _ _ rightTypeAbsent _ _ =>
          exact False.elim
            (present_conflicts_absent leftTypePresent rightTypeAbsent)
  | enum leftFieldAbsent leftFunctionAbsent leftConstructorAbsent
        leftFallbackAbsent leftTypeAbsent leftEnumPresent leftEnumParsed =>
      cases rightParsed with
      | field rightFieldPresent _ =>
          exact False.elim (leftFieldAbsent rightFieldPresent)
      | function _ rightFunctionPresent _ =>
          exact False.elim
            (present_conflicts_absent rightFunctionPresent leftFunctionAbsent)
      | constructor _ _ rightConstructorPresent _ =>
          exact False.elim (present_conflicts_absent rightConstructorPresent
            leftConstructorAbsent)
      | fallback _ _ _ rightFallbackPresent _ =>
          exact False.elim (present_conflicts_absent rightFallbackPresent
            leftFallbackAbsent)
      | typeAlias _ _ _ _ rightTypePresent _ =>
          exact False.elim
            (present_conflicts_absent rightTypePresent leftTypeAbsent)
      | enum _ _ _ _ _ _ rightEnumParsed =>
          exact (enumDeclDeterministicOutcomeSpec none).successOutputUnique
            leftEnumParsed rightEnumParsed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractMemberCoreOutcomeProperties
/-! Deterministic broad outcomes for attribute-free contract-member dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Attribute-free contract members have deterministic successful remainders,
and their exact selected-branch rejections exclude success. -/
theorem contractMemberCoreDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects where
  successOutputUnique := ContractMemberCoreOrdinaryParses.output_unique
  successRejectDisjoint := ContractMemberCoreRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractMemberWithAttributeOutcomeProperties
/-!
Deterministic broad ordinary outcomes for public contract-member dispatch.
Pure derive attachment neither consumes input nor introduces a rejection stage.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token_variant {input : Remainder} {kind : TokenKind}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : ContractMemberCoreTokenPresentAt input kind) : False := by
  unfold ContractMemberCoreTokenPresentAt at present
  exact absent present

/-- Public contract-member success has one final remainder. -/
theorem ContractMemberOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | plain leftHashAbsent leftCoreParsed =>
      cases rightParsed with
      | plain rightHashAbsent rightCoreParsed =>
          exact contractMemberCoreDeterministicOutcomeSpec.successOutputUnique
            leftCoreParsed rightCoreParsed
      | derived rightHashPresent rightDeriveParsed rightCoreParsed
          rightAttached =>
          exact False.elim
            (absent_conflicts_token_variant leftHashAbsent rightHashPresent)
  | derived leftHashPresent leftDeriveParsed leftCoreParsed leftAttached =>
      cases rightParsed with
      | plain rightHashAbsent rightCoreParsed =>
          exact False.elim
            (absent_conflicts_token_variant rightHashAbsent leftHashPresent)
      | derived rightHashPresent rightDeriveParsed rightCoreParsed
          rightAttached =>
          have afterDeriveEq :=
            deriveAttributeDeterministicOutcomeSpec.successOutputUnique
              leftDeriveParsed rightDeriveParsed
          cases afterDeriveEq
          exact contractMemberCoreDeterministicOutcomeSpec.successOutputUnique
            leftCoreParsed rightCoreParsed

/-- Every exact public contract-member rejection excludes plain and
derive-prefixed success. -/
theorem ContractMemberRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ContractMemberRejects input rejected) :
    ¬ ∃ member output, ContractMemberOrdinaryParses input member output := by
  rintro ⟨member, output, successful⟩
  cases rejection with
  | plainCoreRejected rejectedHashAbsent coreRejected =>
      cases successful with
      | plain successfulHashAbsent coreParsed =>
          exact contractMemberCoreDeterministicOutcomeSpec
            |>.successRejectDisjoint coreRejected ⟨_, _, coreParsed⟩
      | derived successfulHashPresent deriveParsed coreParsed attached =>
          exact absent_conflicts_token_variant rejectedHashAbsent
            successfulHashPresent
  | deriveRejected rejectedHashPresent deriveRejected =>
      cases successful with
      | plain successfulHashAbsent coreParsed =>
          exact absent_conflicts_token_variant successfulHashAbsent
            rejectedHashPresent
      | derived successfulHashPresent deriveParsed coreParsed attached =>
          exact deriveAttributeDeterministicOutcomeSpec
            |>.successRejectDisjoint deriveRejected ⟨_, _, deriveParsed⟩
  | derivedCoreRejected rejectedHashPresent rejectedDeriveParsed coreRejected =>
      cases successful with
      | plain successfulHashAbsent coreParsed =>
          exact absent_conflicts_token_variant successfulHashAbsent
            rejectedHashPresent
      | derived successfulHashPresent successfulDeriveParsed coreParsed
          attached =>
          have afterDeriveEq :=
            deriveAttributeDeterministicOutcomeSpec.successOutputUnique
              rejectedDeriveParsed successfulDeriveParsed
          cases afterDeriveEq
          exact contractMemberCoreDeterministicOutcomeSpec
            |>.successRejectDisjoint coreRejected ⟨_, _, coreParsed⟩

/-- Public contract-member outcomes have deterministic successful remainders
and exact rejection/success exclusion. -/
theorem contractMemberDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ContractMemberOrdinaryParses
      ContractMemberRejects where
  successOutputUnique := ContractMemberOrdinaryParses.output_unique
  successRejectDisjoint := ContractMemberRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end
