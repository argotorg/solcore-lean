import Solcore.Syntax.Internal.BlockExactness
import Solcore.Syntax.Internal.ContractMemberOutcomes
import Solcore.Syntax.Internal.SignatureExactness
import Solcore.Syntax.Internal.ContractBodyOutcomes
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.SignatureOutcomes
import Solcore.Syntax.Internal.DeriveOutcomes
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.TypeExactness
import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Internal.StatementValues
import Solcore.Syntax.Internal.SourceFileOutcomes
import Solcore.Syntax.Internal.ImportOutcomes
import Solcore.Syntax.Internal.ExportOutcomes

/-!
Exactness of the declarative grammar of contract members, implementations, traits and
enums: outcomes fix the whole result. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionDeclarationExactnessProperties
/-!
Exactness transport through complete named-function declarations.

The function signature is unconditionally exact. The only remaining premise
is exactness of the isolated `.allow` Core body.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An exact isolated body makes a successful function declaration fix its
complete AST. -/
theorem FunctionDeclOrdinaryParses.value_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input : Remainder} {left right : Syntax.FunctionDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionDeclOrdinaryParses input left afterLeft)
    (rightParsed : FunctionDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSignature leftBody =>
      cases rightParsed with
      | parsed rightSignature rightBody =>
          rcases functionSignatureExactOutcomeSpec.successResultUnique
              leftSignature rightSignature with
            ⟨signatureEq, afterSignatureEq⟩
          subst signatureEq
          subst afterSignatureEq
          rcases bodyOutcomes.successResultUnique leftBody rightBody with
            ⟨bodyEq, afterBodyEq⟩
          subst bodyEq
          rfl

/-- With an exact isolated body, successful function declarations fix their
AST and final remainder. -/
theorem FunctionDeclOrdinaryParses.result_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input : Remainder} {left right : Syntax.FunctionDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionDeclOrdinaryParses input left afterLeft)
    (rightParsed : FunctionDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_exact_body bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- With an exact isolated body, function-declaration rejection fixes its
first failing endpoint. -/
theorem FunctionDeclRejects.output_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input left right : Remainder}
    (leftRejected : FunctionDeclRejects input left)
    (rightRejected : FunctionDeclRejects input right) : left = right := by
  cases leftRejected with
  | signatureRejected leftSignature =>
      cases rightRejected with
      | signatureRejected rightSignature =>
          exact functionSignatureExactOutcomeSpec.rejectOutputUnique
            leftSignature rightSignature
      | bodyRejected rightSignature rightBody =>
          exact False.elim
            (functionSignatureExactOutcomeSpec.successRejectDisjoint
              leftSignature ⟨_, _, rightSignature⟩)
  | bodyRejected leftSignature leftBody =>
      cases rightRejected with
      | signatureRejected rightSignature =>
          exact False.elim
            (functionSignatureExactOutcomeSpec.successRejectDisjoint
              rightSignature ⟨_, _, leftSignature⟩)
      | bodyRejected rightSignature rightBody =>
          have afterSignatureEq :=
            functionSignatureExactOutcomeSpec.successOutputUnique
              leftSignature rightSignature
          subst afterSignatureEq
          exact bodyOutcomes.rejectOutputUnique leftBody rightBody

/-- An exact isolated `.allow` body lifts to exact broad function-declaration
outcomes. -/
theorem functionDeclExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow)) :
    ExactDeterministicOutcomeSpec FunctionDeclOrdinaryParses
      FunctionDeclRejects where
  toDeterministicOutcomeSpec := functionDeclDeterministicOutcomeSpec
  successValueUnique :=
    FunctionDeclOrdinaryParses.value_unique_of_exact_body bodyOutcomes
  rejectOutputUnique :=
    FunctionDeclRejects.output_unique_of_exact_body bodyOutcomes

/-- Fixed-fuel Core statement exactness supplies the isolated `.allow` body
contract and therefore exact broad function-declaration outcomes. -/
theorem functionDeclExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec FunctionDeclOrdinaryParses
      FunctionDeclRejects :=
  functionDeclExactOutcomeSpecOfBody
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .allow)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplMethodExactnessProperties
/-!
Exactness transport through implementation-method wrappers.

The only remaining premise is exactness of the isolated `.allow` body used by
the nested function declaration.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An exact isolated function body makes an implementation method fix its
wrapped declaration AST. -/
theorem ImplMethodOrdinaryParses.value_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input : Remainder} {left right : Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplMethodOrdinaryParses input left afterLeft)
    (rightParsed : ImplMethodOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftDeclaration =>
      cases rightParsed with
      | parsed rightDeclaration =>
          have declarationEq :=
            (functionDeclExactOutcomeSpecOfBody bodyOutcomes)
              |>.successValueUnique leftDeclaration rightDeclaration
          subst declarationEq
          rfl

/-- With an exact isolated function body, an implementation-method success
fixes its AST and final remainder. -/
theorem ImplMethodOrdinaryParses.result_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input : Remainder} {left right : Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplMethodOrdinaryParses input left afterLeft)
    (rightParsed : ImplMethodOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_exact_body bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- With an exact isolated function body, implementation-method rejection
fixes its endpoint. -/
theorem ImplMethodRejects.output_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input left right : Remainder}
    (leftRejected : ImplMethodRejects input left)
    (rightRejected : ImplMethodRejects input right) : left = right := by
  cases leftRejected with
  | declarationRejected leftDeclaration =>
      cases rightRejected with
      | declarationRejected rightDeclaration =>
          exact (functionDeclExactOutcomeSpecOfBody bodyOutcomes)
            |>.rejectOutputUnique leftDeclaration rightDeclaration

/-- An exact isolated `.allow` body lifts to exact implementation-method
outcomes. -/
theorem implMethodExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow)) :
    ExactDeterministicOutcomeSpec ImplMethodOrdinaryParses
      ImplMethodRejects where
  toDeterministicOutcomeSpec := implMethodDeterministicOutcomeSpec
  successValueUnique :=
    ImplMethodOrdinaryParses.value_unique_of_exact_body bodyOutcomes
  rejectOutputUnique :=
    ImplMethodRejects.output_unique_of_exact_body bodyOutcomes

/-- Fixed-fuel Core-statement exactness supplies the isolated function body
contract needed for exact implementation-method outcomes. -/
theorem implMethodExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ImplMethodOrdinaryParses
      ImplMethodRejects :=
  implMethodExactOutcomeSpecOfBody
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .allow)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplBodyExactnessProperties
/-! Exactness transport through prioritized implementation bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem implBody_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem implBody_absent_conflicts_present {kind : TokenKind}
    {input : Remainder}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent present

/-- Exact method outcomes make a method tail fix its methods, closing span,
and final remainder. -/
theorem ImplMethodTailOrdinaryParses.result_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects) :
    ∀ {input : Remainder} {leftMethods rightMethods : List Syntax.ImplMethod}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      ImplMethodTailOrdinaryParses input leftMethods leftClosing afterLeft →
      ImplMethodTailOrdinaryParses input rightMethods rightClosing afterRight →
      leftMethods = rightMethods ∧ leftClosing = rightClosing ∧
        afterLeft = afterRight := by
  intro input leftMethods rightMethods leftClosing rightClosing afterLeft
    afterRight leftParsed
  induction leftParsed generalizing rightMethods rightClosing afterRight with
  | close leftClosing leftToken =>
      intro rightParsed
      cases rightParsed with
      | close rightClosing rightToken =>
          rcases leftToken.result_unique rightToken with
            ⟨closingEq, outputEq⟩
          exact ⟨rfl, closingEq, outputEq⟩
      | next rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (implBody_absent_conflicts_exact rightClosingAbsent leftToken)
  | next leftClosingAbsent leftFunctionPresent leftMethod leftProgress
      leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightClosing rightToken =>
          exact False.elim
            (implBody_absent_conflicts_exact leftClosingAbsent rightToken)
      | next rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          rcases methodOutcomes.successResultUnique leftMethod rightMethod with
            ⟨methodEq, afterMethodEq⟩
          subst methodEq
          subst afterMethodEq
          rcases inductionHypothesis rightTail with
            ⟨methodsEq, closingEq, outputEq⟩
          subst methodsEq
          exact ⟨rfl, closingEq, outputEq⟩

/-- Exact method outcomes fix the paired method-tail value. -/
theorem ImplMethodTailOrdinaryOutcomeParses.value_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects)
    {input : Remainder}
    {left right : SourceSpan × List Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplMethodTailOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : ImplMethodTailOrdinaryOutcomeParses input right afterRight) :
    left = right := by
  rcases left with ⟨leftClosing, leftMethods⟩
  rcases right with ⟨rightClosing, rightMethods⟩
  rcases leftParsed.result_unique methodOutcomes rightParsed with
    ⟨methodsEq, closingEq, outputEq⟩
  subst methodsEq
  subst closingEq
  rfl

/-- Exact method outcomes fix every rejecting method-tail endpoint. -/
theorem ImplMethodTailRejects.output_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects)
    {input left right : Remainder}
    (leftRejected : ImplMethodTailRejects input left)
    (rightRejected : ImplMethodTailRejects input right) : left = right := by
  induction leftRejected generalizing right with
  | unexpected leftClosingAbsent leftFunctionAbsent =>
      cases rightRejected with
      | unexpected => rfl
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (implBody_absent_conflicts_present leftFunctionAbsent
              rightFunctionPresent)
  | methodRejected leftClosingAbsent leftFunctionPresent leftMethod =>
      cases rightRejected with
      | unexpected rightClosingAbsent rightFunctionAbsent =>
          exact False.elim
            (implBody_absent_conflicts_present rightFunctionAbsent
              leftFunctionPresent)
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod =>
          exact methodOutcomes.rejectOutputUnique leftMethod rightMethod
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (methodOutcomes.successRejectDisjoint leftMethod
              ⟨_, _, rightMethod⟩)
  | laterRejected leftClosingAbsent leftFunctionPresent leftMethod leftProgress
      leftTail inductionHypothesis =>
      cases rightRejected with
      | unexpected rightClosingAbsent rightFunctionAbsent =>
          exact False.elim
            (implBody_absent_conflicts_present rightFunctionAbsent
              leftFunctionPresent)
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod =>
          exact False.elim
            (methodOutcomes.successRejectDisjoint rightMethod
              ⟨_, _, leftMethod⟩)
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          have afterMethodEq :=
            methodOutcomes.successOutputUnique leftMethod rightMethod
          subst afterMethodEq
          exact inductionHypothesis rightTail

/-- Exact method outcomes lift through the prioritized method-tail loop. -/
theorem implMethodTailExactOutcomeSpecOfMethod
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects) :
    ExactDeterministicOutcomeSpec ImplMethodTailOrdinaryOutcomeParses
      ImplMethodTailRejects where
  toDeterministicOutcomeSpec := implMethodTailDeterministicOutcomeSpec
  successValueUnique :=
    ImplMethodTailOrdinaryOutcomeParses.value_unique methodOutcomes
  rejectOutputUnique := ImplMethodTailRejects.output_unique methodOutcomes

/-- Exact method outcomes make a complete implementation body fix its span,
methods, and final remainder. -/
theorem ImplBodyOrdinaryParses.result_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects)
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMethods rightMethods : List Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplBodyOrdinaryParses input leftSpan leftMethods afterLeft)
    (rightParsed : ImplBodyOrdinaryParses input rightSpan rightMethods
      afterRight) :
    leftSpan = rightSpan ∧ leftMethods = rightMethods ∧
      afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpening leftClosing leftOpeningToken leftTail =>
      cases rightParsed with
      | parsed rightOpening rightClosing rightOpeningToken rightTail =>
          rcases leftOpeningToken.result_unique rightOpeningToken with
            ⟨openingEq, afterOpeningEq⟩
          subst openingEq
          subst afterOpeningEq
          rcases leftTail.result_unique methodOutcomes rightTail with
            ⟨methodsEq, closingEq, outputEq⟩
          subst methodsEq
          subst closingEq
          exact ⟨rfl, rfl, outputEq⟩

/-- Exact method outcomes fix the paired complete-body value. -/
theorem ImplBodyOrdinaryOutcomeParses.value_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects)
    {input : Remainder}
    {left right : SourceSpan × List Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplBodyOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : ImplBodyOrdinaryOutcomeParses input right afterRight) :
    left = right := by
  rcases left with ⟨leftSpan, leftMethods⟩
  rcases right with ⟨rightSpan, rightMethods⟩
  rcases leftParsed.result_unique methodOutcomes rightParsed with
    ⟨spanEq, methodsEq, outputEq⟩
  subst spanEq
  subst methodsEq
  rfl

/-- Exact method outcomes fix complete implementation-body rejection. -/
theorem ImplBodyRejects.output_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects)
    {input left right : Remainder}
    (leftRejected : ImplBodyRejects input left)
    (rightRejected : ImplBodyRejects input right) : left = right := by
  cases leftRejected with
  | openingMissing leftOpeningAbsent =>
      cases rightRejected with
      | openingMissing => rfl
      | tailRejected rightSpan rightOpening rightTail =>
          exact False.elim
            (implBody_absent_conflicts_exact leftOpeningAbsent rightOpening)
  | tailRejected leftSpan leftOpening leftTail =>
      cases rightRejected with
      | openingMissing rightOpeningAbsent =>
          exact False.elim
            (implBody_absent_conflicts_exact rightOpeningAbsent leftOpening)
      | tailRejected rightSpan rightOpening rightTail =>
          have afterOpeningEq := leftOpening.output_unique rightOpening
          subst afterOpeningEq
          exact leftTail.output_unique methodOutcomes rightTail

/-- Exact method outcomes lift through a complete implementation body. -/
theorem implBodyExactOutcomeSpecOfMethod
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects) :
    ExactDeterministicOutcomeSpec ImplBodyOrdinaryOutcomeParses
      ImplBodyRejects where
  toDeterministicOutcomeSpec := implBodyDeterministicOutcomeSpec
  successValueUnique :=
    ImplBodyOrdinaryOutcomeParses.value_unique methodOutcomes
  rejectOutputUnique := ImplBodyRejects.output_unique methodOutcomes

/-- An exact isolated `.allow` Core body lifts through every implementation
method and therefore through the complete implementation body. -/
theorem implBodyExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow)) :
    ExactDeterministicOutcomeSpec ImplBodyOrdinaryOutcomeParses
      ImplBodyRejects :=
  implBodyExactOutcomeSpecOfMethod
    (implMethodExactOutcomeSpecOfBody bodyOutcomes)

/-- Fixed-fuel Core-statement exactness supplies exact implementation-body
outcomes. -/
theorem implBodyExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ImplBodyOrdinaryOutcomeParses
      ImplBodyRejects :=
  implBodyExactOutcomeSpecOfMethod
    (implMethodExactOutcomeSpecOfStatementFuel statementOutcomes)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTraitMethodExactnessProperties
/-! Exact values and rejection endpoints for signature-only trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A successful trait method fixes its complete AST. -/
theorem TraitMethodOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodOrdinaryParses input left afterLeft)
    (rightParsed : TraitMethodOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSemicolonSpan leftSignature leftSemicolon =>
      cases rightParsed with
      | parsed rightSemicolonSpan rightSignature rightSemicolon =>
          rcases functionSignatureExactOutcomeSpec.successResultUnique
              leftSignature rightSignature with
            ⟨signatureEq, afterSignatureEq⟩
          subst signatureEq
          subst afterSignatureEq
          rcases leftSemicolon.result_unique rightSemicolon with
            ⟨semicolonSpanEq, afterSemicolonEq⟩
          subst semicolonSpanEq
          rfl

/-- A successful trait method fixes its AST and final remainder. -/
theorem TraitMethodOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodOrdinaryParses input left afterLeft)
    (rightParsed : TraitMethodOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Trait-method rejection fixes its first failing endpoint. -/
theorem TraitMethodRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TraitMethodRejects input left)
    (rightRejected : TraitMethodRejects input right) : left = right := by
  cases leftRejected with
  | signatureRejected leftSignature =>
      cases rightRejected with
      | signatureRejected rightSignature =>
          exact functionSignatureExactOutcomeSpec.rejectOutputUnique
            leftSignature rightSignature
      | semicolonMissing rightSignature rightSemicolonAbsent =>
          exact False.elim
            (functionSignatureExactOutcomeSpec.successRejectDisjoint
              leftSignature ⟨_, _, rightSignature⟩)
  | semicolonMissing leftSignature leftSemicolonAbsent =>
      cases rightRejected with
      | signatureRejected rightSignature =>
          exact False.elim
            (functionSignatureExactOutcomeSpec.successRejectDisjoint
              rightSignature ⟨_, _, leftSignature⟩)
      | semicolonMissing rightSignature rightSemicolonAbsent =>
          exact functionSignatureExactOutcomeSpec.successOutputUnique
            leftSignature rightSignature

/-- Signature-only trait methods have fully exact ordinary outcomes. -/
theorem traitMethodExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TraitMethodOrdinaryParses
      TraitMethodRejects where
  toDeterministicOutcomeSpec := traitMethodDeterministicOutcomeSpec
  successValueUnique := TraitMethodOrdinaryParses.value_unique
  rejectOutputUnique := TraitMethodRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTraitBodyExactnessProperties
/-! Exact values and rejection endpoints for prioritized trait bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem traitBody_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem traitBody_absent_conflicts_method_start
    {input : Remainder}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .functionKw))
    (present : TraitMethodStartAt input) : False := by
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

/-- A successful trait-method tail fixes its methods, closing span, and final
remainder. -/
theorem TraitMethodTailOrdinaryParses.result_unique
    {input : Remainder}
    {leftMethods rightMethods : List Syntax.TraitMethod}
    {leftClosingSpan rightClosingSpan : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodTailOrdinaryParses input leftMethods
      leftClosingSpan afterLeft)
    (rightParsed : TraitMethodTailOrdinaryParses input rightMethods
      rightClosingSpan afterRight) :
    leftMethods = rightMethods ∧ leftClosingSpan = rightClosingSpan ∧
      afterLeft = afterRight := by
  induction leftParsed generalizing rightMethods rightClosingSpan afterRight with
  | close leftClosingSpan leftClosing =>
      cases rightParsed with
      | close rightClosingSpan rightClosing =>
          rcases leftClosing.result_unique rightClosing with
            ⟨closingSpanEq, outputEq⟩
          exact ⟨rfl, closingSpanEq, outputEq⟩
      | next rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (traitBody_absent_conflicts_exact rightClosingAbsent leftClosing)
  | next leftClosingAbsent leftFunctionPresent leftMethod leftProgress
      leftTail inductionHypothesis =>
      cases rightParsed with
      | close rightClosingSpan rightClosing =>
          exact False.elim
            (traitBody_absent_conflicts_exact leftClosingAbsent rightClosing)
      | next rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          rcases traitMethodExactOutcomeSpec.successResultUnique leftMethod
              rightMethod with ⟨methodEq, afterMethodEq⟩
          subst methodEq
          subst afterMethodEq
          rcases inductionHypothesis rightTail with
            ⟨methodsEq, closingSpanEq, outputEq⟩
          subst methodsEq
          exact ⟨rfl, closingSpanEq, outputEq⟩

/-- Rejection of the prioritized method loop fixes its failing endpoint. -/
theorem TraitMethodTailRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TraitMethodTailRejects input left)
    (rightRejected : TraitMethodTailRejects input right) : left = right := by
  induction leftRejected generalizing right with
  | unexpected leftClosingAbsent leftFunctionAbsent =>
      cases rightRejected with
      | unexpected => rfl
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod =>
          exact False.elim
            (traitBody_absent_conflicts_method_start leftFunctionAbsent
              rightFunctionPresent)
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (traitBody_absent_conflicts_method_start leftFunctionAbsent
              rightFunctionPresent)
  | methodRejected leftClosingAbsent leftFunctionPresent leftMethod =>
      cases rightRejected with
      | unexpected rightClosingAbsent rightFunctionAbsent =>
          exact False.elim
            (traitBody_absent_conflicts_method_start rightFunctionAbsent
              leftFunctionPresent)
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod =>
          exact traitMethodExactOutcomeSpec.rejectOutputUnique leftMethod
            rightMethod
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (traitMethodExactOutcomeSpec.successRejectDisjoint leftMethod
              ⟨_, _, rightMethod⟩)
  | laterRejected leftClosingAbsent leftFunctionPresent leftMethod
      leftProgress leftTail inductionHypothesis =>
      cases rightRejected with
      | unexpected rightClosingAbsent rightFunctionAbsent =>
          exact False.elim
            (traitBody_absent_conflicts_method_start rightFunctionAbsent
              leftFunctionPresent)
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod =>
          exact False.elim
            (traitMethodExactOutcomeSpec.successRejectDisjoint rightMethod
              ⟨_, _, leftMethod⟩)
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          have afterMethodEq :=
            traitMethodExactOutcomeSpec.successOutputUnique leftMethod
              rightMethod
          subst afterMethodEq
          exact inductionHypothesis rightTail

/-- The single-value tail adapter fixes its closing span and method list. -/
theorem TraitMethodTailOrdinaryOutcomeParses.value_unique
    {input : Remainder}
    {left right : SourceSpan × List Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodTailOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : TraitMethodTailOrdinaryOutcomeParses input right
      afterRight) : left = right := by
  rcases TraitMethodTailOrdinaryParses.result_unique leftParsed rightParsed with
    ⟨methodsEq, closingSpanEq, outputEq⟩
  exact Prod.ext closingSpanEq methodsEq

/-- Prioritized trait-method tails have fully exact ordinary outcomes. -/
theorem traitMethodTailExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TraitMethodTailOrdinaryOutcomeParses
      TraitMethodTailRejects where
  toDeterministicOutcomeSpec := traitMethodTailDeterministicOutcomeSpec
  successValueUnique := TraitMethodTailOrdinaryOutcomeParses.value_unique
  rejectOutputUnique := TraitMethodTailRejects.output_unique

/-- A successful complete trait body fixes its span, methods, and remainder. -/
theorem TraitBodyOrdinaryParses.result_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMethods rightMethods : List Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitBodyOrdinaryParses input leftSpan leftMethods afterLeft)
    (rightParsed : TraitBodyOrdinaryParses input rightSpan rightMethods
      afterRight) :
    leftSpan = rightSpan ∧ leftMethods = rightMethods ∧
      afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpeningSpan leftClosingSpan leftOpening leftMethodsParsed =>
      cases rightParsed with
      | parsed rightOpeningSpan rightClosingSpan rightOpening
          rightMethodsParsed =>
          rcases leftOpening.result_unique rightOpening with
            ⟨openingSpanEq, afterOpeningEq⟩
          subst openingSpanEq
          subst afterOpeningEq
          rcases leftMethodsParsed.result_unique rightMethodsParsed with
            ⟨methodsEq, closingSpanEq, outputEq⟩
          subst methodsEq
          subst closingSpanEq
          exact ⟨rfl, rfl, outputEq⟩

/-- The single-value body adapter fixes its body span and method list. -/
theorem TraitBodyOrdinaryOutcomeParses.value_unique
    {input : Remainder}
    {left right : SourceSpan × List Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitBodyOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : TraitBodyOrdinaryOutcomeParses input right afterRight) :
    left = right := by
  rcases TraitBodyOrdinaryParses.result_unique leftParsed rightParsed with
    ⟨spanEq, methodsEq, outputEq⟩
  exact Prod.ext spanEq methodsEq

/-- Complete trait-body rejection fixes its first failing endpoint. -/
theorem TraitBodyRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TraitBodyRejects input left)
    (rightRejected : TraitBodyRejects input right) : left = right := by
  cases leftRejected with
  | openingMissing leftOpeningAbsent =>
      cases rightRejected with
      | openingMissing => rfl
      | tailRejected rightOpeningSpan rightOpening rightTail =>
          exact False.elim
            (traitBody_absent_conflicts_exact leftOpeningAbsent rightOpening)
  | tailRejected leftOpeningSpan leftOpening leftTail =>
      cases rightRejected with
      | openingMissing rightOpeningAbsent =>
          exact False.elim
            (traitBody_absent_conflicts_exact rightOpeningAbsent leftOpening)
      | tailRejected rightOpeningSpan rightOpening rightTail =>
          have afterOpeningEq := leftOpening.output_unique rightOpening
          subst afterOpeningEq
          exact leftTail.output_unique rightTail

/-- Complete prioritized trait bodies have fully exact ordinary outcomes. -/
theorem traitBodyExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TraitBodyOrdinaryOutcomeParses
      TraitBodyRejects where
  toDeterministicOutcomeSpec := traitBodyDeterministicOutcomeSpec
  successValueUnique := TraitBodyOrdinaryOutcomeParses.value_unique
  rejectOutputUnique := TraitBodyRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTraitDeclarationExactnessProperties
/-! Exact values and rejection endpoints for complete trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem traitDecl_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A successful complete trait declaration fixes its AST. -/
theorem TraitDeclOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.TraitDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitDeclOrdinaryParses input left afterLeft)
    (rightParsed : TraitDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftGenerics leftWhere
      leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightGenerics rightWhere
          rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases genericParametersExactOutcomeSpec.successResultUnique
              leftGenerics rightGenerics with
            ⟨genericsEq, afterGenericsEq⟩
          subst genericsEq
          subst afterGenericsEq
          rcases optionalWhereClauseExactOutcomeSpec.successResultUnique
              leftWhere rightWhere with ⟨whereEq, afterWhereEq⟩
          subst whereEq
          subst afterWhereEq
          rcases leftBody.result_unique rightBody with
            ⟨bodySpanEq, methodsEq, afterBodyEq⟩
          subst bodySpanEq
          subst methodsEq
          rfl

/-- A successful complete trait declaration fixes its AST and remainder. -/
theorem TraitDeclOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.TraitDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitDeclOrdinaryParses input left afterLeft)
    (rightParsed : TraitDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The five-stage trait-declaration rejection sequence has one endpoint. -/
theorem TraitDeclRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TraitDeclRejects input left)
    (rightRejected : TraitDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [traitDecl_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      genericParametersExactOutcomeSpec.successOutputUnique,
      genericParametersExactOutcomeSpec.successRejectDisjoint,
      genericParametersExactOutcomeSpec.rejectOutputUnique,
      optionalWhereClauseExactOutcomeSpec.successOutputUnique,
      optionalWhereClauseExactOutcomeSpec.successRejectDisjoint,
      optionalWhereClauseExactOutcomeSpec.rejectOutputUnique,
      traitBodyExactOutcomeSpec.successOutputUnique,
      traitBodyExactOutcomeSpec.successRejectDisjoint,
      traitBodyExactOutcomeSpec.rejectOutputUnique]

/-- Complete broad trait declarations have fully exact ordinary outcomes. -/
theorem traitDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TraitDeclOrdinaryParses TraitDeclRejects where
  toDeterministicOutcomeSpec := traitDeclDeterministicOutcomeSpec
  successValueUnique := TraitDeclOrdinaryParses.value_unique
  rejectOutputUnique := TraitDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFallbackDeclarationExactnessProperties
/-!
Exactness transport through broad fallback declarations.

The sole remaining premise is an exact isolated `.require` Core body.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem fallback_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Fallback success has one exact AST whenever its isolated body has exact
outcomes. -/
theorem FallbackDeclOrdinaryParses.value_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input : Remainder} {left right : Syntax.FallbackDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FallbackDeclOrdinaryParses input left afterLeft)
    (rightParsed : FallbackDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftParameters leftValidation
        leftModifiers leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightParameters rightValidation
            rightModifiers rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          cases markerSpanEq
          cases afterMarkerEq
          rcases functionParametersExactOutcomeSpec.successResultUnique
              leftParameters rightParameters with
            ⟨parametersEq, afterParametersEq⟩
          cases parametersEq
          cases afterParametersEq
          have afterValidationEq : _ := leftValidation.output_eq_input.trans
            rightValidation.output_eq_input.symm
          cases afterValidationEq
          rcases leftModifiers.result_unique rightModifiers with
            ⟨payableEq, afterModifiersEq⟩
          cases payableEq
          cases afterModifiersEq
          rcases bodyOutcomes.successResultUnique leftBody rightBody with
            ⟨bodyEq, afterBodyEq⟩
          cases bodyEq
          rfl

/-- Under an exact body contract, fallback success fixes its AST and final
remainder. -/
theorem FallbackDeclOrdinaryParses.result_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input : Remainder} {left right : Syntax.FallbackDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FallbackDeclOrdinaryParses input left afterLeft)
    (rightParsed : FallbackDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_exact_body bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Fallback rejection has one endpoint whenever its isolated body has exact
outcomes. -/
theorem FallbackDeclRejects.output_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input left right : Remainder}
    (leftRejected : FallbackDeclRejects input left)
    (rightRejected : FallbackDeclRejects input right) : left = right := by
  cases leftRejected with
  | markerMissing leftMarkerAbsent =>
      cases rightRejected with
      | markerMissing => rfl
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          exact False.elim
            (fallback_absent_conflicts_exact leftMarkerAbsent rightMarker)
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightValidation rightModifiers rightBody =>
          exact False.elim
            (fallback_absent_conflicts_exact leftMarkerAbsent rightMarker)
  | parametersRejected leftMarkerSpan leftMarker leftParameters =>
      cases rightRejected with
      | markerMissing rightMarkerAbsent =>
          exact False.elim
            (fallback_absent_conflicts_exact rightMarkerAbsent leftMarker)
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact functionParametersExactOutcomeSpec.rejectOutputUnique
            leftParameters rightParameters
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightValidation rightModifiers rightBody =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact False.elim
            (functionParametersExactOutcomeSpec.successRejectDisjoint
              leftParameters ⟨_, _, rightParameters⟩)
  | bodyRejected leftMarkerSpan leftMarker leftParameters leftValidation
      leftModifiers leftBody =>
      cases rightRejected with
      | markerMissing rightMarkerAbsent =>
          exact False.elim
            (fallback_absent_conflicts_exact rightMarkerAbsent leftMarker)
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact False.elim
            (functionParametersExactOutcomeSpec.successRejectDisjoint
              rightParameters ⟨_, _, leftParameters⟩)
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightValidation rightModifiers rightBody =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          have afterParametersEq :=
            functionParametersExactOutcomeSpec.successOutputUnique
              leftParameters rightParameters
          cases afterParametersEq
          have afterValidationEq : _ := leftValidation.output_eq_input.trans
            rightValidation.output_eq_input.symm
          cases afterValidationEq
          have afterModifiersEq := leftModifiers.output_unique rightModifiers
          cases afterModifiersEq
          exact bodyOutcomes.rejectOutputUnique leftBody rightBody

/-- An exact isolated required body lifts to fully exact fallback declaration
outcomes. -/
theorem fallbackDeclExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require)) :
    ExactDeterministicOutcomeSpec FallbackDeclOrdinaryParses
      FallbackDeclRejects where
  toDeterministicOutcomeSpec := fallbackDeclDeterministicOutcomeSpec
  successValueUnique :=
    FallbackDeclOrdinaryParses.value_unique_of_exact_body bodyOutcomes
  rejectOutputUnique :=
    FallbackDeclRejects.output_unique_of_exact_body bodyOutcomes

/-- Fixed-fuel Core-statement exactness supplies the isolated body contract
needed for fully exact fallback declarations. -/
theorem fallbackDeclExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec FallbackDeclOrdinaryParses
      FallbackDeclRejects :=
  fallbackDeclExactOutcomeSpecOfBody
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .require)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeConstructorDeclarationExactnessProperties
/-!
Exactness transport through constructor declarations.

The remaining premises are exact recovery-aware parameters and exact isolated
`.require` Core blocks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem constructor_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Constructor success has one exact AST whenever its parameter and body
children have exact outcomes. -/
theorem ConstructorDeclOrdinaryParses.value_unique_of_exact_children
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      FunctionParametersOrdinaryParses FunctionParametersRejects)
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input : Remainder} {left right : Syntax.ConstructorDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorDeclOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftParameters leftModifiers leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightParameters rightModifiers
          rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          cases markerSpanEq
          cases afterMarkerEq
          rcases parameterOutcomes.successResultUnique leftParameters
              rightParameters with ⟨parametersEq, afterParametersEq⟩
          cases parametersEq
          cases afterParametersEq
          rcases leftModifiers.result_unique rightModifiers with
            ⟨payableEq, afterModifiersEq⟩
          cases payableEq
          cases afterModifiersEq
          rcases bodyOutcomes.successResultUnique leftBody rightBody with
            ⟨bodyEq, afterBodyEq⟩
          cases bodyEq
          rfl

/-- Under exact child contracts, constructor success fixes its AST and final
remainder. -/
theorem ConstructorDeclOrdinaryParses.result_unique_of_exact_children
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      FunctionParametersOrdinaryParses FunctionParametersRejects)
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input : Remainder} {left right : Syntax.ConstructorDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorDeclOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_exact_children parameterOutcomes
      bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Constructor rejection has one endpoint whenever its parameter and body
children have exact outcomes. -/
theorem ConstructorDeclRejects.output_unique_of_exact_children
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      FunctionParametersOrdinaryParses FunctionParametersRejects)
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input left right : Remainder}
    (leftRejects : ConstructorDeclRejects input left)
    (rightRejects : ConstructorDeclRejects input right) : left = right := by
  cases leftRejects with
  | markerMissing leftMarkerAbsent =>
      cases rightRejects with
      | markerMissing => rfl
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          exact False.elim
            (constructor_absent_conflicts_exact leftMarkerAbsent rightMarker)
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightModifiers rightBody =>
          exact False.elim
            (constructor_absent_conflicts_exact leftMarkerAbsent rightMarker)
  | parametersRejected leftMarkerSpan leftMarker leftParameters =>
      cases rightRejects with
      | markerMissing rightMarkerAbsent =>
          exact False.elim
            (constructor_absent_conflicts_exact rightMarkerAbsent leftMarker)
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact parameterOutcomes.rejectOutputUnique leftParameters
            rightParameters
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightModifiers rightBody =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact False.elim
            (parameterOutcomes.successRejectDisjoint leftParameters
              ⟨_, _, rightParameters⟩)
  | bodyRejected leftMarkerSpan leftMarker leftParameters leftModifiers
      leftBody =>
      cases rightRejects with
      | markerMissing rightMarkerAbsent =>
          exact False.elim
            (constructor_absent_conflicts_exact rightMarkerAbsent leftMarker)
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact False.elim
            (parameterOutcomes.successRejectDisjoint rightParameters
              ⟨_, _, leftParameters⟩)
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightModifiers rightBody =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          have afterParametersEq := parameterOutcomes.successOutputUnique
            leftParameters rightParameters
          cases afterParametersEq
          have afterModifiersEq := leftModifiers.output_unique rightModifiers
          cases afterModifiersEq
          exact bodyOutcomes.rejectOutputUnique leftBody rightBody

/-- Exact parameter and isolated-body contracts lift to the complete broad
constructor outcome. -/
theorem constructorDeclExactOutcomeSpecOfChildren
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      FunctionParametersOrdinaryParses FunctionParametersRejects)
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require)) :
    ExactDeterministicOutcomeSpec ConstructorDeclOrdinaryParses
      ConstructorDeclRejects where
  toDeterministicOutcomeSpec := constructorDeclDeterministicOutcomeSpec
  successValueUnique :=
    ConstructorDeclOrdinaryParses.value_unique_of_exact_children
      parameterOutcomes bodyOutcomes
  rejectOutputUnique :=
    ConstructorDeclRejects.output_unique_of_exact_children
      parameterOutcomes bodyOutcomes

/-- Once named-parameter exactness is instantiated, an exact isolated body is
the sole remaining premise for exact constructor outcomes. -/
theorem constructorDeclExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require)) :
    ExactDeterministicOutcomeSpec ConstructorDeclOrdinaryParses
      ConstructorDeclRejects :=
  constructorDeclExactOutcomeSpecOfChildren
    functionParametersExactOutcomeSpec bodyOutcomes

/-- With an exact isolated body, constructor success fixes its AST and final
remainder. -/
theorem ConstructorDeclOrdinaryParses.result_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input : Remainder} {left right : Syntax.ConstructorDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorDeclOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  (constructorDeclExactOutcomeSpecOfBody bodyOutcomes).successResultUnique
    leftParsed rightParsed

/-- With an exact isolated body, constructor rejection fixes its endpoint. -/
theorem ConstructorDeclRejects.output_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input left right : Remainder}
    (leftRejects : ConstructorDeclRejects input left)
    (rightRejects : ConstructorDeclRejects input right) : left = right :=
  (constructorDeclExactOutcomeSpecOfBody bodyOutcomes).rejectOutputUnique
    leftRejects rightRejects

/-- Fixed-fuel Core statement exactness discharges the complete constructor
body and therefore the constructor itself. -/
theorem constructorDeclExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ConstructorDeclOrdinaryParses
      ConstructorDeclRejects :=
  constructorDeclExactOutcomeSpecOfBody
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .require)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplHeadArgumentsExactnessProperties
/-! Exact outcomes for required implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem implHeadArgumentListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (NonemptyTrailingDelimitedListParses .less .greater
        TypeExprOrdinaryParses)
      (DelimitedListRejects .less .greater false true
        TypeExprOrdinaryParses TypeExprRejects) :=
  nonemptyTrailingDelimitedListExactOutcomeSpec .less .greater
    typeExprExactOutcomeSpec

/-- Implementation head arguments fix their nonempty delimited-list AST. -/
theorem ImplHeadArgumentsOrdinaryParses.value_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplHeadArgumentsOrdinaryParses input left afterLeft)
    (rightParsed : ImplHeadArgumentsOrdinaryParses input right afterRight) :
    left = right := by
  have encodedEq := implHeadArgumentListExactOutcomeSpec
    |>.successValueUnique leftParsed rightParsed
  cases left with
  | mk leftSpan leftElements =>
      cases leftElements with
      | mk leftHead leftTail =>
          cases right with
          | mk rightSpan rightElements =>
              cases rightElements with
              | mk rightHead rightTail =>
                  simp [Syntax.NonemptyList.toList] at encodedEq
                  simp_all

/-- Implementation head arguments fix their AST and final remainder. -/
theorem ImplHeadArgumentsOrdinaryParses.result_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplHeadArgumentsOrdinaryParses input left afterLeft)
    (rightParsed : ImplHeadArgumentsOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Implementation head-argument rejection has one exact endpoint. -/
theorem ImplHeadArgumentsRejects.output_unique
    {input left right : Remainder}
    (leftRejected : ImplHeadArgumentsRejects input left)
    (rightRejected : ImplHeadArgumentsRejects input right) : left = right :=
  implHeadArgumentListExactOutcomeSpec.rejectOutputUnique leftRejected
    rightRejected

/-- Required implementation head arguments have fully exact outcomes. -/
theorem implHeadArgumentsExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ImplHeadArgumentsOrdinaryParses
      ImplHeadArgumentsRejects where
  toDeterministicOutcomeSpec := implHeadArgumentsDeterministicOutcomeSpec
  successValueUnique := ImplHeadArgumentsOrdinaryParses.value_unique
  rejectOutputUnique := ImplHeadArgumentsRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplDeclarationExactnessProperties
/-! Exactness transport through complete implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem implDecl_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- An exact implementation-body contract makes a declaration fix its AST. -/
theorem ImplDeclOrdinaryParses.value_unique_of_impl_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ImplBodyOrdinaryOutcomeParses ImplBodyRejects)
    {input : Remainder} {left right : Syntax.ImplDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImplDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftDefault leftMarkerSpan leftMarker leftGenerics leftName
      leftArguments leftWhere leftBody =>
      cases rightParsed with
      | parsed rightDefault rightMarkerSpan rightMarker rightGenerics
          rightName rightArguments rightWhere rightBody =>
          rcases leftDefault.result_unique rightDefault with
            ⟨defaultEq, afterDefaultEq⟩
          subst defaultEq
          subst afterDefaultEq
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases optionalGenericParametersExactOutcomeSpec.successResultUnique
              leftGenerics rightGenerics with
            ⟨genericsEq, afterGenericsEq⟩
          subst genericsEq
          subst afterGenericsEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases implHeadArgumentsExactOutcomeSpec.successResultUnique
              leftArguments rightArguments with
            ⟨argumentsEq, afterArgumentsEq⟩
          subst argumentsEq
          subst afterArgumentsEq
          rcases optionalWhereClauseExactOutcomeSpec.successResultUnique
              leftWhere rightWhere with ⟨whereEq, afterWhereEq⟩
          subst whereEq
          subst afterWhereEq
          have bodyEq := bodyOutcomes.successValueUnique
            (show ImplBodyOrdinaryOutcomeParses _ (_, _) _ from leftBody)
            (show ImplBodyOrdinaryOutcomeParses _ (_, _) _ from rightBody)
          cases bodyEq
          rfl

/-- Under an exact implementation-body contract, declaration success fixes
its AST and final remainder. -/
theorem ImplDeclOrdinaryParses.result_unique_of_impl_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ImplBodyOrdinaryOutcomeParses ImplBodyRejects)
    {input : Remainder} {left right : Syntax.ImplDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImplDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_impl_body bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- An exact implementation body makes declaration rejection fix its first
failing endpoint. -/
theorem ImplDeclRejects.output_unique_of_impl_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ImplBodyOrdinaryOutcomeParses ImplBodyRejects)
    {input left right : Remainder}
    (leftRejected : ImplDeclRejects input left)
    (rightRejected : ImplDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 12) [
      OptionalImplDefaultMarkerOrdinaryParses.output_unique,
      implDecl_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      optionalGenericParametersExactOutcomeSpec.successOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successRejectDisjoint,
      optionalGenericParametersExactOutcomeSpec.rejectOutputUnique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      implHeadArgumentsExactOutcomeSpec.successOutputUnique,
      implHeadArgumentsExactOutcomeSpec.successRejectDisjoint,
      implHeadArgumentsExactOutcomeSpec.rejectOutputUnique,
      optionalWhereClauseExactOutcomeSpec.successOutputUnique,
      optionalWhereClauseExactOutcomeSpec.successRejectDisjoint,
      optionalWhereClauseExactOutcomeSpec.rejectOutputUnique,
      bodyOutcomes.rejectOutputUnique]

/-- An exact complete implementation body lifts to exact declaration
outcomes. -/
theorem implDeclExactOutcomeSpecOfImplBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ImplBodyOrdinaryOutcomeParses ImplBodyRejects) :
    ExactDeterministicOutcomeSpec ImplDeclOrdinaryParses
      ImplDeclRejects where
  toDeterministicOutcomeSpec := implDeclDeterministicOutcomeSpec
  successValueUnique :=
    ImplDeclOrdinaryParses.value_unique_of_impl_body bodyOutcomes
  rejectOutputUnique :=
    ImplDeclRejects.output_unique_of_impl_body bodyOutcomes

/-- An exact isolated `.allow` Core body lifts through methods, the complete
implementation body, and the implementation declaration. -/
theorem implDeclExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow)) :
    ExactDeterministicOutcomeSpec ImplDeclOrdinaryParses ImplDeclRejects :=
  implDeclExactOutcomeSpecOfImplBody
    (implBodyExactOutcomeSpecOfBody bodyOutcomes)

/-- With an exact isolated method body, implementation declaration success
fixes its AST and final remainder. -/
theorem ImplDeclOrdinaryParses.result_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input : Remainder} {left right : Syntax.ImplDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImplDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  (implDeclExactOutcomeSpecOfBody bodyOutcomes).successResultUnique leftParsed
    rightParsed

/-- With an exact isolated method body, implementation declaration rejection
fixes its endpoint. -/
theorem ImplDeclRejects.output_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input left right : Remainder}
    (leftRejected : ImplDeclRejects input left)
    (rightRejected : ImplDeclRejects input right) : left = right :=
  (implDeclExactOutcomeSpecOfBody bodyOutcomes).rejectOutputUnique leftRejected
    rightRejected

/-- Fixed-fuel Core-statement exactness supplies exact implementation
declaration outcomes. -/
theorem implDeclExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ImplDeclOrdinaryParses ImplDeclRejects :=
  implDeclExactOutcomeSpecOfImplBody
    (implBodyExactOutcomeSpecOfStatementFuel statementOutcomes)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractFieldExactnessProperties
/-!
Exactness transport through contract storage fields.

Core types are already unconditionally exact.  The only premise is an exact
outcome contract for the optional initializer expression.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem field_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- An exact initializer expression fixes the optional initializer value. -/
theorem OptionalContractFieldInitializerOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightEqual rightExpression =>
          exact False.elim
            (field_absent_conflicts_exact leftAbsent rightEqual)
  | present leftSpan leftEqual leftExpression =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (field_absent_conflicts_exact rightAbsent leftEqual)
      | present rightSpan rightEqual rightExpression =>
          have afterEqualEq := leftEqual.output_unique rightEqual
          subst afterEqualEq
          have expressionEq := expressionOutcomes.successValueUnique
            leftExpression rightExpression
          subst expressionEq
          rfl

/-- An exact initializer expression fixes both the optional value and final
remainder. -/
theorem OptionalContractFieldInitializerOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique expressionOutcomes rightParsed,
    leftParsed.output_unique
      expressionOutcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- An exact initializer expression fixes the committed rejection endpoint. -/
theorem OptionalContractFieldInitializerRejects.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input left right : Remainder}
    (leftRejects : OptionalContractFieldInitializerRejects expressionRejects
      input left)
    (rightRejects : OptionalContractFieldInitializerRejects expressionRejects
      input right) : left = right := by
  cases leftRejects with
  | expressionRejected leftSpan leftEqual leftExpression =>
      cases rightRejects with
      | expressionRejected rightSpan rightEqual rightExpression =>
          have afterEqualEq := leftEqual.output_unique rightEqual
          subst afterEqualEq
          exact expressionOutcomes.rejectOutputUnique leftExpression
            rightExpression

/-- Exact expression outcomes lift through the optional `=` initializer. -/
theorem optionalContractFieldInitializerExactOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    ExactDeterministicOutcomeSpec
      (OptionalContractFieldInitializerOrdinaryParses expressionOrdinary)
      (OptionalContractFieldInitializerRejects expressionRejects) where
  toDeterministicOutcomeSpec :=
    optionalContractFieldInitializerDeterministicOutcomeSpec
      expressionOutcomes.toDeterministicOutcomeSpec
  successValueUnique :=
    OptionalContractFieldInitializerOrdinaryParses.value_unique
      expressionOutcomes
  rejectOutputUnique :=
    OptionalContractFieldInitializerRejects.output_unique expressionOutcomes

/-- Exact initializer outcomes make a successful field fix its complete AST. -/
theorem ContractFieldOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ContractField}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractFieldOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ContractFieldOrdinaryParses expressionOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftColonSpan leftSemicolonSpan leftName leftColon leftType
      leftInitializer leftSemicolon =>
      cases rightParsed with
      | parsed rightColonSpan rightSemicolonSpan rightName rightColon rightType
          rightInitializer rightSemicolon =>
          rcases leftName.result_unique rightName with
            ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases leftColon.result_unique rightColon with
            ⟨colonSpanEq, afterColonEq⟩
          subst colonSpanEq
          subst afterColonEq
          rcases typeExprExactOutcomeSpec.successResultUnique leftType
              rightType with ⟨typeEq, afterTypeEq⟩
          subst typeEq
          subst afterTypeEq
          rcases (optionalContractFieldInitializerExactOutcomeSpec
              expressionOutcomes).successResultUnique leftInitializer
              rightInitializer with ⟨initializerEq, afterInitializerEq⟩
          subst initializerEq
          subst afterInitializerEq
          have semicolonSpanEq := leftSemicolon.span_unique rightSemicolon
          subst semicolonSpanEq
          rfl

/-- Exact initializer outcomes fix the complete field AST and remainder. -/
theorem ContractFieldOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ContractField}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractFieldOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ContractFieldOrdinaryParses expressionOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique expressionOutcomes rightParsed,
    leftParsed.output_unique expressionOutcomes.toDeterministicOutcomeSpec
      rightParsed⟩

/-- The five-stage field rejection sequence has one endpoint. -/
theorem ContractFieldRejects.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input left right : Remainder}
    (leftRejects : ContractFieldRejects expressionOrdinary expressionRejects
      input left)
    (rightRejects : ContractFieldRejects expressionOrdinary expressionRejects
      input right) : left = right := by
  cases leftRejects <;> cases rightRejects <;>
    grind (ematch := 10) [field_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      typeExprExactOutcomeSpec.successOutputUnique,
      typeExprExactOutcomeSpec.successRejectDisjoint,
      typeExprExactOutcomeSpec.rejectOutputUnique,
      (optionalContractFieldInitializerExactOutcomeSpec
        expressionOutcomes).successOutputUnique,
      (optionalContractFieldInitializerExactOutcomeSpec
        expressionOutcomes).successRejectDisjoint,
      (optionalContractFieldInitializerExactOutcomeSpec
        expressionOutcomes).rejectOutputUnique]

/-- Exact initializer expressions lift to exact complete field outcomes. -/
theorem contractFieldExactOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses expressionOrdinary)
      (ContractFieldRejects expressionOrdinary expressionRejects) where
  toDeterministicOutcomeSpec := contractFieldDeterministicOutcomeSpec
    expressionOutcomes.toDeterministicOutcomeSpec
  successValueUnique := ContractFieldOrdinaryParses.value_unique
    expressionOutcomes
  rejectOutputUnique := ContractFieldRejects.output_unique expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeEnumConstructorExactnessProperties
/-! Exact values and rejection endpoints for enum constructors. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem enumConstructor_absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem enumConstructorFields_opening_present
    {input output : Remainder} {fields : DelimitedList Syntax.TypeExpr}
    (parsed : NoTrailingDelimitedListParses .leftParen .rightParen
      TypeExprParses input fields output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftParen } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- Constructor payload lists have exact Core type values and rejection
endpoints. -/
theorem enumConstructorFieldListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (NoTrailingDelimitedListParses .leftParen .rightParen
        TypeExprOrdinaryParses)
      (DelimitedListRejects .leftParen .rightParen true false
        TypeExprOrdinaryParses TypeExprRejects) :=
  noTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    typeExprExactOutcomeSpec

/-- Optional constructor payloads fix their absent or present AST value. -/
theorem OptionalEnumConstructorFieldsOrdinaryParses.value_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.TypeExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalEnumConstructorFieldsOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalEnumConstructorFieldsOrdinaryParses input right
      afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightFields =>
          rcases enumConstructorFields_opening_present rightFields with
            ⟨span, openingPresent⟩
          exact False.elim
            (enumConstructor_absent_conflicts_token leftAbsent openingPresent)
  | present leftFields =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases enumConstructorFields_opening_present leftFields with
            ⟨span, openingPresent⟩
          exact False.elim
            (enumConstructor_absent_conflicts_token rightAbsent openingPresent)
      | present rightFields =>
          rw [enumConstructorFieldListExactOutcomeSpec.successValueUnique
            leftFields rightFields]

/-- Optional constructor payloads fix both their value and remainder. -/
theorem OptionalEnumConstructorFieldsOrdinaryParses.result_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.TypeExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalEnumConstructorFieldsOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalEnumConstructorFieldsOrdinaryParses input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A committed optional constructor-payload rejection has one endpoint. -/
theorem OptionalEnumConstructorFieldsRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalEnumConstructorFieldsRejects input left)
    (rightRejected : OptionalEnumConstructorFieldsRejects input right) :
    left = right := by
  cases leftRejected with
  | present _ leftFields =>
      cases rightRejected with
      | present _ rightFields =>
          exact enumConstructorFieldListExactOutcomeSpec.rejectOutputUnique
            leftFields rightFields

/-- Optional enum-constructor payloads have fully exact outcomes. -/
theorem optionalEnumConstructorFieldsExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      OptionalEnumConstructorFieldsOrdinaryParses
      OptionalEnumConstructorFieldsRejects where
  toDeterministicOutcomeSpec :=
    optionalEnumConstructorFieldsDeterministicOutcomeSpec
  successValueUnique :=
    OptionalEnumConstructorFieldsOrdinaryParses.value_unique
  rejectOutputUnique := OptionalEnumConstructorFieldsRejects.output_unique

/-- A successful enum constructor fixes its complete AST. -/
theorem EnumConstructorOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumConstructorOrdinaryParses input left afterLeft)
    (rightParsed : EnumConstructorOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftName leftFields =>
      cases rightParsed with
      | parsed rightName rightFields =>
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases optionalEnumConstructorFieldsExactOutcomeSpec
              |>.successResultUnique leftFields rightFields with
            ⟨fieldsEq, afterFieldsEq⟩
          subst fieldsEq
          rfl

/-- A successful enum constructor fixes its AST and final remainder. -/
theorem EnumConstructorOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumConstructorOrdinaryParses input left afterLeft)
    (rightParsed : EnumConstructorOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Enum-constructor rejection fixes its first failing endpoint. -/
theorem EnumConstructorRejects.output_unique
    {input left right : Remainder}
    (leftRejected : EnumConstructorRejects input left)
    (rightRejected : EnumConstructorRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      optionalEnumConstructorFieldsExactOutcomeSpec.rejectOutputUnique]

/-- Enum constructors have fully exact ordinary outcomes. -/
theorem enumConstructorExactOutcomeSpec :
    ExactDeterministicOutcomeSpec EnumConstructorOrdinaryParses
      EnumConstructorRejects where
  toDeterministicOutcomeSpec := enumConstructorDeterministicOutcomeSpec
  successValueUnique := EnumConstructorOrdinaryParses.value_unique
  rejectOutputUnique := EnumConstructorRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeEnumBodyExactnessProperties
/-! Exact values and rejection endpoints for canonical enum bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem enumBodyListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (TrailingDelimitedListParses .leftBrace .rightBrace
        EnumConstructorOrdinaryParses)
      EnumBodyRejects :=
  trailingDelimitedListExactOutcomeSpec .leftBrace .rightBrace
    enumConstructorExactOutcomeSpec

/-- A successful enum body fixes its span, constructors, and remainder. -/
theorem EnumBodyOrdinaryParses.result_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftConstructors rightConstructors : List Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumBodyOrdinaryParses input leftSpan leftConstructors
      afterLeft)
    (rightParsed : EnumBodyOrdinaryParses input rightSpan rightConstructors
      afterRight) :
    leftSpan = rightSpan ∧ leftConstructors = rightConstructors ∧
      afterLeft = afterRight := by
  rcases enumBodyListExactOutcomeSpec.successResultUnique leftParsed
      rightParsed with ⟨bodyEq, outputEq⟩
  cases bodyEq
  exact ⟨rfl, rfl, outputEq⟩

/-- The single-value enum-body adapter fixes its span and constructor list. -/
theorem EnumBodyOrdinaryOutcomeParses.value_unique
    {input : Remainder}
    {left right : SourceSpan × List Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumBodyOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : EnumBodyOrdinaryOutcomeParses input right afterRight) :
    left = right := by
  rcases EnumBodyOrdinaryParses.result_unique leftParsed rightParsed with
    ⟨spanEq, constructorsEq, outputEq⟩
  exact Prod.ext spanEq constructorsEq

/-- Enum-body rejection fixes its first failing endpoint. -/
theorem EnumBodyRejects.output_unique
    {input left right : Remainder}
    (leftRejected : EnumBodyRejects input left)
    (rightRejected : EnumBodyRejects input right) : left = right :=
  enumBodyListExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

/-- Canonical enum bodies have fully exact ordinary outcomes. -/
theorem enumBodyExactOutcomeSpec :
    ExactDeterministicOutcomeSpec EnumBodyOrdinaryOutcomeParses
      EnumBodyRejects where
  toDeterministicOutcomeSpec := enumBodyDeterministicOutcomeSpec
  successValueUnique := EnumBodyOrdinaryOutcomeParses.value_unique
  rejectOutputUnique := EnumBodyRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeEnumDeclarationExactnessProperties
/-! Exact values and rejection endpoints for complete enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem enumDecl_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- At any fixed supplied derive attribute, successful enum declarations fix
their complete AST. -/
theorem EnumDeclOrdinaryParses.value_unique
    (deriveAttribute : Option Syntax.DeriveAttribute)
    {input : Remainder} {left right : Syntax.EnumDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumDeclOrdinaryParses deriveAttribute input left afterLeft)
    (rightParsed : EnumDeclOrdinaryParses deriveAttribute input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftParameters leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightParameters
          rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases optionalGenericParametersExactOutcomeSpec.successResultUnique
              leftParameters rightParameters with
            ⟨parametersEq, afterParametersEq⟩
          subst parametersEq
          subst afterParametersEq
          rcases EnumBodyOrdinaryParses.result_unique leftBody rightBody with
            ⟨bodySpanEq, constructorsEq, afterBodyEq⟩
          subst bodySpanEq
          subst constructorsEq
          rfl

/-- At any fixed supplied derive attribute, successful enum declarations fix
their AST and final remainder. -/
theorem EnumDeclOrdinaryParses.result_unique
    (deriveAttribute : Option Syntax.DeriveAttribute)
    {input : Remainder} {left right : Syntax.EnumDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumDeclOrdinaryParses deriveAttribute input left afterLeft)
    (rightParsed : EnumDeclOrdinaryParses deriveAttribute input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique deriveAttribute rightParsed,
    leftParsed.output_unique deriveAttribute rightParsed⟩

/-- The four-stage enum-declaration rejection sequence has one endpoint. -/
theorem EnumDeclRejects.output_unique
    {input left right : Remainder}
    (leftRejected : EnumDeclRejects input left)
    (rightRejected : EnumDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [enumDecl_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successRejectDisjoint,
      optionalGenericParametersExactOutcomeSpec.rejectOutputUnique,
      enumBodyExactOutcomeSpec.successOutputUnique,
      enumBodyExactOutcomeSpec.successRejectDisjoint,
      enumBodyExactOutcomeSpec.rejectOutputUnique]

/-- For every fixed supplied derive attribute, complete enum declarations have
fully exact ordinary outcomes. -/
theorem enumDeclExactOutcomeSpec
    (deriveAttribute : Option Syntax.DeriveAttribute) :
    ExactDeterministicOutcomeSpec (EnumDeclOrdinaryParses deriveAttribute)
      EnumDeclRejects where
  toDeterministicOutcomeSpec :=
    enumDeclDeterministicOutcomeSpec deriveAttribute
  successValueUnique :=
    EnumDeclOrdinaryParses.value_unique deriveAttribute
  rejectOutputUnique := EnumDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeAliasValueExactnessProperties
/-! Unconditional exactness of recovery-aware type-alias values. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Recovery-aware alias-value success constructs one exact type AST. -/
theorem TypeAliasValueOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasValueOrdinaryParses input right afterRight) :
    left = right :=
  leftParsed.value_unique_of_typeExpr typeExprExactOutcomeSpec rightParsed

/-- Recovery-aware alias-value success fixes its AST and final remainder. -/
theorem TypeAliasValueOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasValueOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  leftParsed.result_unique_of_typeExpr typeExprExactOutcomeSpec rightParsed

/-- Recovery-aware type-alias values have fully exact ordinary outcomes. -/
theorem typeAliasValueExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TypeAliasValueOrdinaryParses
      TypeAliasValueRejects :=
  typeAliasValueExactOutcomeSpecOfTypeExpr typeExprExactOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeAliasDeclarationExactnessProperties
/-! Full exact outcomes for recovery-aware transparent type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem typeAlias_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A complete type-alias success constructs one exact declaration AST. -/
theorem TypeAliasDeclOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.TypeAliasDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasDeclOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftKeywordSpan leftEqualSpan leftSemicolonSpan leftKeyword leftName
      leftParameters leftEqual leftValue leftSemicolon =>
      cases rightParsed with
      | parsed rightKeywordSpan rightEqualSpan rightSemicolonSpan rightKeyword
          rightName rightParameters rightEqual rightValue rightSemicolon =>
          rcases leftKeyword.result_unique rightKeyword with
            ⟨keywordSpanEq, afterKeywordEq⟩
          subst keywordSpanEq
          subst afterKeywordEq
          rcases leftName.result_unique rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases leftParameters.result_unique rightParameters with
            ⟨parametersEq, afterParametersEq⟩
          subst parametersEq
          subst afterParametersEq
          rcases leftEqual.result_unique rightEqual with
            ⟨equalSpanEq, afterEqualEq⟩
          subst equalSpanEq
          subst afterEqualEq
          rcases leftValue.result_unique rightValue with
            ⟨valueEq, afterValueEq⟩
          subst valueEq
          subst afterValueEq
          rcases leftSemicolon.result_unique rightSemicolon with
            ⟨semicolonSpanEq, afterSemicolonEq⟩
          subst semicolonSpanEq
          rfl

/-- A complete type-alias success fixes its AST and final remainder. -/
theorem TypeAliasDeclOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.TypeAliasDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasDeclOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The six-stage type-alias rejection sequence has one first failing
endpoint. -/
theorem TypeAliasDeclRejects.output_unique
    {input left right : Remainder}
    (leftRejects : TypeAliasDeclRejects input left)
    (rightRejects : TypeAliasDeclRejects input right) : left = right := by
  cases leftRejects <;> cases rightRejects <;>
    grind [typeAlias_absent_conflicts_exact, ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      optionalTypeAliasParametersExactOutcomeSpec.successOutputUnique,
      optionalTypeAliasParametersExactOutcomeSpec.successRejectDisjoint,
      optionalTypeAliasParametersExactOutcomeSpec.rejectOutputUnique,
      typeAliasValueExactOutcomeSpec.successOutputUnique,
      typeAliasValueExactOutcomeSpec.successRejectDisjoint,
      typeAliasValueExactOutcomeSpec.rejectOutputUnique]

/-- Transparent type aliases have fully exact broad ordinary outcomes. -/
theorem typeAliasDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TypeAliasDeclOrdinaryParses
      TypeAliasDeclRejects where
  toDeterministicOutcomeSpec := typeAliasDeclDeterministicOutcomeSpec
  successValueUnique := TypeAliasDeclOrdinaryParses.value_unique
  rejectOutputUnique := TypeAliasDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractMemberCoreExactnessProperties
/-!
Exactness transport through attribute-free contract-member dispatch.

Type aliases are unconditionally exact. The remaining premises expose the
Core expression, isolated Core bodies, and enum outcome leaves that have not
yet been proved exact globally.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem contractMemberCore_present_conflicts_absent
    {input : Remainder} {kind : TokenKind}
    (present : ContractMemberCoreTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent present

/-- Exact selected child outcomes make broad core-member success fix its AST. -/
theorem ContractMemberCoreOrdinaryParses.value_unique_of_exact_children
    (fieldOutcomes : ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses CoreExpressionOrdinaryParses)
      (ContractFieldRejects CoreExpressionOrdinaryParses
        CoreExpressionPublicRejects))
    (functionOutcomes : ExactDeterministicOutcomeSpec
      FunctionDeclOrdinaryParses FunctionDeclRejects)
    (constructorOutcomes : ExactDeterministicOutcomeSpec
      ConstructorDeclOrdinaryParses ConstructorDeclRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec
      FallbackDeclOrdinaryParses FallbackDeclRejects)
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects)
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberCoreOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberCoreOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind (ematch := 10) [contractMemberCore_present_conflicts_absent,
      fieldOutcomes.successValueUnique,
      functionOutcomes.successValueUnique,
      constructorOutcomes.successValueUnique,
      fallbackOutcomes.successValueUnique,
      typeAliasDeclExactOutcomeSpec.successValueUnique,
      enumOutcomes.successValueUnique]

/-- Exact selected children make broad core-member success fix its AST and
final remainder. -/
theorem ContractMemberCoreOrdinaryParses.result_unique_of_exact_children
    (fieldOutcomes : ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses CoreExpressionOrdinaryParses)
      (ContractFieldRejects CoreExpressionOrdinaryParses
        CoreExpressionPublicRejects))
    (functionOutcomes : ExactDeterministicOutcomeSpec
      FunctionDeclOrdinaryParses FunctionDeclRejects)
    (constructorOutcomes : ExactDeterministicOutcomeSpec
      ConstructorDeclOrdinaryParses ConstructorDeclRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec
      FallbackDeclOrdinaryParses FallbackDeclRejects)
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects)
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberCoreOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberCoreOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_exact_children fieldOutcomes functionOutcomes
      constructorOutcomes fallbackOutcomes enumOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Exact selected child outcomes make broad core-member rejection fix its
selected failure endpoint. -/
theorem ContractMemberCoreRejects.output_unique_of_exact_children
    (fieldOutcomes : ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses CoreExpressionOrdinaryParses)
      (ContractFieldRejects CoreExpressionOrdinaryParses
        CoreExpressionPublicRejects))
    (functionOutcomes : ExactDeterministicOutcomeSpec
      FunctionDeclOrdinaryParses FunctionDeclRejects)
    (constructorOutcomes : ExactDeterministicOutcomeSpec
      ConstructorDeclOrdinaryParses ConstructorDeclRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec
      FallbackDeclOrdinaryParses FallbackDeclRejects)
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects)
    {input left right : Remainder}
    (leftRejected : ContractMemberCoreRejects input left)
    (rightRejected : ContractMemberCoreRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [contractMemberCore_present_conflicts_absent,
      fieldOutcomes.rejectOutputUnique,
      functionOutcomes.rejectOutputUnique,
      constructorOutcomes.rejectOutputUnique,
      fallbackOutcomes.rejectOutputUnique,
      typeAliasDeclExactOutcomeSpec.rejectOutputUnique,
      enumOutcomes.rejectOutputUnique]

/-- Exact branch contracts lift through attribute-free contract-member
dispatch. -/
theorem contractMemberCoreExactOutcomeSpecOfChildren
    (fieldOutcomes : ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses CoreExpressionOrdinaryParses)
      (ContractFieldRejects CoreExpressionOrdinaryParses
        CoreExpressionPublicRejects))
    (functionOutcomes : ExactDeterministicOutcomeSpec
      FunctionDeclOrdinaryParses FunctionDeclRejects)
    (constructorOutcomes : ExactDeterministicOutcomeSpec
      ConstructorDeclOrdinaryParses ConstructorDeclRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec
      FallbackDeclOrdinaryParses FallbackDeclRejects)
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects) :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects where
  toDeterministicOutcomeSpec := contractMemberCoreDeterministicOutcomeSpec
  successValueUnique :=
    ContractMemberCoreOrdinaryParses.value_unique_of_exact_children
      fieldOutcomes functionOutcomes constructorOutcomes fallbackOutcomes
      enumOutcomes
  rejectOutputUnique :=
    ContractMemberCoreRejects.output_unique_of_exact_children fieldOutcomes
      functionOutcomes constructorOutcomes fallbackOutcomes enumOutcomes

/-- Exact public expressions, isolated bodies, and enums discharge every
remaining core-member leaf. The `.require` body contract is shared by
constructors and fallbacks. -/
theorem contractMemberCoreExactOutcomeSpecOfLeaves
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      CoreExpressionOrdinaryParses CoreExpressionPublicRejects)
    (allowBodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    (requireBodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects) :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects :=
  contractMemberCoreExactOutcomeSpecOfChildren
    (contractFieldExactOutcomeSpec expressionOutcomes)
    (functionDeclExactOutcomeSpecOfBody allowBodyOutcomes)
    (constructorDeclExactOutcomeSpecOfBody requireBodyOutcomes)
    (fallbackDeclExactOutcomeSpecOfBody requireBodyOutcomes)
    enumOutcomes

private theorem contractMemberCoreExpressionExactOutcomeSpecOfFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec CoreExpressionOrdinaryParses
      CoreExpressionPublicRejects where
  toDeterministicOutcomeSpec := coreExpressionPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (expressionOutcomes (coreExpressionPublicFuel input))
      |>.successValueUnique leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (expressionOutcomes (coreExpressionPublicFuel input))
      |>.rejectOutputUnique leftRejected rightRejected

/-- Fixed-fuel Core expression and statement exactness supplies all Core-term
leaves; enum exactness remains the sole non-Core premise. -/
theorem contractMemberCoreExactOutcomeSpecOfTermFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel))
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects) :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects :=
  contractMemberCoreExactOutcomeSpecOfLeaves
    (contractMemberCoreExpressionExactOutcomeSpecOfFuel expressionOutcomes)
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .allow)
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .require)
    enumOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractCoreTermExactnessProperties
/-!
Exact contract aggregates from only the remaining Core-term premises.

Unconditional enum exactness discharges the enum branch. The resulting core
member contract lifts through derive attachment and recovery-aware bodies to
complete contract declarations.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact public expressions and isolated Core bodies supply every remaining
core-member leaf. Enum declarations need no additional premise. -/
theorem contractMemberCoreExactOutcomeSpecOfCoreTerms
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      CoreExpressionOrdinaryParses CoreExpressionPublicRejects)
    (allowBodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    (requireBodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require)) :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects :=
  contractMemberCoreExactOutcomeSpecOfLeaves expressionOutcomes
    allowBodyOutcomes requireBodyOutcomes (enumDeclExactOutcomeSpec none)

/-- Fixed-fuel expression and statement exactness alone supplies exact
attribute-free contract members. -/
theorem contractMemberCoreExactOutcomeSpecOfCoreTermFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects :=
  contractMemberCoreExactOutcomeSpecOfTermFuel expressionOutcomes
    statementOutcomes (enumDeclExactOutcomeSpec none)

/-- Fixed-fuel Core-term exactness lifts through derive-aware contract-member
dispatch without further declaration premises. -/
theorem contractMemberExactOutcomeSpecOfCoreTermFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ContractMemberOrdinaryParses
      ContractMemberRejects :=
  contractMemberExactOutcomeSpecOfCore
    (contractMemberCoreExactOutcomeSpecOfCoreTermFuel expressionOutcomes
      statementOutcomes)

/-- Fixed-fuel Core-term exactness lifts through derive attachment and the
recovery-aware body loop to complete contract bodies. -/
theorem contractBodyExactOutcomeSpecOfCoreTermFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ContractBodyOrdinaryOutcomeParses
      ContractBodyRejects :=
  contractBodyExactOutcomeSpecOfCore
    (contractMemberCoreExactOutcomeSpecOfCoreTermFuel expressionOutcomes
      statementOutcomes)

/-- Fixed-fuel Core expression and statement exactness is sufficient for exact
complete contract declarations, including derive attachment and recovery. -/
theorem contractDeclExactOutcomeSpecOfCoreTermFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ContractDeclOrdinaryParses
      ContractDeclRejects :=
  contractDeclExactOutcomeSpecOfCore
    (contractMemberCoreExactOutcomeSpecOfCoreTermFuel expressionOutcomes
      statementOutcomes)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreDeclarationExactnessProperties
/-!
Unconditional exact Core declarations from exact recursive Core terms.

The existing conditional declarations retain their signatures. These thin
specializations discharge their body and initializer premises using the closed
Core term fuel induction, including isolated-body recovery and derive layers.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Function declarations have exact ordinary ASTs and rejection endpoints. -/
theorem functionDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FunctionDeclOrdinaryParses
      FunctionDeclRejects :=
  functionDeclExactOutcomeSpecOfStatementFuel
    coreStatementExactOutcomeSpecWithFuel

/-- Constructor declarations have exact ordinary outcomes without body premises. -/
theorem constructorDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ConstructorDeclOrdinaryParses
      ConstructorDeclRejects :=
  constructorDeclExactOutcomeSpecOfStatementFuel
    coreStatementExactOutcomeSpecWithFuel

/-- Fallback declarations have exact ordinary outcomes without body premises. -/
theorem fallbackDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FallbackDeclOrdinaryParses
      FallbackDeclRejects :=
  fallbackDeclExactOutcomeSpecOfStatementFuel
    coreStatementExactOutcomeSpecWithFuel

/-- Implementation methods have unconditional exact ordinary outcomes. -/
theorem implMethodExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ImplMethodOrdinaryParses ImplMethodRejects :=
  implMethodExactOutcomeSpecOfStatementFuel coreStatementExactOutcomeSpecWithFuel

/-- Implementation bodies have unconditional exact method lists and spans. -/
theorem implBodyExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ImplBodyOrdinaryOutcomeParses ImplBodyRejects :=
  implBodyExactOutcomeSpecOfStatementFuel coreStatementExactOutcomeSpecWithFuel

/-- Complete implementation declarations have unconditional exact outcomes. -/
theorem implDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ImplDeclOrdinaryParses ImplDeclRejects :=
  implDeclExactOutcomeSpecOfStatementFuel coreStatementExactOutcomeSpecWithFuel

/-- Fields with public Core-expression initializers have unconditional exact
outcomes; the generic expression-parameterized field contract remains available. -/
theorem contractFieldPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses CoreExpressionOrdinaryParses)
      (ContractFieldRejects CoreExpressionOrdinaryParses
        CoreExpressionPublicRejects) :=
  contractFieldExactOutcomeSpec coreExpressionPublicExactOutcomeSpec

/-- Attribute-free contract-member dispatch has unconditional exact outcomes. -/
theorem contractMemberCoreExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects :=
  contractMemberCoreExactOutcomeSpecOfCoreTermFuel
    coreExpressionExactOutcomeSpecWithFuel coreStatementExactOutcomeSpecWithFuel

/-- Derive-aware contract members have unconditional exact ordinary outcomes. -/
theorem contractMemberExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ContractMemberOrdinaryParses
      ContractMemberRejects :=
  contractMemberExactOutcomeSpecOfCoreTermFuel
    coreExpressionExactOutcomeSpecWithFuel coreStatementExactOutcomeSpecWithFuel

/-- Recovery-aware contract bodies have unconditional exact values and endpoints. -/
theorem contractBodyExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ContractBodyOrdinaryOutcomeParses
      ContractBodyRejects :=
  contractBodyExactOutcomeSpecOfCoreTermFuel
    coreExpressionExactOutcomeSpecWithFuel coreStatementExactOutcomeSpecWithFuel

/-- Complete contract declarations have unconditional exact ordinary outcomes. -/
theorem contractDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ContractDeclOrdinaryParses ContractDeclRejects :=
  contractDeclExactOutcomeSpecOfCoreTermFuel
    coreExpressionExactOutcomeSpecWithFuel coreStatementExactOutcomeSpecWithFuel

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePlainTopItemExactnessProperties
/-! Exact prioritized top-item dispatch from its remaining module declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact import/export declarations close the remaining plain-item AST cases. -/
theorem PlainTopItemOrdinaryParses.value_unique_of_moduleDeclarations
    (importOutcomes : ExactDeterministicOutcomeSpec ImportDeclOrdinaryParses ImportDeclRejects)
    (exportOutcomes : ExactDeterministicOutcomeSpec ExportDeclOrdinaryParses ExportDeclRejects)
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : PlainTopItemOrdinaryParses input left afterLeft)
    (rightParsed : PlainTopItemOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed
  all_goals
    rename_i leftDeclaration leftSelected leftChild rightDeclaration rightSelected rightChild
    cases leftSelected.unique rightSelected
  all_goals first
    | have valueEq := importOutcomes.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := exportOutcomes.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := pragmaDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := typeAliasDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := functionDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := (enumDeclExactOutcomeSpec none).successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := traitDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := implDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := contractDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl

/-- Selected leaf failure fixes its endpoint; an unrecognized item rewinds. -/
theorem PlainTopItemRejects.output_unique_of_moduleDeclarations
    (importOutcomes : ExactDeterministicOutcomeSpec ImportDeclOrdinaryParses ImportDeclRejects)
    (exportOutcomes : ExactDeterministicOutcomeSpec ExportDeclOrdinaryParses ExportDeclRejects)
    {input left right : Remainder}
    (leftRejected : PlainTopItemRejects input left)
    (rightRejected : PlainTopItemRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected
  all_goals first
    | rename_i leftSelected leftChild rightSelected rightChild
      cases leftSelected.unique rightSelected
    | rename_i leftSelected leftChild rightSelected
      cases leftSelected.unique rightSelected
    | rename_i leftSelected rightSelected rightChild
      cases leftSelected.unique rightSelected
    | rfl
  all_goals first
    | exact importOutcomes.rejectOutputUnique (by assumption) (by assumption)
    | exact exportOutcomes.rejectOutputUnique (by assumption) (by assumption)
    | exact pragmaDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)
    | exact typeAliasDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)
    | exact functionDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)
    | exact (enumDeclExactOutcomeSpec none).rejectOutputUnique (by assumption) (by assumption)
    | exact traitDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)
    | exact implDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)
    | exact contractDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)

/-- The exact plain dispatcher needs only the two remaining module contracts. -/
theorem plainTopItemExactOutcomeSpecOfModuleDeclarations
    (importOutcomes : ExactDeterministicOutcomeSpec ImportDeclOrdinaryParses ImportDeclRejects)
    (exportOutcomes : ExactDeterministicOutcomeSpec ExportDeclOrdinaryParses ExportDeclRejects) :
    ExactDeterministicOutcomeSpec PlainTopItemOrdinaryParses PlainTopItemRejects where
  toDeterministicOutcomeSpec := plainTopItemDeterministicOutcomeSpec
  successValueUnique :=
    PlainTopItemOrdinaryParses.value_unique_of_moduleDeclarations importOutcomes exportOutcomes
  rejectOutputUnique :=
    PlainTopItemRejects.output_unique_of_moduleDeclarations importOutcomes exportOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSyntaxExactnessProperties
/-! Unconditional complete-file syntax exactness from every declaration branch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every prioritized attribute-free declaration now has an exact outcome. -/
theorem plainTopItemExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PlainTopItemOrdinaryParses PlainTopItemRejects :=
  plainTopItemExactOutcomeSpecOfModuleDeclarations
    importDeclExactOutcomeSpec exportDeclExactOutcomeSpec

/-- Leading derive attributes preserve unconditional top-item exactness. -/
theorem topItemExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TopItemOrdinaryParses TopItemRejects :=
  topItemExactOutcomeSpecOfPlain plainTopItemExactOutcomeSpec

/-- Recovery-aware file loops have exact source-order AST lists and endpoints. -/
theorem fileItemsExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FileItemsOrdinaryParses FileItemsRejects :=
  fileItemsExactOutcomeSpecOfTopItem topItemExactOutcomeSpec

/-- Fixed source provenance and comments give an exact complete raw-file result. -/
theorem sourceFileExactOutcomeSpec (file : Syntax.SourceFile)
    (comments : List Syntax.Comment) :
    ExactDeterministicOutcomeSpec (SourceFileOrdinaryParses file comments) SourceFileRejects :=
  sourceFileExactOutcomeSpecOfTopItem topItemExactOutcomeSpec file comments

/-- Attribute-free top items have one complete located AST and remainder. -/
theorem PlainTopItemOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.TopItem}
    (leftParsed : PlainTopItemOrdinaryParses input left afterLeft)
    (rightParsed : PlainTopItemOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  plainTopItemExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Derive-aware top items have one complete located AST and remainder. -/
theorem TopItemOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.TopItem}
    (leftParsed : TopItemOrdinaryParses input left afterLeft)
    (rightParsed : TopItemOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  topItemExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Attribute-free declaration rejection fixes the first failing remainder. -/
theorem PlainTopItemRejects.output_unique {input left right : Remainder}
    (leftRejected : PlainTopItemRejects input left)
    (rightRejected : PlainTopItemRejects input right) : left = right :=
  plainTopItemExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

/-- Derive-aware declaration rejection fixes the first failing remainder. -/
theorem TopItemRejects.output_unique {input left right : Remainder}
    (leftRejected : TopItemRejects input left)
    (rightRejected : TopItemRejects input right) : left = right :=
  topItemExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

/-- A recovery-aware file loop fixes the complete forward item list and remainder. -/
theorem FileItemsOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : List Syntax.TopItem}
    (leftParsed : FileItemsOrdinaryParses input left afterLeft)
    (rightParsed : FileItemsOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  fileItemsExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Comment attachment preserves unconditional complete source-file exactness. -/
theorem SourceFileOrdinaryParses.result_unique
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input afterLeft afterRight : Remainder} {left right : Syntax.ParsedFile}
    (leftParsed : SourceFileOrdinaryParses file comments input left afterLeft)
    (rightParsed : SourceFileOrdinaryParses file comments input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  (sourceFileExactOutcomeSpec file comments).successResultUnique leftParsed rightParsed

/-- Public source syntax has one AST, including nesting-overflow and recovery.
No public remainder, diagnostic trace, or rejection payload is part of this relation. -/
theorem PublicSourceFileOrdinaryParses.value_unique
    {file : Syntax.SourceFile} {tokens : List Syntax.Token} {comments : List Syntax.Comment}
    {left right : Syntax.ParsedFile}
    (leftParsed : PublicSourceFileOrdinaryParses file tokens comments left)
    (rightParsed : PublicSourceFileOrdinaryParses file tokens comments right) : left = right :=
  leftParsed.value_unique_of_exact_topItem topItemExactOutcomeSpec rightParsed

end Solcore.Syntax.DeclarativeGrammar
end
