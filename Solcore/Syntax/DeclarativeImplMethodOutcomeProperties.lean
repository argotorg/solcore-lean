import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeImplMethodOutcomeGrammar

/-! Deterministic exact ordinary outcomes for implementation methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary implementation-method success has one final remainder. -/
theorem ImplMethodOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplMethodOrdinaryParses input left afterLeft)
    (rightParsed : ImplMethodOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftDeclaration =>
      cases rightParsed with
      | parsed rightDeclaration =>
          exact leftDeclaration.output_unique rightDeclaration

/-- Nested declaration rejection excludes every ordinary method success. -/
theorem ImplMethodRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ImplMethodRejects input rejected) :
    ¬ ∃ method output, ImplMethodOrdinaryParses input method output := by
  rintro ⟨method, output, successful⟩
  cases rejection with
  | declarationRejected declarationRejected =>
      cases successful with
      | parsed declarationParsed =>
          exact functionDeclDeterministicOutcomeSpec.successRejectDisjoint
            declarationRejected ⟨_, _, declarationParsed⟩

/-- Implementation methods have deterministic and exclusive ordinary
outcomes. -/
theorem implMethodDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ImplMethodOrdinaryParses ImplMethodRejects where
  successOutputUnique := ImplMethodOrdinaryParses.output_unique
  successRejectDisjoint := ImplMethodRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
