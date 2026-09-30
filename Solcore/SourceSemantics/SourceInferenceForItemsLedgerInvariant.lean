import Solcore.SourceSemantics.SourceInferenceLedgerInvariant

/-!
Pending qualified-template IDs accumulate in source order through a `for`
initializer or post list.  The enclosing loop statement will materialize the
entire pending inventory after both traversals complete.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Source-ordered `for` header sequencing from one actual item theorem.
The suffix is indexed by the inferred item forms, not by syntactic guesses
about which inputs generalize. -/
theorem inferForItemsFuelLedgerPreservation_of_itemSoundness
    {fuel : Nat}
    (itemSound : InferForItemFuelLedgerPreservation fuel) :
    InferForItemsFuelLedgerPreservation fuel := by
  intro context items initial result pending success tracked
  induction items generalizing initial result pending with
  | nil =>
      simp only [Detail.inferForItemsFuel, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      simpa using tracked
  | cons item rest induction =>
      unfold Detail.inferForItemsFuel at success
      cases itemSuccess : Detail.inferForItemFuel fuel context item initial with
      | error error =>
          simp [itemSuccess, bind, Except.bind] at success
      | ok itemResult =>
          rcases itemResult with ⟨inferred, itemState⟩
          simp only [itemSuccess, bind, Except.bind] at success
          cases tailSuccess : Detail.inferForItemsFuel fuel context rest
              itemState with
          | error error =>
              simp [tailSuccess] at success
          | ok tail =>
              simp only [tailSuccess, pure, Pure.pure, Except.pure] at success
              injection success with resultEq
              subst result
              have itemTracked := itemSound itemSuccess tracked
              have tailTracked := induction tailSuccess itemTracked
              simpa [List.flatMap_cons, List.append_assoc] using tailTracked

end Solcore.SourceSemantics.SourceInferenceSoundness
