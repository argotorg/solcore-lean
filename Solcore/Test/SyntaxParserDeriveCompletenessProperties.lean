import Solcore.Syntax.Parser.DeriveCompletenessProperties

/-! External consumers of both directions of exact ordinary completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example {input : State}
    {value : DeriveTarget} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.DeriveTargetParses
      input.declarativeRemainder value remainder) :
    ∃ output, deriveTarget input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (deriveTarget_ordinary_success_iff).mp parsed

example {input : State}
    {value : DeriveTarget} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : deriveTarget input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.DeriveTargetParses
      input.declarativeRemainder value remainder :=
  (deriveTarget_ordinary_success_iff).mpr ⟨output, result, remainderEq⟩

example {input : State}
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.DeriveTargetRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, deriveTarget input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (deriveTarget_ordinary_reject_iff).mp rejection

example {input : State}
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : deriveTarget input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.DeriveTargetRejects input.declarativeRemainder rejected :=
  (deriveTarget_ordinary_reject_iff).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.DeriveAttributeParses
      input.declarativeRemainder value remainder) :
    ∃ output, DeriveAttributeInternals.valid input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (deriveAttributeValid_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : DeriveAttributeInternals.valid input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.DeriveAttributeParses
      input.declarativeRemainder value remainder :=
  (deriveAttributeValid_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.DeriveAttributeValidRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, DeriveAttributeInternals.valid input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (deriveAttributeValid_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : DeriveAttributeInternals.valid input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.DeriveAttributeValidRejects input.declarativeRemainder rejected :=
  (deriveAttributeValid_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example {input : State}
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.DeriveAttributeRecoveredParses
      input.declarativeRemainder value remainder) :
    ∃ output, DeriveAttributeInternals.recovered input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (deriveAttributeRecovered_ordinary_success_iff).mp parsed

example {input : State}
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : DeriveAttributeInternals.recovered input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.DeriveAttributeRecoveredParses
      input.declarativeRemainder value remainder :=
  (deriveAttributeRecovered_ordinary_success_iff).mpr ⟨output, result, remainderEq⟩

example {input : State}
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.DeriveAttributeRecoveredRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, DeriveAttributeInternals.recovered input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (deriveAttributeRecovered_ordinary_reject_iff).mp rejection

example {input : State}
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : DeriveAttributeInternals.recovered input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.DeriveAttributeRecoveredRejects input.declarativeRemainder rejected :=
  (deriveAttributeRecovered_ordinary_reject_iff).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.DeriveAttributeOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, deriveAttribute input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (deriveAttribute_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : deriveAttribute input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.DeriveAttributeOrdinaryParses
      input.declarativeRemainder value remainder :=
  (deriveAttribute_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.DeriveAttributeRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, deriveAttribute input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (deriveAttribute_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : deriveAttribute input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.DeriveAttributeRejects input.declarativeRemainder rejected :=
  (deriveAttribute_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserDeriveCompletenessProperties
