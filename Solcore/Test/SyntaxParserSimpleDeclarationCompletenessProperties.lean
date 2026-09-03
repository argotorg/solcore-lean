import Solcore.Syntax.Parser.SimpleDeclarationCompletenessProperties

/-! External consumers of both directions of exact ordinary completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSimpleDeclarationCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example {input : State} (inputValid : input.ValidFor)
    {value : TypeAliasDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, typeAlias input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (typeAlias_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : TypeAliasDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : typeAlias input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      input.declarativeRemainder value remainder :=
  (typeAlias_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.TypeAliasDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, typeAlias input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (typeAlias_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : typeAlias input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.TypeAliasDeclRejects input.declarativeRemainder rejected :=
  (typeAlias_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example (deriveAttribute : Option DeriveAttribute) {input : State} (inputValid : input.ValidFor)
    {value : EnumDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute
      input.declarativeRemainder value remainder) :
    ∃ output, enumDecl deriveAttribute input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (enumDecl_ordinary_success_iff deriveAttribute inputValid).mp parsed

example (deriveAttribute : Option DeriveAttribute) {input : State} (inputValid : input.ValidFor)
    {value : EnumDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : enumDecl deriveAttribute input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute
      input.declarativeRemainder value remainder :=
  (enumDecl_ordinary_success_iff deriveAttribute inputValid).mpr ⟨output, result, remainderEq⟩

example (deriveAttribute : Option DeriveAttribute) {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.EnumDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, enumDecl deriveAttribute input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (enumDecl_ordinary_reject_iff deriveAttribute inputValid).mp rejection

example (deriveAttribute : Option DeriveAttribute) {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : enumDecl deriveAttribute input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.EnumDeclRejects input.declarativeRemainder rejected :=
  (enumDecl_ordinary_reject_iff deriveAttribute inputValid).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : TraitDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TraitDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, traitDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (traitDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : TraitDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : traitDecl input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.TraitDeclOrdinaryParses
      input.declarativeRemainder value remainder :=
  (traitDecl_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.TraitDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, traitDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (traitDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : traitDecl input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.TraitDeclRejects input.declarativeRemainder rejected :=
  (traitDecl_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserSimpleDeclarationCompletenessProperties
