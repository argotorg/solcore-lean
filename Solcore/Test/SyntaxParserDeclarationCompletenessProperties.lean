import Solcore.Syntax.Parser.FunctionDeclarationCompletenessProperties
import Solcore.Syntax.Parser.ImplementationDeclarationCompletenessProperties
import Solcore.Syntax.Parser.ContractDeclarationCompletenessProperties

/-! Compile-time consumers of declaration grammar completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeclarationCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @functionDecl_ordinary_success_iff
example := @functionDecl_ordinary_reject_iff
example := @constructorDecl_ordinary_success_iff
example := @constructorDecl_ordinary_reject_iff
example := @fallbackDecl_ordinary_success_iff
example := @fallbackDecl_ordinary_reject_iff
example := @implDecl_ordinary_success_iff
example := @implDecl_ordinary_reject_iff
example := @contractDecl_ordinary_success_iff
example := @contractDecl_ordinary_reject_iff

example (location : FunctionLocation)
    {input : State} (inputValid : input.ValidFor)
    {value : FunctionDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.FunctionDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, functionDecl location input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (functionDecl_ordinary_success_iff location inputValid).mp parsed

example (location : FunctionLocation)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.FunctionDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, functionDecl location input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (functionDecl_ordinary_reject_iff location inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : ConstructorDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ConstructorDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, constructorDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (constructorDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ConstructorDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, constructorDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (constructorDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : FallbackDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.FallbackDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, fallbackDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (fallbackDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.FallbackDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, fallbackDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (fallbackDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : ImplDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ImplDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, implDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (implDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ImplDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, implDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (implDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : ContractDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, contractDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (contractDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, contractDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (contractDecl_ordinary_reject_iff inputValid).mp rejection

end Solcore.Test.SyntaxParserDeclarationCompletenessProperties
