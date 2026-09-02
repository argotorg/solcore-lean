import Solcore.Syntax.Parser.FunctionDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionDeclSoundnessProperties

/-! External consumers for strict and broad function-declaration outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionDeclSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @FunctionDeclParses
example := @FunctionDeclOrdinaryParses
example := @FunctionDeclRejects
example := @functionDeclDeterministicOutcomeSpec

example := @functionDecl_reflectsDiagnosticFreeOnSuccess
example := @functionDecl_success_sound
example := @functionDecl_success_sound_and_validFor
example := @functionDecl_success_ordinaryOutcome_sound
example := @functionDecl_reject_ordinaryOutcome_sound
example := @functionDecl_ordinaryOutcome_sound
example := @functionDecl_ordinaryOutcomeSpec

example
    (bodyParses : Remainder → Block → Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : FunctionDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionDecl .module input = .ok declaration next) :
    FunctionDeclParses bodyParses ModuleFunctionModifiersAllowed
      input.declarativeRemainder declaration next.declarativeRemainder :=
  functionDecl_success_sound .module bodyParses bodyReflects bodySound
    diagnosticFree result

example
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : Remainder → Block → Remainder → Prop)
    (bodyValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : FunctionDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionDecl .contract input = .ok declaration next) :
    FunctionDeclParses bodyParses ContractFunctionModifiersAllowed
          input.declarativeRemainder declaration next.declarativeRemainder ∧
      FunctionDecl.ValidFor statementValid input.file declaration :=
  functionDecl_success_sound_and_validFor statementValid .contract bodyParses
    bodyValid bodyReflects bodySound inputValid diagnosticFree result

example {input next : State} {declaration : FunctionDecl}
    (result : functionDecl .module input = .ok declaration next) :
    FunctionDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  functionDecl_success_ordinaryOutcome_sound .module result

example {input rejected : State} {failure : Failure}
    (result : functionDecl .contract input = .reject failure rejected) :
    FunctionDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  functionDecl_reject_ordinaryOutcome_sound .contract result

end Solcore.Test.SyntaxParserFunctionDeclSoundnessProperties
