import Solcore.Syntax.Parser.ImplDeclSoundnessProperties

/-! External consumers for parametric implementation-declaration soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImplSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalImplDefaultMarkerParses
example := @ImplHeadArgumentsParses
example := @ImplMethodParses
example := @ImplMethodTailParses
example := @ImplBodyParses
example := @ImplDeclParses

example := @ImplInternals.implDefaultMarker_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.implDefaultMarker_success_sound
example := @ImplInternals.implDefaultMarker_validFor
example := @ImplInternals.requireImplArguments_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.requireImplArguments_success_shape
example := @ImplInternals.requireImplArguments_reply_validFor
example := @ImplInternals.implHeadArguments_success_sound

example := @ImplInternals.implMethod_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.implMethod_success_sound
example := @ImplInternals.implMethod_success_sound_and_validFor
example := @ImplInternals.implMethod_validFor

example := @ImplInternals.implBody_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.implBody_success_sound
example := @ImplInternals.implBody_success_sound_and_validFor
example := @ImplInternals.implBody_validFor

example := @implDecl_reflectsDiagnosticFreeOnSuccess
example := @implDecl_success_sound
example := @implDecl_success_sound_and_validFor
example := @implDecl_validFor

example
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : Remainder → Block → Remainder → Prop)
    (bodyValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ImplDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implDecl input = .ok declaration next) :
    ImplDeclParses bodyParses input.declarativeRemainder declaration
          next.declarativeRemainder ∧
      ImplDecl.ValidFor statementValid input.file declaration :=
  implDecl_success_sound_and_validFor statementValid bodyParses bodyValid
    bodyWindow bodyReflects bodySound inputValid diagnosticFree result

end Solcore.Test.SyntaxParserImplSoundnessProperties
