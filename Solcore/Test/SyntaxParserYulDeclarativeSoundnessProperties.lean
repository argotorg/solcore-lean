import Solcore.Syntax

/-! External consumers for public Yul statement and body soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulDeclarativeSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @YulStatementParses
example := @YulStatementOrdinaryParses
example := @YulStatementPublicRejects
example := @yulStatementPublicOutcomeSpec

example := @yulStatement_success_clean_sound
example := @yulStatement_success_ordinary_sound
example := @yulStatement_reject_ordinary_sound
example := @yulStatement_reject_boundary_sound

example {input output : State} {statement : YulStmt}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulStatement input = .ok statement output) :
    YulStatementParses input.declarativeRemainder statement
      output.declarativeRemainder :=
  yulStatement_success_clean_sound diagnosticFree result

example {input output : State} {statement : YulStmt}
    (result : yulStatement input = .ok statement output) :
    YulStatementOrdinaryParses input.declarativeRemainder statement
      output.declarativeRemainder :=
  yulStatement_success_ordinary_sound result

example {input rejected : State} {failure : Failure}
    (result : yulStatement input = .reject failure rejected) :
    YulStatementPublicRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  yulStatement_reject_ordinary_sound result

example :
    DeterministicOutcomeSpec YulStatementOrdinaryParses
      YulStatementPublicRejects :=
  yulStatementPublicOutcomeSpec

example := @YulBodyParses
example := @YulBodyOrdinaryParses
example := @YulBodyRejects
example := @YulBodyOutcomeParses

example := @yulBody_success_clean_sound
example := @yulBody_success_ordinary_sound
example := @yulBody_reject_ordinary_sound
example := @yulBody_success_outcome_sound
example := @yulBody_publicOutcomeSpec

example {input output : State} {body : YulParsedBlock}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulBody input = .ok body output) :
    YulBodyParses input.declarativeRemainder body.span body.body
      output.declarativeRemainder :=
  yulBody_success_clean_sound diagnosticFree result

example {input output : State} {body : YulParsedBlock}
    (result : yulBody input = .ok body output) :
    YulBodyOrdinaryParses input.declarativeRemainder body.span body.body
      output.declarativeRemainder :=
  yulBody_success_ordinary_sound result

example {input rejected : State} {failure : Failure}
    (result : yulBody input = .reject failure rejected) :
    YulBodyRejects input.declarativeRemainder rejected.declarativeRemainder :=
  yulBody_reject_ordinary_sound result

example {input output : State} {body : YulParsedBlock}
    (result : yulBody input = .ok body output) :
    YulBodyOutcomeParses input.declarativeRemainder {
      span := body.span
      body := body.body
    } output.declarativeRemainder :=
  yulBody_success_outcome_sound result

example :
    DeterministicOutcomeSpec YulBodyOutcomeParses YulBodyRejects :=
  yulBody_publicOutcomeSpec

end Solcore.Test.SyntaxParserYulDeclarativeSoundnessProperties
