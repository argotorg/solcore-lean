import Solcore.Syntax.DeclarativeIdentifierTraceGrammar
import Solcore.Syntax.DeclarativePragmaOutcomeGrammar

/-! Independent ordered identifier events and complete pragma success traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Concatenate the checked-name events once per identifier in written order. -/
inductive IdentifierListDiagnosticTrace :
    List Syntax.Identifier → List ParseDiagnostic → Prop where
  | nil : IdentifierListDiagnosticTrace [] []
  | cons {name : Syntax.Identifier} {names : List Syntax.Identifier}
      {headTrace tailTrace : List ParseDiagnostic}
      (head : IdentifierDiagnosticTrace name headTrace)
      (tail : IdentifierListDiagnosticTrace names tailTrace) :
      IdentifierListDiagnosticTrace (name :: names) (headTrace ++ tailTrace)

/-- A pragma tail retains only events of newly parsed suffix identifiers. -/
def PragmaItemsTailTraceParses (input : Remainder) (items : List Syntax.Identifier)
    (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  PragmaItemsTailOrdinaryParses input items output ∧
    IdentifierListDiagnosticTrace items trace

/-- Complete item scanning retains its exact grammar and ordered name events. -/
def PragmaItemsTraceParses (input : Remainder) (items : List Syntax.Identifier)
    (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  PragmaItemsOrdinaryParses input items output ∧
    IdentifierListDiagnosticTrace items trace

/-- Only checked items emit diagnostics: the raw pragma name, keyword,
commas, and final semicolon contribute no events. -/
def PragmaDeclTraceParses (input : Remainder) (declaration : Syntax.PragmaDecl)
    (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  PragmaDeclOrdinaryParses input declaration output ∧
    IdentifierListDiagnosticTrace declaration.value.items trace

end Solcore.Syntax.DeclarativeGrammar
