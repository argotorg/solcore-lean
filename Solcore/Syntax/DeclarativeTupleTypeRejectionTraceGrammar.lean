import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceGrammar

/-! Raw tuple rejection is precisely the trailing-enabled parenthesized-list
rejection, including an absent opening marker. The final report is uncommitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev TupleTypeTraceRejects
    (typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (typeRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :=
  TrailingDelimitedListTraceRejects .leftParen .rightParen true .typeExpr
    typeTrace typeRejects source endByte

end Solcore.Syntax.DeclarativeGrammar
