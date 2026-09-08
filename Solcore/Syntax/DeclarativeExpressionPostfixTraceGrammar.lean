import Solcore.Syntax.DeclarativePostfixTailRejectionTraceGrammar

/-! Independent atom-plus-maximal-postfix traces. Atom events precede every
suffix event. The first rejecting report is retained separately, never appended
as an emitted event by this composition. No parser state or fuel occurs here. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ExpressionPostfixTraceParses
    (atomTrace nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterAtom output : Remainder} {base value : Syntax.Expr}
      {atomEvents tailEvents : List ParseDiagnostic}
      (atomParsed : atomTrace source endByte input base afterAtom atomEvents)
      (tailParsed : PostfixTailTraceParses nestedTrace source endByte afterAtom base value output tailEvents) :
      ExpressionPostfixTraceParses atomTrace nestedTrace source endByte input value output (atomEvents ++ tailEvents)

inductive ExpressionPostfixTraceRejects
    (atomTrace nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (atomRejects nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | atomRejected {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (atomRejected : atomRejects source endByte input rejected report trace) :
      ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects source endByte
        input rejected report trace
  | tailRejected {input afterAtom rejected : Remainder} {base : Syntax.Expr} {report : ParseDiagnostic}
      {atomEvents tailEvents : List ParseDiagnostic}
      (atomParsed : atomTrace source endByte input base afterAtom atomEvents)
      (tailRejected : PostfixTailTraceRejects nestedTrace nestedRejects source endByte
        afterAtom base rejected report tailEvents) :
      ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects source endByte
        input rejected report (atomEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
