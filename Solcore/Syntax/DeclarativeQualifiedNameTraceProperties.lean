import Solcore.Syntax.DeclarativeQualifiedNameTraceGrammar
import Solcore.Syntax.DeclarativeIdentifierTraceProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProtectionProperties

/-! Carrier, ordinary erasure, exactness, and protected dotted-name events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem DottedIdentifierTailTraceParses.ordinary
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {components : List Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : DottedIdentifierTailTraceParses source endByte input components output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      DottedIdentifierTailParses input.tokens input.endIndex input.cursor components output.cursor := by
  induction parsed with
  | done stopped => exact ⟨rfl, rfl, .done _ stopped⟩
  | next dotSpan dot name tail ih =>
      rcases dot with ⟨dotToken, rfl⟩
      rcases identifierTraceParses_iff.mp name with ⟨ordinary, _⟩
      refine ⟨ih.1.trans ordinary.2.1, ih.2.1.trans ordinary.2.2.1,
        .next dotSpan dotToken ordinary.1 ?_⟩
      simpa only [ordinary.2.1, ordinary.2.2.1, ordinary.2.2.2, Nat.add_assoc] using ih.2.2

theorem DottedIdentifierTailTraceParses.output_window
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {components : List Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : DottedIdentifierTailTraceParses source endByte input components output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex :=
  ⟨parsed.ordinary.1, parsed.ordinary.2.1⟩

theorem DottedIdentifierTailTraceParses.cursor_eq
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {components : List Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : DottedIdentifierTailTraceParses source endByte input components output trace) :
    output.cursor = input.cursor + 2 * components.length := by
  induction parsed with
  | done => simp
  | next dotSpan dot name tail ih =>
      have nameCursor := (identifierTraceParses_iff.mp name).1.2.2.2
      rcases dot with ⟨_, rfl⟩
      simp only [List.length_cons] at ⊢
      simp only at nameCursor
      omega

theorem QualifiedNameTraceParses.ordinary
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {name : Syntax.QualifiedName} {trace : List ParseDiagnostic}
    (parsed : QualifiedNameTraceParses source endByte input name output trace) :
    QualifiedNameParses input name output := by
  cases parsed with
  | parsed head tail =>
      have first := (identifierTraceParses_iff.mp head).1
      have rest := tail.ordinary
      refine ⟨rest.1.trans first.2.1, rest.2.1.trans first.2.2.1, first.1, ?_, rfl⟩
      simpa only [first.2.1, first.2.2.1, first.2.2.2, tracedQualifiedName,
        qualifiedNameFromSuffix, List.nil_append] using rest.2.2

theorem QualifiedNameTraceParses.output_window
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {name : Syntax.QualifiedName} {trace : List ParseDiagnostic}
    (parsed : QualifiedNameTraceParses source endByte input name output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex :=
  ⟨parsed.ordinary.1, parsed.ordinary.2.1⟩

theorem QualifiedNameTraceParses.cursor_lt
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {name : Syntax.QualifiedName} {trace : List ParseDiagnostic}
    (parsed : QualifiedNameTraceParses source endByte input name output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed head tail =>
      have first := (identifierTraceParses_iff.mp head).1.2.2.2
      have rest := tail.cursor_eq
      omega

theorem DottedIdentifierTailTraceParses.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {left right : List Syntax.Identifier} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : DottedIdentifierTailTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : DottedIdentifierTailTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right afterRight rightTrace with
  | done stopped =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl, rfl⟩
      | next dotSpan dot => exact False.elim (stopped ⟨dotSpan, dot.1⟩)
  | next dotSpan dot name tail ih =>
      cases rightParsed with
      | done stopped => exact False.elim (stopped ⟨dotSpan, dot.1⟩)
      | next otherSpan otherDot otherName otherTail =>
          have afterDotEq := dot.2.trans otherDot.2.symm
          cases afterDotEq
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases ih otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem QualifiedNameTraceParses.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {left right : Syntax.QualifiedName} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : QualifiedNameTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : QualifiedNameTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed head tail =>
      cases rightParsed with
      | parsed otherHead otherTail =>
          rcases head.result_unique otherHead with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem DottedIdentifierTailTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {components : List Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : DottedIdentifierTailTraceParses source endByte input components output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | done => exact .nil
  | next _ _ name _ ih => exact (name.cascadeFilters text lexical).append ih

theorem QualifiedNameTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {name : Syntax.QualifiedName} {trace : List ParseDiagnostic}
    (parsed : QualifiedNameTraceParses source endByte input name output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed head tail => exact (head.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

end Solcore.Syntax.DeclarativeGrammar
