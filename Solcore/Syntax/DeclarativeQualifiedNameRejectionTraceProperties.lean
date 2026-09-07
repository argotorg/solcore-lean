import Solcore.Syntax.DeclarativeQualifiedNameRejectionTraceGrammar
import Solcore.Syntax.DeclarativeQualifiedNameTraceProperties
import Solcore.Syntax.DeclarativeCoreTypeNameOutcomeProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Exact rejected dotted names preserve only the preceding spelling events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem DottedIdentifierTailTraceRejects.ordinary
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DottedIdentifierTailTraceRejects context source endByte input rejected report trace) :
    TypeQualifiedNameTailRejects input rejected := by
  induction rejection with
  | componentRejected span dot absent => exact .componentRejected span dot (.absent absent)
  | laterRejected span dot name tail ih =>
      exact .laterRejected span dot (identifierTraceParses_iff.mp name).1 ih

theorem QualifiedNameTraceRejects.ordinary
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : QualifiedNameTraceRejects context source endByte input rejected report trace) :
    TypeQualifiedNameRejects input rejected := by
  cases rejection with
  | firstRejected absent => exact .firstRejected (.absent absent)
  | tailRejected head tail => exact .tailRejected (identifierTraceParses_iff.mp head).1 tail.ordinary

theorem DottedIdentifierTailTraceRejects.output_window
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DottedIdentifierTailTraceRejects context source endByte input rejected report trace) :
    rejected.tokens = input.tokens ∧ rejected.endIndex = input.endIndex := by
  induction rejection with
  | componentRejected span dot => rcases dot with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
  | laterRejected span dot name tail ih =>
      rcases dot with ⟨_, rfl⟩
      have ordinary := (identifierTraceParses_iff.mp name).1
      exact ⟨ih.1.trans ordinary.2.1, ih.2.trans ordinary.2.2.1⟩

theorem QualifiedNameTraceRejects.output_window
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : QualifiedNameTraceRejects context source endByte input rejected report trace) :
    rejected.tokens = input.tokens ∧ rejected.endIndex = input.endIndex := by
  cases rejection with
  | firstRejected => exact ⟨rfl, rfl⟩
  | tailRejected head tail =>
      have ordinary := (identifierTraceParses_iff.mp head).1
      exact ⟨tail.output_window.1.trans ordinary.2.1, tail.output_window.2.trans ordinary.2.2.1⟩

theorem DottedIdentifierTailTraceRejects.result_unique
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : DottedIdentifierTailTraceRejects context source endByte input afterLeft left leftTrace)
    (rightRejected : DottedIdentifierTailTraceRejects context source endByte input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace := by
  induction leftRejected generalizing afterRight right rightTrace with
  | componentRejected span dot absent reported =>
      cases rightRejected with
      | componentRejected otherSpan otherDot otherAbsent otherReport =>
          have same := dot.2.trans otherDot.2.symm
          cases same
          exact ⟨rfl, reported.diagnostic_unique otherReport, rfl⟩
      | laterRejected otherSpan otherDot name tail =>
          have same := dot.2.trans otherDot.2.symm
          cases same
          exact False.elim (absent ⟨_, _, (identifierTraceParses_iff.mp name).1.1⟩)
  | laterRejected span dot name tail ih =>
      cases rightRejected with
      | componentRejected otherSpan otherDot absent reported =>
          have same := dot.2.trans otherDot.2.symm
          cases same
          exact False.elim (absent ⟨_, _, (identifierTraceParses_iff.mp name).1.1⟩)
      | laterRejected otherSpan otherDot otherName otherTail =>
          have same := dot.2.trans otherDot.2.symm
          cases same
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases ih otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem QualifiedNameTraceRejects.result_unique
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : QualifiedNameTraceRejects context source endByte input afterLeft left leftTrace)
    (rightRejected : QualifiedNameTraceRejects context source endByte input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | firstRejected absent reported =>
      cases rightRejected with
      | firstRejected otherAbsent otherReport => exact ⟨rfl, reported.diagnostic_unique otherReport, rfl⟩
      | tailRejected head tail =>
          exact False.elim (absent ⟨_, _, (identifierTraceParses_iff.mp head).1.1⟩)
  | tailRejected head tail =>
      cases rightRejected with
      | firstRejected absent reported =>
          exact False.elim (absent ⟨_, _, (identifierTraceParses_iff.mp head).1.1⟩)
      | tailRejected otherHead otherTail =>
          rcases head.result_unique otherHead with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem DottedIdentifierTailTraceRejects.disjoint_success
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DottedIdentifierTailTraceRejects context source endByte input rejected report trace) :
    ¬ ∃ components output successTrace,
      DottedIdentifierTailTraceParses source endByte input components output successTrace := by
  rintro ⟨components, output, successTrace, parsed⟩
  exact rejection.ordinary.disjointDotted ⟨components, output.cursor, parsed.ordinary.2.2⟩

theorem QualifiedNameTraceRejects.disjoint_success
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : QualifiedNameTraceRejects context source endByte input rejected report trace) :
    ¬ ∃ name output successTrace,
      QualifiedNameTraceParses source endByte input name output successTrace := by
  rintro ⟨name, output, successTrace, parsed⟩
  exact rejection.ordinary.disjointQualified ⟨name, output, parsed.ordinary⟩

theorem DottedIdentifierTailTraceRejects.cascadeFilters
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DottedIdentifierTailTraceRejects context source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction rejection with
  | componentRejected => exact .nil
  | laterRejected _ _ name _ ih => exact (name.cascadeFilters text lexical).append ih

theorem QualifiedNameTraceRejects.cascadeFilters
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : QualifiedNameTraceRejects context source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | firstRejected => exact .nil
  | tailRejected head tail => exact (head.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

end Solcore.Syntax.DeclarativeGrammar
