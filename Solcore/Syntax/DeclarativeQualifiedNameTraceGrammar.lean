import Solcore.Syntax.DeclarativeIdentifierTraceGrammar

/-! Independent maximal dotted-name success with checked spelling events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Forward components following an already consumed first identifier. Dots
are silent; the first position without a dot ends the complete suffix. -/
inductive DottedIdentifierTailTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → List Syntax.Identifier → Remainder → List ParseDiagnostic → Prop where
  | done {input : Remainder}
      (stopped : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot)) :
      DottedIdentifierTailTraceParses source endByte input [] input []
  | next {input afterDot afterComponent output : Remainder}
      {component : Syntax.Identifier} {components : List Syntax.Identifier}
      {headTrace tailTrace : List ParseDiagnostic}
      (dotSpan : SourceSpan)
      (dot : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (name : IdentifierTraceParses afterDot component afterComponent headTrace)
      (tail : DottedIdentifierTailTraceParses source endByte afterComponent components output tailTrace) :
      DottedIdentifierTailTraceParses source endByte input (component :: components)
        output (headTrace ++ tailTrace)

/-- Finish an existing forward prefix with a newly recognized suffix. The
separate previous last component also permits arbitrary prefix accumulator use. -/
def qualifiedNameFromSuffix (first last : Syntax.Identifier)
    (previous suffix : List Syntax.Identifier) : Syntax.QualifiedName :=
  { span := SourceSpan.cover first.span (finalIdentifier last suffix).span
    value := { components := { head := first, tail := previous ++ suffix } } }

/-- Assemble a nonempty forward component list and its complete covering span. -/
def tracedQualifiedName (first : Syntax.Identifier) (components : List Syntax.Identifier) : Syntax.QualifiedName :=
  qualifiedNameFromSuffix first first [] components

/-- One checked first identifier followed by every available dotted component. -/
inductive QualifiedNameTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.QualifiedName → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterFirst output : Remainder} {first : Syntax.Identifier}
      {components : List Syntax.Identifier} {firstTrace tailTrace : List ParseDiagnostic}
      (head : IdentifierTraceParses input first afterFirst firstTrace)
      (tail : DottedIdentifierTailTraceParses source endByte afterFirst components output tailTrace) :
      QualifiedNameTraceParses source endByte input (tracedQualifiedName first components)
        output (firstTrace ++ tailTrace)

end Solcore.Syntax.DeclarativeGrammar
