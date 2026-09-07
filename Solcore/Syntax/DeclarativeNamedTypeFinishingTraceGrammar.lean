import Solcore.Syntax.DeclarativeGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Finishing a named type has a spelling-dependent diagnostic even without
hyphens. The declaration is independent of parser state, evaluation, and fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def namedTypeTraceValue (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)) : Syntax.TypeExpr := {
  span := match arguments with
    | none => name.span
    | some values => SourceSpan.cover name.span values.span
  value := .named name arguments
}

def UnqualifiedMappingSpelling (name : QualifiedName) : Prop :=
  name.value.components.tail = [] ∧ name.value.components.head.value = "mapping"

inductive NamedTypeFinishingTrace (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)) : List ParseDiagnostic → Prop where
  | canonicalRequired (spelling : UnqualifiedMappingSpelling name) :
      NamedTypeFinishingTrace name arguments [{
        span := (namedTypeTraceValue name arguments).span
        kind := .constraintViolation .mappingRequiresCanonicalForm
      }]
  | ordinary (spelling : ¬ UnqualifiedMappingSpelling name) :
      NamedTypeFinishingTrace name arguments []

end Solcore.Syntax.DeclarativeGrammar
