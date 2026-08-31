import Solcore.Syntax.Parser.Name

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Parse a dotted module path with its optional external-package marker. -/
def modulePath (context : ParseContext) : Parser ModulePath := do
  let state ← getState
  let externalMarker ←
    if isSymbol state .at then
      do
        let marker ← symbol .at context
        pure (some marker.span)
    else
      pure none
  let name ← qualifiedName context .topLevel
  let span := match externalMarker with
    | some marker => SourceSpan.cover marker name.span
    | none => name.span
  pure {
    span
    value := {
      externalMarker
      components := name.value.components
    }
  }

end Solcore.Syntax.Parser
