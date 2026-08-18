import Solcore.Surface.Wire.V1.Syntax

set_option autoImplicit false

namespace Solcore.Surface.Wire.V1

def parseResultSchemaVersion : String := "solcore-parse-result/v1"

/-!
The schema discriminator is emitted by the codec from the fixed version above;
it is not stored as an arbitrary string in the closed payload value.
-/
structure ParseResult where
  value : File
  deriving Repr, BEq

namespace ParseResult

def toSurface (result : ParseResult) : Solcore.Surface.ParsedFile :=
  result.value.toSurface

def ofSurface? (parsed : Solcore.Surface.ParsedFile) : Option ParseResult := do
  let value <- File.ofSurface? parsed
  some { value }

@[simp] theorem ofSurface?_toSurface (result : ParseResult) :
    ofSurface? result.toSurface = some result := by
  cases result
  simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {parsed : Solcore.Surface.ParsedFile}
    {result : ParseResult}
    (projection : ofSurface? parsed = some result) :
    result.toSurface = parsed := by
  cases fileProjection : File.ofSurface? parsed with
  | none => simp [ofSurface?, fileProjection] at projection
  | some file =>
      simp [ofSurface?, fileProjection] at projection
      subst result
      exact File.toSurface_eq_of_ofSurface?_eq_some fileProjection

end ParseResult

end Solcore.Surface.Wire.V1
