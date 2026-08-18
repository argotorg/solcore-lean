import Lean.Data.Json
import Solcore.Profile
import Solcore.Surface.Wire.V1.Diagnostic
import Solcore.Surface.Wire.V1.ParseResult

set_option autoImplicit false

namespace Solcore.Oracle.V4

/-!
Closed value types for the Oracle v4 publication boundary.

Envelope discriminators and profile bindings are derived constants rather than
caller-controlled fields. Query-specific verdict types make incompatible
query, result, phase, resource, and internal-error combinations
unrepresentable before JSON encoding or request-relative validation.
-/

def schemaVersion : String := "solcore-oracle/v4"

def capabilitiesSchema : String := "solcore-capabilities/v4"

def requestIdValid (value : String) : Bool :=
  !value.isEmpty

structure RequestId where
  value : String
  valid : requestIdValid value = true
  deriving Repr, DecidableEq

namespace RequestId

instance : BEq RequestId :=
  ⟨fun first second => first.value == second.value⟩

def ofString? (value : String) : Option RequestId :=
  if valid : requestIdValid value = true then
    some { value, valid }
  else
    none

@[simp] theorem ofString?_value (id : RequestId) :
    ofString? id.value = some id := by
  cases id with
  | mk value valid => simp [ofString?, valid]

theorem value_eq_of_ofString?_eq_some
    {value : String}
    {id : RequestId}
    (projection : ofString? value = some id) :
    id.value = value := by
  unfold ofString? at projection
  split at projection
  next _ =>
    have equality := Option.some.inj projection
    rw [← equality]
  next _ =>
    simp at projection

end RequestId

/-!
A v4 source path is only a nonempty opaque UTF-8 label. No separator, suffix,
normalization, traversal, or host-filesystem policy is attached to this atom.
-/
def sourcePathValid (value : String) : Bool :=
  !value.isEmpty

structure SourcePath where
  value : String
  valid : sourcePathValid value = true
  deriving Repr, DecidableEq

namespace SourcePath

instance : BEq SourcePath :=
  ⟨fun first second => first.value == second.value⟩

def ofString? (value : String) : Option SourcePath :=
  if valid : sourcePathValid value = true then
    some { value, valid }
  else
    none

@[simp] theorem ofString?_value (path : SourcePath) :
    ofString? path.value = some path := by
  cases path with
  | mk value valid => simp [ofString?, valid]

theorem value_eq_of_ofString?_eq_some
    {value : String}
    {path : SourcePath}
    (projection : ofString? value = some path) :
    path.value = value := by
  unfold ofString? at projection
  split at projection
  next _ =>
    have equality := Option.some.inj projection
    rw [← equality]
  next _ =>
    simp at projection

end SourcePath

structure SourceInput where
  path : SourcePath
  content : String
  deriving Repr, BEq, DecidableEq

namespace SourceInput

def toSurface (source : SourceInput) : Solcore.Surface.SourceFile := {
  path := source.path.value
  content := source.content
}

def ofSurface? (file : Solcore.Surface.SourceFile) : Option SourceInput := do
  let path <- SourcePath.ofString? file.path
  some { path, content := file.content }

@[simp] theorem ofSurface?_toSurface (source : SourceInput) :
    ofSurface? source.toSurface = some source := by
  cases source
  simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {file : Solcore.Surface.SourceFile}
    {source : SourceInput}
    (projection : ofSurface? file = some source) :
    source.toSurface = file := by
  cases pathProjection : SourcePath.ofString? file.path with
  | none => simp [ofSurface?, pathProjection] at projection
  | some path =>
      simp [ofSurface?, pathProjection] at projection
      subst source
      cases file
      simp [toSurface,
        SourcePath.value_eq_of_ofString?_eq_some pathProjection]

end SourceInput

structure Limits where
  sourceBytes : Nat
  deriving Repr, BEq, DecidableEq

def Limits.default : Limits := {
  sourceBytes := 1048576
}

inductive QueryKind where
  | capabilities
  | parse
  deriving Repr, BEq, DecidableEq

namespace QueryKind

def all : Array QueryKind := #[.capabilities, .parse]

end QueryKind

inductive Query where
  | capabilities
  | parse (source : SourceInput)
  deriving Repr, BEq, DecidableEq

namespace Query

def kind : Query -> QueryKind
  | .capabilities => .capabilities
  | .parse _ => .parse

def source? : Query -> Option SourceInput
  | .capabilities => none
  | .parse source => some source

end Query

/-!
The profile reference is a singleton. Its external `id` and `digest` fields are
derived below, so no request or response can carry a cross-version binding.
-/
inductive ProfileRef where
  | frontendM2bV1
  deriving Repr, BEq, DecidableEq

namespace ProfileRef

def canonical : ProfileRef := .frontendM2bV1

def id : ProfileRef -> String
  | .frontendM2bV1 => Solcore.m2bFrontendProfile.id

def digest : ProfileRef -> String
  | .frontendM2bV1 => Solcore.m2bFrontendProfileDigest

end ProfileRef

structure Request where
  id : RequestId
  limits : Limits
  query : Query
  deriving Repr, BEq, DecidableEq

namespace Request

def schema (_request : Request) : String :=
  schemaVersion

def spec (_request : Request) : String :=
  Solcore.m2bLanguage.id

def profile (_request : Request) : ProfileRef :=
  ProfileRef.canonical

def queryKind (request : Request) : QueryKind :=
  request.query.kind

end Request

inductive Phase where
  | protocol
  | sourcePreflight
  | surfaceLexing
  | surfaceParsing
  | surfaceEncoding
  deriving Repr, BEq, DecidableEq

inductive FrontendPhase where
  | surfaceLexing
  | surfaceParsing
  deriving Repr, BEq, DecidableEq

namespace FrontendPhase

def toPhase : FrontendPhase -> Phase
  | .surfaceLexing => .surfaceLexing
  | .surfaceParsing => .surfaceParsing

def ofDiagnosticPhase :
    Solcore.Surface.Wire.V1.DiagnosticPhase -> FrontendPhase
  | .surfaceLexing => .surfaceLexing
  | .surfaceParsing => .surfaceParsing

@[simp] theorem toPhase_ofDiagnosticPhase
    (phase : Solcore.Surface.Wire.V1.DiagnosticPhase) :
    (ofDiagnosticPhase phase).toPhase =
      match phase with
      | .surfaceLexing => .surfaceLexing
      | .surfaceParsing => .surfaceParsing := by
  cases phase <;> rfl

end FrontendPhase

inductive ResourceKind where
  | sourceBytes
  deriving Repr, BEq, DecidableEq

inductive VerdictKind where
  | accepted
  | rejected
  | inconclusive
  | internalError
  deriving Repr, BEq, DecidableEq

/-!
The proof field fixes the v4 source-preflight relation: `consumed` is present
and strictly exceeds `limit`. Equality ignores the proof by proof irrelevance.
-/
structure SourceBytesExceeded where
  limit : Nat
  consumed : Nat
  exceeded : limit < consumed
  deriving Repr, DecidableEq

namespace SourceBytesExceeded

instance : BEq SourceBytesExceeded :=
  ⟨fun first second =>
    first.limit == second.limit && first.consumed == second.consumed⟩

def ofValues? (limit consumed : Nat) : Option SourceBytesExceeded :=
  if exceeded : limit < consumed then
    some { limit, consumed, exceeded }
  else
    none

@[simp] theorem ofValues?_fields (exhaustion : SourceBytesExceeded) :
    ofValues? exhaustion.limit exhaustion.consumed = some exhaustion := by
  cases exhaustion with
  | mk limit consumed exceeded => simp [ofValues?, exceeded]

theorem fields_eq_of_ofValues?_eq_some
    {limit consumed : Nat}
    {exhaustion : SourceBytesExceeded}
    (projection : ofValues? limit consumed = some exhaustion) :
    exhaustion.limit = limit ∧ exhaustion.consumed = consumed := by
  unfold ofValues? at projection
  split at projection
  next _ =>
    have equality := Option.some.inj projection
    rw [← equality]
    exact ⟨rfl, rfl⟩
  next _ =>
    simp at projection

def resource (_exhaustion : SourceBytesExceeded) : ResourceKind :=
  .sourceBytes

def phase (_exhaustion : SourceBytesExceeded) : Phase :=
  .sourcePreflight

end SourceBytesExceeded

inductive InternalError where
  | frontendInvariant (phase : FrontendPhase)
  | surfaceWireProjectionFailed
  | oracleResponseInvariant
  deriving Repr, BEq, DecidableEq

namespace InternalError

def phase : InternalError -> Option Phase
  | .frontendInvariant frontendPhase => some frontendPhase.toPhase
  | .surfaceWireProjectionFailed => some .surfaceEncoding
  | .oracleResponseInvariant => none

def code : InternalError -> String
  | .frontendInvariant _ => "frontend-invariant"
  | .surfaceWireProjectionFailed => "surface-wire-projection-failed"
  | .oracleResponseInvariant => "oracle-response-invariant"

end InternalError

/-!
The canonical capability document is a singleton payload. Its exact fields are
defined in `V4.Capabilities`, while the response type can already exclude an
arbitrary capability value.
-/
inductive CapabilityReport where
  | canonical
  deriving Repr, BEq, DecidableEq

inductive CapabilitiesVerdict where
  | accepted (report : CapabilityReport)
  | oracleResponseInvariant
  deriving Repr, BEq, DecidableEq

namespace CapabilitiesVerdict

def kind : CapabilitiesVerdict -> VerdictKind
  | .accepted _ => .accepted
  | .oracleResponseInvariant => .internalError

def phase : CapabilitiesVerdict -> Option Phase
  | .accepted _ => some .protocol
  | .oracleResponseInvariant => none

def internalError? : CapabilitiesVerdict -> Option InternalError
  | .accepted _ => none
  | .oracleResponseInvariant => some .oracleResponseInvariant

end CapabilitiesVerdict

inductive ParseVerdict where
  | accepted (result : Solcore.Surface.Wire.V1.ParseResult)
  | rejected (diagnostic : Solcore.Surface.Wire.V1.Diagnostic)
  | inconclusive (exhaustion : SourceBytesExceeded)
  | internalError (error : InternalError)
  deriving Repr, BEq

namespace ParseVerdict

def kind : ParseVerdict -> VerdictKind
  | .accepted _ => .accepted
  | .rejected _ => .rejected
  | .inconclusive _ => .inconclusive
  | .internalError _ => .internalError

def phase : ParseVerdict -> Option Phase
  | .accepted _ => some .surfaceParsing
  | .rejected diagnostic =>
      some (FrontendPhase.ofDiagnosticPhase diagnostic.phase).toPhase
  | .inconclusive _ => some .sourcePreflight
  | .internalError error => error.phase

end ParseVerdict

inductive ResponseBody where
  | capabilities (verdict : CapabilitiesVerdict)
  | parse (verdict : ParseVerdict)
  deriving Repr, BEq

namespace ResponseBody

def queryKind : ResponseBody -> QueryKind
  | .capabilities _ => .capabilities
  | .parse _ => .parse

def verdictKind : ResponseBody -> VerdictKind
  | .capabilities verdict => verdict.kind
  | .parse verdict => verdict.kind

def phase : ResponseBody -> Option Phase
  | .capabilities verdict => verdict.phase
  | .parse verdict => verdict.phase

end ResponseBody

structure Response where
  id : RequestId
  body : ResponseBody
  deriving Repr, BEq

namespace Response

def schema (_response : Response) : String :=
  schemaVersion

def spec (_response : Response) : String :=
  Solcore.m2bLanguage.id

def profile (_response : Response) : ProfileRef :=
  ProfileRef.canonical

def queryKind (response : Response) : QueryKind :=
  response.body.queryKind

def verdictKind (response : Response) : VerdictKind :=
  response.body.verdictKind

def phase (response : Response) : Option Phase :=
  response.body.phase

end Response

/-!
Protocol errors are outside the response union. Their kind and schema are fixed
by accessors; a recoverable request identifier is necessarily nonempty.
-/
structure ProtocolError where
  id : Option RequestId := none
  code : String
  path : String := ""
  arguments : Lean.Json := .null
  display : String
  deriving BEq

namespace ProtocolError

def kind (_error : ProtocolError) : String :=
  "protocolError"

def schema (_error : ProtocolError) : String :=
  schemaVersion

end ProtocolError

end Solcore.Oracle.V4
