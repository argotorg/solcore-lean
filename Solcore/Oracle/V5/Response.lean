import Lean.Data.Json
import Solcore.Oracle.V5.Observation

/-! Typed, query-indexed response values for Oracle v5. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

/-- The five response verdict tags published by v5. -/
inductive VerdictKind where
  | accepted
  | rejected
  | inconclusive
  | executed
  | internalError
  deriving Repr, BEq, DecidableEq

/--
One canonical semantic rejection. The response codec wraps this value in the
required singleton `diagnostics` array and emits a null display string.
-/
structure Diagnostic where
  code : String
  phase : Phase
  path : List String
  arguments : Lean.Json
  deriving BEq

namespace Diagnostic

def severity (_diagnostic : Diagnostic) : String := "error"

def display (_diagnostic : Diagnostic) : Option String := none

end Diagnostic

/-- The capabilities document is a single derived value, never caller data. -/
inductive CapabilityReport where
  | canonical
  deriving Repr, BEq, DecidableEq

/-- The only payload accepted by a successful Core-check query. -/
structure CoreCheckResult where
  resultType : Solcore.Core.Wire.V3.Ty
  deriving Repr, BEq, DecidableEq

inductive CapabilitiesVerdict where
  | accepted (report : CapabilityReport)
  | inconclusive (exhaustion : Exhaustion)
  | internalError (error : InternalError)
  deriving Repr, BEq, DecidableEq

namespace CapabilitiesVerdict

def kind : CapabilitiesVerdict → VerdictKind
  | .accepted _ => .accepted
  | .inconclusive _ => .inconclusive
  | .internalError _ => .internalError

def phase : CapabilitiesVerdict → Option Phase
  | .accepted _ => some .protocol
  | .inconclusive exhaustion => some exhaustion.phase
  | .internalError error => error.phase

end CapabilitiesVerdict

inductive CoreCheckVerdict where
  | accepted (result : CoreCheckResult)
  | rejected (diagnostic : Diagnostic)
  | inconclusive (exhaustion : Exhaustion)
  | internalError (error : InternalError)
  deriving BEq

namespace CoreCheckVerdict

def kind : CoreCheckVerdict → VerdictKind
  | .accepted _ => .accepted
  | .rejected _ => .rejected
  | .inconclusive _ => .inconclusive
  | .internalError _ => .internalError

def phase : CoreCheckVerdict → Option Phase
  | .accepted _ => some .coreChecking
  | .rejected diagnostic => some diagnostic.phase
  | .inconclusive exhaustion => some exhaustion.phase
  | .internalError error => error.phase

end CoreCheckVerdict

inductive ExecuteVerdict where
  | rejected (diagnostic : Diagnostic)
  | inconclusive (exhaustion : Exhaustion)
  | executed (observation : ExecutionObservation)
  | internalError (error : InternalError)
  deriving BEq

namespace ExecuteVerdict

def kind : ExecuteVerdict → VerdictKind
  | .rejected _ => .rejected
  | .inconclusive _ => .inconclusive
  | .executed _ => .executed
  | .internalError _ => .internalError

def phase : ExecuteVerdict → Option Phase
  | .rejected diagnostic => some diagnostic.phase
  | .inconclusive exhaustion => some exhaustion.phase
  | .executed _ => some .contractExecution
  | .internalError error => error.phase

end ExecuteVerdict

/-- Query/verdict compatibility is enforced by construction. -/
inductive ResponseBody where
  | capabilities (verdict : CapabilitiesVerdict)
  | coreCheck (verdict : CoreCheckVerdict)
  | execute (verdict : ExecuteVerdict)
  deriving BEq

namespace ResponseBody

def queryKind : ResponseBody → QueryKind
  | .capabilities _ => .capabilities
  | .coreCheck _ => .coreCheck
  | .execute _ => .execute

def verdictKind : ResponseBody → VerdictKind
  | .capabilities verdict => verdict.kind
  | .coreCheck verdict => verdict.kind
  | .execute verdict => verdict.kind

def phase : ResponseBody → Option Phase
  | .capabilities verdict => verdict.phase
  | .coreCheck verdict => verdict.phase
  | .execute verdict => verdict.phase

end ResponseBody

/-- Every non-protocol Oracle v5 response repeats the validated request ID. -/
structure Response where
  id : RequestId
  body : ResponseBody
  deriving BEq

namespace Response

def schema (_response : Response) : String := schemaVersion

def spec (_response : Response) : String := Solcore.m3aLanguage.id

def profile (_response : Response) : ProfileRef := ProfileRef.canonical

def queryKind (response : Response) : QueryKind := response.body.queryKind

def verdictKind (response : Response) : VerdictKind := response.body.verdictKind

def phase (response : Response) : Option Phase := response.body.phase

end Response

/-- A strict transport failure outside the typed response union. -/
structure ProtocolError where
  id : Option RequestId := none
  code : String
  path : String := ""
  arguments : Lean.Json := .null
  display : String
  deriving BEq

namespace ProtocolError

def kind (_error : ProtocolError) : String := "protocolError"

def schema (_error : ProtocolError) : String := schemaVersion

end ProtocolError

end Solcore.Oracle.V5
