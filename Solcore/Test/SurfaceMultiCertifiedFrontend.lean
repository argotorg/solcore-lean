import Solcore.Surface.Multi.CertifiedFrontend

/-! Executable regressions for the proof-argument-free certified frontend. -/

set_option autoImplicit false

namespace Tests

open Solcore.Workspace
open Solcore.Surface.Multi

private inductive ExpectedPhase where
  | lexical
  | parse
  | structural
  deriving BEq

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def certifiedFrontendSource : IO SourceId := do
  match CanonicalSourcePath.parse "CertifiedFrontend.solc" with
  | some path => pure { library := .main, path }
  | none => throw (IO.userError "the certified-frontend test path is invalid")

private def surfaceDiagnosticPhase : SurfaceDiagnostic → ExpectedPhase
  | .lexical _ => .lexical
  | .parse _ => .parse
  | .structural _ => .structural

private def expectFailure
    (source : SourceId)
    (content : String)
    (phase : ExpectedPhase)
    (code : String) : IO Unit := do
  let file : WorkspaceFile := { id := source, content }
  match parseModule file with
  | .ok _ =>
      throw (IO.userError
        s!"certified frontend unexpectedly accepted the {code} fixture")
  | .error reported =>
      let diagnostic := reported.head
      assertTrue (reported.tail.isEmpty)
        s!"the {code} fixture emitted more than one diagnostic"
      assertTrue (surfaceDiagnosticPhase diagnostic == phase)
        s!"the {code} fixture was reported by the wrong frontend phase"
      assertTrue (diagnosticSource diagnostic == source)
        s!"the {code} fixture diagnostic changed its source identity"
      assertTrue (diagnosticCode diagnostic == code)
        s!"the certified frontend changed diagnostic {code}"

private def expectSuccess (source : SourceId) : IO Unit := do
  let file : WorkspaceFile := {
    id := source
    content := "function f(x: word) { return 0; }"
  }
  match parseModule file with
  | .error reported =>
      throw (IO.userError
        s!"the certified frontend rejected a valid function: {reprStr reported}")
  | .ok certified =>
      assertTrue (certified.file == file)
        "the successful certificate changed its input file"
      assertTrue (certified.module.span.source == source &&
          certified.module.payload.source == source)
        "the successful certificate changed its module source identity"
      match certified.module.payload.items with
      | [item] =>
          match item.payload with
          | .functionDecl _ => pure ()
          | _ => throw (IO.userError
              "the successful certificate did not contain a function item")
      | _ => throw (IO.userError
          "the successful certificate did not contain exactly one item")

/-- Exercise first-failing-phase diagnostics and one certified success through
the public frontend entry point. -/
def testMultiCertifiedFrontend : IO Unit := do
  let source ← certifiedFrontendSource
  expectFailure source "\"" .lexical "MSL0003"
  expectFailure source "data" .parse "MSP0001"
  expectFailure source "function f(x) { return 0; }" .structural "MSS0019"
  expectSuccess source

end Tests
