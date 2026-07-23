import Solcore.Oracle.Stream

set_option autoImplicit false

namespace Solcore.Oracle

private def help : String :=
  String.intercalate "\n" [
    "solcore-oracle — executable Solcore specification oracle",
    "",
    "Usage:",
    "  solcore-oracle                 Read NDJSON requests from standard input",
    "  solcore-oracle capabilities    Print the Oracle v1 capability report",
    "  solcore-oracle capabilities-v2 Print the M1b Core capability report",
    "  solcore-oracle capabilities-v3 Print the M1c Core capability report",
    "  solcore-oracle --version       Print the specification version",
    "  solcore-oracle --help          Print this help"
  ]

private def emitJson (json : Lean.Json) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn json.compress
  stdout.flush

private def emitProtocolError (error : ProtocolError) : IO Unit :=
  emitJson (Lean.toJson error)

private def processLine (line : String) : IO Unit :=
  emitJson (processJsonLine line)

partial def serve (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    return
  else
    processLine line
    serve stdin

private def capabilitiesRequest : Request := {
  schema := schemaVersion
  id := "capabilities"
  spec := draftLanguage.id
  profile := {
    id := draftCoreProfile.id
    digest := draftCoreProfileDigest
  }
  query := { kind := .capabilities }
}

private def capabilitiesV2Request : V2.Request := {
  schema := V2.schemaVersion
  id := "capabilities-v2"
  spec := m1aLanguage.id
  profile := {
    id := m1aCoreProfile.id
    digest := m1aCoreProfileDigest
  }
  limits := V2.CoreLimits.default
  query := { kind := .capabilities }
}

private def capabilitiesV3Request : V3.Request := {
  schema := V3.schemaVersion
  id := "capabilities-v3"
  spec := m1cLanguage.id
  profile := {
    id := m1cCoreProfile.id
    digest := m1cCoreProfileDigest
  }
  limits := V3.CoreLimits.default
  query := { kind := .capabilities }
}

def run (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] =>
      IO.println help
      return 0
  | ["--version"] =>
      IO.println draftLanguage.id
      return 0
  | ["capabilities"] =>
      match handle capabilitiesRequest with
      | .ok response =>
          emitJson (Lean.toJson response)
          return 0
      | .error error =>
          emitProtocolError error
          return 1
  | ["capabilities-v2"] =>
      match V2.handle capabilitiesV2Request with
      | .ok response =>
          emitJson (Lean.toJson response)
          return 0
      | .error error =>
          emitJson (Lean.toJson error)
          return 1
  | ["capabilities-v3"] =>
      match V3.handle capabilitiesV3Request with
      | .ok response =>
          emitJson (Lean.toJson response)
          return 0
      | .error error =>
          emitJson (Lean.toJson error)
          return 1
  | [] =>
      serve (← IO.getStdin)
      return 0
  | _ =>
      IO.eprintln help
      return 2

end Solcore.Oracle

def main (args : List String) : IO UInt32 :=
  Solcore.Oracle.run args
