import Solcore.Oracle.V5.ContractAdmission
import Solcore.Oracle.V5.RootInstallation
import Solcore.Oracle.V5.ScenarioPreparation
import Solcore.ContractRuntime.RuntimeScalars.TextProperties

/-! Canonical Oracle v5 diagnostics for scenario preparation. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.ScenarioDiagnostic

open Solcore.ContractRuntime

private def diagnostic
    (phase : Phase)
    (code : String)
    (path : List String)
    (arguments : Lean.Json) : Diagnostic := {
  code
  phase
  path
  arguments
}

private def addressText (address : Address) : String :=
  encodeAddressText address

private def wordText (word : Solcore.Core.Word) : String :=
  encodeWordText word

def ofWorldError : WorldMaterializationError → Diagnostic
  | .duplicateAccount address => diagnostic .worldValidation
      "oracle.v5.world.duplicate-account"
      ["world", "accounts", addressText address]
      (.mkObj [("address", addressText address)])
  | .duplicateStorageSlot address slot => diagnostic .worldValidation
      "oracle.v5.world.duplicate-storage-slot"
      ["world", "accounts", addressText address, "storage", wordText slot]
      (.mkObj [
        ("address", addressText address),
        ("slot", wordText slot)
      ])
  | .zeroStorageValue address slot => diagnostic .worldValidation
      "oracle.v5.world.zero-storage-value"
      ["world", "accounts", addressText address, "storage", wordText slot,
        "value"]
      (.mkObj [
        ("address", addressText address),
        ("slot", wordText slot)
      ])
  | .danglingContract address id => diagnostic .worldValidation
      "oracle.v5.reference.dangling-contract"
      ["world", "accounts", addressText address, "code"]
      (.mkObj [("id", id)])

def ofEnvironmentError : EnvironmentMaterializationError → Diagnostic
  | .duplicateCallAddress address => diagnostic .environmentValidation
      "oracle.v5.environment.duplicate-call-address"
      ["environment", "callRegistry", addressText address]
      (.mkObj [("address", addressText address)])
  | .duplicateTemplateId templateId => diagnostic .environmentValidation
      "oracle.v5.environment.duplicate-template-id"
      ["environment", "creationTemplates", wordText templateId]
      (.mkObj [("templateId", wordText templateId)])
  | .duplicateCreationRoute creator nonce =>
      diagnostic .environmentValidation
        "oracle.v5.environment.duplicate-creation-route"
        ["environment", "creationAddressPolicy", "routes",
          addressText creator, wordText nonce]
        (.mkObj [
          ("creator", addressText creator),
          ("nonce", wordText nonce)
        ])
  | .danglingCallContract address id => diagnostic .environmentValidation
      "oracle.v5.reference.dangling-contract"
      ["environment", "callRegistry", addressText address, "contract"]
      (.mkObj [("id", id)])
  | .danglingInitializer templateId id => diagnostic .environmentValidation
      "oracle.v5.reference.dangling-contract"
      ["environment", "creationTemplates", wordText templateId,
        "initializer"]
      (.mkObj [("id", id)])
  | .danglingRuntime templateId id => diagnostic .environmentValidation
      "oracle.v5.reference.dangling-contract"
      ["environment", "creationTemplates", wordText templateId, "runtime"]
      (.mkObj [("id", id)])

def ofProbeError (duplicate : DuplicateProbe) : Diagnostic :=
  diagnostic .probeValidation "oracle.v5.probe.duplicate"
    ["invocation", "probes", toString duplicate.secondIndex]
    (.mkObj [
      ("firstIndex", Lean.toJson duplicate.firstIndex),
      ("secondIndex", Lean.toJson duplicate.secondIndex)
    ])

def ofRootRejection
    (target : Address) : RootInstallationRejection → Diagnostic
  | .targetAbsent => diagnostic .rootInstallation
      "oracle.v5.root.target-absent"
      ["world", "accounts", addressText target]
      (.mkObj [("target", addressText target)])
  | .targetCodeAbsent => diagnostic .rootInstallation
      "oracle.v5.root.target-code-absent"
      ["world", "accounts", addressText target, "code"]
      (.mkObj [("target", addressText target)])

/-- Collapse the preparation sum while retaining checker projection failures. -/
def ofPreparationError :
    ScenarioPreparationError → Except InternalError Diagnostic
  | .contractAdmission error => ContractAdmissionDiagnostic.ofError error
  | .worldValidation error => .ok (ofWorldError error)
  | .environmentValidation error => .ok (ofEnvironmentError error)
  | .probeValidation error => .ok (ofProbeError error)

end Solcore.Oracle.V5.ScenarioDiagnostic
