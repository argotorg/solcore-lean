import Solcore.Baseline
import Solcore.Feature
import Solcore.Oracle.V5.Response

/-! The singleton, metadata-derived Oracle v5 capability report. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

namespace CapabilityReport

def schema (_report : CapabilityReport) : String := capabilitiesSchema

def spec (_report : CapabilityReport) : String := Solcore.m3aLanguage.id

def profile (_report : CapabilityReport) : Solcore.SpecProfile :=
  Solcore.m3aContractProfile

def profileDigest (_report : CapabilityReport) : String :=
  Solcore.m3aContractProfileDigest

def coreSchema (_report : CapabilityReport) : String :=
  Solcore.Core.Wire.V3.schemaVersion

def checkResultSchema (_report : CapabilityReport) : String :=
  Solcore.Oracle.V5.checkResultSchema

def executionSchema (_report : CapabilityReport) : String :=
  Solcore.Oracle.V5.executionSchema

def stateObservationSchema (_report : CapabilityReport) : String :=
  Solcore.Oracle.V5.stateObservationSchema

def contractProfiles (_report : CapabilityReport) : Array String :=
  #["returnWord", "wordOutcomeV1"]

def abiProfiles (_report : CapabilityReport) : Array String :=
  #["staticWordAbiV1"]

def implementedQueries (_report : CapabilityReport) : Array QueryKind :=
  QueryKind.all

def maxNestedCallDepth (_report : CapabilityReport) : Nat := 1

def observationKinds (_report : CapabilityReport) : Array String :=
  #["accountPresence", "storage", "balance", "nonce", "code"]

def defaultLimits (_report : CapabilityReport) : Limits := Limits.default

def baselines (_report : CapabilityReport) :
    Array Solcore.ImplementationBaseline :=
  Solcore.implementationBaselines

def features (_report : CapabilityReport) : Array Solcore.FeatureRow :=
  Solcore.m3aContractFeatureMatrix

end CapabilityReport

def capabilityReport : CapabilityReport := .canonical

@[simp] theorem capabilityReport_schema :
    capabilityReport.schema = "solcore-capabilities/v5" := rfl

@[simp] theorem capabilityReport_spec :
    capabilityReport.spec = "solcore/0.1.0-draft.5" := rfl

@[simp] theorem capabilityReport_profileDigest :
    capabilityReport.profileDigest =
      "sha256:da3d49b830d25705634cfda568691f1f12fe5a7d038bd0b7ca5839134c1073d5" :=
  rfl

@[simp] theorem capabilityReport_coreSchema :
    capabilityReport.coreSchema = "solcore-semantic-core/v3" := rfl

@[simp] theorem capabilityReport_contractProfiles :
    capabilityReport.contractProfiles = #["returnWord", "wordOutcomeV1"] := rfl

@[simp] theorem capabilityReport_abiProfiles :
    capabilityReport.abiProfiles = #["staticWordAbiV1"] := rfl

@[simp] theorem capabilityReport_implementedQueries :
    capabilityReport.implementedQueries =
      #[.capabilities, .coreCheck, .execute] := rfl

@[simp] theorem capabilityReport_maxNestedCallDepth :
    capabilityReport.maxNestedCallDepth = 1 := rfl

end Solcore.Oracle.V5
