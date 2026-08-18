import Solcore.Baseline
import Solcore.Feature
import Solcore.Oracle.V4.Schema
import Solcore.Surface.Wire.V1.Codec

set_option autoImplicit false

namespace Solcore.Oracle.V4

/-!
The Oracle v4 capability report is a singleton with derived fields. This keeps
the public result payload closed while reusing the canonical M2b metadata
objects directly.
-/
namespace CapabilityReport

def schema (_report : CapabilityReport) : String :=
  capabilitiesSchema

def spec (_report : CapabilityReport) : String :=
  Solcore.m2bLanguage.id

def profile (_report : CapabilityReport) : Solcore.SpecProfile :=
  Solcore.m2bFrontendProfile

def profileDigest (_report : CapabilityReport) : String :=
  Solcore.m2bFrontendProfileDigest

def surfaceSchema (_report : CapabilityReport) : String :=
  Solcore.Surface.Wire.V1.schemaVersion

def parseResultSchema (_report : CapabilityReport) : String :=
  Solcore.Surface.Wire.V1.parseResultSchemaVersion

def baselines (_report : CapabilityReport) :
    Array Solcore.ImplementationBaseline :=
  Solcore.implementationBaselines

def implementedQueries (_report : CapabilityReport) : Array QueryKind :=
  QueryKind.all

def features (_report : CapabilityReport) : Array Solcore.FeatureRow :=
  Solcore.m2bFrontendFeatureMatrix

def defaultLimits (_report : CapabilityReport) : Limits :=
  Limits.default

end CapabilityReport

def capabilityReport : CapabilityReport :=
  .canonical

@[simp] theorem capabilityReport_schema :
    capabilityReport.schema = "solcore-capabilities/v4" := by
  rfl

@[simp] theorem capabilityReport_spec :
    capabilityReport.spec = "solcore/0.1.0-draft.4" := by
  rfl

@[simp] theorem capabilityReport_profile :
    capabilityReport.profile = Solcore.m2bFrontendProfile := by
  rfl

@[simp] theorem capabilityReport_profileDigest :
    capabilityReport.profileDigest = Solcore.m2bFrontendProfileDigest := by
  rfl

@[simp] theorem capabilityReport_surfaceSchema :
    capabilityReport.surfaceSchema = "solcore-surface/v1" := by
  rfl

@[simp] theorem capabilityReport_parseResultSchema :
    capabilityReport.parseResultSchema = "solcore-parse-result/v1" := by
  rfl

@[simp] theorem capabilityReport_implementedQueries :
    capabilityReport.implementedQueries = #[.capabilities, .parse] := by
  rfl

@[simp] theorem capabilityReport_defaultSourceBytes :
    capabilityReport.defaultLimits.sourceBytes = 1048576 := by
  rfl

end Solcore.Oracle.V4
