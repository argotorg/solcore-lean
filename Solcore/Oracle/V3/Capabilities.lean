import Solcore.Baseline
import Solcore.Core.Wire.V2
import Solcore.Feature
import Solcore.Oracle.V3.Schema

set_option autoImplicit false

namespace Solcore.Oracle.V3

structure CapabilityReport where
  schema : String
  spec : String
  profile : SpecProfile
  profileDigest : String
  coreSchema : String
  checkResultSchema : String
  valueObservationSchema : String
  baselines : Array ImplementationBaseline
  implementedQueries : Array QueryKind
  features : Array FeatureRow
  defaultLimits : CoreLimits
  deriving Lean.ToJson

def capabilityReport : CapabilityReport := {
  schema := capabilitiesSchema
  spec := m1cLanguage.id
  profile := m1cCoreProfile
  profileDigest := m1cCoreProfileDigest
  coreSchema := Core.Wire.V2.schemaVersion
  checkResultSchema
  valueObservationSchema
  baselines := implementationBaselines
  implementedQueries := QueryKind.all
  features := m1cFeatureMatrix
  defaultLimits := CoreLimits.default
}

end Solcore.Oracle.V3
