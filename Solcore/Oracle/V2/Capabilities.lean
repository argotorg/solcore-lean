import Solcore.Baseline
import Solcore.Core.Wire
import Solcore.Feature
import Solcore.Oracle.V2.Schema

set_option autoImplicit false

namespace Solcore.Oracle.V2

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
  spec := m1aLanguage.id
  profile := m1aCoreProfile
  profileDigest := m1aCoreProfileDigest
  coreSchema := Core.Wire.schemaVersion
  checkResultSchema
  valueObservationSchema
  baselines := implementationBaselines
  implementedQueries := QueryKind.all
  features := m1aFeatureMatrix
  defaultLimits := CoreLimits.default
}

end Solcore.Oracle.V2
