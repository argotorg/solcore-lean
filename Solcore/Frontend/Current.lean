import Solcore.Frontend.ProgramInterfaces
import Solcore.Frontend.Internal.SignatureProperties
import Solcore.Frontend.ProgramSignatureFormation
import Solcore.Frontend.Internal.CheckingProperties
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.ExecutableImplMethods
import Solcore.Frontend.SourceStageAnalysis
import Solcore.Frontend.SourceSpecialization
import Solcore.Frontend.SourceSpecializationWorklist
import Solcore.Frontend.SourceCoreElaboration
import Solcore.Frontend.SourceCore.Lowering
import Solcore.Frontend.SourceCore.Internal.FaultSites
import Solcore.Frontend.SourceCore.Internal.Entries
import Solcore.Frontend.SourceCore.Internal.DirectLinking
import Solcore.Frontend.SourceCompiler
import Solcore.Frontend.Internal.RuntimeValidation


import Solcore.Frontend.SourceCore.Data

import Solcore.Frontend.SourceCore.GeneralFunctions
import Solcore.Frontend.SourceCore.Internal.Allocation
import Solcore.Frontend.SourceCore.CompatibleCatalog
import Solcore.Frontend.SourceCore.Compatible
import Solcore.Frontend.SourceCore.CompatibleFunctions
import Solcore.Frontend.SourceCore.Internal.CallableOutputs
import Solcore.Frontend.SourceCore.Internal.CallableViews
import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.Frontend.SourceCore.Internal.CallablePrincipals
import Solcore.Frontend.SourceCore.Internal.CallableAncestry
import Solcore.Frontend.SourceCore.Internal.CallablePaired
import Solcore.Frontend.SourceCore.Internal.CallableIndexed
import Solcore.Frontend.SourceCoreUnified
import Solcore.Frontend.SourceCoreCompiler
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Frontend.SourceCoreExecution

/-!
# Current pipeline

Imports every stage of the current whole-program pipeline. It declares nothing.
-/

/-! Current whole-program source pipeline and preservation results. -/
