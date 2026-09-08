import Solcore.Frontend.LocalReference
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.LocalReferenceElaboration
import Solcore.Frontend.LocalReferenceElaborationProperties
import Solcore.Frontend.LocalReferenceEvaluation
import Solcore.Frontend.LocalReferenceExecutionProperties

/-!
Canonical local-reference semantic adapter with explicit caller-supplied name,
type, and runtime tables. Only identifiers and grouping are supported here;
no source program resolution, parser change, or wire publication is implied.
-/
