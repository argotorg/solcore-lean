import Solcore.Semantics.CheckedCoreContract

/-! Checked initializer/runtime pairs selected by immutable creation identifiers. -/

set_option autoImplicit false

namespace Solcore.Semantics

/-- Checker-accepted initializer code and the runtime code it may install. -/
structure CheckedCreationTemplate where
  initializer : CheckedCoreContract
  runtime : CheckedCoreContract

/-- Immutable checked creation templates indexed by a full Core Word. -/
structure CheckedCreationTemplateRegistry where
  lookup : Core.Word → Option CheckedCreationTemplate

namespace CheckedCreationTemplateRegistry

/-- The registry in which no creation template is available. -/
def empty : CheckedCreationTemplateRegistry := {
  lookup := fun _ => none
}

end CheckedCreationTemplateRegistry

end Solcore.Semantics
