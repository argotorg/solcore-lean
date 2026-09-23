import Solcore.ContractRuntime.CheckedCoreContract

/-! Checked initializer/runtime pairs selected by immutable creation identifiers. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

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

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCreationTemplateRegistryProperties`
-/

/-! Projection and empty-registry laws for checked creation templates. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace CheckedCreationTemplate

@[simp] theorem mk_initializer
    (initializer runtime : CheckedCoreContract) :
    (CheckedCreationTemplate.mk initializer runtime).initializer = initializer :=
  rfl

@[simp] theorem mk_runtime
    (initializer runtime : CheckedCoreContract) :
    (CheckedCreationTemplate.mk initializer runtime).runtime = runtime :=
  rfl

end CheckedCreationTemplate

namespace CheckedCreationTemplateRegistry

@[simp] theorem empty_lookup (identifier : Core.Word) :
    empty.lookup identifier = none :=
  rfl

end CheckedCreationTemplateRegistry

end Solcore.ContractRuntime
