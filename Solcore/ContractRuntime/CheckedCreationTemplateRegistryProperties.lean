import Solcore.ContractRuntime.CheckedCreationTemplateRegistry

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
