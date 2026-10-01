import Solcore.Core.DefinitionExtension
import Solcore.Core.OrderedMapping

/-! A source catalog keeps its own nominal identities. Additional ordinary Core
definitions are an authenticated suffix, not invented source declarations.
This receipt transports old registrations and typing without claiming that new
administrative closures were typable in the smaller catalog. -/
set_option autoImplicit false
namespace Solcore.Core

structure AmbientDefinitions (base : DataEnvironment) where
  definitions : DataEnvironment
  basePrefix : base.Extends definitions

def AmbientDefinitions.original (base : DataEnvironment) : AmbientDefinitions base :=
  ⟨base, .refl base⟩

def AmbientDefinitions.append (base suffix : DataEnvironment) : AmbientDefinitions base :=
  ⟨base ++ suffix, .append base suffix⟩

theorem OrderedMapping.Layout.Registered.extend_definitions {base future : DataEnvironment}
    {layout : OrderedMapping.Layout} (registered : layout.Registered base)
    (extension : base.Extends future) : layout.Registered future :=
  ⟨registered.keyWellFormed.extend_definitions extension,
    registered.valueWellFormed.extend_definitions extension, extension.lookup registered.lookup⟩

end Solcore.Core
