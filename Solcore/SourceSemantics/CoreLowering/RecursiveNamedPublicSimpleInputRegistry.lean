import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning

/-! Actual scalar and product argument encoding preserves the session metadata
registry. This follows from the retained startup operation; Source typing and
value representation are not premises. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
open Frontend SourceInference

theorem StartAt.simple_registry
    {artifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session artifact} {key : SourceCoreIndexedSession.Key}
    {arguments : List SourceCorePublicValues.Value}
    {fuel : Nat} {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {recipe : SourceCoreIndexedSession.Recipe} {root : SourceCoreIndexedSession.Root recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    (started : StartAt session key arguments fuel checkpoint recipe root
      world store native encodedValues)
    (atRegistry : session.RegistryAt registry)
    (simple : ∀ argument ∈ arguments, SourceCoreIndexedSession.SimplePublic argument) :
    encodedValues.registry = registry := by
  have unchanged := started.original.simple_registry simple
  cases checkpoint
  cases session
  exact (congrArg SourceCoreCompatibleValues.Context.registry started.values).symm.trans
    (unchanged.trans atRegistry)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
