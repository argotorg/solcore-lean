import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry

/-! Empty public argument encoding preserves the original session's metadata
registry. The receipt uses the actual startup encoder and retains its exact
context; neither Source typing nor a value representation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
open Frontend SourceInference

theorem StartAt.empty_registry
    {artifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session artifact} {key : SourceCoreIndexedSession.Key}
    {fuel : Nat} {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {recipe : SourceCoreIndexedSession.Recipe} {root : SourceCoreIndexedSession.Root recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    (started : RecursiveNamedPublicStartMeaning.StartAt session key [] fuel checkpoint recipe root
      world store native encodedValues)
    (atRegistry : session.RegistryAt registry) : encodedValues.registry = registry := by
  exact started.simple_registry atRegistry (by intro argument member; cases member)


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
