import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning

/-! Actual input encoding of an authenticated function handle preserves the
metadata registry, including when the handle was retained across earlier calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
open Frontend SourceInference

theorem StartAt.function_registry
    {artifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session artifact} {key : SourceCoreIndexedSession.Key}
    {handle : SourceCorePublicValues.Handle}
    {fuel : Nat} {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {recipe : SourceCoreIndexedSession.Recipe} {root : SourceCoreIndexedSession.Root recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    (started : StartAt session key [.function handle] fuel checkpoint recipe root
      world store native encodedValues)
    (atRegistry : session.RegistryAt registry) :
    encodedValues.registry = registry := by
  have unchanged := started.original.function_registry
  cases checkpoint
  cases session
  exact (congrArg SourceCoreCompatibleValues.Context.registry started.values).symm.trans
    (unchanged.trans atRegistry)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
