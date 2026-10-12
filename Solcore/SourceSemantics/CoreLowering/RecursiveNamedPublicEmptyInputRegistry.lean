import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning

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
  obtain ⟨actualRoot, _found, _key, arity, encoded, accepted, _origin, _request, _world,
    _initial, _slots, values⟩ := started.original
  have noSource : actualRoot.inputs = [] := List.length_eq_zero_iff.mp arity
  generalize nativeTypes : actualRoot.types = types at encoded accepted _initial values
  cases types with
  | nil =>
    rw [noSource] at accepted
    cases accepted
    cases checkpoint
    cases session
    exact (congrArg SourceCoreCompatibleValues.Context.registry (started.values.symm.trans values)).trans atRegistry
  | cons head tail =>
    rw [noSource] at accepted
    cases accepted


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
