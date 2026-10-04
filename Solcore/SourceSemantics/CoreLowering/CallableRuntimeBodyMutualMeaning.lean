import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins

/-! One source induction and one native induction close a family of actual
static bodies. The expression interface is internal to the enclosing mutual
proof and receives only strictly smaller original body obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ι : Type} (origins : ι → Origin values ambient registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include extension faithful observations in
/-- Source children may use the current budget; callee bodies are strict. -/
theorem preserves_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget (PreservesAt functions program (origins callee))) →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults (origins i).protectedEntry)
    (size : Nat) : ∀ i, PreservesAt functions program (origins i) size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro i entry outcome after trace
    have children : ∀ context, (origins i).validity context → RecursiveNamedHeaderContracts.AtMost size
        (fun child => RecursiveNamedBoundedContracts.PreservesAt child
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context
          (origins i).function.evidence (origins i).function.source ((origins i).certificates context)
          faults (origins i).protectedEntry) := by
      intro context valid child within
      exact expressionMeaning i context valid size child within (fun callee smaller strict => ih smaller strict callee)
    exact (origins i).body.preserves_sized functions (origins i).definitions (origins i).registered extension
      program faithful observations (origins i).escapedFault (origins i).transport (origins i).binders
      (origins i).extend (origins i).runtimeOf size size (Nat.le_refl size) children
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
      entry.unmapped entry.installed trace

include extension faithful observations functionTypes in
/-- Native finish inversion selects original strict children. Reflection
returns the source grade without a preservation or source-trace premise. -/
theorem reflects_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget (ReflectsAt functions program (origins callee))) →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults (origins i).protectedEntry)
    (size : Nat) : ∀ i, ReflectsAt functions program (origins i) size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro i entry value finalStore completed
    have children : ∀ context, (origins i).validity context → RecursiveNamedBoundedContracts.Below size
        (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context
          (origins i).function.evidence (origins i).function.source ((origins i).certificates context)
          faults (origins i).protectedEntry) := by
      intro context valid child smaller
      exact expressionMeaning i context valid size child (Nat.le_of_lt smaller)
        (fun callee smaller strict => ih smaller strict callee)
    exact (origins i).body.reflects_sized functions (origins i).definitions (origins i).registered extension
      program faithful observations functionTypes (origins i).escapedFault (origins i).transport (origins i).binders
      (origins i).extend (origins i).runtimeOf size size (Nat.le_refl size) children
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
      entry.unmapped entry.installed completed

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning
