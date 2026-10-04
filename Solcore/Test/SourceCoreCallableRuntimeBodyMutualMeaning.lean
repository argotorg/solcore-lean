import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning

/-! Concrete builtin certificates close both neutral body contracts. The family
may contain different actual sources, dictionaries, code, and protected entries.
The named adapter retains the original source/native child grades and state.
This formal test adds no runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableRuntimeBodyMutualMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins

abbrev source_family := @CallableRuntimeBodyMutualMeaning.preserves_at
abbrev native_family := @CallableRuntimeBodyMutualMeaning.reflects_at
abbrev named_source := @RecursiveNamedCatalogMutualMeaning.preserves_at_with_family
abbrev named_native := @RecursiveNamedCatalogMutualMeaning.reflects_at_with_family
abbrev actual_named_entry := @RecursiveNamedCatalogMutualMeaning.NamedFamily.entry

variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ι : Type} (origins : ι → Origin values ambient registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (readFuel : ι → Nat) (reasonAt : ι → ExpressionId → Word)
  (certificates : ∀ i context, (origins i).certificates context =
    CompatibleExpressionBuiltinRuntime.Certificate (readFuel i) values (origins i).function.source context
      (origins i).solved (reasonAt i))
  (uninitialized : ∀ i id location, faults (.uninitializedLocation location) ((reasonAt i) id))
  (missing : ∀ i id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((reasonAt i) id).add tag))

include extension faithful observations functionTypes certificates uninitialized missing in
/-- The only semantic children come from the actual builtin certificate family. -/
theorem closed_builtin_preserves (size : Nat) : ∀ i, PreservesAt functions program (origins i) size := by
  apply CallableRuntimeBodyMutualMeaning.preserves_at origins functions extension program faithful observations
  intro i context valid budget child within _
  rw [certificates i context]
  have runtime := (origins i).runtimeOf valid
  intro scope id lowered
  exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
    (ProtectedExpressionMeaning.preserves_of_typed (origins i).protectedEntry
      (CompatibleExpressionBuiltinRuntime.preserves (fuel := readFuel i) (source := (origins i).function.source) functions extension faithful observations functionTypes
        program (origins i).function.evidence runtime.ledger runtime.runtime (origins i).body.unique
        (uninitialized i) (missing i))) child (scope := scope) (id := id) (lowered := lowered)

include extension faithful observations functionTypes certificates uninitialized missing in
/-- Reflection starts from each original native completion and returns an
independent source grade and the full retained entry. -/
theorem closed_builtin_reflects (size : Nat) : ∀ i, ReflectsAt functions program (origins i) size := by
  apply CallableRuntimeBodyMutualMeaning.reflects_at origins functions extension program faithful observations functionTypes
  intro i context valid budget child within _
  rw [certificates i context]
  have runtime := (origins i).runtimeOf valid
  intro scope id lowered
  exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
    (ProtectedExpressionMeaning.reflects_of_typed (origins i).protectedEntry
      (CompatibleExpressionBuiltinRuntime.reflects (fuel := readFuel i) (source := (origins i).function.source) functions extension faithful observations functionTypes
        program (origins i).function.evidence runtime.ledger runtime.runtime (uninitialized i) (missing i))) child (scope := scope) (id := id) (lowered := lowered)

/-- Selection keeps the strict original callee grade; it does not rebuild it. -/
theorem original_native_child {budget child : Nat} (strict : child < budget)
    (below : ∀ i, RecursiveNamedBoundedContracts.Below budget (ReflectsAt functions program (origins i)))
    (i : ι) : ReflectsAt functions program (origins i) child := below i child strict

/-- Source and native budgets are independent interfaces. -/
theorem original_source_child {budget child : Nat} (strict : child < budget)
    (below : ∀ i, RecursiveNamedBoundedContracts.Below budget (PreservesAt functions program (origins i)))
    (i : ι) : PreservesAt functions program (origins i) child := below i child strict

/-- Static nesting rank is not a premise of either native or source decrease. -/
theorem equal_grade_not_strict (size : Nat) : ¬ size < size := Nat.lt_irrefl size

end Tests.SourceCoreCallableRuntimeBodyMutualMeaning
