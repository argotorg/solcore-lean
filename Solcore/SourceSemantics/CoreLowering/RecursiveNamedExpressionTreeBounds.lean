import Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionHeadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinHeadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionHeadBounds

/-! The existing recursive expression Tree closes its child obligations within
one inclusive budget. All catalog body obligations remain explicit below that
budget for the subsequent mutual induction. Static syntax and receipts do not
contain body execution. Source and native costs are independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {compilation : SourceCoreFunctions.Context}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificate : GenericExpressionMeaning.Certificate}

include extension faithful functionLeaves functionTypes unique owners missing in
/-- Every existing head uses child obligations at the same inclusive budget;
only an actual named callee consumes the strictly smaller body contract. -/
theorem head_preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCatalog.Head headers compilation source context)
        values source context reasonAt certificate) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered head
  cases head with
  | primitive head =>
    exact RecursiveNamedExpressionCompositionsBounds.Head.preserves_at functions program evidence
      entry_transport budget size within unique children head
  | constructor receipt form accepted sequence =>
    exact RecursiveNamedDataExpressionHeadBounds.preserves_at (calls := RecursiveNamedCatalog.Head headers compilation source context) functions extension faithful functionLeaves functionTypes
      program evidence unique missing entry_transport budget size within children
      ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩
  | member metadata baseMetadata form layout certified =>
    exact RecursiveNamedDataExpressionHeadBounds.preserves_at (calls := RecursiveNamedCatalog.Head headers compilation source context) functions extension faithful functionLeaves functionTypes
      program evidence unique missing entry_transport budget size within children
      ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩
  | index header found form sourceType first second =>
    exact RecursiveNamedDataExpressionHeadBounds.preserves_at (calls := RecursiveNamedCatalog.Head headers compilation source context) functions extension faithful functionLeaves functionTypes
      program evidence unique missing entry_transport budget size within children
      ⟨.index header found form sourceType first second, .index header found form sourceType first second⟩
  | builtin head =>
    exact RecursiveNamedBuiltinHeadBounds.Head.preserves_at functions functionLeaves program evidence unique
      entry_transport budget size within children head
  | call head =>
    exact RecursiveNamedExpressionHeadBounds.preserves_at functions budget size within unique owners
      (fun child smaller => children child (Nat.le_of_lt smaller)) bodies head

include extension faithful functionLeaves functionTypes missing in
/-- Original native children select their own pointwise obligations. Reflection
constructs a separately measured source trace. -/
theorem head_reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCatalog.Head headers compilation source context)
        values source context reasonAt certificate) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered head
  cases head with
  | primitive head =>
    exact RecursiveNamedExpressionCompositionsBounds.Head.reflects_at functions program evidence
      entry_transport budget size within children head
  | constructor receipt form accepted sequence =>
    exact RecursiveNamedDataExpressionHeadBounds.reflects_at (calls := RecursiveNamedCatalog.Head headers compilation source context) functions extension faithful functionLeaves functionTypes
      program evidence missing entry_transport budget size within children
      ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩
  | member metadata baseMetadata form layout certified =>
    exact RecursiveNamedDataExpressionHeadBounds.reflects_at (calls := RecursiveNamedCatalog.Head headers compilation source context) functions extension faithful functionLeaves functionTypes
      program evidence missing entry_transport budget size within children
      ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩
  | index header found form sourceType first second =>
    exact RecursiveNamedDataExpressionHeadBounds.reflects_at (calls := RecursiveNamedCatalog.Head headers compilation source context) functions extension faithful functionLeaves functionTypes
      program evidence missing entry_transport budget size within children
      ⟨.index header found form sourceType first second, .index header found form sourceType first second⟩
  | builtin head =>
    exact RecursiveNamedBuiltinHeadBounds.Head.reflects_at functions functionLeaves program evidence
      entry_transport budget size within children head
  | call head =>
    exact RecursiveNamedExpressionHeadBounds.reflects_at functions budget size within
      (fun child smaller => children child (Nat.le_of_lt smaller)) bodies head

include extension faithful functionLeaves functionTypes valid unique owners uninitialized missing in
/-- Structural induction closes every expression child of the same Tree. The
remaining catalog-body Below family is the explicit mutual-induction boundary. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head headers compilation source context)
        fuel values source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered tree
  induction tree generalizing size with
  | fragment child =>
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed _
        (CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
          program evidence valid unique uninitialized missing)) size child
  | @node id lowered entries head children ih =>
    have meaning : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (CompatibleExpressionCalls.Entries scope entries) faults
        (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
      intro child childWithin current expression code certified
      obtain ⟨rfl, member⟩ := certified
      exact ih expression code member child childWithin
    intro root found
    exact head_preserves_at functions extension faithful functionLeaves functionTypes evidence unique owners missing
      budget size within meaning bodies head found

include extension faithful functionLeaves functionTypes valid uninitialized missing in
/-- Reflection uses the same structural Tree, with original native bounds and
independent source costs. No source body trace is an input. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head headers compilation source context)
        fuel values source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered tree
  induction tree generalizing size with
  | fragment child =>
    exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed _
        (CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
          program evidence valid uninitialized missing)) size child
  | @node id lowered entries head children ih =>
    have meaning : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (CompatibleExpressionCalls.Entries scope entries) faults
        (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
      intro child childWithin current expression code certified
      obtain ⟨rfl, member⟩ := certified
      exact ih expression code member child childWithin
    intro root found
    exact head_reflects_at functions extension faithful functionLeaves functionTypes evidence missing
      budget size within meaning bodies head found

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds
