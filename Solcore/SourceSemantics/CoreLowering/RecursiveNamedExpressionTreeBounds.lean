import Solcore.SourceSemantics.CoreLowering.RecursiveNamedTupleHeadBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionHeadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinHeadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionHeadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallEvidenceHeads

/-! The existing recursive expression Tree closes its child obligations within
one inclusive budget. All catalog body obligations remain explicit below that
budget for the subsequent mutual induction. Static syntax and receipts do not
contain body execution. Source and native costs are independent. The
authenticated family fixes the same caller evidence for every child; only its
source call inversion additionally consumes requirement ID uniqueness. -/
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
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificate : GenericExpressionMeaning.Certificate}

include extension faithful functionLeaves functionTypes unique missing in
/-- Every existing head uses child obligations at the same inclusive budget;
only an actual named callee consumes the strictly smaller body contract. -/
theorem head_preserves_at_with_calls (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P)
    (callMeaning : RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
      (calls certificate) faults P) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (calls)
        values source context reasonAt certificate) faults
      P := by
  intro scope id lowered head
  cases head with
  | primitive head =>
    exact RecursiveNamedExpressionCompositionsBounds.Head.preserves_at functions program evidence
      transport budget size within unique children head
  | constructor receipt form accepted sequence =>
    exact RecursiveNamedDataExpressionHeadBounds.preserves_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence unique missing transport budget size within children
      ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩
  | member metadata baseMetadata form layout certified =>
    exact RecursiveNamedDataExpressionHeadBounds.preserves_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence unique missing transport budget size within children
      ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩
  | index header found form sourceType first second =>
    exact RecursiveNamedDataExpressionHeadBounds.preserves_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence unique missing transport budget size within children
      ⟨.index header found form sourceType first second, .index header found form sourceType first second⟩
  | builtin head =>
    exact RecursiveNamedBuiltinHeadBounds.Head.preserves_at functions functionLeaves program evidence unique
      transport budget size within children head
  | tuple receipt sequence =>
    exact RecursiveNamedTupleHeadBounds.preserves_at functions program evidence transport budget size within unique children
      ⟨_, _, _, _, rfl, receipt, sequence⟩
  | call head => exact callMeaning head

include extension faithful functionLeaves functionTypes unique owners missing in
/-- Every existing head uses child obligations at the same inclusive budget;
only an actual named callee consumes the strictly smaller body contract. -/
theorem head_preserves_at_with_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
      protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)
    (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → BodyAuthorization (headers := headers) (locations := locations)
      (capturePrefix := capturePrefix) functions registry header (conditions header))
    (authenticated : Bool)
    (idsUnique : authenticated = true → RequirementIdsUnique context)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        values source context reasonAt certificate) faults
      P :=
  head_preserves_at_with_calls functions extension faithful functionLeaves functionTypes evidence unique missing P transport
    (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context) budget size within children
    (by
      intro scope id lowered head
      cases authenticated with
      | false =>
        exact RecursiveNamedExpressionHeadBounds.preserves_at_for functions P transport catalog conditions authorized budget size within unique owners
          (fun child smaller => children child (Nat.le_of_lt smaller)) bodies head
      | true =>
        exact RecursiveNamedCallEvidenceHeads.preserves_at_for functions P transport catalog conditions authorized budget size within (idsUnique rfl) unique owners
          (fun child smaller => children child (Nat.le_of_lt smaller)) bodies head)

include extension faithful functionLeaves functionTypes unique owners missing in
theorem head_preserves_at_with (authenticated : Bool)
    (idsUnique : authenticated = true → RequirementIdsUnique context)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        values source context reasonAt certificate) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  head_preserves_at_with_for functions extension faithful functionLeaves functionTypes evidence unique owners missing
    _ entry_transport (fun entry => entry) (fun _ => fun {_ _ _ _ _ _ _ _ _ _ _ _} _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial) authenticated idsUnique budget size within children
    (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodies header member child smaller entry trace)

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
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  head_preserves_at_with functions extension faithful functionLeaves functionTypes evidence unique owners missing false (fun impossible => Bool.noConfusion impossible) budget size within children bodies

include extension faithful functionLeaves functionTypes missing in
/-- Original native children select their own pointwise obligations. Reflection
constructs a separately measured source trace. -/
theorem head_reflects_at_with_calls (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P)
    (callMeaning : RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
      (calls certificate) faults P) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (calls)
        values source context reasonAt certificate) faults
      P := by
  intro scope id lowered head
  cases head with
  | primitive head =>
    exact RecursiveNamedExpressionCompositionsBounds.Head.reflects_at functions program evidence
      transport budget size within children head
  | constructor receipt form accepted sequence =>
    exact RecursiveNamedDataExpressionHeadBounds.reflects_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence missing transport budget size within children
      ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩
  | member metadata baseMetadata form layout certified =>
    exact RecursiveNamedDataExpressionHeadBounds.reflects_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence missing transport budget size within children
      ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩
  | index header found form sourceType first second =>
    exact RecursiveNamedDataExpressionHeadBounds.reflects_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence missing transport budget size within children
      ⟨.index header found form sourceType first second, .index header found form sourceType first second⟩
  | builtin head =>
    exact RecursiveNamedBuiltinHeadBounds.Head.reflects_at functions functionLeaves program evidence
      transport budget size within children head
  | tuple receipt sequence =>
    exact RecursiveNamedTupleHeadBounds.reflects_at functions program evidence transport budget size within children
      ⟨_, _, _, _, rfl, receipt, sequence⟩
  | call head => exact callMeaning head

include extension faithful functionLeaves functionTypes missing in
/-- Original native children select their own pointwise obligations. Reflection
constructs a separately measured source trace. -/
theorem head_reflects_at_with_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
      protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)
    (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → BodyAuthorization (headers := headers) (locations := locations)
      (capturePrefix := capturePrefix) functions registry header (conditions header))
    (authenticated : Bool)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        values source context reasonAt certificate) faults
      P :=
  head_reflects_at_with_calls functions extension faithful functionLeaves functionTypes evidence missing P transport
    (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context) budget size within children
    (by
      intro scope id lowered head
      cases authenticated with
      | false =>
        exact RecursiveNamedExpressionHeadBounds.reflects_at_for functions P transport catalog conditions authorized budget size within
          (fun child smaller => children child (Nat.le_of_lt smaller)) bodies head
      | true =>
        exact RecursiveNamedCallEvidenceHeads.reflects_at_for functions P transport catalog conditions authorized budget size within
          (fun child smaller => children child (Nat.le_of_lt smaller)) bodies head)

include extension faithful functionLeaves functionTypes missing in
theorem head_reflects_at_with (authenticated : Bool)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        values source context reasonAt certificate) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  head_reflects_at_with_for functions extension faithful functionLeaves functionTypes evidence missing
    _ entry_transport (fun entry => entry) (fun _ => fun {_ _ _ _ _ _ _ _ _ _ _ _} _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial) authenticated budget size within children
    (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodies header member child smaller entry trace)

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
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  head_reflects_at_with functions extension faithful functionLeaves functionTypes evidence missing false budget size within children bodies

include extension faithful functionLeaves functionTypes unique uninitialized missing in
/-- Structural induction closes every expression child of the same Tree. The
remaining catalog-body Below family is the explicit mutual-induction boundary. -/
theorem preserves_at_with_literals_with_for (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (P : ProtectedExpressionMeaning.Entry)
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (heads : ∀ certificate child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → RecursiveNamedBoundedContracts.PreservesAt smaller
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P) →
      RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (CompatibleExpressionCalls.Head calls values source context reasonAt certificate) faults P) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      P := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites generalizing size with
  | fragment child childSites =>
    intro root found
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed P
        (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful functionLeaves functionTypes
          program evidence unique uninitialized missing literalMeaning)) size ⟨child, childSites⟩ found
  | @node id lowered entries head children childSites ih =>
    have meaning : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (CompatibleExpressionCalls.Entries scope entries) faults
        P := by
      intro child childWithin current expression code certified
      obtain ⟨rfl, member⟩ := certified
      exact ih expression code member child childWithin
    intro root found
    exact heads _ size within meaning head found

include extension faithful functionLeaves functionTypes unique owners uninitialized missing in
theorem preserves_at_with_literals_with (authenticated : Bool)
    (idsUnique : authenticated = true → RequirementIdsUnique context)
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  preserves_at_with_literals_with_for functions extension faithful functionLeaves functionTypes evidence unique uninitialized missing
    _ _ literalMeaning budget size within
    (fun _ child childWithin children => head_preserves_at_with functions extension faithful functionLeaves functionTypes evidence unique owners missing authenticated idsUnique budget child childWithin children bodies)

include extension faithful functionLeaves functionTypes unique owners uninitialized missing in
/-- Structural induction closes every expression child of the same Tree. The
remaining catalog-body Below family is the explicit mutual-induction boundary. -/
theorem preserves_at_with_literals
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCatalog.Head headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  preserves_at_with_literals_with functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing false (fun impossible => Bool.noConfusion impossible) literalMeaning budget size within bodies

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
  exact preserves_at_with_literals functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes unique owners uninitialized missing in
/-- Structural induction closes every expression child of the same Tree. The
remaining catalog-body Below family is the explicit mutual-induction boundary. -/
theorem preserves_at_runtime_with (authenticated : Bool)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  preserves_at_with_literals_with functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing authenticated (fun _ => runtime.idsUnique)
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtime unique faults) budget size within bodies

include extension faithful functionLeaves functionTypes unique owners uninitialized missing in
/-- Structural induction closes every expression child of the same Tree. The
remaining catalog-body Below family is the explicit mutual-induction boundary. -/
theorem preserves_at_runtime
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCatalog.Head headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  preserves_at_runtime_with functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing false sameLedger runtime budget size within bodies

include extension faithful functionLeaves functionTypes uninitialized missing in
/-- Reflection uses the same structural Tree, with original native bounds and
independent source costs. No source body trace is an input. -/
theorem reflects_at_with_literals_with_for (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (P : ProtectedExpressionMeaning.Entry)
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (heads : ∀ certificate child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt smaller
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P) →
      RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (CompatibleExpressionCalls.Head calls values source context reasonAt certificate) faults P) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      P := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites generalizing size with
  | fragment child childSites =>
    intro root found
    exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed P
        (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful functionLeaves functionTypes
          program evidence uninitialized missing literalMeaning)) size ⟨child, childSites⟩ found
  | @node id lowered entries head children childSites ih =>
    have meaning : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (CompatibleExpressionCalls.Entries scope entries) faults
        P := by
      intro child childWithin current expression code certified
      obtain ⟨rfl, member⟩ := certified
      exact ih expression code member child childWithin
    intro root found
    exact heads _ size within meaning head found

include extension faithful functionLeaves functionTypes uninitialized missing in
theorem reflects_at_with_literals_with (authenticated : Bool)
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  reflects_at_with_literals_with_for functions extension faithful functionLeaves functionTypes evidence uninitialized missing
    _ _ literalMeaning budget size within
    (fun _ child childWithin children => head_reflects_at_with functions extension faithful functionLeaves functionTypes evidence missing authenticated budget child childWithin children bodies)

include extension faithful functionLeaves functionTypes uninitialized missing in
/-- Reflection uses the same structural Tree, with original native bounds and
independent source costs. No source body trace is an input. -/
theorem reflects_at_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCatalog.Head headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  reflects_at_with_literals_with functions extension faithful functionLeaves functionTypes evidence uninitialized missing false literalMeaning budget size within bodies

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
  exact reflects_at_with_literals functions extension faithful functionLeaves functionTypes evidence uninitialized missing
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes uninitialized missing in
/-- Reflection uses the same structural Tree, with original native bounds and
independent source costs. No source body trace is an input. -/
theorem reflects_at_runtime_with (authenticated : Bool)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  reflects_at_with_literals_with functions extension faithful functionLeaves functionTypes evidence uninitialized missing authenticated
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtime source faults) budget size within bodies

include extension faithful functionLeaves functionTypes uninitialized missing in
/-- Reflection uses the same structural Tree, with original native bounds and
independent source costs. No source body trace is an input. -/
theorem reflects_at_runtime
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCatalog.Head headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  reflects_at_runtime_with functions extension faithful functionLeaves functionTypes evidence uninitialized missing false sameLedger runtime budget size within bodies

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds
