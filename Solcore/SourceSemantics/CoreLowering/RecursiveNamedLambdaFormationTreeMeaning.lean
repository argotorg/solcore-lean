import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionNativeTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds

/-! Lambda formation belongs to the existing expression tree. The same static
code retains its complete builtin body receipt. Actual named-call output supplies
aligned callee state; neither a native type nor an arbitrary BodyState supplies
source history. Indirect lambda application remains a separate boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationTreeMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedLambdaFormationHeads

variable {values : SourceCoreCompatibleValues.Context}
  {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program} {locations : Locations}
  {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

abbrev Calls (authenticated : Bool) := Head (registry := registry) (faults := faults) caller context evidence
  (RecursiveNamedCallEvidenceHeads.Calls (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (if authenticated then some evidence else none) headers
    (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source context)

abbrev Expressions (authenticated : Bool) :=
  RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor (Calls (caller := caller) (headers := headers)
    (context := context) (evidence := evidence) (registry := registry) (faults := faults) authenticated)
    fuel values caller.function.source context solved reasonAt

local notation "P" => RecursiveNamedLambdaFormationEntries.protectedEntry
  (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1

variable (profile : values.checked.catalog.callableContracts = true)
local notation "F" => CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile

/-- Local scopes are shared exactly; only the used administrative prefix is
required to agree. An arbitrary unused administrative suffix remains present. -/
theorem agrees_scope (leading : Core.Context) {source target : Core.Context}
    (same : NativeExpressionContextSupport.Agrees source.length source target) :
    NativeExpressionContextSupport.Agrees (leading ++ source).length (leading ++ source) (leading ++ target) := by
  induction leading with
  | nil => exact same
  | cons head tail ih => simpa only [List.cons_append, List.length_cons] using ih.lift head

theorem projected (authenticated : Bool)
    (alignment : RecursiveNamedLambdaFormationEntries.FormationHeader
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
      (CallableIndexedNamedGeneration.context indexed caller.named) 0)
    {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (head : Calls (caller := caller) (headers := headers) (context := context) (evidence := evidence)
      (registry := registry) (faults := faults) authenticated children scope id lowered)
    (found : caller.function.source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases head with
  | lambda head => exact head.projected alignment found
  | existing head =>
    cases authenticated with
    | false =>
      exact RecursiveNamedCallEvidenceHeads.projected (evidence := []) (.ordinary head) found
    | true =>
      exact RecursiveNamedCallEvidenceHeads.projected head found

theorem native (authenticated : Bool)
    {administrative : Core.Context}
    (slots : RecursiveNamedExpressionNativeTyping.Slots (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers
      (CallableIndexedNamedGeneration.context indexed caller.named) administrative)
    (same : NativeExpressionContextSupport.Agrees (nativePrefix caller).length (nativePrefix caller) administrative)
    {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Calls (caller := caller) (headers := headers) (context := context) (evidence := evidence)
      (registry := registry) (faults := faults) authenticated children scope id lowered)
    (childrenTyped : ∀ child code, children scope child code →
      CompatibleExpressionScalarNativeTyping.NativeTyping indexed.layouts.definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) :
    CompatibleExpressionScalarNativeTyping.NativeTyping indexed.layouts.definitions
      (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  cases head with
  | lambda head => exact head.native administrative (agrees_scope _ same)
  | existing head =>
    cases authenticated with
    | false =>
      exact RecursiveNamedCallEvidenceHeads.native_at (evidence := evidence) (CallableIndexedAmbient.ambientDefinitions indexed).basePrefix slots (.ordinary head) childrenTyped
    | true =>
      exact RecursiveNamedCallEvidenceHeads.native_at (evidence := evidence) (CallableIndexedAmbient.ambientDefinitions indexed).basePrefix slots head childrenTyped

section Compiler
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates

def lambdaForm : ExpressionForm → Prop
  | .lambda _ _ _ => True
  | _ => False

/-- The actual lambda compiler output retains its Code and complete static Body.
Every other form and every ordered child uses the same sole compiler recursion. -/
theorem of_functions (authenticated : Bool)
    (alignment : RecursiveNamedLambdaFormationEntries.FormationHeader
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
      (CallableIndexedNamedGeneration.context indexed caller.named) 0)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {admitted : ExpressionId → Prop}
    (admission : AdmissionFor lambdaForm caller.function.source admitted) (coverage : ReachedCoverage headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers context)
    (emptyEvidence : SelectedEmptyEvidence (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → caller.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered (CallableIndexedNamedGeneration.context indexed caller.named).plan instantiation)
    (unique : NodeOccurrencesUnique caller.function.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations caller.function.source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context (CompatibleExpressionBuiltins.Syntax caller.function.source))
    (selectedValid : SelectedDeclarationLaw (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source context admitted)
    (policyFor : PolicyForWith (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (headers := headers) (if authenticated then some evidence else none) policy (CallableIndexedNamedGeneration.context indexed caller.named) readFuel values caller.function.source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callableProfile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax caller.function.source id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (lambdas : ∀ fuel id node lowered, admitted id → caller.function.source.lookupExpression? id = some node →
      lambdaForm node.form → ExpressionHasType caller.function.source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
        (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered →
      Nonempty (Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered))
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : caller.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType caller.function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered) :
    Expressions (caller := caller) (headers := headers) (context := context) (evidence := evidence)
      (registry := registry) (faults := faults) (fuel := readFuel)
      (solved := (CallableIndexedNamedGeneration.context indexed caller.named).solvedRequirements) (reasonAt := reasonAt)
      authenticated scope id lowered := by
  apply tree_of_functions_at_runtime_with_calls (if authenticated then some evidence else none)
    (Calls (caller := caller) (headers := headers) (context := context) (evidence := evidence)
      (registry := registry) (faults := faults) authenticated)
    (fun head => .existing head) (fun {_ _ _ _ _} head found => projected authenticated alignment head found)
    lambdaForm admission coverage sourceTypes emptyEvidence order unique declarations signatures
    constructorValid fragmentValid selectedValid policyFor native active callableProfile fragmentCoercions coercions
    (fun fuel id node lowered allowed found form typed accepted => by
      obtain ⟨head⟩ := lambdas fuel id node lowered allowed found form typed accepted
      exact .lambda head) allowed found typed accepted
end Compiler

section Meaning
variable (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (alignments : ∀ header, header ∈ headers → RecursiveNamedLambdaFormationEntries.FormationHeader
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed header
    (CallableIndexedNamedGeneration.context indexed header.named) 0)
  (callerAligned : RecursiveNamedLambdaFormationEntries.FormationHeader
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
    (CallableIndexedNamedGeneration.context indexed caller.named) 0)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (unique : NodeOccurrencesUnique caller.function.source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include owners complete alignments callerAligned unique in
theorem call_preserves_at (authenticated : Bool) (idsUnique : RequirementIdsUnique context)
    {children : GenericExpressionMeaning.Certificate} (budget size : Nat) (within : size ≤ budget)
    (childrenMeaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry F)
        program context evidence caller.function.source children faults P))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := 0) F registry header faults
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry F)
      program context evidence caller.function.source
      (Calls (caller := caller) (headers := headers) (context := context) (evidence := evidence)
        (registry := registry) (faults := faults) authenticated children) faults P := by
  intro scope id lowered head
  cases head with
  | lambda head => exact RecursiveNamedLambdaFormationHeads.preserves_at profile complete callerAligned size unique ⟨head⟩
  | existing head =>
    have forget := fun {scope mapping world heap store canonical} (entry : P scope mapping world heap store canonical) =>
      RecursiveNamedLambdaFormationEntries.catalog entry
    have authorized : ∀ header, header ∈ headers → BodyAuthorization
        (headers := headers) (locations := locations) (capturePrefix := 0) F registry header
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry) := by
      intro header member
      exact RecursiveNamedLambdaFormationEntries.authorize F registry (alignments header member)
    intro node found
    cases authenticated with
    | false =>
      exact RecursiveNamedExpressionHeadBounds.preserves_at_for F P RecursiveNamedLambdaFormationEntries.transport forget
        _ authorized budget size within unique owners childrenMeaning bodies head found
    | true =>
      exact RecursiveNamedCallEvidenceHeads.preserves_at_for F P RecursiveNamedLambdaFormationEntries.transport forget
        _ authorized budget size within idsUnique unique owners childrenMeaning bodies head found

include complete alignments callerAligned in
theorem call_reflects_at (authenticated : Bool)
    {children : GenericExpressionMeaning.Certificate} (budget size : Nat) (within : size ≤ budget)
    (childrenMeaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry F)
        program context evidence caller.function.source children faults P))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := 0) F registry header faults
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry F)
      program context evidence caller.function.source
      (Calls (caller := caller) (headers := headers) (context := context) (evidence := evidence)
        (registry := registry) (faults := faults) authenticated children) faults P := by
  intro scope id lowered head
  cases head with
  | lambda head => exact RecursiveNamedLambdaFormationHeads.reflects_at profile complete callerAligned size ⟨head⟩
  | existing head =>
    have forget := fun {scope mapping world heap store canonical} (entry : P scope mapping world heap store canonical) =>
      RecursiveNamedLambdaFormationEntries.catalog entry
    have authorized : ∀ header, header ∈ headers → BodyAuthorization
        (headers := headers) (locations := locations) (capturePrefix := 0) F registry header
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry) := by
      intro header member
      exact RecursiveNamedLambdaFormationEntries.authorize F registry (alignments header member)
    intro node found
    cases authenticated with
    | false =>
      exact RecursiveNamedExpressionHeadBounds.reflects_at_for F P RecursiveNamedLambdaFormationEntries.transport forget
        _ authorized budget size within childrenMeaning bodies head found
    | true =>
      exact RecursiveNamedCallEvidenceHeads.reflects_at_for F P RecursiveNamedLambdaFormationEntries.transport forget
        _ authorized budget size within childrenMeaning bodies head found

include complete alignments callerAligned extension unique owners uninitialized missing in
theorem preserves_at (authenticated : Bool)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := 0) F registry header faults
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry F)
      program context evidence caller.function.source
      (Expressions (caller := caller) (headers := headers) (context := context) (evidence := evidence)
        (registry := registry) (faults := faults) (fuel := fuel) (solved := solved) (reasonAt := reasonAt) authenticated) faults P := by
  apply RecursiveNamedExpressionTreeBounds.preserves_at_with_literals_with_for F extension
    (CallableIndexedLambdaValues.identity_faithful indexed) (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile)
    (CallableIndexedLambdaRuntimeValues.runtime_views indexed program registry faults profile) evidence unique uninitialized missing
    _ P (CompatibleExpressionLiteralRuntime.preserves F program context evidence sameLedger runtime unique faults)
    budget size within
  intro certificate child childWithin children
  apply RecursiveNamedExpressionTreeBounds.head_preserves_at_with_calls F extension
    (CallableIndexedLambdaValues.identity_faithful indexed) (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile)
    (CallableIndexedLambdaRuntimeValues.runtime_views indexed program registry faults profile) evidence unique missing
    P RecursiveNamedLambdaFormationEntries.transport _ budget child childWithin children
  exact call_preserves_at profile complete alignments callerAligned unique owners authenticated runtime.idsUnique budget child childWithin
    (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies

include complete alignments callerAligned extension uninitialized missing in
theorem reflects_at (authenticated : Bool)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := 0) F registry header faults
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry F)
      program context evidence caller.function.source
      (Expressions (caller := caller) (headers := headers) (context := context) (evidence := evidence)
        (registry := registry) (faults := faults) (fuel := fuel) (solved := solved) (reasonAt := reasonAt) authenticated) faults P := by
  apply RecursiveNamedExpressionTreeBounds.reflects_at_with_literals_with_for F extension
    (CallableIndexedLambdaValues.identity_faithful indexed) (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile)
    (CallableIndexedLambdaRuntimeValues.runtime_views indexed program registry faults profile) evidence uninitialized missing
    _ P (CompatibleExpressionLiteralRuntime.reflects F program context evidence sameLedger runtime caller.function.source faults)
    budget size within
  intro certificate child childWithin children
  apply RecursiveNamedExpressionTreeBounds.head_reflects_at_with_calls F extension
    (CallableIndexedLambdaValues.identity_faithful indexed) (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile)
    (CallableIndexedLambdaRuntimeValues.runtime_views indexed program registry faults profile) evidence missing
    P RecursiveNamedLambdaFormationEntries.transport _ budget child childWithin children
  exact call_reflects_at profile complete alignments callerAligned authenticated budget child childWithin
    (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationTreeMeaning
