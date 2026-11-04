import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSamePolicyCompilerLeafReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedNamedFamilyClosure
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryMembers
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaProtocolContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaJointStaticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaEntries

/-!
# Prepared callables: mixed heads

Compiler and runtime heads of mixed bodies, branching catalog sites and canonical flow bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerHeads
/-! A finite static call head retains the genuine named, prepared lambda or
indirect compiler receipt at one root policy and its actual child positions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles

def extraForm : ExpressionForm → Prop
  | .lambda _ _ _ | .call _ _ (.indirect _) => True
  | _ => False

def extraChildren : ExpressionForm → List ExpressionId
  | .call callee ids (.indirect _) => callee :: ids
  | _ => []

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
  {reasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel (source caller.named) scope rootId reasonAt rootLowered)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
    (source caller.named) sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) certificates)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))

/-- Prepared alternatives keep their literal factory and the supplied compiler
certificate. The named alternative retains its original dictionary variants. -/
inductive Head
    (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
      rootFuel (source caller.named) scope rootId reasonAt rootLowered)
    (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
      (source caller.named) sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) certificates)
    (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | named {childScope id lowered}
      (head : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
        (context compiled.indexed caller.named) (source caller.named) sourceContext children childScope id lowered) :
      Head root factory headers children childScope id lowered
  | prepared_lambda {childFuel id lowered node parameters result statements reported}
      (found : (source caller.named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed caller.named) (source caller.named) scope id node parameters result statements reported reasonAt lowered)
      (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
        sourceContext evidence scope id lowered)
      (samePolicy : receipt.formation.produced.site.code.policy = root.selected.policy)
      (sameBody : receipt.formation.produced.site.code.lowerBody = root.selected.lowerBody)
      (sameFuel : receipt.formation.produced.site.code.fuel = childFuel)
      (sameView : receipt.formation.produced.site.code.view = source caller.named)
      (sameReason : receipt.formation.produced.site.code.reasonAt = reasonAt)
      (sameCertificate : HEq receipt.formation.produced.site.code.receipt certificate)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type) :
      Head root factory headers children scope id lowered
  | prepared_indirect {childFuel id lowered node callee ids metadata}
      (found : (source caller.named).lookupExpression? id = some node)
      (form : node.form = .call callee ids (.indirect metadata))
      (receipt : CallableIndexedOwnedIndirectCompilerReceipts.Receipt compiled.indexed.ancestry.graph.inputs.callable [] factory
        (policy := root.selected.policy) (body := root.selected.lowerBody) (fuel := childFuel)
        (id := id) (callee := callee) (ids := ids) (metadata := metadata) (reasonAt := reasonAt) (lowered := lowered))
      (ordered : ∀ child code, (child, code) ∈ receipt.compiler.entries → children scope child code) :
      Head root factory headers children scope id lowered

/-- Existing genuine named heads enter this finite family without alteration. -/
theorem include_named {children childScope id lowered}
    (head : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
      (context compiled.indexed caller.named) (source caller.named) sourceContext children childScope id lowered) :
    Head root factory headers children childScope id lowered := .named head

/-- Projection follows the same parent metadata and emitted annotation. -/
theorem projected {children childScope id lowered node}
    (head : Head root factory headers children childScope id lowered)
    (found : (source caller.named).lookupExpression? id = some node) :
    compiled.compatible.checked.catalog.project node.type = .ok lowered.type := by
  cases head with
  | named actual => exact RecursiveNamedCallEvidenceHeads.projected actual found
  | prepared_lambda actualFound _ _ _ _ _ _ _ _ _ metadata =>
    have same := Option.some.inj (actualFound.symm.trans found)
    exact same ▸ metadata.projected
  | prepared_indirect _ _ receipt _ =>
    have same := Option.some.inj (receipt.compiler.found.symm.trans found)
    have emitted := congrArg SourceCoreBasic.LoweredExpr.type receipt.compiler.output
    simpa only [same, emitted] using receipt.parentMetadata.projected

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedRuntimeHeads
/-! Finite runtime branches retain their actual named parameter receipt or
prepared ordinary index. Strict family members supply the existing body
continuations internally. Indirect global/prior classification and qualified
value storage remain separate from these constructor-specific adapters. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedRuntimeHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open RecursiveNamedBoundedContracts (Below)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

section NamedMembers
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (owner : OwnedKey keys)

/-- A genuine strict named family member gives the Source continuation at
that exact allocated parameter receipt, including its original agreement. -/
theorem named_source_bodies (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer
      (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
        (headers := headers) (registry := registry) (faults := faults) functions owner i))
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) (member : header ∈ headers) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
  intro initial argumentsPool arguments receipt _agreement child strict
  exact (ih ⟨header, member, initial, argumentsPool, arguments, receipt⟩ child
    (Nat.lt_of_lt_of_le strict within)).1

/-- Native members keep their measured parameter prefix and restoration
receipt, while selecting the independent native conjunct at the true child. -/
theorem named_native_bodies (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer
      (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
        (headers := headers) (registry := registry) (faults := faults) functions owner i))
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) (member : header ∈ headers) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
  intro initial argumentsPool arguments receipt prefixSize bodyStore value finalStore
    _prefix _prefixStrict _restored child strict
  exact (ih ⟨header, member, initial, argumentsPool, arguments, receipt⟩ child
    (Nat.lt_of_lt_of_le strict within)).2

end NamedMembers

section NamedHeads
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : OwnedKey keys) (caller : Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source caller.named))
  (covers : evidence.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source caller.named))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  {certificate : GenericExpressionMeaning.Certificate}

include wellFormed runtime covers unique owners idsUnique sameLayouts in
/-- The mixed named constructor uses actual ordered child expressions and
body members at their genuine parameter input, without a completed body law. -/
private theorem named_preserves (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (children : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named) certificate faults))
    (ih : ∀ i, Below outer
      (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family (headers := headers)
        (registry := registry) (faults := faults)
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named)
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named)
        (CallableIndexedNamedGeneration.source caller.named) context evidence certificate) faults size := by
  exact CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.preserves_head
    (compilation := CallableIndexedNamedGeneration.context compiled.indexed caller.named) (certificate := certificate)
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    owner (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
    evidence wellFormed runtime covers unique owners idsUnique sameLayouts budget size headWithin children
    (named_source_bodies _ owner outer budget within ih)

include wellFormed runtime covers unique sameLayouts in
/-- The native named constructor preserves its own argument/body grades and
reconstructs the independent Source outcome at the real restored caller. -/
private theorem named_reflects (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (children : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named) certificate faults))
    (ih : ∀ i, Below outer
      (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family (headers := headers)
        (registry := registry) (faults := faults)
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named)
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named)
        (CallableIndexedNamedGeneration.source caller.named) context evidence certificate) faults size := by
  exact CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.reflects_head
    (compilation := CallableIndexedNamedGeneration.context compiled.indexed caller.named) (certificate := certificate)
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    owner (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
    evidence wellFormed runtime covers unique sameLayouts budget size headWithin children
    (named_native_bodies _ owner outer budget within ih)

end NamedHeads

section FormationHeads
variable (caller : Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  (owner : OwnedKey keys) (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source caller.named)) (covers : evidence.Covers context)

include complete globals slots prefixZero wellFormed runtime covers in
/-- A literal mixed lambda Formation runs once at identity inclusion of the
full prepared model. Its existing result does not promise a stored sidecar. -/
private theorem formation_preserves (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named)
      (CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.Certificate caller context evidence) faults size := by
  exact CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.preserves_head_at caller context evidence owner profile
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    (fun related => related) complete globals slots prefixZero wellFormed runtime covers rfl size

include complete globals slots prefixZero wellFormed runtime covers in
/-- Native formation keeps the original caller packet and an independent
Source grade; all prior model alternatives remain unchanged. -/
private theorem formation_reflects (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named)
      (CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.Certificate caller context evidence) faults size := by
  exact CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.reflects_head_at caller context evidence owner profile
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    (fun related => related) complete globals slots prefixZero wellFormed runtime covers rfl size

end FormationHeads

/-- Exact selection keeps the actual prior alternative or the known formed
constructor. This finite split never upgrades an opaque prior relation. -/
theorem selection_cases {mapping : LocationMap} {world : StoreTyping}
    {raw : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (selected : CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selection
      headers keys registry faults mapping world raw source native type) :
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world raw source native type ∨
      CallableIndexedOwnedPreparedOrdinaryFormedMembers.FormedAt headers keys registry faults mapping world raw source native type := by
  cases selected with
  | prior original => exact Or.inl original
  | @prepared_ordinary function scope actual owner captured code history support origin prefixContext globals referenceIndex typed prepared =>
    right
    let i : OrdinaryIndex compiled := {
      function := function, mapping := mapping, world := world, scope := scope, capturedActual := actual
      captured := captured, code := code, support := support, prepared := prepared }
    exact .ordinary i owner history origin prefixContext globals referenceIndex typed

section Applications
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads

variable
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)


variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

variable {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource tree unique parent in
/-- The actual indirect compiler branch produces one callee post. Its global,
prior and classifier alternatives remain in the original conditional prefix. -/
theorem indirect_reflects_prefix (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (CallableIndexedOwnedStoredIndirectNativePrefix.ForModel.FaultPrefix
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial budget value finalStore ∨
      CallableIndexedOwnedPreparedStoredIndirectParentPrefix.ValuePrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
        (sourceTypes := sourceTypes) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) := by
  exact CallableIndexedOwnedPreparedStoredIndirectParentPrefix.reflects_parent
    (bridge := bridge) (profile := profile) (compiler := compiler) (prepared := prepared)
    (certified := certified) (found := found) (sourceTyped := sourceTyped) (parentTyped := parentTyped)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed)
    (initial := initial) (admitted := admitted) (caller := caller) (sidecarSource := sidecarSource)
    (tree := tree) (unique := unique) (parent := parent) budget children completed within

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
    compiler.original dispatch.row)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {lambdaScope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captured : CallableIndexedLambdaValues.Captures compiled.indexed calleeMap calleeWorld lambdaScope function.captured capturedActual)
  (code : CallableIndexedLambdaValues.Code compiled.indexed function lambdaScope captured.administrative)
  (history : CallableIndexedLambdaValues.History code)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (seed : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 lambdaScope captured.canonical owner.key.frameLocation)
  (referenceIndex : code.referenceIndex = lambdaScope.length + 1 + compiled.indexed.base.globals.length)
  (sameNative : calleeNative = CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual)
  (selectedType : RuntimeValueHasType calleeWorld calleeNative
    (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities)
  {table : SourceCoreFaultSites.Table}
  (rebuilt : support.issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep support.issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep support.issued.assignments reason token → faults reason token)
  (interprets : ∀ context, CallableIndexedOwnedTypedLambdaBodyContinuations.Validity
      (program := Program.ofChecked compiled.sourceProgram) captured code context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := support.certificates support.body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory
        support.diagnosticPolicy function.source support.issued.invalidOperand)
      (faults := faults) (registry := registry) support.issued
      (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys)) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) table)

include parentTyped wellFormed runtime covers locals admitted tree unique parent actualFunctionType
  calleeTrace post accepted observed referenceIndex sameNative selectedType seed extension faithful observations
  rebuilt operandIncluded unaryIncluded interprets in
/-- The known selected ordinary index supplies its strict native expression
members. The original whole fourth bind and current caller restore run once. -/
theorem prepared_application_reflects (budget : Nat)
    (outer : Nat) (within : budget ≤ outer)
    (ih : ∀ i, RecursiveNamedCatalogInvocationBounds.Below outer
      (CallableIndexedOwnedPreparedRuntimeFamilyMembers.Family (headers := headers) (keys := keys)
        (registry := registry) (faults := faults)
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) i))
    {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared initial budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared initial budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    CallableIndexedOwnedPreparedStoredIndirectApplication.ResultAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld) (sidecar := sidecar)
      bridge profile compiler prepared initial dispatch budget value finalStore := by
  let i : OrdinaryIndex compiled := {
    function := function, mapping := calleeMap, world := calleeWorld, scope := lambdaScope
    capturedActual := capturedActual, captured := captured, code := code, support := support, prepared := seed }
  exact CallableIndexedOwnedPreparedStoredIndirectApplication.reflects_selected
    (bridge := bridge) (profile := profile) (compiler := compiler) (prepared := prepared)
    (parentTyped := parentTyped) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    (locals := locals) (initial := initial) (admitted := admitted) (tree := tree) (unique := unique)
    (parent := parent) (actualFunctionType := actualFunctionType) (calleeTrace := calleeTrace) (post := post)
    (dispatch := dispatch) (accepted := accepted) (owner := owner)
    (captured := captured) (code := code) (history := history) (support := support) (seed := seed)
    (observed := observed) (referenceIndex := referenceIndex) (sameNative := sameNative) (selectedType := selectedType)
    (extension := extension) (faithful := faithful) (observations := observations) (rebuilt := rebuilt)
    (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (interprets := interprets)
    budget (CallableIndexedOwnedPreparedRuntimeFamilyMembers.reflects_below
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      outer budget within ih i) original step passed

include parentTyped wellFormed runtime covers locals admitted tree unique parent actualFunctionType
  environments agrees typed calleeTrace post accepted observed referenceIndex sameNative selectedType seed
  dispatch selected extension faithful observations rebuilt operandIncluded unaryIncluded interprets in
/-- Only the actual called suffix requests ordinary strict expression members.
An argument fault has no physical count or body-child demand. -/
theorem prepared_selected_preserves (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after)
    (physicalCount : CallableIndexedOwnedPreparedStoredIndirectPreservation.PhysicalArity (context := context) (evidence := evidence) (source := source)
      (environment := environment) suffix)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget)
    (outer : Nat) (within : budget ≤ outer)
    (ih : CallableIndexedOwnedStoredIndirectCallBounds.ForModel.CalledSuffix
        (context := context) (evidence := evidence) (environment := environment) suffix →
      ∀ i, RecursiveNamedCatalogInvocationBounds.Below outer
        (CallableIndexedOwnedPreparedRuntimeFamilyMembers.Family (headers := headers) (keys := keys)
          (registry := registry) (faults := faults)
          (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) i)) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata
        (CallableIndexedOwnedPreparedStoredIndirectApplication.boundaryOutcome outcome) after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults) (context := context)
        bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial outcome after value finalStore finalMap finalWorld := by
  let i : OrdinaryIndex compiled := {
    function := function, mapping := calleeMap, world := calleeWorld, scope := lambdaScope
    capturedActual := capturedActual, captured := captured, code := code, support := support, prepared := seed }
  exact CallableIndexedOwnedPreparedStoredIndirectPreservation.preserves_selected
    (bridge := bridge) (profile := profile) (compiler := compiler) (prepared := prepared)
    (parentTyped := parentTyped) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    (locals := locals) (initial := initial) (admitted := admitted) (tree := tree) (unique := unique)
    (parent := parent) (actualFunctionType := actualFunctionType) (calleeTrace := calleeTrace) (post := post)
    (dispatch := dispatch) (selected := selected) (accepted := accepted) (owner := owner)
    (captured := captured) (code := code) (history := history) (support := support) (seed := seed)
    (observed := observed) (referenceIndex := referenceIndex) (sameNative := sameNative) (selectedType := selectedType)
    (extension := extension) (faithful := faithful) (observations := observations) (rebuilt := rebuilt)
    (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (interprets := interprets)
    (environments := environments) (agrees := agrees) (typed := typed)
    budget children suffix physicalCount argumentsWithin callWithin
    (fun called => CallableIndexedOwnedPreparedRuntimeFamilyMembers.preserves_below
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      outer budget within (ih called) i)

end Applications

/-- This certificate names one actual scope/id/code, so a finite branch
consumer cannot silently apply to a different compiled occurrence. -/
def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate :=
  fun requestedScope requestedId requestedCode =>
    requestedScope = scope ∧ requestedId = id ∧ requestedCode = lowered

section Restrict
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  {bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {size : Nat}

private theorem preserves_point
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size)
    (member : certificate scope id lowered) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source (Point scope id lowered) faults size := by
  intro requestedScope requestedId requestedCode same
  obtain ⟨rfl, rfl, rfl⟩ := same
  exact meaning member

private theorem reflects_point
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source certificate faults size)
    (member : certificate scope id lowered) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source (Point scope id lowered) faults size := by
  intro requestedScope requestedId requestedCode same
  obtain ⟨rfl, rfl, rfl⟩ := same
  exact meaning member
end Restrict

section MixedBranches
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
variable {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
  {reasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel (source caller.named) rootScope rootId reasonAt rootLowered)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
    (source caller.named) context evidence rootScope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) certificates)
  {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- The static mixed Head remains attached to its literal runtime certificate.
This definition does not classify an arbitrary Head or an actual Source value. -/
def At (_head : CallableIndexedOwnedPreparedMixedCompilerHeads.Head root factory headers children scope id lowered) :
    GenericExpressionMeaning.Certificate := Point scope id lowered

variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : OwnedKey keys) (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source caller.named))
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique (source caller.named))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)

include wellFormed runtime covers unique sameLayouts owners idsUnique in
/-- Use the actual mixed named constructor with strict named family members
and ordered admitted children at that same root/caller occurrence. -/
theorem named_branch_preserves
    (named : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) context children scope id lowered)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named)
      (At root factory (CallableIndexedOwnedPreparedMixedCompilerHeads.Head.named named)) faults size := by
  exact preserves_point
    (named_preserves profile owner caller context evidence wellFormed runtime covers unique owners idsUnique sameLayouts
      outer budget size headWithin within arguments ih) named

include wellFormed runtime covers unique sameLayouts in
/-- The actual mixed named native branch keeps the original measured children
and current restored pool, with an independent Source witness. -/
theorem named_branch_reflects
    (named : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) context children scope id lowered)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named)
      (At root factory (CallableIndexedOwnedPreparedMixedCompilerHeads.Head.named named)) faults size := by
  exact reflects_point
    (named_reflects profile owner caller context evidence wellFormed runtime covers unique sameLayouts
      outer budget size headWithin within arguments ih) named

variable
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)

include complete globals slots prefixZero wellFormed runtime covers in
/-- The actual compiled lambda receipt supplies Formation literally. No
qualification is recovered from its broad runtime ResultAt after formation. -/
theorem formation_branch_preserves
    {childFuel : Nat} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId} {reported : Ty}
    (found : (source caller.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named)
      rootScope id node parameters result statements reported reasonAt lowered)
    (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
      context evidence rootScope id lowered)
    (samePolicy : receipt.formation.produced.site.code.policy = root.selected.policy)
    (sameBody : receipt.formation.produced.site.code.lowerBody = root.selected.lowerBody)
    (sameFuel : receipt.formation.produced.site.code.fuel = childFuel)
    (sameView : receipt.formation.produced.site.code.view = source caller.named)
    (sameReason : receipt.formation.produced.site.code.reasonAt = reasonAt)
    (sameCertificate : HEq receipt.formation.produced.site.code.receipt certificate)
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type)
    (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named)
      (At (headers := headers) (children := children) root factory (CallableIndexedOwnedPreparedMixedCompilerHeads.Head.prepared_lambda
        found form certificate receipt samePolicy sameBody sameFuel sameView sameReason sameCertificate metadata)) faults size := by
  exact preserves_point
    (formation_preserves caller context evidence owner profile complete globals slots prefixZero wellFormed runtime covers size)
    ⟨receipt.formation⟩

include complete globals slots prefixZero wellFormed runtime covers in
/-- Native formation consumes the same literal compiled receipt and owning
caller frame at its actual mixed lambda constructor. -/
theorem formation_branch_reflects
    {childFuel : Nat} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId} {reported : Ty}
    (found : (source caller.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named)
      rootScope id node parameters result statements reported reasonAt lowered)
    (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
      context evidence rootScope id lowered)
    (samePolicy : receipt.formation.produced.site.code.policy = root.selected.policy)
    (sameBody : receipt.formation.produced.site.code.lowerBody = root.selected.lowerBody)
    (sameFuel : receipt.formation.produced.site.code.fuel = childFuel)
    (sameView : receipt.formation.produced.site.code.view = source caller.named)
    (sameReason : receipt.formation.produced.site.code.reasonAt = reasonAt)
    (sameCertificate : HEq receipt.formation.produced.site.code.receipt certificate)
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type)
    (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named)
      (At (headers := headers) (children := children) root factory (CallableIndexedOwnedPreparedMixedCompilerHeads.Head.prepared_lambda
        found form certificate receipt samePolicy sameBody sameFuel sameView sameReason sameCertificate metadata)) faults size := by
  exact reflects_point
    (formation_reflects caller context evidence owner profile complete globals slots prefixZero wellFormed runtime covers size)
    ⟨receipt.formation⟩

end MixedBranches

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedRuntimeHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
/-! Bare assignment diagnostics retain their actual fixed fault interpretation.
The original compiler tree and header diagnostic receipts remain paired. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CallableIndexedOwnedPreparedStagedBranchingTree
open GenericImperativeMatch

private theorem empty_steps
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {place : PlaceResolution} {prepared : SourceCoreCompatibleDataPlaces.Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {leaf : TypeSystem.Ty}
    (shape : GenericAssignmentStatements.Shape values source context certificate scope administrative
      definitions place prepared codes leaf) (bare : place.projections = []) : prepared.steps = [] := by
  cases shape with
  | bare _ layout => exact layout.steps
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))

variable {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

/-- A bare target has no projection/default errors; operand errors retain their
actual diagnostic law. -/
private theorem reachable_bare
    {certificate : GenericExpressionMeaning.Certificate} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (empty : head.prepared.steps = [])
    (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid) :
    head.ReachableErrors registry faults := by
  refine ⟨?_, fun nonempty => False.elim (nonempty empty), operands⟩
  intro root resolved reason token count fault
  rw [empty] at fault
  cases fault

theorem assignment_site
    {certificate : GenericExpressionMeaning.Certificate} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs}
    {site : SourceCoreElaboration.ErrorSite} {fuel : Nat}
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs)
    (signatures : context.signatures = values.checked.signatures)
    (retained : head.PreparedAt site fuel (invalidProjection site assignment.target.root)
      (missingDefault site assignment.target.root))
    (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid)
    (registry : SourceCoreRawMetadata.Registry) :
    PreparedBranchingCatalogSites.AssignmentSite invalidProjection missingDefault registry faults head := by
  by_cases bare : assignment.target.projections = []
  · exact .existing (reachable_bare (empty_steps head.shape bare) operands)
  · exact .projected origin signatures bare retained operands

/-- The compiler retains the exact tree and its real catalog interpretation.
Bare routes do not constrain the registry. -/
structure Collected
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (faults : FunctionCalls.FaultRep)
    (layouts : SourceCoreAllocationLayouts.Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (position : GenericImperativeMatch.Position) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop where
  tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative context scope position expected type code
  sites : ∀ registry, PreparedBranchingCatalogSites.CatalogSites invalidProjection missingDefault registry faults tree

namespace Collected

 theorem breaking {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type) := by
  refine ⟨.breaking found form, ?_⟩
  intro registry
  exact .breaking (found := found) (form := form)

 theorem continuing {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type) := by
  refine ⟨.continuing found form, ?_⟩
  intro registry
  exact .continuing (found := found) (form := form)

 theorem body {context scope mode statements expected type code}
      (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected)
      (body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode statements) expected type code := by
  refine ⟨.body syntaxTree body, ?_⟩
  intro registry
  exact .body (syntaxTree := syntaxTree) (body := body)

 theorem uninitialized {context nextContext scope mode id node binder rest expected type body payload}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body) := by
  refine ⟨.uninitialized found form monomorphic extended ordinary projected allocation annotation same remaining.tree, ?_⟩
  intro registry
  exact .uninitialized (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.tree) (remaining.sites registry)

 theorem initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.tree, ?_⟩
  intro registry
  exact .initialized (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.tree) (remaining.sites registry)

 theorem discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨.discard found form notTail expressionFound value remaining.tree, ?_⟩
  intro registry
  exact .discard (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining.tree) (remaining.sites registry)

 theorem block {context scope mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body) := by
  refine ⟨.block found form inner.tree remaining.tree, ?_⟩
  intro registry
  exact .block (found := found) (form := form) (inner := inner.tree) (remaining := remaining.tree) (inner.sites registry) (remaining.sites registry)

 theorem ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode)
      (elseTree : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body) := by
  refine ⟨.ifThen found form conditionFound conditionType conditionTree thenTree.tree elseTree.tree remaining.tree, ?_⟩
  intro registry
  exact .ifThen (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree.tree) (elseTree := elseTree.tree) (remaining := remaining.tree) (thenTree.sites registry) (elseTree.sites registry) (remaining.sites registry)

 theorem whileLoop {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type loopCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body) := by
  refine ⟨.whileLoop found form conditionFound conditionType conditionTree loopBody.tree nativeTyped remaining.tree, ?_⟩
  intro registry
  exact .whileLoop (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody.tree) (nativeTyped := nativeTyped) (remaining := remaining.tree) (loopBody.sites registry) (remaining.sites registry)

 theorem assign {context scope mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid)
      (bare : assignment.target.projections = []) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.assign found form head remaining.tree, ?_⟩
  intro registry
  exact .assign (found := found) (form := form) (head := head) (remaining := remaining.tree) (remaining.sites registry) (.existing (reachable_bare (empty_steps head.shape bare) operands))

 theorem assignPrepared {context scope mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (site : ∀ registry, PreparedBranchingCatalogSites.AssignmentSite invalidProjection missingDefault registry faults head) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.assign found form head remaining.tree, ?_⟩
  intro registry
  exact .assign (found := found) (form := form) (head := head) (remaining := remaining.tree) (remaining.sites registry) (site registry)

 theorem bitNot {context scope mode id node assignment rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (unary : head.Errors faults) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.bitNot found form head remaining.tree, ?_⟩
  intro registry
  exact .bitNot (found := found) (form := form) (head := head) (remaining := remaining.tree) (remaining.sites registry) unary

 theorem bitNotProjected {context scope mode id node assignment rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
      (head : CompatibleProjectedBitNotStatements.Head values source context (certificates context) scope administrative definitions assignment)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (unary : PreparedBranchingCatalogSites.UnarySite invalidProjection missingDefault head) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.bitNotProjected found form head remaining.tree, ?_⟩
  intro registry
  exact .bitNotProjected (found := found) (form := form) (head := head) (remaining := remaining.tree) (remaining.sites registry) unary

 theorem matchWith {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
      (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
      (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
      (compilation : SourceCoreCompatibleDataMatches.Context)
      (sameValues : compilation.values = values) (sameDefinitions : compilation.definitions = definitions)
      (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError)))
      (requests : List GenericMatchChildren.Request)
      (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched)
      (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
      (children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (patternContext : GenericImperativeMatch.Tree.MatchContextFields compilation context) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched body) := by
  refine ⟨.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary (fun request member childContext related => (children request member childContext related).tree) remaining.tree, ?_⟩
  intro registry
  exact .matchWith (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := (fun request member childContext related => (children request member childContext related).tree)) (remaining := remaining.tree) catalog patternContext (fun request member childContext related => (children request member childContext related).sites registry) (remaining.sites registry)

 theorem terminalBlock {context scope mode id node statements rest expected type innerCode suffix}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode)
      (stops : GenericLexicalStatements.Stopped source statements)
      (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode suffix) := by
  refine ⟨.terminalBlock unique found form inner.tree stops issued, ?_⟩
  intro registry
  exact .terminalBlock (unique := unique) (found := found) (form := form) (inner := inner.tree) (stops := stops) (issued := issued) (inner.sites registry)

 theorem terminalIf {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode)
      (elseTree : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false elseBody) expected type elseCode)
      (thenStops : GenericLexicalStatements.Stopped source thenBody) (elseStops : GenericLexicalStatements.Stopped source elseBody)
      (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  refine ⟨.terminalIf unique found form conditionFound conditionType conditionTree thenTree.tree elseTree.tree thenStops elseStops issued, ?_⟩
  intro registry
  exact .terminalIf (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree.tree) (elseTree := elseTree.tree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (thenTree.sites registry) (elseTree.sites registry)

 theorem terminalMatch {context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
      (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
      (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
      (compilation : SourceCoreCompatibleDataMatches.Context)
      (sameValues : compilation.values = values) (sameDefinitions : compilation.definitions = definitions)
      (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError)))
      (requests : List GenericMatchChildren.Request)
      (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched)
      (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
      (children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code)
      (stops : ReachableMatchContinuations.DefaultStopped source id resolution)
      (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (patternContext : GenericImperativeMatch.Tree.MatchContextFields compilation context) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched suffix) := by
  refine ⟨.terminalMatch unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary (fun request member childContext related => (children request member childContext related).tree) stops issued, ?_⟩
  intro registry
  exact .terminalMatch (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := (fun request member childContext related => (children request member childContext related).tree)) (stops := stops) (issued := issued) catalog patternContext (fun request member childContext related => (children request member childContext related).sites registry)


 theorem forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post statements)
      (initial : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body) := by
  refine ⟨.forLoop found form initial.tree remaining.tree, ?_⟩
  intro registry
  exact .forLoop (found := found) (form := form) (initial := initial.tree)
    (remaining := remaining.tree) (initial.sites registry) (remaining.sites registry)


 theorem initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode)
      (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
      (postSites : ∀ registry, PreparedBranchingCatalogSites.HeaderSites invalidProjection missingDefault registry faults postTree)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  refine ⟨.initializersDone conditionFound conditionType conditionTree loopBody.tree postTree nativeTyped, ?_⟩
  intro registry
  exact .initializersDone (conditionFound := conditionFound) (conditionType := conditionType)
    (conditionTree := conditionTree) (loopBody := loopBody.tree) (postTree := postTree)
    (nativeTyped := nativeTyped) (loopBody.sites registry) (postSites registry)


 theorem initializerUninitialized {context nextContext scope binder rest body payload condition post statements expected type}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body) := by
  refine ⟨.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining.tree, ?_⟩
  intro registry
  exact .initializerUninitialized (monomorphic := monomorphic) (extended := extended)
    (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation)
    (same := same) (remaining := remaining.tree) (remaining.sites registry)


 theorem initializerInitialized {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.tree, ?_⟩
  intro registry
  exact .initializerInitialized (monomorphic := monomorphic) (extended := extended)
    (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType)
    (initial := initial) (allocation := allocation) (annotation := annotation)
    (same := same) (remaining := remaining.tree) (remaining.sites registry)


 theorem initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨.initializerDiscard found value remaining.tree, ?_⟩
  intro registry
  exact .initializerDiscard (found := found) (value := value) (remaining := remaining.tree)
    (remaining.sites registry)


 theorem initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body)
      (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid)
      (bare : assignment.target.projections = []) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.initializerAssign head remaining.tree, ?_⟩
  intro registry
  exact .initializerAssign (head := head) (remaining := remaining.tree)
    (remaining.sites registry)
    (.existing (reachable_bare (empty_steps head.shape bare) operands))
 theorem initializerAssignPrepared {context scope assignment operator rhs rest body condition post statements expected type}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body)
      (site : ∀ registry, PreparedBranchingCatalogSites.AssignmentSite invalidProjection missingDefault registry faults head) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.initializerAssign head remaining.tree, ?_⟩
  intro registry
  exact .initializerAssign (head := head) (remaining := remaining.tree)
    (remaining.sites registry)
    (site registry)
 theorem initializerBitNot {context scope assignment rest body condition post statements expected type}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body)
      (unary : head.Errors faults) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.initializerBitNot head remaining.tree, ?_⟩
  intro registry
  exact .initializerBitNot (head := head) (remaining := remaining.tree)
    (remaining.sites registry)
    unary

 theorem initializerBitNotProjected {context scope assignment rest body condition post statements expected type}
      (head : CompatibleProjectedBitNotStatements.Head values source context (certificates context) scope administrative definitions assignment)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body)
      (unary : PreparedBranchingCatalogSites.UnarySite invalidProjection missingDefault head) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.initializerBitNotProjected head remaining.tree, ?_⟩
  intro registry
  exact .initializerBitNotProjected (head := head) (remaining := remaining.tree)
    (remaining.sites registry)
    unary

end Collected
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalFlowBounds
/-! The actual JointBody supplies flow under the canonical authority retained
by its parameter packet. Ordinary and selected-method callers use their real
Nested and Origin protocols, marked allocation, binding and frame transport.
The original prepared head/loop producer consumes only smaller expression
members of this same protocol family. No bare base environment is upgraded to
a canonical packet, and no completed body or flow law is stored in Origin. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (JointBody trackedFactory)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity)
open CallableIndexedOwnedTypedLambdaProtocolContinuations (FlowPreserves FlowReflects)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

/-- The finite caller form selects existing canonical operations. A principal
keeps its real Named identity; it is never converted into an ordinary Header.
Full method selection and dictionary authority remain in the actual Support. -/
inductive Origin (compiled : SourceCoreUnifiedCompilation.Compiled) where
  | ordinary (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  | principal (named : CallableIndexedNamedGeneration.Named)

namespace Origin
variable (origin : Origin compiled) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

def protocol : ProtectedStateTransition.Protocol (Records keys) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller
  | .principal named => CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner named

def bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier
    (headers := headers) (fun _ => True) (protocol (headers := headers) origin owner) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller
  | .principal named => CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner named

def transport : ProtectedStateTransition.AdministrativeTransport (protocol (headers := headers) origin owner) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller
  | .principal named => CallableIndexedOwnedOriginCanonicalState.administrativeTransport owner named

def bindings : ProtectedStateTransition.Bindings (protocol (headers := headers) origin owner) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedNestedCanonicalState.bindings owner caller
  | .principal named => CallableIndexedOwnedOriginCanonicalState.bindings owner named

variable {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- Each branch is the original packet-preserving allocator, including its
actual returned ordered pool. No allocation execution contract is supplied. -/
def producer : ProtectedStateTransition.MarkedAllocation.Producer
    (protocol (headers := headers) origin owner) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedNestedCanonicalState.markedProducer owner caller
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  | .principal named => CallableIndexedOwnedOriginCanonicalState.markedProducer owner named
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

theorem acquire (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (producer (headers := headers) (registry := registry) origin owner functions).toOrdinary location native := by
  cases origin with
  | ordinary caller =>
      exact CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner caller
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable
  | principal named =>
      exact CallableIndexedOwnedOriginCanonicalState.readyAt_of_stableOwner owner named
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable
end Origin

variable
  {named : CallableIndexedNamedGeneration.Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (issued : IssuedSource compiled code.compilation.owner function.source)
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (body : JointBody namedCompilation code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
    diagnosticPolicy issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
  (origin : Origin compiled) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep issued.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := certificates body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
      (faults := faults) (registry := registry) issued
      (Origin.bridge (headers := headers) origin owner) functions table)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- The same prepared flow is closed from E at sizes at most budget. The
original finite head and loop operations are constructed internally once. -/
theorem preserves_flow (budget : Nat)
    (meaning : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (Origin.bridge (headers := headers) origin owner)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured code body.toBody functions (Origin.bridge (headers := headers) origin owner)
        (registry := registry) (faults := faults)) := by
  exact CallableIndexedOwnedContextualLambdaPreparedFlowBounds.preserves_flow
    (active := code.active) (onError := code.allocationError)
    (expressionSyntax := expressionSyntax function.source) (certificates := certificates body.readFuel function.source)
    (administrative := captured.administrative) (registry := registry) (faults := faults)
    (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
    issued (Origin.bridge (headers := headers) origin owner) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (Origin.producer (headers := headers) (registry := registry) origin owner functions)
    (Origin.acquire (headers := headers) (registry := registry) origin owner functions)
    (Origin.transport (headers := headers) origin owner) (Origin.bindings (headers := headers) origin owner)
    body.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended).1 meaning body.prepared

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- F reflection consumes the native strict E family; its Source grade is
independent. The same actual JointBody and receiving table are retained. -/
theorem reflects_flow (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (Origin.bridge (headers := headers) origin owner)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    Below budget (FlowReflects captured code body.toBody functions (Origin.bridge (headers := headers) origin owner)
      (registry := registry) (faults := faults)) := by
  exact CallableIndexedOwnedContextualLambdaPreparedFlowBounds.reflects_flow
    (active := code.active) (onError := code.allocationError)
    (expressionSyntax := expressionSyntax function.source) (certificates := certificates body.readFuel function.source)
    (administrative := captured.administrative) (registry := registry) (faults := faults)
    (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
    issued (Origin.bridge (headers := headers) origin owner) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (Origin.producer (headers := headers) (registry := registry) origin owner functions)
    (Origin.acquire (headers := headers) (registry := registry) origin owner functions)
    (Origin.transport (headers := headers) origin owner) (Origin.bindings (headers := headers) origin owner)
    body.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended).1 functionTypes reflection body.prepared

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalFlowBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginGlobalsCarriers
/-! Both authentic caller protocols already retain their actual canonical
Globals observations. This carrier projects those literal fields and restores
the same reached pool. Forgetting its slot observations is definitionally the
original Origin bridge; no base-state packet or Source authority is inferred. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginGlobalsCarriers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (origin : Origin compiled) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- The original complete packet supplies its own slots at the same pool. -/
def carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier
    (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 1 index.scope index.canonical)
    (Origin.protocol (headers := headers) origin owner) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedNestedCallerProtocol.carrier owner caller
  | .principal named => CallableIndexedOwnedOriginCanonicalState.carrier owner named

/-- The semantic bridge, actual returned pool and record lists are unchanged. -/
theorem forget_slots :
    CallableIndexedOwnedIndirectCallerProtocol.forget_slots (carrier (headers := headers) origin owner) =
      Origin.bridge (headers := headers) origin owner := by
  cases origin <;> rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginGlobalsCarriers
end
