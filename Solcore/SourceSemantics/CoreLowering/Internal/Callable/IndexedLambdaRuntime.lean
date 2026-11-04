import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies

/-!
# Indexed callables: nested lambda runtime

Certificates and body meaning of nested and named lambdas at runtime, and invocation through views.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeCertificates
/-! Literal lambda leaves retain their actual Code and a smaller static body.
The compiler view is observed by a full node lookup; the accepted body and its
original view remain inside the receipt. Named calls impose no rank decrease.
Transport changes only reached node and child certificates, preserving every
ordered child, same dictionary and emitted code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeCertificates
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open RecursiveNamedCatalog RecursiveNamedLambdaFormationHeads
variable {values : SourceCoreCompatibleValues.Context} {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
  {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {compilation : SourceCoreFunctions.Context} {source view : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}

abbrev RankedSupport := Nat → CallableIndexedLambdaRuntimeValues.SupportFamily indexed

/-- The source index is an actual node observation, not equality of the entire
view with the closure source. Code already retains its original body callback. -/
structure Lambda (support : RankedSupport (indexed := indexed)) (rank : Nat)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (source : TypedSource) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  code : Code indexed (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
    scope (nativePrefix caller)
  childRank : Nat
  smaller : childRank < rank
  body : support childRank code
  compilation : code.compilation = CallableIndexedNamedGeneration.context indexed caller.named
  active : code.active = []
  identifier : code.id = id
  emitted : code.lowered = lowered
  found : source.lookupExpression? id = some code.sourceNode
  sourceType : code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
  nativeType : lowered.type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore
  requirements : code.sourceNode.requirements = []
  coercions : code.sourceNode.coercions = []
  snapshots : code.policy.snapshotLambda code.id = true

theorem Lambda.of_site {support : RankedSupport (indexed := indexed)} {rank childRank : Nat}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {scope : SourceCoreLocalCell.Scope}
    (site : CallableIndexedLambdaGeneration.Site indexed caller.named parameters result statements
      context evidence [] scope (nativePrefix caller))
    (smaller : childRank < rank) (body : support childRank site.code)
    (found : source.lookupExpression? site.code.id = some site.code.sourceNode)
    (sourceType : site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence []))
    (requirements : site.code.sourceNode.requirements = []) (coercions : site.code.sourceNode.coercions = []) :
    Nonempty (Lambda support rank caller source context evidence scope site.code.id site.code.lowered) :=
  ⟨{parameters := parameters, result := result, statements := statements, code := site.code,
    childRank := childRank, smaller := smaller, body := body, compilation := site.compilation,
    active := site.active, identifier := rfl, emitted := rfl, found := found, sourceType := sourceType,
    nativeType := site_native_type site, requirements := requirements, coercions := coercions,
    snapshots := site.snapshots}⟩

inductive Head (support : RankedSupport (indexed := indexed)) (rank : Nat)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | existing {scope id lowered}
      (head : CallableLambdaViewNamedRuntimeCertificates.Head (ambient := CallableIndexedAmbient.ambientDefinitions indexed)
        headers compilation source context evidence children scope id lowered) :
      Head support rank caller headers compilation source context evidence children scope id lowered
  | lambda {scope id lowered}
      (head : Lambda support rank caller source context evidence scope id lowered) :
      Head support rank caller headers compilation source context evidence children scope id lowered

abbrev Certificates (support : RankedSupport (indexed := indexed)) (rank : Nat)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :=
  RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
    (Head support rank caller headers compilation source context evidence) fuel values source context solved reasonAt

/-- Lexical syntax is only an actual full node receipt; the concrete Tree
separately supplies every supported expression and nested literal body. -/
def Nodes (source : TypedSource) (id : ExpressionId) : Prop :=
  ∃ node, source.lookupExpression? id = some node

structure BodyReceipt (support : RankedSupport (indexed := indexed)) (rank : Nat)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code indexed function scope administrative)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  source : function.source = CallableIndexedNamedGeneration.source caller.named
  compilation : code.compilation = CallableIndexedNamedGeneration.context indexed caller.named
  active : code.active = []
  administrative : administrative = nativePrefix caller
  body : CallableIndexedLambdaStaticBodySupport.BodyWith Nodes
    (fun fuel source context => Certificates support rank caller headers code.compilation fuel source context
      function.evidence code.compilation.solvedRequirements code.reasonAt)
    code program registry faults

/-- The recursion orders only static nested literals. Named calls in each body
retain the complete existing family and do not contain a rank condition. -/
def BodyAt
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (rank : Nat) : CallableIndexedLambdaRuntimeValues.SupportFamily indexed :=
  fun {_ _ _} code => BodyReceipt
    (fun childRank {_ _ _} childCode =>
      if _smaller : childRank < rank then BodyAt headers caller registry faults childRank childCode else Empty)
    rank caller headers code registry faults
termination_by rank


def BodyAt.receipt {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code indexed function scope administrative} {rank : Nat}
    (body : BodyAt headers caller registry faults rank code) :
    BodyReceipt (fun childRank {_ _ _} childCode => if _smaller : childRank < rank then
      BodyAt headers caller registry faults childRank childCode else Empty)
      rank caller headers code registry faults := by
  rw [BodyAt] at body
  exact body

def BodyAt.recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code indexed function scope administrative} {rank : Nat}
    (body : BodyAt headers caller registry faults rank code) (environment : Dynamic.Environment) :
    BodyAt headers caller registry faults rank (recaptureCode code environment) := by
  rw [BodyAt]
  have actual := body.receipt
  exact {
    source := actual.source
    compilation := actual.compilation
    active := actual.active
    administrative := actual.administrative
    body := recaptureBodyWith code actual.body environment }

/-- The existential rank is stored in the same Code's static support. -/
abbrev Support (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    CallableIndexedLambdaRuntimeValues.SupportFamily indexed :=
  fun {_ _ _} code => Σ caller : Header indexed.ancestry values indexed.layouts.definitions program,
    Σ rank : Nat, BodyAt headers caller registry faults rank code

/-- Captured globals and the full actual carried source metadata are separate
from call-time catalog authority. Both remain unchanged under heap extension. -/
def Condition
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (locations : Locations (prepared := indexed.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)) :
    CallableIndexedLambdaRuntimeValues.SupportCondition indexed (Support headers registry faults) :=
  fun {_ _ _ scope _} captured _ history body =>
    history.metadata = CallableIndexedNamedGeneration.state body.1.named ∧ ∃ location,
      CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 scope captured.canonical location

theorem condition_stable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
    (captured : Captures indexed mapping world scope function.captured actual)
    (code : Code indexed function scope captured.administrative) (history : History code)
    (body : Support headers registry faults code)
    {locations : Locations (prepared := indexed.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)}
    (supported : Condition (registry := registry) (faults := faults) headers locations captured code history body)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Condition (registry := registry) (faults := faults) headers locations (captured.extend maps worlds) code history body := supported

def model
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (locations : Locations (prepared := indexed.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : values.checked.catalog.callableContracts = true) :
    FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions indexed) :=
  CallableIndexedLambdaRuntimeValues.modelWith indexed (Support headers registry faults)
    (Condition headers locations) (condition_stable (headers := headers) (locations := locations)
      (registry := registry) (faults := faults)) profile


section View
variable {support : RankedSupport (indexed := indexed)} {rank : Nat}
  {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)

def Lambda.transport {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Lambda support rank caller source context evidence scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    Lambda support rank caller view context evidence scope id lowered :=
  {head with found := (expression_lookup edited avoids reached).symm.trans head.found}

theorem found {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Head support rank caller headers compilation source context evidence children scope id lowered) :
    ∃ node, source.lookupExpression? id = some node := by
  cases head with
  | existing head => exact CallableLambdaViewNamedRuntimeCertificates.canonical_call_found head
  | lambda head => exact ⟨_, head.found⟩

include edited avoids in
theorem transport {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificates support rank caller headers compilation fuel source context evidence solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    Certificates support rank caller headers compilation fuel view context evidence solved reasonAt scope id lowered := by
  exact CallableLambdaViewNamedRuntimeCertificates.transport_generic
    (target := Head support rank caller headers compilation view context evidence) edited avoids
    (fun head => found head)
    (fun found head reached children => by
      cases head with
      | lambda leaf => exact .lambda (leaf.transport edited avoids reached)
      | existing head =>
        cases head with
        | ordinary receipt =>
          have same := Option.some.inj (found.symm.trans receipt.metadata.found)
          cases same
          exact .existing (.ordinary (CallableLambdaViewNamedRuntimeCertificates.ordinary_transport edited avoids receipt reached children))
        | authenticated receipt => exact .existing (CallableLambdaViewNamedRuntimeCertificates.call_transport edited avoids found receipt reached children))
    receipt reached

end View
end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNamedRuntimeBodyMeaning
/-! The canonical lambda body retains the actual view's named emission and
same caller dictionary. Its expression proof reuses the existing finite Tree
fold and catalog mutual induction. Source and native grades remain independent;
actual closure installation and restoration are handled by the entry adapters. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNamedRuntimeBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableLambdaViewNamedRuntimeCertificates


open CallableIndexedLambdaValues CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableLambdaViewEdits CallableLambdaBodyReachability

/-- The lexical support records actual nodes; execution remains restricted by
its separate concrete expression certificates. -/
def Nodes (source : TypedSource) (id : ExpressionId) : Prop :=
  ∃ node, source.lookupExpression? id = some node

section BodyReceipt
variable {values : ValuesContext} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code prepared function scope administrative) {program : Program}
  {headers : Inventory prepared.ancestry values prepared.layouts.definitions program}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

abbrev Body (headers : Inventory prepared.ancestry values prepared.layouts.definitions program)
    (code : Code prepared function scope administrative) (program : Program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  CallableIndexedLambdaStaticBodySupport.BodyWith Nodes
    (fun fuel source context => Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared) function.evidence headers code.compilation fuel source context
      code.compilation.solvedRequirements code.reasonAt) code program registry faults

/-- The actual compiler-view tree is reindexed through the one static fold.
Original emissions and Direct acceptance retain the actual ordered child action;
only reached node lookup and static typing return to the canonical source. -/
theorem of_tree
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function) (readFuel : Nat) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy)
    {changed : List ExpressionId}
    (edited : LocalView function.source code.view changed)
    (avoids : Avoids function.source (function.body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique function.source)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow)
    {tree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values code.view
      (Nodes code.view)
      (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith
        (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (some function.evidence) headers code.compilation readFuel code.view context
        code.compilation.solvedRequirements code.reasonAt)
      prepared.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow}
    (sites : tree.CatalogSites .reachable registry faults) :
    ∃ body : Body headers code program registry faults,
      body.toContext = inputs ∧ body.readFuel = readFuel ∧ body.policy = policy ∧ body.flow = flow := by
  have unchanged := LocalView.refl code.view
  have fresh : Avoids code.view (function.body.map NodeId.statement) [] := by intro id member; cases member
  obtain ⟨actual, actualSites⟩ := CallableLambdaViewMatchRuntimeCertificates.transport_sites_with
    (afterSyntax := Nodes code.view)
    (after := fun context => Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared)
      function.evidence headers code.compilation readFuel code.view context code.compilation.solvedRequirements code.reasonAt)
    (tree := tree)
    unchanged fresh (edited.metadata.unique unique)
    (fun _ _ receipt => receipt)
    (fun _ _ _ _ reached receipt => CallableLambdaViewNamedRuntimeCertificates.transport unchanged fresh receipt reached)
    sites (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
  obtain ⟨body, sameContext, sameFuel, samePolicy, sameFlow, _⟩ :=
    CallableIndexedLambdaStaticBodySupport.BodyWith.of_tree
      (expressionSyntax := Nodes)
      (certificates := fun fuel source context => Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared) function.evidence headers code.compilation fuel source context
        code.compilation.solvedRequirements code.reasonAt)
      code inputs frame readFuel policy callback edited avoids unique sameLedger
      (fun id reached receipt => by
        obtain ⟨node, found⟩ := receipt
        exact ⟨node, (expression_lookup edited avoids reached).trans found⟩)
      (fun _ _ _ _ reached receipt =>
        CallableLambdaViewNamedRuntimeCertificates.canonical_transport
          ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
          (avoids.view edited.metadata) receipt (reached.metadata edited.metadata))
      projection generated actualSites
  exact ⟨body, sameContext, sameFuel, samePolicy, sameFlow⟩

/-- Same-D static fields feed the shared flow/finish kernel. -/
def Body.toKernel (body : Body headers code program registry faults) :
    CallableRuntimeBodyKernel.BodyFor prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values function
      (Nodes function.source)
      (fun context => Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared) function.evidence headers code.compilation body.readFuel function.source context
        code.compilation.solvedRequirements code.reasonAt)
      (fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
      .reachable (CallableIndexedAmbient.ambientDefinitions prepared)
      administrative body.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      code.receipt.resultCore code.receipt.body code.compilation.internalReason code.compilation.internalReason registry faults :=
  { flow := body.flow, tree := body.tree, sites := body.sites, initialValid := body.valid,
    projection := body.projection, unique := body.unique, emitted := body.emitted }
/-- The legacy builtin record keeps its original fields and constructor. -/
def builtin_kernel (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults) :
    CallableRuntimeBodyKernel.BodyFor prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values function
      (CompatibleExpressionBuiltins.Syntax function.source)
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate body.readFuel values function.source context
        code.compilation.solvedRequirements code.reasonAt)
      (fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
      .reachable (CallableIndexedAmbient.ambientDefinitions prepared)
      administrative body.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      code.receipt.resultCore code.receipt.body code.compilation.internalReason code.compilation.internalReason registry faults :=
  { flow := body.flow, tree := body.tree, sites := body.sites, initialValid := body.valid,
    projection := body.projection, unique := body.unique, emitted := body.emitted }

end BodyReceipt

section Heads
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {compilation : SourceCoreFunctions.Context}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate}
  (P : ProtectedExpressionMeaning.Entry) (transport : ProtectedExpressionMeaning.Transport P)
  (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
    protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)
  (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
  (authorized : ∀ header, header ∈ headers → BodyAuthorization (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header (conditions header))

include transport catalog authorized in
theorem head_preserves_for
    (budget size : Nat) (within : size ≤ budget)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (arguments : RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence certificate) faults P := by
  intro scope id lowered head
  cases head with
  | authenticated head =>
    exact RecursiveNamedCallEvidenceHeads.preserves_at_for functions P transport catalog conditions authorized
      budget size within idsUnique unique owners arguments bodies head
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed installed trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨caller⟩ := catalog installed
    have independent := RecursiveNamedArgumentTraceBounds.source_inv receipt.metadata receipt.form receipt.calleeFound
      receipt.predicates receipt.evidenceEmpty unique trace
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      RecursiveNamedExpressionHeadBounds.call_preserves_bounded_for functions receipt.sequence receipt.nativeTypes packed
        P transport (conditions receipt.header) (authorized receipt.header receipt.member) budget arguments (bodies receipt.header receipt.member)
        owners receipt.member caller installed environments heaps locals agrees typed independent within
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, preserved, heapMetadata⟩
    · change Evaluates actual store (lowered.expression.rename ξ) value finalStore
      rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot]
      exact evaluated
    · simpa only [receipt.sourceType, receipt.nativeType] using represented


include transport catalog authorized in
private theorem head_preserves
    (budget size : Nat) (within : size ≤ budget)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (arguments : RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence certificate) faults P :=
  head_preserves_for functions P transport catalog conditions authorized budget size within idsUnique unique owners arguments bodies

include transport catalog authorized in
theorem head_reflects_for
    (budget size : Nat) (within : size ≤ budget)
    (arguments : RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence certificate) faults P := by
  intro scope id lowered head
  cases head with
  | authenticated head =>
    exact RecursiveNamedCallEvidenceHeads.reflects_at_for functions P transport catalog conditions authorized
      budget size within arguments bodies head
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed installed evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨caller⟩ := catalog installed
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    change EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore at evaluated
    rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot] at evaluated
    obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      RecursiveNamedExpressionHeadBounds.call_reflects_bounded_for functions receipt.sequence receipt.nativeTypes packed
        P transport (conditions receipt.header) (authorized receipt.header receipt.member) budget arguments (bodies receipt.header receipt.member)
        receipt.member caller installed environments heaps locals agrees typed evaluated within
    obtain ⟨sourceSize, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro receipt.metadata receipt.form receipt.calleeFound
      receipt.calleeForm receipt.calleeRequirements receipt.calleeCoercions receipt.valid receipt.predicates receipt.evidenceEmpty trace
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, independent,
      by simpa only [receipt.sourceType, receipt.nativeType] using represented,
      finalHeaps, maps, worlds, preserved, heapMetadata⟩


include transport catalog authorized in
private theorem head_reflects
    (budget size : Nat) (within : size ≤ budget)
    (arguments : RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence certificate) faults P :=
  head_reflects_for functions P transport catalog conditions authorized budget size within arguments bodies

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations functionTypes valid unique owners uninitialized missing transport catalog authorized in
private theorem expressions_preserves (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificates evidence headers compilation fuel source context solved reasonAt) faults P := by
  exact RecursiveNamedExpressionTreeBounds.preserves_at_with_literals_with_for
    functions extension faithful observations functionTypes evidence unique uninitialized missing
    (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence) P
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence valid.ledger valid.runtime unique faults)
    budget size within (by
      intro certificate child childWithin children
      exact RecursiveNamedExpressionTreeBounds.head_preserves_at_with_calls
        functions extension faithful observations functionTypes evidence unique missing P transport
        (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence) budget child childWithin children
        (head_preserves functions P transport catalog conditions authorized budget child childWithin valid.runtime.idsUnique unique owners
          (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies))

include extension faithful observations functionTypes valid uninitialized missing transport catalog authorized in
private theorem expressions_reflects (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificates evidence headers compilation fuel source context solved reasonAt) faults P := by
  exact RecursiveNamedExpressionTreeBounds.reflects_at_with_literals_with_for
    functions extension faithful observations functionTypes evidence uninitialized missing
    (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence) P
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence valid.ledger valid.runtime source faults)
    budget size within (by
      intro certificate child childWithin children
      exact RecursiveNamedExpressionTreeBounds.head_reflects_at_with_calls
        functions extension faithful observations functionTypes evidence missing P transport
        (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence) budget child childWithin children
        (head_reflects functions P transport catalog conditions authorized budget child childWithin
          (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies))

end Heads


section ClosedCatalog
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The catalog contains static profiles for every actual named parameter
state, at each header's own complete dictionary. No body execution is a field. -/
structure CatalogFamily (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program))
    (capturePrefix : Nat) (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context
  expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop
  diagnosticPolicy : AssignmentDiagnosticPolicy
  prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1
  profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileForWith true diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults
  uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id)
  missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag)
  escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped

variable (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (family : CatalogFamily headers locations capturePrefix functions registry faults)
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (P : ProtectedExpressionMeaning.Entry) (transport : ProtectedExpressionMeaning.Transport P)
  (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
    protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)

include extension faithful observations functionTypes owners family valid unique uninitialized missing transport catalog in
/-- Same-D canonical expression preservation closes every named body through
the one existing catalog strong induction. The protected source entry remains
independent of the lambda's native type and installed ghost. -/
theorem expressions_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificates evidence headers compilation fuel source context solved reasonAt) faults P := by
  have bodies := RecursiveNamedCatalogMutualMeaning.preserves_at_runtime_evidence
    functions extension faithful observations functionTypes owners family.uninitialized family.missing family.escaped
    family.prefixMatches family.profiles
  intro scope id lowered receipt
  exact expressions_preserves (fuel := fuel) functions P transport catalog (fun _ => fun _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial)
    extension faithful observations functionTypes valid unique owners uninitialized missing budget size within (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after _ trace
      exact bodies child header member entry trace) receipt

include extension faithful observations functionTypes family valid uninitialized missing transport catalog in
/-- Reflection uses only original native children. The catalog strong induction
returns independently measured source traces for the same full dictionaries. -/
theorem expressions_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificates evidence headers compilation fuel source context solved reasonAt) faults P := by
  have bodies := RecursiveNamedCatalogMutualMeaning.reflects_at_runtime_evidence
    functions extension faithful observations functionTypes family.uninitialized family.missing family.escaped
    family.prefixMatches family.profiles
  intro scope id lowered receipt
  exact expressions_reflects (fuel := fuel) functions P transport catalog (fun _ => fun _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial)
    extension faithful observations functionTypes valid uninitialized missing budget size within (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodies child header member entry trace) receipt
end ClosedCatalog


section NamedExecution
variable {values : ValuesContext} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code prepared function scope administrative) (history : History code) {program : Program}
  {headers : Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : Body headers code program registry faults)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions (Identity prepared))
  (functionTypes : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (family : CatalogFamily headers locations capturePrefix functions registry faults)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)

private abbrev sourceEntry
    (headers : Inventory prepared.ancestry values prepared.layouts.definitions program)
    (locations : Locations (prepared := prepared.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)) (capturePrefix : Nat) :
    ProtectedExpressionMeaning.Entry := CallableIndexedLambdaCatalogEntries.protectedEntry code history headers locations
  capturePrefix code.compilation.administrativePrefix

include body extension observations functionTypes owners family uninitialized missing escaped in
/-- The source grade is the original parent-supplied body grade. Named callee
meaning is closed by CatalogFamily's static profiles and the existing mutual
induction; the lambda ghost remains in its independent source entry. -/
theorem Body.preserves_sized (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      environment canonical prepared.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      1 + prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode prepared.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : sourceEntry code history headers locations capturePrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      mapping world before store canonical)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.receipt.body.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      sourceEntry code history headers locations capturePrefix
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context,
      CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedHeaderContracts.AtMost budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence function.source
        (Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared) function.evidence headers code.compilation
          body.readFuel function.source context code.compilation.solvedRequirements code.reasonAt) faults (sourceEntry code history headers locations capturePrefix)) := by
    intro context valid child within
    exact expressions_preserves_at functions extension (identity_faithful prepared) observations functionTypes owners
      family valid body.unique uninitialized missing (sourceEntry code history headers locations capturePrefix)
      CallableIndexedLambdaCatalogEntries.transport (fun ⟨entry⟩ => ⟨entry.catalog⟩) budget child within
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata, _, entry⟩ :=
    body.toKernel.preserves_sized functions rfl (CallableIndexedAmbient.frame_registered prepared) extension program
      (identity_faithful prepared) observations escaped
      CallableIndexedLambdaCatalogEntries.transport CallableIndexedLambdaCatalogEntries.binds
      (fun valid extended => valid.extend extended) (fun valid => valid) budget size within expressions
      environments heaps locals agrees typed reference read unmapped installed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata, entry⟩

include body extension observations functionTypes family uninitialized missing escaped in
/-- Reflection consumes the original native body witness. No source execution
or preservation theorem is used to obtain its independent source grade. -/
theorem Body.reflects_sized (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      environment canonical prepared.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      1 + prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode prepared.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : sourceEntry code history headers locations capturePrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.receipt.body.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      sourceEntry code history headers locations capturePrefix
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context,
      CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence function.source
        (Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared) function.evidence headers code.compilation
          body.readFuel function.source context code.compilation.solvedRequirements code.reasonAt) faults (sourceEntry code history headers locations capturePrefix)) := by
    intro context valid child smaller
    exact expressions_reflects_at functions extension (identity_faithful prepared) observations functionTypes
      family valid uninitialized missing (sourceEntry code history headers locations capturePrefix)
      CallableIndexedLambdaCatalogEntries.transport (fun ⟨entry⟩ => ⟨entry.catalog⟩) budget child (Nat.le_of_lt smaller)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, _, entry⟩ :=
    body.toKernel.reflects_sized functions rfl (CallableIndexedAmbient.frame_registered prepared) extension program
      (identity_faithful prepared) observations functionTypes escaped
      CallableIndexedLambdaCatalogEntries.transport CallableIndexedLambdaCatalogEntries.binds
      (fun valid extended => valid.extend extended) (fun valid => valid) budget size within expressions
      environments heaps locals agrees typed reference read unmapped installed evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, entry⟩
end NamedExecution

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNamedRuntimeBodyMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeBodyMeaning
/-! Nested formation uses the same ranked static receipts and function model
as every argument and heap value. Runtime decrease remains the original body
size; only nested literal support uses the independent static rank. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedLambdaFormationHeads
open CallableIndexedLambdaNestedRuntimeCertificates

variable {values : SourceCoreCompatibleValues.Context} {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
  {locations : Locations (prepared := indexed.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)}
  {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {rank : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

abbrev LowerSupport (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) (rank : Nat) :
    RankedSupport (indexed := indexed) :=
  fun childRank {_ _ _} code => if _smaller : childRank < rank then
    BodyAt headers caller registry faults childRank code else Empty

abbrev LambdaAt (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (rank : Nat) (source : TypedSource) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :=
  CallableIndexedLambdaNestedRuntimeCertificates.Lambda
    (LowerSupport headers caller registry faults rank) rank caller source context evidence

section Leaf
variable (head : LambdaAt headers caller registry faults rank source context evidence scope id lowered)

def formed (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure caller.named head.parameters head.result head.statements context evidence environment

def actualCode (environment : Dynamic.Environment) : Code indexed (formed head environment) scope (nativePrefix caller) :=
  recaptureCode head.code environment

def childBody : BodyAt headers caller registry faults head.childRank head.code := by
  simpa only [LowerSupport, dif_pos head.smaller] using head.body

def actualSupport (environment : Dynamic.Environment) :
    Support headers registry faults (actualCode head environment) :=
  ⟨caller, head.childRank, (childBody head).recapture environment⟩

def historyAt {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry caller headers locations 0 1 scope mapping world heap store canonical)
    (environment : Dynamic.Environment) : History (actualCode head environment) where
  native := entry.catalog.authority.current
  ghost := entry.catalog.authority.ghost
  metadata := CallableIndexedNamedGeneration.state caller.named
  carried := entry.history
  source := rfl
  owner := by change caller.named.signature.key = head.code.compilation.owner; rw [head.compilation]; rfl
  active := head.active.symm

theorem reference_index : head.code.referenceIndex = scope.length + 1 + indexed.base.globals.length := by
  simp only [Code.referenceIndex, head.compilation, SourceCoreCallableIndexedAncestry.creationReferenceIndex,
    CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext]

/-- No current ghost is replaced while forming the nested value. The value
copies its captured cells; captured history and the finite global prefix are
built from the same reached state and kept by the copies. -/
theorem formation
    (profile : values.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical actual : Environment} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {ξ : Renaming}
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry
      (model headers locations registry faults profile)) mapping world heap store) :
    ∃ value captured finalHeap finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
        environment heap id (.closure (formed head captured)) finalHeap ∧
      Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment heap captured
        finalHeap ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word value) finalStore ∧
      CompatiblePayload.ValueRep values.checked registry
        (model headers locations registry faults profile)
        finalMap finalWorld head.code.sourceNode.type (.closure (formed head captured)) value lowered.type ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry
        (model headers locations registry faults profile)) finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap finalHeap := by
  let captured : Captures indexed mapping world scope environment actual := captures_for complete globals entry related agrees typed
  let code : Code indexed (formed head environment) scope captured.administrative := actualCode head environment
  let history : History code := historyAt head entry environment
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef indexed.ancestry.layout.frame.type entry.catalog.authority.frameLocation) := by
    have bound : head.code.referenceIndex < scope.length + (nativePrefix caller).length := by
      rw [reference_index head]
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
    change (canonical.take (scope.length + (nativePrefix caller).length))[head.code.referenceIndex]? = _
    rw [List.getElem?_take, if_pos bound, reference_index head, ← globals]
    exact entry.reference
  obtain ⟨formedRecord⟩ := CallableIndexedLambdaValues.formation captured code history head.snapshots
    (reference_index head) heaps reference entry.catalog.authority.frame.read
  let body : Support headers registry faults formedRecord.closureCode := actualSupport head formedRecord.captured
  have supported : Condition (registry := registry) (faults := faults) headers locations
      (function := formedRecord.closure) formedRecord.captures formedRecord.closureCode formedRecord.closureHistory
      body := by
    change formedRecord.closureHistory.metadata = CallableIndexedNamedGeneration.state caller.named ∧ ∃ location,
      CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 scope formedRecord.canonical location
    exact ⟨rfl, entry.catalog.authority.frameLocation,
      (capture_globals_for complete globals slots entry related agrees typed).of_slots formedRecord.slots⟩
  obtain ⟨sourceValue, native, represented⟩ := CallableIndexedLambdaRuntimeValues.formation_with
    indexed program (support := Support headers registry faults) (P := Condition headers locations)
    formedRecord body supported profile heaps.runtime_hasTypes
    (by change Dynamic.OrdinaryRequirementLayout head.code.sourceNode.requirements head.code.sourceNode.coercions []; rw [head.requirements, head.coercions]; rfl) head.coercions
  refine ⟨CallableIndexedLambdaValues.value code formedRecord.embedding history.native formedRecord.closureActual,
    formedRecord.captured, formedRecord.finalHeap, formedRecord.finalStore, formedRecord.finalMap,
    formedRecord.finalWorld, ?_, formedRecord.copy, ?_, ?_, formedRecord.heaps, formedRecord.maps,
    formedRecord.worlds, formedRecord.frame, formedRecord.copy.metadata_extends⟩
  · change Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
      environment heap head.code.id (.closure (formed head formedRecord.captured)) formedRecord.finalHeap at sourceValue
    simpa only [head.identifier] using sourceValue
  · exact Eq.mp (congrArg (fun expression => Evaluates actual store expression
      (.inRight .word (CallableIndexedLambdaValues.value code formedRecord.embedding history.native
        formedRecord.closureActual)) formedRecord.finalStore)
      (congrArg (fun output : SourceCoreBasic.LoweredExpr => output.expression.rename ξ) head.emitted)) native
  · rw [head.sourceType, head.nativeType]
    exact .function represented

local notation "F" => model headers locations registry faults
local notation "P" => CallableIndexedLambdaNestedFormationEntries.protectedEntry caller headers locations 0 1

theorem preserves_leaf_at
    (profile : values.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
    (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
    (size : Nat) (unique : NodeOccurrencesUnique source) :
    RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry (F profile)) program context evidence source
      (fun scope id lowered => Nonempty (LambdaAt headers caller registry faults rank source context evidence scope id lowered)) faults P := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    related heaps locals agrees typed installed trace
  obtain ⟨leaf⟩ := certified
  obtain ⟨entry⟩ := installed
  have sourceFound : (CallableIndexedNamedGeneration.source caller.named).lookupExpression? id = some leaf.code.sourceNode := by
    simpa only [CallableIndexedLambdaGeneration.closure, leaf.identifier] using leaf.code.sourceFound
  rw [sameSource] at found unique trace
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  cases trace.sound with
  | value evaluated =>
    rename_i result
    have original : Dynamic.ExpressionEvaluates program (formed leaf environment).context (formed leaf environment).evidence
        (formed leaf environment).source environment before leaf.code.id result after := by
      simpa only [formed, CallableIndexedLambdaGeneration.closure, leaf.identifier] using evaluated
    obtain ⟨captured, rfl, copy⟩ := source_value_of_code (actualCode leaf environment) unique leaf.coercions original
    obtain ⟨value, formedCaptured, finalHeap, finalStore, finalMap, finalWorld, _, formedCopy, native, represented,
        finalHeaps, maps, worlds, frame, metadata⟩ :=
      formation leaf profile complete globals slots entry related agrees typed heaps
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formedCopy
    exact ⟨.inRight .word value, finalStore, finalMap, finalWorld, native, .value represented, finalHeaps, maps, worlds,
      frame, metadata⟩
  | fault failed =>
    rename_i reason
    apply False.elim
    apply excludes_fault_of_code (program := program) (actualCode leaf environment) unique leaf.coercions
    change Dynamic.ExpressionFaults program context evidence (CallableIndexedNamedGeneration.source caller.named) environment before leaf.code.id reason after
    simpa only [leaf.identifier] using failed

theorem reflects_leaf_at
    (profile : values.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
    (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
    (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry (F profile)) program context evidence source
      (fun scope id lowered => Nonempty (LambdaAt headers caller registry faults rank source context evidence scope id lowered)) faults P := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    related heaps locals agrees typed installed completed
  obtain ⟨leaf⟩ := certified
  obtain ⟨entry⟩ := installed
  have sourceFound : (CallableIndexedNamedGeneration.source caller.named).lookupExpression? id = some leaf.code.sourceNode := by
    simpa only [CallableIndexedLambdaGeneration.closure, leaf.identifier] using leaf.code.sourceFound
  rw [sameSource] at found
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨nativeValue, captured, finalHeap, formedStore, finalMap, finalWorld, sourceValue, _, native, represented,
      finalHeaps, maps, worlds, frame, metadata⟩ :=
    formation leaf profile complete globals slots entry related agrees typed heaps
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound native
  have original : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id
      (.value (.closure (formed leaf captured))) finalHeap := by
    simpa only [sameSource] using (Dynamic.ExpressionEvaluatesOutcome.value sourceValue)
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size original
  exact ⟨sourceSize, _, finalHeap, finalMap, finalWorld, sized, .value represented, finalHeaps, maps, worlds, frame,
    metadata⟩

end Leaf

section Expressions
variable
  (profile : values.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (globals : caller.globals = indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations 0
    (model headers locations registry faults profile) registry faults)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

local notation "F" => model headers locations registry faults profile
local notation "P" => CallableIndexedLambdaNestedFormationEntries.protectedEntry caller headers locations 0 1
local notation "Calls" => CallableIndexedLambdaNestedRuntimeCertificates.Head
  (LowerSupport headers caller registry faults rank) rank caller headers
  (CallableIndexedNamedGeneration.context indexed caller.named) source context evidence
local notation "Cert" => CallableIndexedLambdaNestedRuntimeCertificates.Certificates
  (LowerSupport headers caller registry faults rank) rank caller headers
  (CallableIndexedNamedGeneration.context indexed caller.named) fuel source context evidence solved reasonAt

private theorem observations : CompatibleEquality.FunctionObservations values.checked.catalog F (Identity indexed) :=
  CallableIndexedLambdaRuntimeValues.observationsWith indexed (Support headers registry faults) (Condition headers locations)
    (condition_stable (headers := headers) (locations := locations) (registry := registry) (faults := faults)) profile

private theorem runtimeViews : FunctionRuntimeViews F :=
  CallableIndexedLambdaRuntimeValues.runtimeViewsWith indexed (Support headers registry faults) (Condition headers locations)
    (condition_stable (headers := headers) (locations := locations) (registry := registry) (faults := faults)) profile

include complete globals slots extension family valid sameSource unique owners uninitialized missing in
/-- The same expression fold closes ordered children. Only actual named callee
profiles enter the existing catalog strong induction; nested formation supplies
its smaller static receipt without a runtime body execution premise. -/
theorem expressions_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry F) program context evidence source Cert faults P := by
  have bodies := RecursiveNamedCatalogMutualMeaning.preserves_at_runtime_evidence
    F extension (identity_faithful indexed) (observations profile) (runtimeViews profile) owners
    family.uninitialized family.missing family.escaped family.prefixMatches family.profiles
  intro scope id lowered certified
  exact RecursiveNamedExpressionTreeBounds.preserves_at_with_literals_with_for (fuel := fuel)
    F extension (identity_faithful indexed) (observations profile) (runtimeViews profile) evidence unique uninitialized missing
    Calls P (CompatibleExpressionLiteralRuntime.preserves F program context evidence valid.ledger valid.runtime unique faults)
    budget size within (by
      intro certificate child childWithin children
      apply RecursiveNamedExpressionTreeBounds.head_preserves_at_with_calls
        F extension (identity_faithful indexed) (observations profile) (runtimeViews profile) evidence unique missing
        P CallableIndexedLambdaNestedFormationEntries.transport Calls budget child childWithin children
      intro scope id lowered receipt
      cases receipt with
      | lambda leaf =>
        exact preserves_leaf_at profile complete globals slots sameSource child unique ⟨leaf⟩
      | existing receipt =>
        exact CallableIndexedLambdaNamedRuntimeBodyMeaning.head_preserves_for F P
          CallableIndexedLambdaNestedFormationEntries.transport CallableIndexedLambdaNestedFormationEntries.catalog
          (fun _ => fun _ => True) (fun _ _ => by unfold RecursiveNamedCatalogInvocationBounds.BodyAuthorization; intros; trivial)
          budget child childWithin valid.runtime.idsUnique unique owners
          (fun smaller strict => children smaller (Nat.le_of_lt strict))
          (by
            intro header member smaller _ arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after _ trace
            exact bodies smaller header member entry trace) receipt) certified

include complete globals slots extension family valid sameSource uninitialized missing in
/-- Native reflection uses the original ordered children and obtains an
independent source grade. Formation compares only the same pure native leaf. -/
theorem expressions_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry F) program context evidence source Cert faults P := by
  have bodies := RecursiveNamedCatalogMutualMeaning.reflects_at_runtime_evidence
    F extension (identity_faithful indexed) (observations profile) (runtimeViews profile)
    family.uninitialized family.missing family.escaped family.prefixMatches family.profiles
  intro scope id lowered certified
  exact RecursiveNamedExpressionTreeBounds.reflects_at_with_literals_with_for (fuel := fuel)
    F extension (identity_faithful indexed) (observations profile) (runtimeViews profile) evidence uninitialized missing
    Calls P (CompatibleExpressionLiteralRuntime.reflects F program context evidence valid.ledger valid.runtime source faults)
    budget size within (by
      intro certificate child childWithin children
      apply RecursiveNamedExpressionTreeBounds.head_reflects_at_with_calls
        F extension (identity_faithful indexed) (observations profile) (runtimeViews profile) evidence missing
        P CallableIndexedLambdaNestedFormationEntries.transport Calls budget child childWithin children
      intro scope id lowered receipt
      cases receipt with
      | lambda leaf => exact reflects_leaf_at profile complete globals slots sameSource child ⟨leaf⟩
      | existing receipt =>
        exact CallableIndexedLambdaNamedRuntimeBodyMeaning.head_reflects_for F P
          CallableIndexedLambdaNestedFormationEntries.transport CallableIndexedLambdaNestedFormationEntries.catalog
          (fun _ => fun _ => True) (fun _ _ => by unfold RecursiveNamedCatalogInvocationBounds.BodyAuthorization; intros; trivial)
          budget child childWithin (fun smaller strict => children smaller (Nat.le_of_lt strict))
          (by
            intro header member smaller _ arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after _ trace
            exact bodies smaller header member entry trace) receipt) certified
end Expressions

section Body
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code indexed function outerScope administrative)

abbrev Body (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) (rank : Nat)
    (code : Code indexed function outerScope administrative) :=
  BodyReceipt (LowerSupport headers caller registry faults rank) rank caller headers code registry faults

/-- The actual compiler view supplies the canonical Tree through the shared
transport. The same dictionary and every ordered child code remain in the receipt. -/
theorem Body.of_tree
    (sameSource : function.source = CallableIndexedNamedGeneration.source caller.named)
    (sameCompilation : code.compilation = CallableIndexedNamedGeneration.context indexed caller.named)
    (sameActive : code.active = []) (sameAdministrative : administrative = nativePrefix caller)
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function) (readFuel : Nat) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy)
    {changed : List ExpressionId}
    (edited : CallableLambdaViewEdits.LocalView function.source code.view changed)
    (avoids : CallableLambdaBodyReachability.Avoids function.source (function.body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique function.source)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow)
    {tree : GenericImperativeMatch.Tree indexed.layouts code.compilation.owner code.active
      indexed.ancestry.layout.frame indexed.base.globals.length code.allocationError values code.view
      (Nodes code.view)
      (fun context => CallableIndexedLambdaNestedRuntimeCertificates.Certificates
        (LowerSupport headers caller registry faults rank) rank caller headers code.compilation readFuel code.view context
        function.evidence code.compilation.solvedRequirements code.reasonAt)
      indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow}
    (sites : tree.CatalogSites .reachable registry faults) :
    ∃ body : Body headers caller registry faults rank code,
      body.body.toContext = inputs ∧ body.body.readFuel = readFuel ∧ body.body.policy = policy ∧ body.body.flow = flow := by
  obtain ⟨body, sameContext, sameFuel, samePolicy, sameFlow, _⟩ :=
    CallableIndexedLambdaStaticBodySupport.BodyWith.of_tree
      (expressionSyntax := Nodes)
      (certificates := fun fuel source context => CallableIndexedLambdaNestedRuntimeCertificates.Certificates
        (LowerSupport headers caller registry faults rank) rank caller headers code.compilation fuel source context
        function.evidence code.compilation.solvedRequirements code.reasonAt)
      code inputs frame readFuel policy callback edited avoids unique sameLedger
      (fun id reached receipt => by
        obtain ⟨node, found⟩ := receipt
        exact ⟨node, (CallableLambdaBodyReachability.expression_lookup edited avoids reached).trans found⟩)
      (fun _ _ _ _ reached receipt => CallableIndexedLambdaNestedRuntimeCertificates.transport
        ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
        (avoids.view edited.metadata) receipt (reached.metadata edited.metadata))
      projection generated sites
  exact ⟨⟨sameSource, sameCompilation, sameActive, sameAdministrative, body⟩, sameContext, sameFuel, samePolicy, sameFlow⟩

def Body.toKernel (body : Body headers caller registry faults rank code) :
    CallableRuntimeBodyKernel.BodyFor indexed.layouts code.compilation.owner code.active
      indexed.ancestry.layout.frame indexed.base.globals.length code.allocationError values function
      (Nodes function.source)
      (fun context => CallableIndexedLambdaNestedRuntimeCertificates.Certificates
        (LowerSupport headers caller registry faults rank) rank caller headers code.compilation body.body.readFuel function.source context
        function.evidence code.compilation.solvedRequirements code.reasonAt)
      (fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
      .reachable (CallableIndexedAmbient.ambientDefinitions indexed)
      administrative body.body.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      code.receipt.resultCore code.receipt.body code.compilation.internalReason code.compilation.internalReason registry faults :=
  { flow := body.body.flow, tree := body.body.tree, sites := body.body.sites, initialValid := body.body.valid,
    projection := body.body.projection, unique := body.body.unique, emitted := body.body.emitted }

end Body

section Execution
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code indexed function outerScope administrative)
  (body : Body headers caller registry faults rank code)
  (profile : values.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (globals : caller.globals = indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations 0
    (model headers locations registry faults profile) registry faults)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
local notation "F" => model headers locations registry faults profile
local notation "P" => CallableIndexedLambdaNestedFormationEntries.protectedEntry caller headers locations 0 1
include body complete globals slots extension owners family uninitialized missing escaped in
/-- The source grade is the original parent-supplied body grade. Named callee
meaning is closed by CatalogFamily's static profiles and the existing mutual
induction; the lambda ghost remains in its independent source entry. -/
theorem Body.preserves_sized (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      environment canonical indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry F mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope).length +
      1 + indexed.base.globals.length]? = some (.cellRef indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : P
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      mapping world before store canonical)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.body.context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.receipt.body.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry F)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      P
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
        finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context,
      CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedHeaderContracts.AtMost budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry F) program context function.evidence function.source
        (CallableIndexedLambdaNestedRuntimeCertificates.Certificates
          (LowerSupport headers caller registry faults rank) rank caller headers code.compilation
          body.body.readFuel function.source context function.evidence code.compilation.solvedRequirements code.reasonAt) faults (P)) := by
    intro context valid child within scope id lowered certified
    apply expressions_preserves_at (rank := rank) (fuel := body.body.readFuel) (solved := code.compilation.solvedRequirements)
      profile complete globals slots extension family valid body.source body.body.unique owners uninitialized missing budget child within
    simpa only [body.compilation] using certified
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata, _, entry⟩ :=
    body.toKernel.preserves_sized F rfl (CallableIndexedAmbient.frame_registered indexed) extension program
      (identity_faithful indexed) (observations profile) escaped
      CallableIndexedLambdaNestedFormationEntries.transport CallableIndexedLambdaNestedFormationEntries.binds
      (fun valid extended => valid.extend extended) (fun valid => valid) budget size within expressions
      environments heaps locals agrees typed reference read unmapped installed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata, entry⟩

include body complete globals slots extension family uninitialized missing escaped in
/-- Reflection consumes the original native body witness. No source execution
or preservation theorem is used to obtain its independent source grade. -/
theorem Body.reflects_sized (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      environment canonical indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry F mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope).length +
      1 + indexed.base.globals.length]? = some (.cellRef indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : P
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.receipt.body.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.body.context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry F)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      P
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
        finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context,
      CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry F) program context function.evidence function.source
        (CallableIndexedLambdaNestedRuntimeCertificates.Certificates
          (LowerSupport headers caller registry faults rank) rank caller headers code.compilation
          body.body.readFuel function.source context function.evidence code.compilation.solvedRequirements code.reasonAt) faults (P)) := by
    intro context valid child smaller scope id lowered certified
    apply expressions_reflects_at (rank := rank) (fuel := body.body.readFuel) (solved := code.compilation.solvedRequirements)
      profile complete globals slots extension family valid body.source uninitialized missing budget child (Nat.le_of_lt smaller)
    simpa only [body.compilation] using certified
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, _, entry⟩ :=
    body.toKernel.reflects_sized F rfl (CallableIndexedAmbient.frame_registered indexed) extension program
      (identity_faithful indexed) (observations profile) (runtimeViews profile) escaped
      CallableIndexedLambdaNestedFormationEntries.transport CallableIndexedLambdaNestedFormationEntries.binds
      (fun valid extended => valid.extend extended) (fun valid => valid) budget size within expressions
      environments heaps locals agrees typed reference read unmapped installed evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, entry⟩
end Execution

section ReachedEntry
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code indexed function outerScope administrative} {history : History code}
  (body : Body headers caller registry faults rank code)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {environment : Dynamic.Environment} {canonical : Environment} {before : Dynamic.Heap} {store : Store}

/-- The actual lambda ghost and full carried metadata are retained. Only the
bundle tag uses the original reached environment's independent type relation. -/
def Body.entry_of_source
    (installed : CallableIndexedLambdaCatalogEntries.SourceEntry code history headers locations 0
      code.compilation.administrativePrefix scope mapping world before store canonical)
    (metadata : history.metadata = CallableIndexedNamedGeneration.state caller.named)
    (globals : caller.globals = indexed.base.globals.length)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical indexed.layouts.definitions) :
    CallableIndexedLambdaNestedFormationEntries.Entry caller headers locations 0 1 scope mapping world before store canonical := by
  have samePrefix : code.compilation.administrativePrefix = 1 := by
    rw [body.compilation]
    rfl
  have same : CallableIndexedLambdaCatalogEntries.SourceEntry code history headers locations 0 1
      scope mapping world before store canonical := by simpa only [samePrefix] using installed
  exact CallableIndexedLambdaNestedFormationEntries.Entry.of_lambda same metadata
    (CallableIndexedLambdaNestedFormationEntries.bundle_of_environment related (by rw [body.administrative]; rfl)) globals
end ReachedEntry
end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeBodyMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewInvocation
/-! Ordinary lambda entry uses the formation receipt's actual capture and
code, installs its authenticated lexical state, and constructs the parameter
prefix. The concrete body certificate is static; it contains no body run. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

structure Body {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program) where
  frame : Dynamic.ClosureFrame program function
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  kinds : ∀ binding ∈ code.receipt.loweredParameters,
    function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false
  referenceIndex : code.referenceIndex = scope.length + 1 + prepared.base.globals.length
  readFuel : Nat
  policy : SourceCoreLoops.Policy
  bodyFuel : Nat
  certificate : BuiltinNamedBody.Certificate prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError readFuel values
    function.source context code.compilation.solvedRequirements code.reasonAt
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body function.resultType code.receipt.resultCore policy bodyFuel code.compilation.internalReason
    code.compilation.internalReason code.receipt.body
  valid : CompatibleExpressionLiterals.ContextValid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source

/-- The original compiler certificate still supplies its canonical static
body receipt. The public Body record and its original accepted field are retained. -/
def Body.semantic {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {code : Code prepared function scope administrative} {program : Program}
    (body : Body code program) : CallableIndexedLambdaSemanticInvocation.Body code program :=
  { context := body.context, types := body.types, extended := body.extended,
    kinds := body.kinds, referenceIndex := body.referenceIndex, frame := body.frame,
    readFuel := body.readFuel, certificate := body.certificate.semantic, valid := body.valid, unique := body.unique }

abbrev parameters := @CallableIndexedLambdaEntryPrefix.parameters
abbrev prefix_accepted := @CallableIndexedLambdaEntryPrefix.prefix_accepted
abbrev bodyEmbedding := CallableIndexedLambdaEntryPrefix.bodyEmbedding

abbrev Entry {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
    (registry : SourceCoreRawMetadata.Registry) (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location) (current : NativeFrame) (currentGhost : GhostFrame) :=
  CallableIndexedLambdaSemanticInvocation.Entry captured code history body.semantic profile registry arguments nativeArguments
    before store location current currentGhost

/- Fully qualified field access remains available for the original Entry. -/
section EntryFields
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment} {captured : Captures prepared mapping world scope function.captured capturedActual}
  {code : Code prepared function scope captured.administrative} {history : History code}
  {program : Program} {body : Body code program} {profile : values.checked.catalog.callableContracts = true}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

abbrev Entry.next (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.next entry
abbrev Entry.nextHistory (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.nextHistory entry
abbrev Entry.actual (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.actual entry
abbrev Entry.actualContext (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.actualContext entry
abbrev Entry.embedding (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.embedding entry
abbrev Entry.entry (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.entry entry
abbrev Entry.wrap (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) {result : Value} {bodyStore : Store} :=
  CallableIndexedLambdaEntryPrefix.Entry.wrap (result := result) (bodyStore := bodyStore) entry
abbrev Entry.unwrap (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) {result : Value} {finalStore : Store} :=
  CallableIndexedLambdaEntryPrefix.Entry.unwrap (result := result) (finalStore := finalStore) entry
abbrev Entry.unmapped (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.unmapped entry
abbrev Entry.referenceTyped (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.referenceTyped entry
abbrev Entry.currentHistory (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.currentHistory entry
abbrev Entry.currentRead (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.currentRead entry
end EntryFields

/-- Every native prefix step is derived from its actual compiler receipt.
The caller token and lexical token have independent carried histories. -/
theorem entry_exists {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
      mapping world code.receipt.loweredParameters arguments nativeArguments)
    {before : Dynamic.Heap} {store : Store} {location : Location}
    {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
    (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
    (unmapped : location ∉ mapping)
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true) :
    Nonempty (Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost) := by
  exact CallableIndexedLambdaSemanticInvocation.entry_exists captured code history body.semantic profile
    represented heaps locals reference read currentCarried unmapped allowed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewCalls
/-! Ordinary closure calls combine concrete lexical builtin bodies with the
actual indexed frame and marked parameter prefix. The lambda's generation
receipt and caller history remain semantic inputs. Completed native execution
constructs the independent source call; no body execution is an input. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaViewInvocation
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

abbrev represented_closure := @CallableIndexedLambdaCalls.represented_closure
abbrev applyPayload := CallableIndexedLambdaCalls.applyPayload

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))

include extension uninitialized missing in
theorem Entry.preserves
    (entry : Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost)
    {copies environment : Dynamic.Environment} {copied bound after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact CallableIndexedLambdaSemanticCalls.Entry.preserves captured code history body.semantic profile extension uninitialized missing entry copy allocated trace

include extension uninitialized missing in
theorem Entry.reflects
    (entry : Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost)
    {result : Value} {finalStore : Store}
    (evaluated : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result finalStore) :
    ∃ copies copied environment bound outcome after finalMap finalWorld,
      Dynamic.EnvironmentCopies function.source function.captured before copies copied ∧
      Dynamic.BindersAllocate copies copied function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function body.context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact CallableIndexedLambdaSemanticCalls.Entry.reflects captured code history body.semantic profile extension uninitialized missing entry evaluated

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem reflects {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {result : Value} {finalStore : Store}
    (evaluated : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact CallableIndexedLambdaSemanticCalls.reflects captured code history body.semantic profile extension represented heaps locals reference read currentCarried unmapped allowed uninitialized missing evaluated

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem preserves {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact CallableIndexedLambdaSemanticCalls.preserves captured code history body.semantic profile extension represented heaps locals reference read currentCarried unmapped allowed uninitialized missing executed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewCalls
end
