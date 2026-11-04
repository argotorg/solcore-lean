import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.AcceptedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalDirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedImperative
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedBodies

/-!
# Accepted bodies: direct calls

Adds direct calls at expression roots to the expression closure, and closes a family of
rows by one strong induction on the grade.

Main declarations:
- `CellAwareInvocationAcceptedDirectCalls.preserves` and
  `CellAwareInvocationAcceptedDirectCalls.reflects`, the direct-call head;
- `CellAwareInvocationAcceptedCallTrees.CallSubset` and
  `CellAwareInvocationAcceptedCallTrees.CallTree`, the extended subset and its trees;
- `CellAwareInvocationAcceptedCallExpressions.ClosedCalls` and
  `CellAwareInvocationAcceptedCallExpressions.Ports`, its premises;
- `CellAwareInvocationAcceptedNamedApplication.preserves` and
  `CellAwareInvocationAcceptedNamedApplication.reflects`, applying a named row;
- `CellAwareInvocationAcceptedCallFamily.Row`,
  `CellAwareInvocationAcceptedCallFamily.preserves` and
  `CellAwareInvocationAcceptedCallFamily.reflects`, the family closure;
- `CellAwareInvocationAcceptedCallAuthority.ports`, call authority from an inventory.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectSites
/-! Direct declaration calls of named-row bodies as compiler sites. A direct
site has no coercions or requirements, is not a generalized initializer,
selects a monomorphic declaration and lies in a row without evidence
assumptions, so the named policy's special callback
declines it and its read policy is the compatible reader, as for the ordinary
sites of `CellAwareNamedExpressionSyntax.Site`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectSites
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

/-- A direct declaration call of a named-row body. -/
structure DirectSite {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) (callee : ExpressionId) (arguments : List ExpressionId)
    (instantiation : DeclarationInstantiation) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : node.form = .call callee arguments (.declaration instantiation)
  coercions : node.coercions = []
  requirements : node.requirements = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  monomorphic : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Monomorphic instantiation
  assumptions : named.specialized.assumptions = []

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id callee : ExpressionId}
  {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}

theorem contextual (site : DirectSite prepared named source id callee arguments instantiation) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, site.found, site.form]

private theorem evidence_none (site : DirectSite prepared named source id callee arguments instantiation)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  simp [SourceCoreEvidence.lowerWithProjector, site.found, site.form, site.requirements, site.coercions,
    site.assumptions]

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- The named policy's special callback declines a direct site. -/
theorem special (site : DirectSite prepared named source id callee arguments instantiation) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, contextual site, bind, Except.bind, pure, Except.pure, site.found,
    site.notInitializer, Option.filter_none]
  rw [evidence_none site child budget scope reasonAt]
  simp [site.form]

theorem read (site : DirectSite prepared named source id callee arguments instantiation) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectSites
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallTrees
/-! Direct calls at the expression roots of named-row bodies. `CallSubset`
adds to the first subset the direct calls whose arguments are first-subset
sites and whose instantiation the caller's family admits (`called`).
`CallTree` keeps, at such a call, the compiler's direct-call receipt at the
body's compile context, the authority of the selected header and the subset
receipt tree of every argument. A call nested inside another expression is
not covered yet. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallTrees
open Core Frontend SourceInference DataPatternValues
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedExpressionSyntax (Site)
open CellAwareInvocationAcceptedExpressionTrees (Subset Tree)
open CellAwareInvocationAcceptedDirectSites (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt Monomorphic)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port)

/-- Expression roots of the extended subset: first-subset sites, and direct
calls whose arguments are first-subset sites and whose instantiation the
caller's family admits. -/
inductive CallSubset {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (called : DeclarationInstantiation → Prop) : ExpressionId → Prop where
  | subset {id} (subset : Subset prepared named source id) : CallSubset prepared named source called id
  | call {id callee ids instantiation} (site : DirectSite prepared named source id callee ids instantiation)
      (selected : called instantiation) (arguments : ∀ argument ∈ ids, Subset prepared named source argument) :
      CallSubset prepared named source called id

/-- Static receipts at extended roots. The certificate of the argument
sequence is the first-subset receipt tree at every scope. -/
inductive CallTree (whole : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram)))
    (called : DeclarationInstantiation → Prop) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (solved : List SolvedRequirement) (source : TypedSource)
    (sourceContext : SourceSemantics.Context) (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | tree {id lowered}
      (tree : Tree whole.compatible.checked readFuel solved source sourceContext reasonAt scope id lowered) :
      CallTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered
  | call {policy body fuel id callee ids instantiation lowered types}
      (receipt : Receipt policy body fuel compilation (.initial whole.compatible.checked) source scope id callee ids
        instantiation reasonAt lowered)
      (port : Port receipt headers)
      (requirements : receipt.node.requirements = [])
      (monomorphic : Monomorphic instantiation)
      (selected : called instantiation)
      (arguments : DataExpressionSequence.Tree source
        (fun current child code => Tree whole.compatible.checked readFuel solved source sourceContext reasonAt
          current child code)
        scope ids types receipt.codes) :
      CallTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered

section Embedding
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource}

theorem subset_found {id : ExpressionId} (subset : Subset prepared named source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases subset with
  | literal site _ | read site _ | unary site _ _ | binary site _ _ _ | conditional site _ _ _ _
  | group site _ _ | pair site _ _ _ => exact ⟨_, site.found⟩

end Embedding

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {called : DeclarationInstantiation → Prop}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : Compilation whole.indexed named diagnostics code) (rootFuel : Nat)
  {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}

private theorem special {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    (site : DirectSite whole.indexed named source id callee ids instantiation) :
    ∀ child budget, (match (namedPolicy generation rootFuel).lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context whole.indexed named) child budget source scope id reasonAt) = .ok none :=
  fun child budget => CellAwareInvocationAcceptedDirectSites.special generation site rootFuel child budget scope reasonAt

private theorem argument_rel {lower : ExpressionId → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr}
    {relation : ExpressionId → SourceCoreBasic.LoweredExpr → Prop} :
    ∀ {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr},
      (∀ argument ∈ ids, ∀ {lowered}, lower argument = .ok lowered → relation argument lowered) →
      ids.mapM lower = .ok codes → ListRel relation ids codes := by
  intro ids
  induction ids with
  | nil =>
    intro codes _ generated
    simp at generated
    subst codes
    exact .nil
  | cons argument rest ih =>
    intro codes each generated
    cases head : lower argument with
    | error reason => simp [List.mapM_cons, head, bind, Except.bind] at generated
    | ok lowered =>
      cases tail : rest.mapM lower with
      | error reason => simp [List.mapM_cons, head, tail, bind, Except.bind] at generated
      | ok restCodes =>
        simp only [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at generated
        subst codes
        exact .cons (each argument List.mem_cons_self head)
          (ih (fun other member => each other (List.mem_cons_of_mem _ member)) tail)

/-- The accepted named compiler yields the extended receipt tree at every
extended root. A call's authority is the input `ports`, as the older direct
families take theirs. -/
theorem of_call_subset {id : ExpressionId}
    (subset : CallSubset whole.indexed named source called id)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy generation rootFuel)
      (namedLowerBody generation) fuel (context whole.indexed named) source scope id reasonAt = .ok lowered)
    (ports : ∀ {fuel : Nat} {callScope : SourceCoreLocalCell.Scope} {callId callee : ExpressionId}
      {ids : List ExpressionId} {instantiation : DeclarationInstantiation} {callCode : SourceCoreBasic.LoweredExpr}
      (receipt : Receipt (namedPolicy generation rootFuel) (namedLowerBody generation) fuel
        (context whole.indexed named) (.initial whole.compatible.checked) source callScope callId callee ids
        instantiation reasonAt callCode),
      Nonempty (Port receipt headers)) :
    CallTree whole headers called (context whole.indexed named) whole.indexed.fuel
      (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope id lowered := by
  cases subset with
  | subset subset =>
    exact .tree (CellAwareInvocationAcceptedExpressionTrees.of_subset generation rootFuel subset unique declarations
      found typed accepted)
  | @call callee ids instantiation site selected arguments =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedDirectCallCertificates.of_supported
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation) (fuel := fuel)
        (compilation := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found site.form
        ((site.monomorphic.ordinary _).supported) (special generation rootFuel site)
        (CellAwareInvocationAcceptedDirectSites.read generation site rootFuel) accepted
      obtain ⟨port⟩ := ports receipt
      have nodeEq : receipt.node = site.node := Option.some.inj (receipt.metadata.found.symm.trans site.found)
      obtain ⟨_types, _calleeValid, _application, typing⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique site.found site.form
          site.coercions typed
      have relation := argument_rel
        (relation := fun argument lowered => ∃ node, source.lookupExpression? argument = some node ∧
          Tree whole.compatible.checked whole.indexed.fuel (context whole.indexed named).solvedRequirements source
            sourceContext reasonAt scope argument lowered)
        (fun argument member {lowered} generated => by
          obtain ⟨argumentNode, argumentFound⟩ := subset_found (arguments argument member)
          exact ⟨argumentNode, argumentFound,
            CellAwareInvocationAcceptedExpressionTrees.of_subset generation rootFuel (arguments argument member)
              unique declarations argumentFound
              (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member
                argumentFound) generated⟩)
        receipt.generated
      obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children relation
      exact .call receipt port (nodeEq ▸ site.requirements) site.monomorphic selected sequence

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallTrees
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectCalls
/-! Direct declaration calls at accepted cell-aware sites. The argument vector,
the issued global cell read and the restoration of the caller carrier are
proved here from the actual compiler receipt. Applying the selected named
closure is an explicit input below the Source (or native) grade of the call:
the size induction across bodies discharges it from the callee's own accepted
body. As in the plain-heap direct head, the caller carrier retains every
ordinary global slot, and every reached caller retains the physical cache. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedSourceAt)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port EvidenceAt)
open CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds (Point)
universe u

section Application
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))

/-- Applying the issued closure of `header` to packed arguments from a reached
caller pool with its physical capture and cache: callee entry, body and the
restoration of the same pool over accepted cells, with the Source grade of the
application. This is the cross-body input of a direct-call site. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope mapping world before store canonical} (owner : OwnedKey keys)
    (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store),
    CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store → header ∈ headers → StableRows caller →
  ∀ {context arguments payloads}, Dynamic.TypeContextSupports header.context context →
    Dynamic.HeapWellTyped header.function.context before →
    Dynamic.ValuesHaveTypes header.function.context before arguments header.types →
    CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
  ∀ {rawD function}, NamedSourceAt header rawD function →
  ∀ {invocation outcome after},
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) registry size invocation context
      before (.global function) arguments outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: capture.named.captured) store
        (header.code.rename capture.named.embedding.lift) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned

/-- Native completion of the same issued closure from the same caller pool
reconstructs an independent Source application and the restored pool. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope mapping world before store canonical} (owner : OwnedKey keys)
    (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store),
    CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store → header ∈ headers → StableRows caller →
  ∀ {context arguments payloads}, Dynamic.TypeContextSupports header.context context →
    Dynamic.HeapWellTyped header.function.context before →
    Dynamic.ValuesHaveTypes header.function.context before arguments header.types →
    CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
  ∀ {rawD function}, NamedSourceAt header rawD function →
  ∀ {invocation value finalStore},
    EvaluationSize size (DataPatternValues.packValues payloads :: capture.named.captured) store
      (header.code.rename capture.named.embedding.lift) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) registry sourceSize invocation
        context before (.global function) arguments outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget →
    PreservesAt (attachment := attachment) (headers := headers) (keys := keys) model registry faults header size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget →
    ReflectsAt (attachment := attachment) (headers := headers) (keys := keys) model registry faults header size

end Application

section Head
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id callee ids instantiation reasonAt lowered)
  (port : Port receipt headers)
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun current => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix current.scope current.canonical) callerProtocol)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (cache : ∀ {current}, callerProtocol.State current →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled current.mapping current.store)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation} (index : ActualBodyInvocation.Index compiled bodyRelation)
  (registry : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)

private theorem result_type : lowered.type = port.header.output :=
  receipt.result.symm.trans ((congrArg SourceCoreCalls.Signature.resultType port.signature).symm.trans
    port.header.resultType)

private theorem parameter_type : port.header.named.signature.parameterType =
    (SourceCoreCalls.packArguments receipt.codes).type := by
  rw [port.signature]
  exact receipt.parameter

include owner receipt port evidenceAt callerBridge keyPhysical cache unique wellFormed runtime covers in
/-- A direct call at an accepted site preserves its staged execution when the
selected callee's application does below the same Source grade. Argument
faults stop before the global read, as in the original helper. -/
theorem preserves {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      callerBridge.forgetSlots context model index registry invocation children faults size)
    (application : PreservesBelow (attachment := attachment) (headers := headers) (keys := keys)
      model registry faults port.header size) :
    CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) callerBridge.forgetSlots context model
      index registry invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, applicationValid, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
    wellFormed runtime.signatures applicationValid
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have originalTrace := trace
  rcases CallableIndexedOwnedPreparedStagedDirectSourceInversion.children
      unique receipt.metadata.found receipt.form receipt.metadata.coercions trace with
    ⟨sequenceSize, invocationSize, argumentsHeap, sources, name, evidence, sameSize,
      _calleeOccurrence, _valid, sourceTrace, produced, invoked⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    have invocationBelow : invocationSize < size := by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    obtain ⟨values, middleStore, middleMap, middleWorld, argumentsEvaluated, represented, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentEffect, reached, related, post⟩ :=
      CellAwareInvocationExpressionSequence.preserves_values callerBridge.forgetSlots size sequence unique
        orderedTyping childMeaning environments heaps locals agrees actualTyped initial admitted authority physical
        frameOwner ownerFrame sourceTrace argumentsWithin
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      CallableIndexedOwnedPreparedStagedDirectArgumentRows.at_successful_arguments receipt port evidenceAt
        wellFormed runtime covers locals admitted.heap calleeValid applicationValid sourceTrace represented typing
    have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt produced
    rw [sourceEq] at invoked
    obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
      port.prepared port.aligned port.member keyPhysical (cache reached) middleHeaps.runtime_hasTypes
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyEffect, finalState, bodyRelated⟩ :=
      application invocationSize invocationBelow owner (callerBridge.pool reached) capture (cache reached)
        port.member post.rows supports headerHeap headerArguments parameters middleHeaps port.sourceAt invoked
    have selected := OptionalCell.read_success compilation.internalReason
      (show Evaluates (DataPatternValues.packValues values :: actual) middleStore
        (.var (ξ (current.length + compilation.administrativePrefix + port.header.slot) + 1))
        (.cellRef (OptionalCell.cellType port.header.named.signature.functionType)
          (owner.key.locations port.header)) middleStore from
        .var (agrees (callerBridge.slots initial port.header port.member))) capture.read
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, argumentEffect.trans bodyEffect,
      returned, returnedRelated, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot]
      exact SourceCoreCalls.call_success argumentsEvaluated selected bodyEvaluated
    · simpa only [rows.2, nativeResult] using result
    · exact SelectedStagedPostAdmission.after_expression_sized initial returned admitted
        (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) runtime covers locals typed
        originalTrace (argumentFrame.trans bodyFrame)
  · subst outcomeEq
    have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, _post⟩ :=
      CellAwareInvocationExpressionSequence.preserves_fault callerBridge.forgetSlots size sequence unique
        orderedTyping childMeaning environments heaps locals agrees actualTyped initial admitted authority physical
        frameOwner ownerFrame sourceTrace argumentsWithin
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename]
      simpa only [receipt.result] using SourceCoreCalls.call_argument_failure
        (signature := receipt.signature)
        (index := ξ (current.length + compilation.administrativePrefix + receipt.index))
        (internalReason := compilation.internalReason) (receipt.parameter.symm ▸ argumentsEvaluated)
    · exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted
        (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) runtime covers locals typed
        originalTrace frame

include owner receipt port evidenceAt callerBridge keyPhysical cache unique wellFormed runtime covers in
/-- Native completion of a direct call at an accepted site reconstructs its
staged execution when the selected callee's application does below the native
grade of the call. -/
theorem reflects {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      callerBridge.forgetSlots context model index registry invocation children faults size)
    (application : ReflectsBelow (attachment := attachment) (headers := headers) (keys := keys)
      model registry faults port.header size) :
    CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) callerBridge.forgetSlots context model
      index registry invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, applicationValid, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
    wellFormed runtime.signatures applicationValid
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.declaration instantiation))
      receipt.node.requirements :=
    ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, receipt.form, rfl, receipt.metadata.coercions⟩
  obtain ⟨name, calleeOccurrence, valid⟩ :=
    CallableIndexedOwnedPreparedStagedDirectArgumentRows.callee_receipt receipt runtime calleeValid
  rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, middleMap, middleWorld, sourceTrace, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentEffect, reached, related, post⟩ :=
    CellAwareInvocationExpressionSequence.reflects callerBridge.forgetSlots size sequence unique orderedTyping
      childMeaning environments heaps locals agrees actualTyped initial admitted authority physical frameOwner
      ownerFrame argumentEvaluation smaller
  cases represented with
  | fault matched =>
    have evaluated := SourceCoreCalls.call_argument_failure
      (signature := port.header.named.signature)
      (index := ξ (current.length + compilation.administrativePrefix + port.header.slot))
      (internalReason := compilation.internalReason) (parameter.symm ▸ argumentEvaluation.sound)
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
    have trace := Staging.Recursive.Size.Expression.directArgumentsFault occurrence calleeOccurrence sourceTrace
    refine ⟨_, _, argumentsHeap, middleMap, middleWorld, trace, ?_, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentEffect, reached, related, ?_⟩
    · rw [← receipt.result, ← port.signature]
      exact .fault matched
    · exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted
        (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) runtime covers locals typed
        trace argumentFrame
  | @values sources values payloads =>
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      CallableIndexedOwnedPreparedStagedDirectArgumentRows.at_successful_arguments receipt port evidenceAt
        wellFormed runtime covers locals admitted.heap calleeValid applicationValid sourceTrace payloads typing
    obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
      port.prepared port.aligned port.member keyPhysical (cache reached) middleHeaps.runtime_hasTypes
    obtain ⟨bodySize, bodySmaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
      argumentEvaluation.sound (agrees (callerBridge.slots initial port.header port.member)) capture.read completed
    obtain ⟨invocationSize, outcome, after, finalMap, finalWorld, invoked, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyEffect, finalState, bodyRelated⟩ :=
      application bodySize bodySmaller owner (callerBridge.pool reached) capture (cache reached) port.member
        post.rows supports headerHeap headerArguments parameters middleHeaps port.sourceAt bodyEvaluation
    have produced := evidenceAt.produces
    have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt produced
    rw [← sourceEq] at invoked
    have trace := Staging.Recursive.Size.Expression.directApplied occurrence calleeOccurrence valid sourceTrace
      produced invoked
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, argumentEffect.trans bodyEffect,
      returned, returnedRelated, ?_⟩
    · simpa only [rows.2, nativeResult] using result
    · exact SelectedStagedPostAdmission.after_expression_sized initial returned admitted
        (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) runtime covers locals typed
        trace (argumentFrame.trans bodyFrame)

end Head

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectCalls
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallBounds
/-! Meaning of the extended receipt tree. First-subset roots use the existing
structural bounds; a direct call goes through the direct-call head, with its
arguments from the subset bounds and its evidence from the call's empty
requirements. The application of each admitted callee header below the grade
is the input that the row lemma supplies. The caller carrier retains the global
slots at the body's administrative prefix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CellAwareInvocationExpressionBounds
open CellAwareInvocationAcceptedExpressionTrees (Tree)
open CellAwareInvocationAcceptedCallTrees (CallTree)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds (Point)
universe u

private theorem tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {stored : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree source certificate scope ids stored codes)
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids types) :
    stored = types := by
  induction tree generalizing types with
  | nil => cases typing; rfl
  | single found _generated =>
    cases typing with
    | cons head tail =>
      cases tail
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact congrArg (fun type => [type]) sourceType
  | cons found _generated tail ih =>
    cases typing with
    | cons head rest =>
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [sourceType, ih rest]

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : OwnedKey keys) {compilation : SourceCoreFunctions.Context}
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun current => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix current.scope current.canonical) callerProtocol)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (cache : ∀ {current}, callerProtocol.State current →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled current.mapping current.store)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, faults (.semantic (.uninitializedLocation location)) (reasonAt id))
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram)
    registry)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  {called : DeclarationInstantiation → Prop}

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions

include callerBridge keyPhysical cache extension sameLedger uninitialized selectedBodies wellFormed runtime covers in
/-- Every extended receipt tree preserves its staged Source execution at
every grade, given the application of every admitted callee header below the
grade. -/
theorem preserves_call_tree {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CallTree compiled headers called compilation readFuel solved invocation.source context reasonAt scope id
      lowered) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
        (keys := keys) valueModel registry faults header size) :
    PreservesAt (attachment := attachment) callerBridge.forgetSlots context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  cases tree with
  | tree tree =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationAcceptedExpressionBounds.preserves_tree callerBridge.forgetSlots functions
      extension sameLedger faults uninitialized selectedBodies runtime covers tree size ⟨rfl, rfl, rfl⟩
  | call receipt port requirements monomorphic selected arguments =>
    intro current child code point node found typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace
    obtain ⟨rfl, rfl, rfl⟩ := point
    cases Option.some.inj (found.symm.trans receipt.metadata.found)
    obtain ⟨_sourceTypes, _calleeValid, application, typing⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
        receipt.form receipt.metadata.coercions typed
    have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
      wellFormed runtime.signatures application
    have stored := tree_types arguments unique typing
    have ordered := rows.1 ▸ stored ▸ arguments
    have childMeaning : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation
        (fun current child code => Tree compiled.compatible.checked readFuel solved invocation.source context reasonAt
          current child code) faults size := by
      intro smaller _ argumentScope argument argumentCode argumentTree
      exact CellAwareInvocationAcceptedExpressionBounds.preserves_tree callerBridge.forgetSlots functions extension
        sameLedger faults uninitialized selectedBodies runtime covers argumentTree smaller ⟨rfl, rfl, rfl⟩
    have evidenceAt := CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence receipt port
      (monomorphic.ordinary _) requirements context invocation.evidence
    exact CellAwareInvocationAcceptedDirectCalls.preserves owner receipt port evidenceAt callerBridge keyPhysical cache
      valueModel index registry faults unique wellFormed runtime covers size ordered childMeaning
      (applications port.header port.member (port.metadata ▸ selected)) ⟨rfl, rfl, rfl⟩ found typed
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace

include callerBridge keyPhysical cache extension sameLedger uninitialized selectedBodies wellFormed runtime covers in
/-- Native completion of every extended receipt tree reconstructs its staged
Source execution, given the native application of every admitted callee header
below the grade. -/
theorem reflects_call_tree {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CallTree compiled headers called compilation readFuel solved invocation.source context reasonAt scope id
      lowered) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
        (keys := keys) valueModel registry faults header size) :
    ReflectsAt (attachment := attachment) callerBridge.forgetSlots context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  cases tree with
  | tree tree =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationAcceptedExpressionBounds.reflects_tree callerBridge.forgetSlots functions
      extension sameLedger faults uninitialized selectedBodies runtime covers tree size ⟨rfl, rfl, rfl⟩
  | call receipt port requirements monomorphic selected arguments =>
    intro current child code point node found typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed
    obtain ⟨rfl, rfl, rfl⟩ := point
    cases Option.some.inj (found.symm.trans receipt.metadata.found)
    obtain ⟨_sourceTypes, _calleeValid, application, typing⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
        receipt.form receipt.metadata.coercions typed
    have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
      wellFormed runtime.signatures application
    have stored := tree_types arguments unique typing
    have ordered := rows.1 ▸ stored ▸ arguments
    have childMeaning : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation
        (fun current child code => Tree compiled.compatible.checked readFuel solved invocation.source context reasonAt
          current child code) faults size := by
      intro smaller _ argumentScope argument argumentCode argumentTree
      exact CellAwareInvocationAcceptedExpressionBounds.reflects_tree callerBridge.forgetSlots functions extension
        sameLedger faults uninitialized selectedBodies runtime covers argumentTree smaller ⟨rfl, rfl, rfl⟩
    have evidenceAt := CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence receipt port
      (monomorphic.ordinary _) requirements context invocation.evidence
    exact CellAwareInvocationAcceptedDirectCalls.reflects owner receipt port evidenceAt callerBridge keyPhysical cache
      valueModel index registry faults unique wellFormed runtime covers size ordered childMeaning
      (applications port.header port.member (port.metadata ▸ selected)) ⟨rfl, rfl, rfl⟩ found typed
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallExpressions
/-! The expression closure with direct calls at the roots of a named-row body.
`ClosedCalls` states that every expression the compiler accepts for the body is
an extended root (`CallSubset`). The receipt of each accepted expression is
extracted from the compiler's own acceptance and closed by the extended bounds;
the inputs are the call authority of the body's call receipts and the
application of every admitted callee header below the budget. The bridge is
the ordinary caller carrier of the slot-retaining protocol. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CellAwareInvocationAcceptedTerminals (children)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)
open CellAwareInvocationAcceptedCallTrees (CallSubset)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (Key whole (Program.ofChecked whole.sourceProgram))}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (called : DeclarationInstantiation → Prop)

/-- The extended expression roots as a predicate on the actual accepted
receipts of the named row. -/
def Accepted (fuel : Nat) : GenericExpressionMeaning.Certificate :=
  fun scope expression lowered => children (rowIndex generation record) fuel scope expression lowered ∧
    CallSubset whole.indexed named (CallableIndexedNamedGeneration.source named) called expression

/-- Every expression the compiler accepts for the named row, at any fuel and
scope, is an extended root. -/
def ClosedCalls : Prop :=
  ∀ fuel scope expression lowered, children (rowIndex generation record) fuel scope expression lowered →
    CallSubset whole.indexed named (CallableIndexedNamedGeneration.source named) called expression

/-- Every direct-call receipt of the named row's compiler selects a header of
the catalog. -/
def Ports : Prop :=
  ∀ {rootFuel fuel : Nat} {scope : SourceCoreLocalCell.Scope} {callId callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation} {callCode : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt (namedPolicy generation rootFuel) (namedLowerBody generation) fuel
      (CallableIndexedNamedGeneration.context whole.indexed named) (.initial whole.compatible.checked)
      (CallableIndexedNamedGeneration.source named) scope callId callee ids instantiation
      (rowIndex generation record).reasonAt callCode),
    Nonempty (Port receipt headers)

variable {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (owner : OwnedKey keys) (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

private theorem reads_lowered {fuel : Nat} {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults) :
    ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead fuel
        (SourceCoreCompatibleValues.Context.initial whole.compatible.checked)
        invocation.source context (rowIndex generation record).reasonAt scope id lowered →
      ∀ location, faults (.semantic (.uninitializedLocation location))
        ((rowIndex generation record).reasonAt id) := by
  intro scope id lowered receipt location
  obtain ⟨certificate, _type, _binding⟩ := receipt
  exact reads id certificate.node certificate.name certificate.binder
    (sourceEq ▸ certificate.metadata.found) certificate.form location

/-- Every accepted extended root of the named row preserves its staged Source
execution at every grade, given the call authority and the application of
every admitted callee header below the grade. -/
theorem preserves (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context
      (rowIndex generation record).source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (rowIndex generation record).compilation.solvedRequirements)
    (ports : Ports (headers := headers) generation record) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True) (headers := headers) (keys := keys) model registry faults
        header size) :
    CellAwareInvocationExpressionBounds.PreservesAt (attachment := fun _ _ _ => True)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots context model (rowIndex generation record) registry
      invocation (Accepted generation record called fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context invocation.source :=
    sourceEq ▸ runtime
  have uninitialized := reads_lowered generation record invocation faults (fuel := whole.indexed.fuel)
    (context := context) sourceEq reads
  intro scope id lowered accepted node found typed mapping world administrative environment canonical
    actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped
    initial admitted authority physical
  obtain ⟨generated, subset⟩ := accepted
  have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
  change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
  | succ rootFuel =>
    rw [GeneralizedLocalInitializerCompilation.named_contextual generation record] at generated
    have unique := sourceRuntime.graph.nodeOccurrencesUnique
    rw [sourceNamed] at unique found typed
    have tree := CellAwareInvocationAcceptedCallTrees.of_call_subset (headers := headers) generation rootFuel subset
      unique physical.declarations found typed generated ports
    rw [← sourceNamed] at tree found typed
    exact CellAwareInvocationAcceptedCallBounds.preserves_call_tree (attachment := fun _ _ _ => True)
      (compilation := CallableIndexedNamedGeneration.context whole.indexed named) owner
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations) keyPhysical
      (fun state => state.physical) functions extension sameLedger faults uninitialized selectedBodies wellFormed
      sourceRuntime covers tree size applications ⟨rfl, rfl, rfl⟩ found typed environments heaps locals agrees
      actualTyped initial admitted authority physical

/-- Every completed native run of an accepted extended root reconstructs an
independent Source grade, outcome and reached heap. -/
theorem reflects (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context
      (rowIndex generation record).source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (rowIndex generation record).compilation.solvedRequirements)
    (ports : Ports (headers := headers) generation record) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True) (headers := headers) (keys := keys) model registry faults
        header size) :
    CellAwareInvocationExpressionBounds.ReflectsAt (attachment := fun _ _ _ => True)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots context model (rowIndex generation record) registry
      invocation (Accepted generation record called fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context invocation.source :=
    sourceEq ▸ runtime
  have uninitialized := reads_lowered generation record invocation faults (fuel := whole.indexed.fuel)
    (context := context) sourceEq reads
  intro scope id lowered accepted node found typed mapping world administrative environment canonical
    actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped
    initial admitted authority physical
  obtain ⟨generated, subset⟩ := accepted
  have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
  change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
  | succ rootFuel =>
    rw [GeneralizedLocalInitializerCompilation.named_contextual generation record] at generated
    have unique := sourceRuntime.graph.nodeOccurrencesUnique
    rw [sourceNamed] at unique found typed
    have tree := CellAwareInvocationAcceptedCallTrees.of_call_subset (headers := headers) generation rootFuel subset
      unique physical.declarations found typed generated ports
    rw [← sourceNamed] at tree found typed
    exact CellAwareInvocationAcceptedCallBounds.reflects_call_tree (attachment := fun _ _ _ => True)
      (compilation := CallableIndexedNamedGeneration.context whole.indexed named) owner
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations) keyPhysical
      (fun state => state.physical) functions extension sameLedger faults uninitialized selectedBodies wellFormed
      sourceRuntime covers tree size applications ⟨rfl, rfl, rfl⟩ found typed environments heaps locals agrees
      actualTyped initial admitted authority physical

/-- A named row whose accepted expressions are all extended roots discharges
the accepted-expression input of the statement closure on the slot-retaining
protocol at a budget, given the call authority and the application of every
admitted callee header below the budget. -/
theorem expressions (closed : ClosedCalls generation record called) (budget : Nat)
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (ports : Ports (headers := headers) generation record)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True) (headers := headers) (keys := keys) model registry faults
        header budget ∧
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True) (headers := headers) (keys := keys) model registry faults
        header budget) :
    CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True) (receiving := receiving)
      (functions := functions)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots (rowIndex generation record) registry invocation faults budget := by
  intro fuel context runtime covers sameLedger
  refine ⟨?_, ?_⟩
  · intro size smaller scope id lowered generated
    exact preserves generation record called owner keyPhysical registry invocation faults fuel sourceEq extension
      reads selectedBodies wellFormed runtime covers sameLedger ports size
      (fun header member admitted below less => (applications header member admitted).1 below
        (Nat.lt_trans less smaller))
      ⟨generated, closed fuel scope id lowered generated⟩
  · intro size smaller scope id lowered generated
    exact reflects generation record called owner keyPhysical registry invocation faults fuel sourceEq extension
      reads selectedBodies wellFormed runtime covers sameLedger ports size
      (fun header member admitted below less => (applications header member admitted).2 below
        (Nat.lt_trans less smaller))
      ⟨generated, closed fuel scope id lowered generated⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallExpressions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallAuthority
/-! Call authority of a named row's direct calls from a complete inventory. A
direct-call receipt selects a physical global slot; the indexed globals are
the signatures of the indexed functions, and a complete inventory issues a
header for every function index. `of_inventory_at` then supplies the `Port`. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallAuthority
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {inputs : List (Input whole)}
  (rows : Inventory inputs)
  (complete : ∀ {index : Nat} {function : SourceCoreGeneralFunctions.Function},
    whole.indexed.base.functions[index]? = some function →
    ∃ input ∈ inputs, input.prepared.index = index ∧ input.prepared.named = function)
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)

include complete in
/-- Every direct-call receipt of a named row's compiler selects a header of a
complete inventory. -/
theorem ports : CellAwareInvocationAcceptedCallExpressions.Ports (headers := headers rows) generation record := by
  intro rootFuel fuel scope callId callee ids instantiation callCode receipt
  have global : whole.indexed.base.globals[receipt.index]? = some receipt.signature := receipt.global
  rw [CallableIndexedPreparedInventories.cached_globals whole, List.getElem?_map, Option.map_eq_some_iff] at global
  obtain ⟨function, functionFound, signatureEq⟩ := global
  obtain ⟨input, member, slot, namedEq⟩ := complete functionFound
  obtain ⟨issued, retained⟩ := rows.row_at input member
  exact CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory_at receipt rows
    ⟨issued.header, CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory.header_member retained,
      issued.aligned.slot.trans slot,
      (congrArg (·.signature) issued.aligned.named).trans ((congrArg (·.signature) namedEq).trans signatureEq)⟩
    rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallAuthority
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedGlobalSlots
/-! Cell allocation for the canonical caller protocol that retains every
physical global slot and the physical cache. The same genuine cell allocation
of the ordinary pool runs underneath; its new canonical cell shifts the slots
with the scope, and its administrative frame preserves the cache. With the
existing bindings, administrative transport and ordinary caller carrier, this
lets an accepted body keep the `Globals` facts that direct-call sites read. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedGlobalSlots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedHistory
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {catalog : SourceCoreDataCatalog.Catalog}

/-- The ordinary pool's cell allocation with the slot facts carried along. -/
def slotsProducer (callerPrefix : Nat) (model : GenericHeap.CellModel compiled.indexed.layouts.definitions) :
    ProtectedStateTransition.CellAllocation.Producer (catalog := catalog)
      (CallableIndexedOwnedPhysicalCanonicalState.slotsProtocol headers keys callerPrefix)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native =>
    (CallableIndexedOwnedCellAllocationProducer.producer (catalog := catalog) headers keys model).Ready
      state.val location native
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native
      sourceCell payload sourceLocation environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩ :=
      (CallableIndexedOwnedCellAllocationProducer.producer (catalog := catalog) headers keys model).complete
        allocation annotation same definitions registered environments agrees heaps reference read payloadAt cell
        allocated initial.val ready
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨⟨final, initial.property.prepend request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))⟩, related⟩⟩

/-- The physical layer over `slotsProducer`: the allocation's administrative
frame extends the cache authority of the input state. -/
def producer (callerPrefix : Nat) (model : GenericHeap.CellModel compiled.indexed.layouts.definitions) :
    ProtectedStateTransition.CellAllocation.Producer (catalog := catalog)
      (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys callerPrefix)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native =>
    (slotsProducer (catalog := catalog) (headers := headers) (keys := keys) callerPrefix model).Ready
      state.base location native
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native
      sourceCell payload sourceLocation environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩ :=
      (slotsProducer (catalog := catalog) (headers := headers) (keys := keys) callerPrefix model).complete
        allocation annotation same definitions registered environments agrees heaps reference read payloadAt cell
        allocated initial.base ready
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨⟨final, initial.physical.extend frame⟩, related⟩⟩

/-- Readiness of the wrapped producer is the ordinary pool's readiness. -/
theorem ready_iff (callerPrefix : Nat) (model : GenericHeap.CellModel compiled.indexed.layouts.definitions)
    {index : ProtectedStateTransition.Index}
    (state : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys callerPrefix).State index)
    (location : Location) (native : NativeFrame) :
    (producer (catalog := catalog) callerPrefix model).Ready state location native ↔
      (CallableIndexedOwnedCellAllocationProducer.producer (catalog := catalog) headers keys model).Ready
        state.base.val location native :=
  Iff.rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedGlobalSlots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedEntry
/-! The named entry of an accepted call, over any generalized instance model of
the caller's cells. It is `CellAwareNamedEntry.prepare_selected` with two more
receipts: the parameter spine of the canonical environment, which places the
callee capture's global slots after the parameters, and a sized inversion of
native completion into a strictly smaller body completion. The parameter
prefix agreement is sized for that purpose (`SizedAgreement`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataEquality
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedAllocationCompletion
open CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedOwnedAdmittedBodyEntries
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

/-- A finite prefix around a continuation: wrapping is exact, and a sized
completion of the whole unwraps to a continuation completion no larger. -/
structure SizedAgreement (environment : Environment) (store : Store) (whole : Expr)
    (nextEnvironment : Environment) (nextStore : Store) (next : Expr) : Prop where
  wrap : ∀ {result finalStore}, Evaluates nextEnvironment nextStore next result finalStore →
    Evaluates environment store whole result finalStore
  unwrap : ∀ {size result finalStore}, EvaluationSize size environment store whole result finalStore →
    ∃ smaller, smaller ≤ size ∧ EvaluationSize smaller nextEnvironment nextStore next result finalStore

namespace SizedAgreement

theorem refl (environment : Environment) (store : Store) (code : Expr) :
    SizedAgreement environment store code environment store code :=
  ⟨id, fun evaluation => ⟨_, Nat.le_refl _, evaluation⟩⟩

theorem trans {environment middleEnvironment nextEnvironment : Environment}
    {store middleStore nextStore : Store} {whole middle next : Expr}
    (first : SizedAgreement environment store whole middleEnvironment middleStore middle)
    (second : SizedAgreement middleEnvironment middleStore middle nextEnvironment nextStore next) :
    SizedAgreement environment store whole nextEnvironment nextStore next := by
  refine ⟨fun evaluation => first.wrap (second.wrap evaluation), ?_⟩
  intro size result finalStore evaluation
  obtain ⟨middleSize, middleLe, middleEvaluation⟩ := first.unwrap evaluation
  obtain ⟨nextSize, nextLe, nextEvaluation⟩ := second.unwrap middleEvaluation
  exact ⟨nextSize, Nat.le_trans nextLe middleLe, nextEvaluation⟩

theorem letE {environment : Environment} {before middle : Store} {initializer body : Expr} {value : Value}
    (evaluated : Evaluates environment before initializer value middle) :
    SizedAgreement environment before (.letE initializer body) (value :: environment) middle body := by
  refine ⟨fun body => .letE evaluated body, ?_⟩
  intro size result finalStore evaluation
  obtain ⟨smaller, less, body⟩ := evaluation.let_body evaluated
  exact ⟨smaller, Nat.le_of_lt less, body⟩

theorem bind {environment : Environment} {before middle : Store} {computation body : Expr} {type : Ty}
    {value : Value} (evaluated : Evaluates environment before computation (.inRight .word value) middle) :
    SizedAgreement environment before (LanguageResult.bind type computation body) (value :: environment) middle body := by
  refine ⟨fun body => LanguageResult.bind_success type evaluated body, ?_⟩
  intro size result finalStore evaluation
  obtain ⟨smaller, less, body⟩ := evaluation.bind_success evaluated
  exact ⟨smaller, Nat.le_of_lt less, body⟩

end SizedAgreement

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var found => exact .var (agrees found)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index selected found
  exact agrees found

/-- `CellAwareParameterTyped.Stateful.prefix_typed` with a sized agreement. -/
theorem prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {total : Nat} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source total output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {cells : GenericHeap.CellModel nativeDefinitions}
    (ordinaryCells : GenericHeap.OrdinaryCells model cells)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol layouts layout cells)
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.insertion start) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (total_eq : total = allTypes.length)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt (catalog := catalog) producer contextLocation native) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      (∃ suffix, finalStore = store ++ suffix) ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.insertion start))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (CellAwareParameterTyped.prefixContext bindings actualContext)
        nativeDefinitions ∧
      SizedAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
          finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩ := by
  induction tree generalizing mapping world environment canonical logical actual heap store ξ sources values actualContext with
  | nil =>
    cases represented
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, ⟨[], by simp⟩, sourceLayout, actualLayout,
      ⟨[], rfl, rfl, rfl⟩, actualTyped, SizedAgreement.refl _ _ _, ⟨initial, protocol.refl initial⟩⟩
  | @cons scope start binder payload bindings next allocation annotation same tail ih =>
    cases represented with
    | @cons _ _ sourceValue value _ sourceValues nativeValues head rest =>
      have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
      have projection := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
      rw [← FunctionArguments.argumentProjection_eq, ← total_eq] at projection
      have initializer : Evaluates actual store
          ((LanguageResult.success (SourceCoreFunctions.argumentProjection start total (.var start))).rename ξ)
          (.inRight .word value) store := .inRight ((selects_rename projection actualLayout).evaluates store)
      have canonicalLayout : EnvironmentsAgree (request source scope start (binder, payload)).references
          canonical (value :: logical) := agree_insert sourceLayout value
      have referenceAt : (value :: logical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
          (request source scope start (binder, payload))]? = some (.cellRef layout.type contextLocation) := by
        have found := canonicalLayout reference
        have kind := kinds (binder, payload) (by simp)
        change source.inputs.any (fun input => decide (input.id = binder.id)) = named at kind
        have isNamed : SourceCoreCallableIndexedAllocationFrames.isNamedInput
            (request source scope start (binder, payload)) = named := kind
        simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex, isNamed]
        exact found
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextHeaps, nextReference, frame,
        nextState, nextRelated⟩ :=
        producer.complete allocation annotation same definitions registered environments
          canonicalLayout heaps referenceAt read (.initialized rfl rfl)
          (ordinaryCells.inject (.initialized head)) (.ordinary Dynamic.Heap.Allocates.append)
          initial (readyAt initial read)
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      have nextEnvironments := CallableIndexedOrdinaryAllocation.bind_environment (id := binder.id) environments
        nextReference
      have nextSourceLayout : EnvironmentsAgree (Renaming.insertion (start + 1))
          (nextRef :: canonical) (nextRef :: logical) := by
        intro index selectedValue found
        have selected := sourceLayout.lift nextRef found
        simpa only [Renaming.lift_insertion] using selected
      have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
          (nextRef :: logical) (nextRef :: value :: actual) := by
        have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) :=
          agree_insert actualLayout value
        intro index selectedValue found
        exact inserted.lift nextRef found
      have renamedAllocation := CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl)
        allocationEval (actualLayout.lift value)
      have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨stillUnmapped, stillRead⟩ := frame contextLocation unmapped bound
      have nextRead := stillRead.trans read
      have nextSelected : ∀ {index selectedValue}, nativeValues[index]? = some selectedValue →
          allValues[(start + 1) + index]? = some selectedValue := by
        intro index selectedValue found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
        finalFrame, storeExtension, finalSourceLayout, finalActualLayout, spine, finalTyped, agreement, finalState,
        finalRelated⟩ :=
        ih (rest.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
          (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload])
            from ⟨_, rfl⟩))
          nextEnvironments nextHeaps nextSourceLayout nextActualLayout
          (show RuntimeEnvironmentHasTypes
              (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload])
              (nextRef :: value :: actual) (OptionalCell.referenceType payload :: payload :: actualContext)
              nativeDefinitions from
            .cons (.cellRef nextReference.typed)
              (.cons ((model.runtime_hasType head).weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)))
          (show (nextRef :: logical)[start + 1]? = some (DataPatternValues.packValues allValues) from bundleSlot)
          nextSelected (fun binding member => kinds binding (List.mem_cons_of_mem _ member))
          (show (nextRef :: canonical)[(((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals)]? =
            some (.cellRef layout.type contextLocation) from by
              have nextIndex : (((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals) =
                  (scope.length + (if named then 0 else 1) + globals) + 1 := by simp only [List.length_cons]; omega
              rw [nextIndex]
              exact reference)
          nextRead stillUnmapped nextState
      refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, .cons .append allocated, finalEnvironments, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload])
          from ⟨_, rfl⟩).trans worlds,
        frame.trans finalFrame, ?_, ?_, finalActualLayout, ?_, finalTyped, ?_,
        ⟨finalState, protocol.trans nextRelated finalRelated⟩⟩
      · obtain ⟨suffix, storeEq⟩ := storeExtension
        exact ⟨_, storeEq.trans (List.append_assoc _ _ _)⟩
      · intro index selectedValue found
        simpa only [List.length_cons, DataMatchCoreAllocation.liftMany, Renaming.lift_insertion] using
          finalSourceLayout found
      · obtain ⟨added, length, canonicalEq, logicalEq⟩ := spine
        exact ⟨added ++ [nextRef], by simp [length], by simpa [List.append_assoc, nextRef, request] using canonicalEq,
          by simpa [List.append_assoc, nextRef, request] using logicalEq⟩
      · simp only [LoopStatements.rename_insert_lift] at agreement
        apply SizedAgreement.trans ?_ agreement
        simpa only [LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne, nextRef, request] using
          (SizedAgreement.bind initializer).trans (SizedAgreement.letE renamedAllocation)

private theorem monomorphic_context {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner context parameters types final)
    (initial : ∀ id scheme, (id, scheme) ∈ context.locals → scheme.quantified = []) :
    ∀ id scheme, (id, scheme) ∈ final.locals → scheme.quantified = [] := by
  induction extended with
  | nil => exact initial
  | @cons context binder next rest types final payload mono head tail ih =>
    apply ih
    cases head
    intro id scheme member
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp only [mono, TypeSystem.Scheme.mono]
    · exact initial id scheme member

private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type definitions) :
    DataHeap.EnvRepresents catalog mapping world (type :: administrative) scope environment
      (Environment.insertAt canonical scope.length value) definitions := by
  induction related with
  | nil suffixTyped => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed suffixTyped)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

section Entry
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel compiled.indexed.layouts.definitions}

/-- `CellAwareNamedParameterEntry.parameters_selected` over any instance model,
with the parameter spine and a sized agreement. -/
theorem parameters
    (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (sameGlobals : header.globals = compiled.indexed.base.globals.length)
    (sourceTyping : SelectedCompilationNamedSourceTyping.Certified header)
    (empty : header.function.context.locals = [])
    (ownership : LocalIdentityOwnership header.function.source)
    (native : NativeFrame) (id : Word)
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some id)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      native (.named id) (some (CallableIndexedNamedGeneration.state header.named)))
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {administrative actualContext : Core.Context} {canonical actual : Environment} {embedding : Renaming}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative [] [] canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances)
      mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (agrees : EnvironmentsAgree embedding (DataPatternValues.packValues payloads :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (location : Core.Location)
    (reference : canonical[compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : location ∉ mapping)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      (protocol headers keys) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
      (GeneralizedLocalDescriptorHeap.cellModel model instances))
    (initial : State headers keys ⟨[], mapping, world, heap, store, canonical⟩)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer location native) :
    ∃ environment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] heap header.function.parameters arguments environment finalHeap ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        environment finalCanonical compiled.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances)
        finalMap finalWorld finalHeap finalStore ∧
      SourceReceipt program header.function header.context environment finalHeap ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (CellAwareParameterTyped.prefixContext header.bindings actualContext)
        compiled.indexed.layouts.definitions ∧
      SizedAgreement actual store (header.parameterCode.rename embedding)
        finalActual finalStore (header.body.rename finalEmbedding) ∧
      (∃ added : Environment, added.length = header.bindings.length ∧
        finalCanonical = added ++ DataPatternValues.packValues payloads :: canonical) ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store finalMap finalWorld finalHeap finalStore ∧
      CellAwareScopeAuthority.At instances header.named.signature.key []
        finalMap finalWorld finalHeap finalStore environment ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        Relates initial reached ∧
      ∃ physical : CellAwareScopePhysical.Physical compiled header.named header.context
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          finalCanonical finalMap finalWorld finalHeap finalStore environment,
        physical.location = location ∧ physical.native = native := by
  have accepted := header.acceptedPrefix
  rw [sameLayouts, sameGlobals] at accepted
  have tree := CallableIndexedParameterCertificates.of_accepted header.onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues payloads :: canonical) := by intro index value found; exact found
  have length : (header.bindings.map Prod.snd).length = payloads.length := by simpa using represented.length.2
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld,
      finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, storeExtension,
      _lookups, actualLayout, spine, finalTyped, agreement, reached, related⟩ :=
    prefix_sized tree GeneralizedLocalDescriptorHeap.ordinary_cells
      (protocol headers keys) producer rfl header.registered represented environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using reference) read unmapped initial ready
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (header.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length =
      header.bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical header.bindings.length
      (DataPatternValues.packValues payloads) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  rw [← header.parameters] at allocated
  have sourceReceipt := SelectedCompilationNamedAdmission.parameter_source sourceTyping allocated heapTyped argumentsTyped
  have metadata := GenericLexicalContext.binders_metadata allocated
  have monomorphic := monomorphic_context header.extended (by intro id scheme member; rw [empty] at member; cases member)
  have authority : CellAwareScopeAuthority.At instances
      header.named.signature.key [] finalMap finalWorld finalHeap finalStore environment :=
    CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  have finalReference : finalLogical[header.bindings.length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location) := by
    rw [logicalEq]
    have index : header.bindings.length + 1 + compiled.indexed.base.globals.length =
        added.length + (compiled.indexed.base.globals.length + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  obtain ⟨stillUnmapped, stillRead⟩ := preservation location unmapped (List.getElem?_eq_some_iff.mp read).1
  have sourceEq : header.function.source = CallableIndexedNamedGeneration.source header.named := header.agreement.source
  let physical : CellAwareScopePhysical.Physical compiled header.named header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      finalLogical finalMap finalWorld finalHeap finalStore environment :=
    CellAwareScopePhysical.Physical.of_monomorphic native id selected carried
    (by simpa only [← sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using
      (RecursiveNamedHeaderScopeDeclarations.header_scope (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        header))
    (sourceEq ▸ ownership)
    (by simpa only [← sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using
      (CellAwareScopeDeclarations.header_scope (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        header))
    location (by simpa using finalReference) (stillRead.trans read) stillUnmapped
    sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  obtain ⟨suffix, storeEq⟩ := storeExtension
  have effect : CellAwareScopeAuthority.Effect instances
      mapping world heap store finalMap finalWorld finalHeap finalStore := by
    rw [storeEq]
    exact .append store suffix metadata maps worlds
  refine ⟨environment, finalHeap, finalLogical, finalActual, finalStore, finalMap, finalWorld, finalEmbedding,
    allocated, (by simpa only [List.append_nil] using finalWithBundle), finalHeaps, sourceReceipt, actualLayout,
    finalTyped, agreement, ⟨added, prefixLength, logicalEq⟩, preservation, effect, authority, reached, related,
    physical, rfl, rfl⟩

variable {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)
  (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}

/-- `CellAwareNamedEntry.prepare_selected` over any instance model of the
caller's cells, with the parameter spine and a sized inversion of native
completion. -/
theorem prepare
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (sameGlobals : header.globals = compiled.indexed.base.globals.length)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      header.named.signature.key = .ok header.named.specialized)
    (sourceTyping : SelectedCompilationNamedSourceTyping.Certified header)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances)
      mapping world before store)
    (stable : StableRows caller) :
    ∃ environment finalHeap finalCanonical finalActual finalContext finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment finalHeap ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        environment finalCanonical compiled.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances)
        finalMap finalWorld finalHeap finalStore ∧
      SourceReceipt program header.function header.context environment finalHeap ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext compiled.indexed.layouts.definitions ∧
      (∃ added : Environment, added.length = header.bindings.length ∧
        finalCanonical = added ++ DataPatternValues.packValues payloads :: capture.canonical) ∧
      AdministrativePreserved mapping
        (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame compiled.indexed.ancestry.graph.table
            ((compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key)).getD
              Word.zero))))
        finalMap finalStore ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld finalHeap finalStore ∧
      CellAwareScopeAuthority.At instances header.named.signature.key []
        finalMap finalWorld finalHeap finalStore environment ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        Relates caller reached ∧ StableRows reached ∧
      ∃ physical : CellAwareScopePhysical.Physical compiled header.named header.context
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          finalCanonical finalMap finalWorld finalHeap finalStore environment,
        physical.location = owner.key.frameLocation ∧
      (∀ {value bodyStore}, Evaluates finalActual finalStore (header.body.rename finalEmbedding) value bodyStore →
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value
          (bodyStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current))) ∧
      (∀ {size value bodyStore}, EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value bodyStore →
        ∃ smaller reachedStore, smaller < size ∧
          EvaluationSize smaller finalActual finalStore (header.body.rename finalEmbedding) value reachedStore ∧
          bodyStore = reachedStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current)) := by
  have originalTyping := sourceTyping
  obtain ⟨_facts, certified⟩ := originalTyping
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certified.locals_empty
  have ownership : LocalIdentityOwnership header.function.source := by
    rw [header.frame.source]
    exact certified.local_identity_ownership
  let row := caller.rows owner.position
  have rowLocation : row.authority.frameLocation = owner.key.frameLocation := row.frame_eq
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [rowLocation] using row.authority.unmapped
  have current : store.read? owner.key.frameLocation =
      some (encode compiled.indexed.ancestry.layout.frame row.authority.current) := by
    simpa only [rowLocation] using row.authority.frame.read
  obtain ⟨origin, index, selected, frame, emitted⟩ :=
    CallableIndexedFormation.namedBody_receipt compiled.indexed.ancestry header.hook
  have history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named origin) (some (CallableIndexedNamedGeneration.state header.named)) := by
    rw [← frame]
    exact named_complete compiled.indexed.ancestry.graph
      (CallableIndexedNamedGeneration.seed compiled.indexed selected record)
  let installed := install caller owner.position (.stable history)
  have written : store.write? owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)) =
      some (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp current).1, rfl⟩
  have referenceTyped : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    simpa only [rowLocation] using row.authority.typed
  have installedHeaps := heaps.write_administrative
    (fun found => unmapped (List.mem_of_getElem? found)) referenceTyped
    (encode_runtime_typed world header.registered (.state index)) written
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) headers keys
    (GeneralizedLocalDescriptorHeap.cellModel model instances)
  let initial : State headers keys ⟨[], mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)),
      capture.canonical⟩ := installed
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer owner.key.frameLocation (.state index) := by
    intro index reached read
    exact CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position read history
  let actual := .unit :: encode compiled.indexed.ancestry.layout.frame row.authority.current ::
    DataPatternValues.packValues payloads :: capture.captured
  let embedding := Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift)
  have layout : EnvironmentsAgree embedding (DataPatternValues.packValues payloads :: capture.canonical) actual :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix
        (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame row.authority.current)) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := compiled.indexed.layouts.definitions))
    (.cons (encode_runtime_typed world header.registered row.authority.current)
      (.cons (CallableIndexedParameters.Arguments.pack_typed represented) capture.typed))
  obtain ⟨environment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld, finalEmbedding,
      allocated, environments, finalHeaps, sourceReceipt, agrees, finalTyped, agreement, spine, preserved,
      effect, lexical, reached, related, physical, locationEq, _nativeEq⟩ :=
    parameters header sameLayouts sameGlobals sourceTyping empty ownership (.state index) origin selected history
      represented capture.environments installedHeaps heapTyped argumentsTyped layout actualTyped
      owner.key.frameLocation (by simpa only [sameGlobals] using capture.reference)
      (Store.write?_reads_written written) unmapped producer initial ready
  have finalStable := GeneralizedLocalParameterAdmission.after_parameters caller reached owner.position
    (fun i _ => stable i) history preserved
  have fullEffect := (CellAwareScopeAuthority.Effect.set_unmapped store
    (encode compiled.indexed.ancestry.layout.frame (.state index)) unmapped).trans effect
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  have renamed : header.code.rename capture.embedding.lift = withFrame
      (.var (capture.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (header.parameterCode.rename capture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have next : Evaluates (encode compiled.indexed.ancestry.layout.frame row.authority.current ::
      DataPatternValues.packValues payloads :: capture.captured) store
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) store := by
    rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
    exact CallableIndexedContextFrames.literal_evaluates _ _ _ _
  refine ⟨environment, finalHeap, finalCanonical, finalActual, _, finalStore, finalMap, finalWorld, finalEmbedding,
    allocated, environments, finalHeaps, sourceReceipt, agrees, finalTyped, spine, ?_, fullEffect, lexical,
    reached, (install_related caller owner.position (.stable history)).trans related, finalStable,
    physical, locationEq, ?_, ?_⟩
  · simpa only [selected, Option.getD_some, frame] using preserved
  · intro value bodyStore evaluated
    have parameterRun := agreement.wrap evaluated
    simp only [embedding, GenericExpressionMeaning.rename_prefix] at parameterRun
    rw [renamed]
    exact CallableContextFrames.withFrame_evaluates (.var reference) current next parameterRun
  · intro size value bodyStore evaluated
    rw [renamed] at evaluated
    obtain ⟨_nextSize, child, installedValue, nextStore, reachedStore, actualNext, parameterRun, _nextLess,
        childLess, restored⟩ :=
      RecursiveNamedCallBounds.with_frame (.var reference) current evaluated
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic actualNext.sound next
    have parameterSized : EvaluationSize child actual
        (nextStore.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)))
        (header.parameterCode.rename embedding) value reachedStore := by
      simpa only [embedding, GenericExpressionMeaning.rename_prefix] using parameterRun
    obtain ⟨smaller, smallerLe, bodyRun⟩ := agreement.unwrap parameterSized
    exact ⟨smaller, reachedStore, Nat.lt_of_le_of_lt smallerLe childLess, bodyRun, restored⟩

end Entry

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedApplication
/-! The row lemma of direct calls: the application input of
`CellAwareInvocationAcceptedDirectCalls` comes from the callee's own accepted
body. The named entry runs over the caller's accepted cells
(`CellAwareInvocationAcceptedNamedEntry.prepare`); its parameter spine and the
caller's physical cache and capture slots give the body a state of the
slot-retaining protocol (`CallableIndexedOwnedPhysicalCanonicalState`), on
which the accepted flow runs with the cell producer of
`CellAwareInvocationAcceptedGlobalSlots`. The entry, body and restoration
effects compose. The body's accepted-expression meaning below the grade is the
only expression input; the size induction across bodies supplies it. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedApplication
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedSourceAt)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)

private theorem monomorphic_context {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner context parameters types final)
    (initial : ∀ id scheme, (id, scheme) ∈ context.locals → scheme.quantified = []) :
    ∀ id scheme, (id, scheme) ∈ final.locals → scheme.quantified = [] := by
  induction extended with
  | nil => exact initial
  | @cons context binder next rest types final payload mono head tail ih =>
    apply ih
    cases head
    intro id scheme member
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp only [mono, TypeSystem.Scheme.mono]
    · exact initial id scheme member

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (Key whole (Program.ofChecked whole.sourceProgram))}

private theorem statements (header : Header whole (Program.ofChecked whole.sourceProgram))
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed header.named diagnostics code) :
    generation.statements = header.function.body := by
  have same := (RecursiveNamedPreparedSourceFrames.compiled_roots_eq generation).symm.trans
    (header.agreement.source ▸ header.agreement.roots)
  exact (List.map_inj_right (fun _ _ same => NodeId.statement.inj same)).mp same

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (header : Header whole (Program.ofChecked whole.sourceProgram))
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (sameNamed : header.named = named)
  (sameLayouts : header.layouts = whole.indexed.layouts)
  (sameGlobals : header.globals = whole.indexed.base.globals.length)
  (sameBindings : header.bindings = named.inputs)
  (sameBody : header.body = generation.body)
  (sameSolved : header.solved = named.specialized.function.solvedRequirements)
  (projection : whole.compatible.checked.catalog.project header.function.resultType = .ok named.signature.resultType)
  (support : SelectedCompilationNamedSupport.Support whole)
  (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics)
  (assignments : ∃ first, SourceCoreAssignmentFaultSites.prepare (CallableIndexedNamedGeneration.source named) first =
    .ok generation.own.assignments)
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (body : AcceptedNamedBodyFlow.Body (rowIndex generation record).policy (rowIndex generation record).fuel
    (rowIndex generation record).compilerSource (rowIndex generation record).scope
    (rowIndex generation record).statements (rowIndex generation record).result
    (rowIndex generation record).reasonAt (rowIndex generation record).fellThrough
    (rowIndex generation record).escaped (rowIndex generation record).body)
  (covered : CellAwareInvocationAcceptedFlow.Covered (rowIndex generation record).source header.function.resultType
    (CellAwareInvocationAcceptedMatches.Admitted (rowIndex generation record))
    (CellAwareInvocationAcceptedInputs.Generalized (rowIndex generation record)) body.tree)
  (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext (rowIndex generation record).scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
    (rowIndex generation record).body nativeType whole.indexed.layouts.definitions)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))

local notation "rootFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" =>
  CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry rootFunctions
local notation "accepted" => GeneralizedLocalDescriptorHeap.cellModel model
  (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True))
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved projection support
  issued assignments artifact checked covered native wellFormed in
/-- The callee row's accepted body discharges the application input of the
direct-call head at a Source grade, given the meaning of the body's accepted
expressions below that grade on the slot-retaining protocol. -/
theorem preserves (size : Nat)
    (expressions : ∀ (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex generation record) stages child faults size) :
    CellAwareInvocationAcceptedDirectCalls.PreservesAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size := by
  subst sameNamed
  intro scope mapping world before store canonical owner caller capture cache _member stable context arguments
    payloads _supports heapTyped argumentsTyped represented heaps rawD function sourceAt invocation outcome after trace
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨bodySize, child, bodyEnvironment, bound, finalContext, bodyOutcome, selected, allocated, bodyTrace,
      converted, smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix sourceAt wellFormed arity trace
  have certified := support.certified header
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped, spine,
      prefixFrame, prefixEffect, _lexical, reached, related, rows, physical, frameEq, wrap, _unwrap⟩ :=
    CellAwareInvocationAcceptedNamedEntry.prepare owner caller header capture.named sameLayouts sameGlobals record
      certified heapTyped argumentsTyped represented heaps stable
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entryAllocated allocated
  rw [← sameEnvironment, ← sameHeap, ← statements header generation] at bodyTrace
  have sourceEq : child.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : child.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements :=
    header.valid.ledger.trans sameSolved
  obtain ⟨typingFinal, typingFacts, originalTyped, _completes⟩ := sourceReceipt.bodyTyped
  have functionTyped : StatementsHaveType (CallableIndexedNamedGeneration.source header.named)
      {returnType := header.function.resultType} header.context generation.statements typingFinal typingFacts := by
    simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source]
      using originalTyped
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements :=
    ⟨_, typingFinal, typingFacts, functionTyped⟩
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ runtime.graph.nodeOccurrencesUnique
  obtain ⟨_facts, certificate⟩ := certified
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certificate.locals_empty
  have monomorphic := monomorphic_context header.extended
    (by intro id scheme member; rw [empty] at member; cases member)
  have prefixEq : RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header =
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative := by
    simp only [RecursiveNamedLambdaFormationHeads.nativePrefix, CellAwareNamedPreparedReceipt.administrative capture,
      header.parameterType, List.cons_append]
  rw [prefixEq] at native
  obtain ⟨added, addedLength, canonicalEq⟩ := spine
  have rowLocation : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
    (caller.rows owner.position).frame_eq
  have frameRead : store.read? owner.key.frameLocation = some (SourceCoreCallableIndexedFrames.encode
      whole.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) := by
    simpa only [rowLocation] using (caller.rows owner.position).authority.frame.read
  have scopeLength : added.length = (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length := by
    simpa only [List.length_map, List.length_reverse] using addedLength
  let initial := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine cache frameRead _ prefixFrame reached
    capture.slots (DataPatternValues.packValues payloads) scopeLength canonicalEq
  let producer := CellAwareInvocationAcceptedGlobalSlots.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) (headers := headers) (keys := keys)
    1 accepted
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index state read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read state.base.val owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CellAwareInvocationAcceptedGlobalSlots.producer,
      CellAwareInvocationAcceptedGlobalSlots.slotsProducer, CallableIndexedOwnedCellAllocationProducer.producer,
      frameEq, OwnedKey.key] using result
  let frame : ActualBodyInvocation.Frame (rowIndex generation record) :=
    ⟨physical.native, .named physical.id, CallableIndexedNamedGeneration.state header.named, physical.carried,
      .named (CallableIndexedNamedGeneration.seed whole.indexed physical.selected record), rfl, rfl⟩
  let bodyPhysical : CellAwareInvocationPhysical.Physical (attachment := fun _ _ _ => True) whole
      (rowIndex generation record)
      header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entryCanonical entryMap entryWorld entryHeap entryStore entryEnvironment :=
    CellAwareInvocationPhysical.Physical.of_monomorphic (attachment := fun _ _ _ => True) frame physical.declarations
    physical.ownership physical.sourceDeclarations physical.location physical.reference physical.read physical.unmapped
    sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  have scopeEq : (rowIndex generation record).scope =
      header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) := by
    rw [sameBindings]
    rfl
  have meaning := CellAwareInvocationAcceptedFlow.body_preserves (attachment := fun _ _ _ => True)
    (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 capture.keyPhysical.locations).forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
    (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1) (rowIndex generation record) producer
    (CallableIndexedAmbient.frame_registered whole.indexed) stages child faults
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative) size
    (expressions owner capture.keyPhysical selected)
    (CellAwareInvocationAcceptedNamedInvocation.writes profile generation record issued assignments receiver
      (protocol := CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1) sourceEq
      runtime.graph.nodeOccurrencesUnique)
    artifact checked sourceEq unique (control := {returnType := header.function.resultType})
    (expected := header.function.resultType) rfl rfl
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
    functionTyped projection body covered native (Nat.le_of_lt smaller)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  rw [scopeEq] at meaning
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, bodyHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, bodyEffect, bodyState, bodyRelated, _bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed initial
      ⟨sourceReceipt.heapTyped, rows⟩
      (CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic)
      bodyPhysical owner frameEq.symm ready bodyTrace
  have evaluatedHeader : Evaluates entryActual entryStore (header.body.rename entryEmbedding) value bodyStore := by
    rw [sameBody]
    exact evaluated
  have resultEq : (rowIndex generation record).result = header.output :=
    header.resultType
  rw [resultEq, ← CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq converted] at result
  have worlds := prefixEffect.worlds.trans bodyWorlds
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState.base.val owner.position bodyHeaps worlds
      (prefixFrame.trans bodyFrame) (related.trans bodyRelated)
  have effect := CellAwareOwnedBodyRestoration.restored_effect caller bodyState.base.val owner.position
    (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True)) (prefixEffect.trans bodyEffect)
  exact ⟨value, _, finalMap, finalWorld, wrap evaluatedHeader, result, restoredHeaps,
    prefixEffect.maps.trans bodyMaps, worlds, restoredFrame, prefixEffect.metadata.trans bodyMetadata, effect,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState.base.val owner.position, restoredRelated⟩

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved projection support
  issued assignments artifact checked covered native in
/-- Native completion of the callee row's closure body reconstructs the staged
application at an independent grade, given the native meaning of the body's
accepted expressions below the native grade of the closure body. The callee's
own registry scope is a row receipt. -/
theorem reflects (size : Nat) {bodyScope : Staging.Recursive.Scope}
    (bodySelected : (stages).Closure header.function bodyScope)
    (expressions : ∀ (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex generation record) stages child faults size) :
    CellAwareInvocationAcceptedDirectCalls.ReflectsAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size := by
  subst sameNamed
  intro scope mapping world before store canonical owner caller capture cache _member stable context arguments
    payloads _supports heapTyped argumentsTyped represented heaps rawD function sourceAt invocation value finalStore
    completed
  have certified := support.certified header
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped, spine,
      prefixFrame, prefixEffect, _lexical, reached, related, rows, physical, frameEq, _wrap, unwrap⟩ :=
    CellAwareInvocationAcceptedNamedEntry.prepare owner caller header capture.named sameLayouts sameGlobals record
      certified heapTyped argumentsTyped represented heaps stable
  obtain ⟨bodySize, reachedStore, bodyLess, bodyEvaluation, finalEq⟩ := unwrap completed
  have compiledEvaluation : EvaluationSize bodySize entryActual entryStore (generation.body.rename entryEmbedding)
      value reachedStore := by
    rw [← sameBody]
    exact bodyEvaluation
  have sourceEq : bodyScope.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source bodySelected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : bodyScope.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence bodySelected] using
      sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements :=
    header.valid.ledger.trans sameSolved
  obtain ⟨typingFinal, typingFacts, originalTyped, _completes⟩ := sourceReceipt.bodyTyped
  have functionTyped : StatementsHaveType (CallableIndexedNamedGeneration.source header.named)
      {returnType := header.function.resultType} header.context generation.statements typingFinal typingFacts := by
    simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source]
      using originalTyped
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements :=
    ⟨_, typingFinal, typingFacts, functionTyped⟩
  have unique : NodeOccurrencesUnique bodyScope.source := sourceEq ▸ runtime.graph.nodeOccurrencesUnique
  obtain ⟨_facts, certificate⟩ := certified
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certificate.locals_empty
  have monomorphic := monomorphic_context header.extended
    (by intro id scheme member; rw [empty] at member; cases member)
  have prefixEq : RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header =
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative := by
    simp only [RecursiveNamedLambdaFormationHeads.nativePrefix, CellAwareNamedPreparedReceipt.administrative capture,
      header.parameterType, List.cons_append]
  rw [prefixEq] at native
  obtain ⟨added, addedLength, canonicalEq⟩ := spine
  have rowLocation : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
    (caller.rows owner.position).frame_eq
  have frameRead : store.read? owner.key.frameLocation = some (SourceCoreCallableIndexedFrames.encode
      whole.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) := by
    simpa only [rowLocation] using (caller.rows owner.position).authority.frame.read
  have scopeLength : added.length = (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length := by
    simpa only [List.length_map, List.length_reverse] using addedLength
  let initial := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine cache frameRead _ prefixFrame reached
    capture.slots (DataPatternValues.packValues payloads) scopeLength canonicalEq
  let producer := CellAwareInvocationAcceptedGlobalSlots.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) (headers := headers) (keys := keys)
    1 accepted
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index state read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read state.base.val owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CellAwareInvocationAcceptedGlobalSlots.producer,
      CellAwareInvocationAcceptedGlobalSlots.slotsProducer, CallableIndexedOwnedCellAllocationProducer.producer,
      frameEq, OwnedKey.key] using result
  let frame : ActualBodyInvocation.Frame (rowIndex generation record) :=
    ⟨physical.native, .named physical.id, CallableIndexedNamedGeneration.state header.named, physical.carried,
      .named (CallableIndexedNamedGeneration.seed whole.indexed physical.selected record), rfl, rfl⟩
  let bodyPhysical : CellAwareInvocationPhysical.Physical (attachment := fun _ _ _ => True) whole
      (rowIndex generation record)
      header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entryCanonical entryMap entryWorld entryHeap entryStore entryEnvironment :=
    CellAwareInvocationPhysical.Physical.of_monomorphic (attachment := fun _ _ _ => True) frame physical.declarations
    physical.ownership physical.sourceDeclarations physical.location physical.reference physical.read physical.unmapped
    sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  have scopeEq : (rowIndex generation record).scope =
      header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) := by
    rw [sameBindings]
    rfl
  have meaning := CellAwareInvocationAcceptedFlow.body_reflects (attachment := fun _ _ _ => True)
    (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 capture.keyPhysical.locations).forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
    (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1) (rowIndex generation record) producer
    (CallableIndexedAmbient.frame_registered whole.indexed) stages bodyScope faults
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative) size
    (expressions owner capture.keyPhysical bodySelected)
    (CellAwareInvocationAcceptedNamedInvocation.writes profile generation record issued assignments receiver
      (protocol := CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1) sourceEq
      runtime.graph.nodeOccurrencesUnique)
    artifact checked sourceEq unique (control := {returnType := header.function.resultType})
    (expected := header.function.resultType) rfl rfl
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
    functionTyped projection body covered native (Nat.le_of_lt bodyLess)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  rw [scopeEq] at meaning
  obtain ⟨sourceSize, bodyContext, bodyOutcome, after, finalMap, finalWorld, trace, matched, result, bodyHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyEffect, bodyState, bodyRelated, _bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed initial
      ⟨sourceReceipt.heapTyped, rows⟩
      (CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic)
      bodyPhysical owner frameEq.symm ready compiledEvaluation
  have bodyTrace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages sourceSize
      bodyScope header.context entryEnvironment entryHeap header.function.body bodyContext bodyOutcome after := by
    rw [← statements header generation]
    exact trace
  have applied := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.applies (caller := invocation)
    (context := context) sourceAt (SelectedCompilationPhysicalProgramSupport.stagePrepared whole) bodySelected
    header.extended entryAllocated bodyTrace matched
  have resultEq : (rowIndex generation record).result = header.output :=
    header.resultType
  rw [resultEq] at result
  have worlds := prefixEffect.worlds.trans bodyWorlds
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState.base.val owner.position bodyHeaps worlds
      (prefixFrame.trans bodyFrame) (related.trans bodyRelated)
  have effect := CellAwareOwnedBodyRestoration.restored_effect caller bodyState.base.val owner.position
    (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True)) (prefixEffect.trans bodyEffect)
  rw [finalEq]
  exact ⟨_, _, after, finalMap, finalWorld, applied, result, restoredHeaps,
    prefixEffect.maps.trans bodyMaps, worlds, restoredFrame, prefixEffect.metadata.trans bodyMetadata, effect,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState.base.val owner.position, restoredRelated⟩

include profile receiver record sameNamed sameBindings sameBody sameSolved projection support in
/-- A callee row whose accepted expressions all lie in the first closed subset
has accepted-expression meaning on the slot-retaining protocol at every grade,
from the same receipts as the public named root. -/
theorem expressions_closed
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (closed : CellAwareInvocationAcceptedExpressions.Closed (rowIndex generation record)) (size : Nat) :
    ∀ (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex generation record) stages child faults size := by
  subst sameNamed
  intro owner keyPhysical child selected
  obtain ⟨_facts, certificate⟩ := support.certified header
  have functionUnique : NodeOccurrencesUnique header.function.source := by
    rw [header.frame.source]
    exact certificate.graph_closed.wellFormed.nodeOccurrencesUnique
  have unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using functionUnique
  exact CellAwareInvocationAcceptedExpressions.expressions (attachment := fun _ _ _ => True)
    (receiving := completion.result.context.registry) (functions := rootFunctions)
    (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
    (rowIndex generation record) stages child faults closed size
    (((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source)
    completion.result.extension
    (CellAwareInvocationAcceptedNamedInvocation.reads generation record issuer receiver unique)
    support.registryBodies

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved projection support
  issued assignments artifact checked covered native wellFormed in
/-- A closed-subset callee row discharges the application input of the
direct-call head at every Source grade, without the size induction. -/
theorem preserves_closed
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (closed : CellAwareInvocationAcceptedExpressions.Closed (rowIndex generation record)) (size : Nat) :
    CellAwareInvocationAcceptedDirectCalls.PreservesAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  preserves profile receiver header generation record sameNamed sameLayouts sameGlobals sameBindings sameBody
    sameSolved projection support issued assignments artifact checked body covered native wellFormed size
    (expressions_closed profile receiver header generation record sameNamed sameBindings sameBody sameSolved
      projection support issuer closed size)

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved projection support
  issued assignments artifact checked covered native in
/-- A closed-subset callee row discharges the native application input of the
direct-call head at every native grade. -/
theorem reflects_closed
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (closed : CellAwareInvocationAcceptedExpressions.Closed (rowIndex generation record)) (size : Nat)
    {bodyScope : Staging.Recursive.Scope} (bodySelected : (stages).Closure header.function bodyScope) :
    CellAwareInvocationAcceptedDirectCalls.ReflectsAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  reflects profile receiver header generation record sameNamed sameLayouts sameGlobals sameBindings sameBody
    sameSolved projection support issued assignments artifact checked body covered native size bodySelected
    (expressions_closed profile receiver header generation record sameNamed sameBindings sameBody sameSolved
      projection support issuer closed size)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedApplication
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallEntry
/-! The entry of a call-containing named row at the public root. It is the
body-trace counterpart of `CellAwareInvocationAcceptedNamedApplication`: the
named entry over the caller's accepted cells, the body on the slot-retaining
protocol with the body's accepted-expression meaning as input, and the restored
caller with its post-admission, packaged as the root's `NamedResultAt`, as
`CellAwareInvocationAcceptedNamedInvocation.preserves_selected` does for
first-subset rows on the plain caller protocol. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedSourceAt)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)

private theorem monomorphic_context {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner context parameters types final)
    (initial : ∀ id scheme, (id, scheme) ∈ context.locals → scheme.quantified = []) :
    ∀ id scheme, (id, scheme) ∈ final.locals → scheme.quantified = [] := by
  induction extended with
  | nil => exact initial
  | @cons context binder next rest types final payload mono head tail ih =>
    apply ih
    cases head
    intro id scheme member
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp only [mono, TypeSystem.Scheme.mono]
    · exact initial id scheme member

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (Key whole (Program.ofChecked whole.sourceProgram))}

private theorem statements (header : Header whole (Program.ofChecked whole.sourceProgram))
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed header.named diagnostics code) :
    generation.statements = header.function.body := by
  have same := (RecursiveNamedPreparedSourceFrames.compiled_roots_eq generation).symm.trans
    (header.agreement.source ▸ header.agreement.roots)
  exact (List.map_inj_right (fun _ _ same => NodeId.statement.inj same)).mp same

/-- Post-admission on the slot-retaining protocol is post-admission of its
plain caller pool. -/
private theorem post_base {index : ProtectedStateTransition.Index}
    {state : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State index}
    (owner : OwnedKey keys) (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    (post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
      context type outcome state) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      CallableIndexedOwnedBodyRestorationAdmission.bridge context type outcome state.base.val := by
  cases outcome with
  | value value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨post.rows, post.successful⟩
    | stage scope call reason => exact post

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (header : Header whole (Program.ofChecked whole.sourceProgram))
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (sameNamed : header.named = named)
  (sameLayouts : header.layouts = whole.indexed.layouts)
  (sameGlobals : header.globals = whole.indexed.base.globals.length)
  (sameBindings : header.bindings = named.inputs)
  (sameBody : header.body = generation.body)
  (sameSolved : header.solved = named.specialized.function.solvedRequirements)
  (projection : whole.compatible.checked.catalog.project header.function.resultType = .ok named.signature.resultType)
  (support : SelectedCompilationNamedSupport.Support whole)
  (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics)
  (assignments : ∃ first, SourceCoreAssignmentFaultSites.prepare (CallableIndexedNamedGeneration.source named) first =
    .ok generation.own.assignments)
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (body : AcceptedNamedBodyFlow.Body (rowIndex generation record).policy (rowIndex generation record).fuel
    (rowIndex generation record).compilerSource (rowIndex generation record).scope
    (rowIndex generation record).statements (rowIndex generation record).result
    (rowIndex generation record).reasonAt (rowIndex generation record).fellThrough
    (rowIndex generation record).escaped (rowIndex generation record).body)
  (covered : CellAwareInvocationAcceptedFlow.Covered (rowIndex generation record).source header.function.resultType
    (CellAwareInvocationAcceptedMatches.Admitted (rowIndex generation record))
    (CellAwareInvocationAcceptedInputs.Generalized (rowIndex generation record)) body.tree)
  (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext (rowIndex generation record).scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
    (rowIndex generation record).body nativeType whole.indexed.layouts.definitions)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))

local notation "rootFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" =>
  CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry rootFunctions
local notation "accepted" => GeneralizedLocalDescriptorHeap.cellModel model
  (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True))
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved projection support
  issued assignments artifact checked covered native in
/-- A staged Source trace of a call-containing row's body determines the
native entry, body and restoration from a reached caller pool with its
physical cache and capture: the body runs on the slot-retaining protocol, and
the result is the root's `NamedResultAt` over accepted cells. -/
theorem preserves_selected {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store : Store} {canonical : Environment} (owner : OwnedKey keys)
    (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store)
    (cache : CallableIndexedOwnedPhysicalGlobals.Authority whole mapping store)
    (stable : StableRows caller) {arguments : List Dynamic.Value} {payloads : List Value}
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents accepted mapping world before store)
    {child : Staging.Recursive.Scope} (selected : (stages).Closure header.function child)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (bodyTrace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size child
      header.context environment bound header.function.body finalContext bodyOutcome after)
    (expressions : ∀ (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex generation record) stages child faults size) :
    ∃ value finalStore finalMap finalWorld,
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        rootFunctions accepted owner caller header capture.named payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result bodyOutcome) after value finalStore finalMap finalWorld
        faults := by
  subst sameNamed
  have certified := support.certified header
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped, spine,
      prefixFrame, prefixEffect, _lexical, reached, related, rows, physical, frameEq, wrap, _unwrap⟩ :=
    CellAwareInvocationAcceptedNamedEntry.prepare owner caller header capture.named sameLayouts sameGlobals record
      certified heapTyped argumentsTyped represented heaps stable
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entryAllocated allocated
  rw [← sameEnvironment, ← sameHeap, ← statements header generation] at bodyTrace
  have sourceEq : child.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : child.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements :=
    header.valid.ledger.trans sameSolved
  obtain ⟨typingFinal, typingFacts, originalTyped, _completes⟩ := sourceReceipt.bodyTyped
  have functionTyped : StatementsHaveType (CallableIndexedNamedGeneration.source header.named)
      {returnType := header.function.resultType} header.context generation.statements typingFinal typingFacts := by
    simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source]
      using originalTyped
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements :=
    ⟨_, typingFinal, typingFacts, functionTyped⟩
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ runtime.graph.nodeOccurrencesUnique
  obtain ⟨_facts, certificate⟩ := certified
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certificate.locals_empty
  have monomorphic := monomorphic_context header.extended
    (by intro id scheme member; rw [empty] at member; cases member)
  have prefixEq : RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header =
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative := by
    simp only [RecursiveNamedLambdaFormationHeads.nativePrefix, CellAwareNamedPreparedReceipt.administrative capture,
      header.parameterType, List.cons_append]
  rw [prefixEq] at native
  obtain ⟨added, addedLength, canonicalEq⟩ := spine
  have rowLocation : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
    (caller.rows owner.position).frame_eq
  have frameRead : store.read? owner.key.frameLocation = some (SourceCoreCallableIndexedFrames.encode
      whole.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) := by
    simpa only [rowLocation] using (caller.rows owner.position).authority.frame.read
  have scopeLength : added.length = (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length := by
    simpa only [List.length_map, List.length_reverse] using addedLength
  let initial := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine cache frameRead _ prefixFrame reached
    capture.slots (DataPatternValues.packValues payloads) scopeLength canonicalEq
  let producer := CellAwareInvocationAcceptedGlobalSlots.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) (headers := headers) (keys := keys)
    1 accepted
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index state read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read state.base.val owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CellAwareInvocationAcceptedGlobalSlots.producer,
      CellAwareInvocationAcceptedGlobalSlots.slotsProducer, CallableIndexedOwnedCellAllocationProducer.producer,
      frameEq, OwnedKey.key] using result
  let frame : ActualBodyInvocation.Frame (rowIndex generation record) :=
    ⟨physical.native, .named physical.id, CallableIndexedNamedGeneration.state header.named, physical.carried,
      .named (CallableIndexedNamedGeneration.seed whole.indexed physical.selected record), rfl, rfl⟩
  let bodyPhysical : CellAwareInvocationPhysical.Physical (attachment := fun _ _ _ => True) whole
      (rowIndex generation record)
      header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entryCanonical entryMap entryWorld entryHeap entryStore entryEnvironment :=
    CellAwareInvocationPhysical.Physical.of_monomorphic (attachment := fun _ _ _ => True) frame physical.declarations
    physical.ownership physical.sourceDeclarations physical.location physical.reference physical.read physical.unmapped
    sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  have scopeEq : (rowIndex generation record).scope =
      header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) := by
    rw [sameBindings]
    rfl
  have meaning := CellAwareInvocationAcceptedFlow.body_preserves (attachment := fun _ _ _ => True)
    (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 capture.keyPhysical.locations).forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
    (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1) (rowIndex generation record) producer
    (CallableIndexedAmbient.frame_registered whole.indexed) stages child faults
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative) size
    (expressions owner capture.keyPhysical selected)
    (CellAwareInvocationAcceptedNamedInvocation.writes profile generation record issued assignments receiver
      (protocol := CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1) sourceEq
      runtime.graph.nodeOccurrencesUnique)
    artifact checked sourceEq unique (control := {returnType := header.function.resultType})
    (expected := header.function.resultType) rfl rfl
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
    functionTyped projection body covered native (Nat.le_refl size)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  rw [scopeEq] at meaning
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, bodyHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, _bodyEffect, bodyState, bodyRelated, bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed initial
      ⟨sourceReceipt.heapTyped, rows⟩
      (CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic)
      bodyPhysical owner frameEq.symm ready bodyTrace
  have evaluatedHeader : Evaluates entryActual entryStore (header.body.rename entryEmbedding) value bodyStore := by
    rw [sameBody]
    exact evaluated
  have resultEq : (rowIndex generation record).result = header.output :=
    header.resultType
  rw [resultEq] at result
  have worlds := prefixEffect.worlds.trans bodyWorlds
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState.base.val owner.position bodyHeaps worlds
      (prefixFrame.trans bodyFrame) (related.trans bodyRelated)
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState.base.val owner.position stable (post_base owner capture.keyPhysical bodyPost) supports restoredFrame
  exact ⟨value, _, finalMap, finalWorld, wrap evaluatedHeader, result, restoredHeaps,
    prefixEffect.maps.trans bodyMaps, worlds, restoredFrame, prefixEffect.metadata.trans bodyMetadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState.base.val owner.position, restoredRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallFamily
/-! The size induction across bodies for direct calls. A family of rows is
given by the instantiations it admits (`called`): every catalog header with an
admitted instantiation has the receipts of a named row whose accepted
expressions are extended roots calling only admitted instantiations (`Row`).
One strong induction on the grade gives the accepted-expression meaning of
every family body on the slot-retaining protocol: at a call of a given grade
the direct-call head needs the callee's application below that grade, and the
row lemma gives it from the callee body's expressions below it. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallFamily
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (Key whole (Program.ofChecked whole.sourceProgram))}

/-- The receipts of one family row, as the public named root takes them, with
the extended closure and call authority of its body and its own registry
scope. -/
structure Row (called : DeclarationInstantiation → Prop)
    (header : Header whole (Program.ofChecked whole.sourceProgram)) where
  named : SourceCoreGeneralFunctions.Function
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  code : Expr
  generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code
  record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized
  sameNamed : header.named = named
  sameLayouts : header.layouts = whole.indexed.layouts
  sameGlobals : header.globals = whole.indexed.base.globals.length
  sameBindings : header.bindings = named.inputs
  sameBody : header.body = generation.body
  sameSolved : header.solved = named.specialized.function.solvedRequirements
  projection : whole.compatible.checked.catalog.project header.function.resultType = .ok named.signature.resultType
  issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics
  assignments : ∃ first, SourceCoreAssignmentFaultSites.prepare (CallableIndexedNamedGeneration.source named) first =
    .ok generation.own.assignments
  body : AcceptedNamedBodyFlow.Body (rowIndex generation record).policy (rowIndex generation record).fuel
    (rowIndex generation record).compilerSource (rowIndex generation record).scope
    (rowIndex generation record).statements (rowIndex generation record).result
    (rowIndex generation record).reasonAt (rowIndex generation record).fellThrough
    (rowIndex generation record).escaped (rowIndex generation record).body
  covered : CellAwareInvocationAcceptedFlow.Covered (rowIndex generation record).source header.function.resultType
    (CellAwareInvocationAcceptedMatches.Admitted (rowIndex generation record))
    (CellAwareInvocationAcceptedInputs.Generalized (attachment := fun _ _ _ => True) (rowIndex generation record))
    body.tree
  native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext (rowIndex generation record).scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
    (rowIndex generation record).body nativeType whole.indexed.layouts.definitions
  issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key)
  closed : CellAwareInvocationAcceptedCallExpressions.ClosedCalls generation record called
  ports : CellAwareInvocationAcceptedCallExpressions.Ports (headers := headers) generation record
  bodyScope : Staging.Recursive.Scope
  bodySelected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function bodyScope

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (support : SelectedCompilationNamedSupport.Support whole)
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  {called : DeclarationInstantiation → Prop}
  (rows : ∀ header, header ∈ headers → called header.instantiation → Row (headers := headers) called header)

local notation "rootFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" =>
  CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry rootFunctions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private theorem row_source {header : Header whole (Program.ofChecked whole.sourceProgram)}
    (row : Row (headers := headers) called header) {child : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function child) :
    child.source = (rowIndex row.generation row.record).source := by
  show child.source = CallableIndexedNamedGeneration.source row.named
  rw [← row.sameNamed]
  exact ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source

include support in
private theorem row_unique {header : Header whole (Program.ofChecked whole.sourceProgram)}
    (row : Row (headers := headers) called header) :
    NodeOccurrencesUnique (CallableIndexedNamedGeneration.source row.named) := by
  obtain ⟨_facts, certificate⟩ := support.certified header
  have functionUnique : NodeOccurrencesUnique header.function.source := by
    rw [header.frame.source]
    exact certificate.graph_closed.wellFormed.nodeOccurrencesUnique
  rw [← row.sameNamed]
  simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using functionUnique

include profile receiver support artifact checked wellFormed rows in
/-- Every family body has its accepted-expression meaning on the
slot-retaining protocol at every grade, for every owner key with physical
locations and every registry scope of its function. -/
theorem expressions (size : Nat) :
    ∀ header (member : header ∈ headers) (admitted : called header.instantiation) (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex (rows header member admitted).generation (rows header member admitted).record) stages child faults
        size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro header member admitted owner keyPhysical child selected
    have applications : ∀ callee, callee ∈ headers → called callee.instantiation →
        CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True)
          (headers := headers) (keys := keys) model stages faults callee size ∧
        CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True)
          (headers := headers) (keys := keys) model stages faults callee size := by
      intro callee calleeMember calleeAdmitted
      let row := rows callee calleeMember calleeAdmitted
      refine ⟨fun smaller less => ?_, fun smaller less => ?_⟩
      · exact CellAwareInvocationAcceptedNamedApplication.preserves profile receiver callee row.generation row.record
          row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
          support row.issued row.assignments artifact checked row.body row.covered row.native wellFormed smaller
          (fun calleeOwner calleeKey _ calleeSelected =>
            ih smaller less callee calleeMember calleeAdmitted calleeOwner calleeKey calleeSelected)
      · exact CellAwareInvocationAcceptedNamedApplication.reflects profile receiver callee row.generation row.record
          row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
          support row.issued row.assignments artifact checked row.body row.covered row.native smaller row.bodySelected
          (fun calleeOwner calleeKey _ calleeSelected =>
            ih smaller less callee calleeMember calleeAdmitted calleeOwner calleeKey calleeSelected)
    let row := rows header member admitted
    exact CellAwareInvocationAcceptedCallExpressions.expressions row.generation row.record called owner keyPhysical
      stages child faults row.closed size (row_source row selected) completion.result.extension
      (CellAwareInvocationAcceptedNamedInvocation.reads row.generation row.record row.issuer receiver
        (row_unique support row))
      support.registryBodies wellFormed row.ports applications

include profile receiver support artifact checked wellFormed rows in
/-- The direct-call head's application input holds for every admitted header
at every Source grade. -/
theorem preserves (header : Header whole (Program.ofChecked whole.sourceProgram)) (member : header ∈ headers)
    (admitted : called header.instantiation) (size : Nat) :
    CellAwareInvocationAcceptedDirectCalls.PreservesAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  let row := rows header member admitted
  CellAwareInvocationAcceptedNamedApplication.preserves profile receiver header row.generation row.record
    row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
    support row.issued row.assignments artifact checked row.body row.covered row.native wellFormed size
    (fun owner keyPhysical _ selected =>
      expressions profile receiver support artifact checked wellFormed rows size header member admitted owner
        keyPhysical selected)

include profile receiver support artifact checked wellFormed rows in
/-- The direct-call head's native application input holds for every admitted
header at every native grade. -/
theorem reflects (header : Header whole (Program.ofChecked whole.sourceProgram)) (member : header ∈ headers)
    (admitted : called header.instantiation) (size : Nat) :
    CellAwareInvocationAcceptedDirectCalls.ReflectsAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  let row := rows header member admitted
  CellAwareInvocationAcceptedNamedApplication.reflects profile receiver header row.generation row.record
    row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
    support row.issued row.assignments artifact checked row.body row.covered row.native size row.bodySelected
    (fun owner keyPhysical _ selected =>
      expressions profile receiver support artifact checked wellFormed rows size header member admitted owner
        keyPhysical selected)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallFamily
end
