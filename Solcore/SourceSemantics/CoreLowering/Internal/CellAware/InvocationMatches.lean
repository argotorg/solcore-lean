import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationPhysical
import Solcore.SourceSemantics.CoreLowering.DataMatchBranchPrefix
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationStatements
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedMatches
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StatementAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.Staging.RecursiveBodyErasure
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericLexical
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedLiteralSites
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchReady

/-!
# Cell-aware invocations: matches

Matches in one actual body invocation: physical state, heads, both directions, sequences and tree heads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPhysical
/-! Match prefixes retain the actual invocation's frame and generalized local
entries. The hidden native slot has no Source declaration; successful pattern
bindings are the ordinary cells allocated by the independent Source trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open CellAwareInvocationPhysical

private theorem full_internal {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {internal : Resolved.LocalId} (payload : Core.Ty)
    (absent : internal ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id))
    (declarations : CellAwareScopeDeclarations.Full source scope context) :
    CellAwareScopeDeclarations.Full source ((internal, payload) :: scope) context := by
  intro id declared index type selected authentic
  by_cases same : internal = id
  · subst id
    have present : declared ∈ (SourceCoreDataPlaces.declaredBinders source).filter
        (fun candidate => decide (candidate.id = internal)) := by
      rw [authentic]
      exact List.mem_singleton_self declared
    obtain ⟨member, sameId⟩ := List.mem_filter.mp present
    exact False.elim (absent (List.mem_map.mpr ⟨declared, member, of_decide_eq_true sameId⟩))
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry => exact declarations _ _ _ _ previous authentic

private theorem full_binders {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context final : SourceSemantics.Context} {bindings : List (TypedBinder × Core.Ty)}
    (members : ∀ binder ∈ bindings.map Prod.fst, binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (extended : BindersExtend source.owner context (bindings.map Prod.fst) final)
    (declarations : CellAwareScopeDeclarations.Full source scope context) :
    CellAwareScopeDeclarations.Full source
      (bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope) final := by
  induction bindings generalizing context scope with
  | nil => cases extended; exact declarations
  | cons binding rest ih =>
    cases extended with
    | cons head tail =>
      exact ih (fun binder present => members binder (List.mem_cons_of_mem _ present)) tail
        (CellAwareScopeDeclarations.scope_bind binding.2 (members binding.1 List.mem_cons_self) declarations head)

private theorem binders_preserve_read {environment finalEnvironment : Dynamic.Environment}
    {heap finalHeap : Dynamic.Heap} {binders : List TypedBinder} {values : List Dynamic.Value}
    (allocated : Dynamic.BindersAllocate environment heap binders values finalEnvironment finalHeap)
    {location cell} (read : Dynamic.Heap.Reads heap location cell) :
    Dynamic.Heap.Reads finalHeap location cell := by
  induction allocated with
  | nil => exact read
  | cons allocation _ ih => exact ih (allocation.preserves_read read)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {index : ActualBodyInvocation.Index compiled bodyRelation}

private theorem allocated_entries {context finalContext : SourceSemantics.Context}
    {frameLocation mapping world store environment finalEnvironment heap finalHeap binders values}
    (allocated : Dynamic.BindersAllocate environment heap binders values finalEnvironment finalHeap)
    (extended : BindersExtend index.source.owner context binders finalContext)
    (entries : ∀ {id location}, Dynamic.Environment.LooksUp environment id location →
      Entry (attachment := attachment) compiled index context frameLocation id location mapping world finalHeap store) :
    ∀ {id location}, Dynamic.Environment.LooksUp finalEnvironment id location →
      Entry (attachment := attachment) compiled index finalContext frameLocation id location mapping world finalHeap store := by
  induction allocated generalizing context finalContext with
  | nil => cases extended; exact entries
  | cons allocation tail ih =>
    cases extended with
    | cons head remaining =>
      apply ih remaining
      intro id location lookup
      cases lookup with
      | head => exact .ordinary (binders_preserve_read tail allocation.reads_new) rfl
      | tail different previous => exact (entries previous).recontext head different

theorem allocated_authority {mapping world store environment finalEnvironment heap finalHeap binders values}
    (allocated : Dynamic.BindersAllocate environment heap binders values finalEnvironment finalHeap)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      index.owner index.active mapping world finalHeap store environment) :
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      index.owner index.active mapping world finalHeap store finalEnvironment := by
  induction allocated with
  | nil => exact authority
  | cons allocation tail ih =>
    exact ih (.cons (.ordinary (binders_preserve_read tail allocation.reads_new) rfl) authority)

/-- The actual selected arm uses the same invocation, caller and active
substitution. Its new cells come from BindersAllocate; old descriptor rows
come from the concrete match-prefix effect. -/
def arm {context finalContext : SourceSemantics.Context}
    {scope canonical mapping world heap store environment hiddenHeap finalHeap finalEnvironment
      finalCanonical finalMap finalWorld finalStore internal payload}
    {bindings : List (TypedBinder × Core.Ty)} {values : List Dynamic.Value}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment)
    (hidden : internal ∉ (SourceCoreDataPlaces.declaredBinders index.source).map (·.id))
    (members : ∀ binder ∈ bindings.map Prod.fst, binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (extended : BindersExtend index.source.owner context (bindings.map Prod.fst) finalContext)
    (allocated : Dynamic.BindersAllocate environment hiddenHeap (bindings.map Prod.fst) values finalEnvironment finalHeap)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      mapping world heap store finalMap finalWorld finalHeap finalStore)
    (reference : finalCanonical[(bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current)
        ((internal, payload) :: scope)).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type physical.location))
    (read : finalStore.read? physical.location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame physical.native))
    (unmapped : physical.location ∉ finalMap) :
    Physical (attachment := attachment) compiled index finalContext
      (bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) ((internal, payload) :: scope))
      finalCanonical finalMap finalWorld finalHeap finalStore finalEnvironment :=
  ⟨physical.frame,
    CompatibleMatchArmScopes.scope_binders
      (CompatibleMatchArmScopes.scope_internal payload hidden physical.declarations) members extended,
    physical.ownership, full_binders members extended (full_internal payload hidden physical.sourceDeclarations),
    physical.location, reference, read, unmapped,
    allocated_entries allocated extended (fun lookup => (physical.entries lookup).transport effect)⟩

/-- A default or empty selection exposes only the internal scrutinee slot. -/
def parent {context : SourceSemantics.Context}
    {scope canonical mapping world heap store environment finalHeap finalCanonical finalMap finalWorld finalStore internal payload}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment)
    (hidden : internal ∉ (SourceCoreDataPlaces.declaredBinders index.source).map (·.id))
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      mapping world heap store finalMap finalWorld finalHeap finalStore)
    (reference : finalCanonical[((internal, payload) :: scope).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type physical.location))
    (read : finalStore.read? physical.location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame physical.native))
    (unmapped : physical.location ∉ finalMap) :
    Physical (attachment := attachment) compiled index context ((internal, payload) :: scope)
      finalCanonical finalMap finalWorld finalHeap finalStore environment :=
  ⟨physical.frame, CompatibleMatchArmScopes.scope_internal payload hidden physical.declarations,
    physical.ownership, full_internal payload hidden physical.sourceDeclarations,
    physical.location, reference, read, unmapped, fun lookup => (physical.entries lookup).transport effect⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPhysical
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchHeads
/-! Selected match children retain their actual Source grades and reached
caller states. Restoring lexical bindings preserves captured heap cells and
both semantic and staging failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedConditionalHeads (BranchPreserves BranchReflects)
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchSelectionPrefix DataMatchBranchPrefix
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  (parent : SourceSemantics.Context) (control : ControlContext) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (expected : TypeSystem.Ty) (type : Ty) (budget : Nat)

def ArmPreservesBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend invocation.source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType invocation.source control armContext statements staticFinal facts →
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge armContext
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
      stages invocation faults administrative finalScope false statements expected type body budget

def ArmReflectsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend invocation.source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType invocation.source control armContext statements staticFinal facts →
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge armContext
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
      stages invocation faults administrative finalScope false statements expected type body budget

def DefaultPreservesBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType invocation.source control parent statements staticFinal facts →
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge parent
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
      stages invocation faults administrative finalScope false statements expected type body budget

def DefaultReflectsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType invocation.source control parent statements staticFinal facts →
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge parent
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
      stages invocation faults administrative finalScope false statements expected type body budget

private theorem selected_pattern {source : TypedSource} {control : ControlContext}
    {context : SourceSemantics.Context} {raw : TypeSystem.Ty} {cases : List TypedMatchCase}
    {caseFacts : List BodyFacts} {fallback : Option (List StatementId)}
    {value : Dynamic.Value} {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (typed : MatchCasesHaveType source control context raw cases caseFacts)
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.arm statements bindings)) :
    ∃ arm ∈ cases, ∃ binders arity,
      TypedMatchPatternHasType context arm.pattern raw binders arity ∧ bindings.map Prod.fst = binders := by
  cases selected with
  | head matched =>
    cases typed with
    | cons head _ =>
      cases head with
      | intro pattern _ _ =>
        exact ⟨_, List.mem_cons_self, _, _, pattern, DataMatchSourceScopes.PatternMatches.binders pattern matched⟩
  | tail _ selected =>
    cases typed with
    | cons _ tail =>
      obtain ⟨arm, member, binders, arity, pattern, same⟩ := selected_pattern tail selected
      exact ⟨arm, List.mem_cons_of_mem _ member, binders, arity, pattern, same⟩
termination_by cases.length
decreasing_by simp_all

theorem selected_members {source : TypedSource} {control : ControlContext} {context : SourceSemantics.Context}
    {site : StatementId} {statement : StatementNode} {resolution : MatchResolution}
    {raw : TypeSystem.Ty} {caseFacts : List BodyFacts}
    {value : Dynamic.Value} {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (found : source.lookupStatement? site = some statement) (form : statement.form = .matchWith resolution)
    (typed : MatchCasesHaveType source control context raw resolution.cases caseFacts)
    (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings)) :
    ∀ binder ∈ bindings.map Prod.fst, binder ∈ SourceCoreDataPlaces.declaredBinders source := by
  obtain ⟨arm, member, binders, arity, pattern, same⟩ := selected_pattern typed selected
  rw [same]
  exact CompatibleMatchArmScopes.pattern_declarations found form member pattern

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchReflection
/-! Forward execution of the actual match compiler head uses the reached
scrutinee state, real marked allocation prefix and selected staged body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchMeaning
open DataMatchBranchPrefix GenericLexicalContext CallableIndexedHistory
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedMatchHeads (restore_rep restore_arm restore_parent)
open CellAwareInvocationMatchHeads
open CellAwareInvocationExpressionBounds
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  {allocationSource : TypedSource}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
local notation "compilation" => (SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)
local notation "ambient" => CallableIndexedAmbient.ambientDefinitions compiled.indexed
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "instances" => GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances
local notation "frame" => compiled.indexed.ancestry.layout.frame
local notation "globals" => compiled.indexed.base.globals.length
local notation "layouts" => compiled.indexed.layouts

include bridge functions index in
theorem reflects
    (sourceEq : invocation.source = index.source)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : (compilation).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      ((layouts).allocatorAt index.owner index.active onError)))
    (definitions : (layouts).definitions = (ambient).definitions) (registered : (frame).Registered (ambient).definitions)
    (extended : SourceCoreRawMetadata.Extends (compilation).values.registry receiving)
    {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation allocationSource scope id resolution type reason
      expressionCertificate bodyCertificate code)
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary certificate)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = (compilation).signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed (compilation).checked.signatures)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
    (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
    {compilerNode : ExpressionNode}
    (compilerFound : allocationSource.lookupExpression? resolution.scrutinee = some compilerNode)
    (sameType : compilerNode.type = node.type)
    {statement : StatementNode}
    (statementFound : index.source.lookupStatement? id = some statement)
    (statementForm : statement.form = .matchWith resolution)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
    (budget : Nat)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      callerProtocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings callerProtocol)
    (children : ∀ child, child < budget → ReflectsAt (attachment := attachment) bridge context model index stages invocation expressionCertificate faults child)
    (armMeaning : ArmReflectsBelow (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context control resolution bodyCertificate expected type budget scope)
    (defaultMeaning : DefaultReflectsBelow (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context control resolution bodyCertificate expected type budget scope)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming}
    {value : Core.Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (ambient).definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (ambient).definitions)
    (runtime : Dynamic.SourceRuntimeValid program context index.source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = index.compilation.solvedRequirements)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At instances index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Match program stages sourceSize invocation context environment before resolution outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have fullCertificate := certificate
  have hiddenAbsence := CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh physical.ownership statementFound statementForm
  cases certificate with
  | matchWith readStatement allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression loweredSameType arms fallback branches hiddenCompiled =>
    obtain ⟨childNode, child, childSize, input, middleStore, childFound, childCertificate, childSmaller, childCompleted⟩ :=
      RecursiveNamedMatchSourceBounds.Certificate.initial_evaluation_sized fullCertificate completed
    have childEq := uniqueExpression _ childCertificate
    subst child
    have nodeEq := Option.some.inj (compilerFound.symm.trans childFound)
    subst childNode
    obtain ⟨sourceSize, sourceOutcome, middleHeap, middleMap, middleWorld, sourceEval, represented,
      middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
      children childSize (Nat.lt_of_lt_of_le childSmaller within) childCertificate found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childCompleted
    cases represented with
    | fault matched =>
      have failed := CompatibleMatchScrutineeReflection.Certificate.failure_preserves fullCertificate uniqueExpression childCompleted.sound
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
      exact ⟨_, _, middleHeap, middleMap, middleWorld, .scrutineeFault sourceEval, .fault matched,
        middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost.at_fault_type⟩
    | value payload =>
      obtain ⟨valueTyped, middleReady⟩ := firstPost.at_value
      let middlePhysical := physical.transport firstEffect firstFrame
      have reference := physical.reference
      have read := middlePhysical.read
      have unmapped := middlePhysical.unmapped
      obtain ⟨hiddenHeap, location, selection, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selected, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds, secondFrame,
        selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩, secondEffect⟩ :=
        CellAwareMatchSelectedPrefix.success_with_effect fullCertificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid instances GeneralizedLocalDescriptorHeap.ordinary_cells callerProtocol producer stateBindings definitions registered extended compilerFound uniqueExpression (sameType.symm ▸ payload) (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference read unmapped childCompleted.sound middleState ready
      rw [sameType] at hiddenAllocated
      obtain ⟨bodySize, bodySmaller, bodyEval⟩ := agreement.remaining completed
      cases selectedBody with
      | @arm statements bindings compiledBindings finalEnvironment finalHeap body binders allocated certified =>
        obtain ⟨armContext, staticFinal, facts, extendedContext, bodyTyped, _⟩ :=
          DataMatchSourceScopes.MatchCasesSelect.arm_scope casesTyped selected
        have selectedReady := (CallableIndexedOwnedMatchPrefixAdmission.after_arm_prefix bridge
          middleState selectedState middleReady valueTyped hiddenAllocated casesTyped selected extendedContext allocated secondFrame).1
        have selectedMembers := selected_members statementFound statementForm (sourceEq ▸ casesTyped) selected
        let selectedPhysical := CellAwareInvocationMatchPhysical.arm middlePhysical hiddenAbsence
          (by simpa only [binders] using selectedMembers) (by simpa only [binders, sourceEq] using extendedContext)
          (by simpa only [binders] using allocated) secondEffect selectedReference selectedRead selectedUnmapped
        have selectedAuthority : CellAwareScopeAuthority.At instances index.owner index.active selectedMap selectedWorld selectedHeap selectedStore selectedEnvironment :=
          CellAwareInvocationMatchPhysical.allocated_authority (index := index) allocated
            (authority.transport (firstEffect.trans secondEffect))
        have fields := Dynamic.BindersExtend.runtimeContextFields extendedContext
        obtain ⟨bodySourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
          finalHeaps, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, thirdEffect, bodyState, bodyRelated, bodyPost⟩ :=
          armMeaning rfl selected (.arm binders allocated certified) extendedContext bodyTyped _
            (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller within)) selectedEnv selectedRelated
            (binders_agree extendedContext (arm_monomorphic casesTyped selected)
              (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) allocated)
            selectedLayout selectedTyped (runtime.transport fields) (fields.covers covers) (fields.solvedRequirements.trans sameLedger)
            (by simpa only [sourceEq] using (show ProtectedStateImperativeTypedSourceSites.Statements invocation.source armContext statements from ⟨control, staticFinal, facts, bodyTyped⟩))
            selectedState selectedReady selectedAuthority selectedPhysical owner sameLocation ready bodyEval
        exact ⟨_, _, after, finalMap, finalWorld,
          .arm (lookupExpression?_sound found) sourceEval hiddenAllocated selected extendedContext allocated sourceBody,
          restore_rep related environment, finalHeaps,
          firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame), firstMetadata.trans
            ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans ((binders_metadata allocated).trans thirdMetadata)),
          firstEffect.trans (secondEffect.trans thirdEffect),
          returnTo.restore bodyState, callerProtocol.trans firstRelated
            (callerProtocol.trans selectionRelated (callerProtocol.trans bodyRelated (returnTo.related bodyState))),
          restore_arm bridge returnTo extendedContext bodyState environment bodyPost⟩
      | @default statements body certified =>
        have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge
          middleState selectedState middleReady valueTyped hiddenAllocated secondFrame
        obtain ⟨staticFinal, facts, bodyTyped⟩ := defaultTyped selected.defaultBody_eq
        let selectedPhysical := CellAwareInvocationMatchPhysical.parent middlePhysical hiddenAbsence secondEffect selectedReference selectedRead selectedUnmapped
        have selectedAuthority : CellAwareScopeAuthority.At instances index.owner index.active selectedMap selectedWorld hiddenHeap selectedStore environment :=
          authority.transport (firstEffect.trans secondEffect)
        obtain ⟨bodySourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
          finalHeaps, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, thirdEffect, bodyState, bodyRelated, bodyPost⟩ :=
          defaultMeaning (environment := environment) (heap := hiddenHeap) rfl selected (.default certified) bodyTyped _
            (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller within)) selectedEnv selectedRelated
            (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) selectedLayout selectedTyped
            runtime covers sameLedger
            (by simpa only [sourceEq] using (show ProtectedStateImperativeTypedSourceSites.Statements invocation.source context statements from ⟨control, staticFinal, facts, bodyTyped⟩))
            selectedState selectedReady selectedAuthority selectedPhysical owner sameLocation ready bodyEval
        exact ⟨_, _, after, finalMap, finalWorld,
          .default (lookupExpression?_sound found) sourceEval hiddenAllocated selected sourceBody,
          restore_rep related environment, finalHeaps,
          firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame), firstMetadata.trans
            ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans thirdMetadata),
          firstEffect.trans (secondEffect.trans thirdEffect),
          returnTo.restore bodyState, callerProtocol.trans firstRelated
            (callerProtocol.trans selectionRelated (callerProtocol.trans bodyRelated (returnTo.related bodyState))),
          restore_parent bridge returnTo bodyState environment bodyPost⟩
      | noBranch =>
        have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge
          middleState selectedState middleReady valueTyped hiddenAllocated secondFrame
        have finished : Evaluates selectedActual selectedStore ((LocalLoop.fallthrough type).rename selectedEmbedding)
            (LocalLoop.fallthroughValue type) selectedStore := .inRight (.inLeft (.inLeft .unit))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyEval.sound finished
        exact ⟨_, .fallthrough environment, hiddenHeap, selectedMap, selectedWorld,
          .noBranch (lookupExpression?_sound found) sourceEval hiddenAllocated selected,
          .fallthrough environment (Or.inl rfl), selectedRelated,
          firstMaps.trans secondMaps, firstWorlds.trans secondWorlds, firstFrame.trans secondFrame,
          firstMetadata.trans (.of_allocation hiddenAllocated), firstEffect.trans secondEffect, returnTo.restore selectedState,
          callerProtocol.trans firstRelated (callerProtocol.trans selectionRelated (returnTo.related selectedState)),
          restore_parent bridge returnTo selectedState environment (outcome := .fallthrough environment) selectedReady⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPreservation
/-! Forward execution of the actual match compiler head uses the reached
scrutinee state, real marked allocation prefix and selected staged body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchMeaning
open DataMatchBranchPrefix GenericLexicalContext CallableIndexedHistory
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedMatchHeads (restore_rep restore_arm restore_parent)
open CellAwareInvocationMatchHeads
open CellAwareInvocationExpressionBounds
universe u
private theorem default_selected {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {statements : List StatementId}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.default statements)) :
    fallback = some statements := by
  cases selected with
  | default => rfl
  | tail _ next => exact default_selected next
termination_by cases.length
decreasing_by simp_all

private theorem allocations_same {before left right : Dynamic.Heap} {type : TypeSystem.Ty} {value : Option Dynamic.Value}
    {a b : Dynamic.Location} (first : Dynamic.Heap.Allocates before type value a left)
    (second : Dynamic.Heap.Allocates before type value b right) : left = right := by
  cases first; cases second; rfl

private theorem binders_same {environment a b : Dynamic.Environment} {before left right : Dynamic.Heap}
    {binders : List TypedBinder} {values : List Dynamic.Value}
    (first : Dynamic.BindersAllocate environment before binders values a left)
    (second : Dynamic.BindersAllocate environment before binders values b right) : a = b ∧ left = right := by
  induction first generalizing b right with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons allocation rest ih =>
    cases second with
    | cons allocation' rest' =>
      cases allocation
      cases allocation'
      exact ih rest'

private theorem extensions_same {owner : Resolved.DeclarationId} {context a b : SourceSemantics.Context}
    {binders : List TypedBinder} (first : BindersExtend owner context binders a)
    (second : BindersExtend owner context binders b) : a = b := by
  induction first generalizing b with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons head' tail' =>
      cases head
      cases head'
      exact ih tail'


variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  {allocationSource : TypedSource}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
local notation "compilation" => (SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)
local notation "ambient" => CallableIndexedAmbient.ambientDefinitions compiled.indexed
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "instances" => GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances
local notation "frame" => compiled.indexed.ancestry.layout.frame
local notation "globals" => compiled.indexed.base.globals.length
local notation "layouts" => compiled.indexed.layouts

include bridge functions index in
theorem preserves
    (sourceEq : invocation.source = index.source)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : (compilation).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      ((layouts).allocatorAt index.owner index.active onError)))
    (definitions : (layouts).definitions = (ambient).definitions) (registered : (frame).Registered (ambient).definitions)
    (extended : SourceCoreRawMetadata.Extends (compilation).values.registry receiving)
    {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation allocationSource scope id resolution type reason
      expressionCertificate bodyCertificate code)
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary certificate)
    (unique : NodeOccurrencesUnique invocation.source)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = (compilation).signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed (compilation).checked.signatures)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
    (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
    {compilerNode : ExpressionNode}
    (compilerFound : allocationSource.lookupExpression? resolution.scrutinee = some compilerNode)
    (sameType : compilerNode.type = node.type)
    {statement : StatementNode}
    (statementFound : index.source.lookupStatement? id = some statement)
    (statementForm : statement.form = .matchWith resolution)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
    (budget : Nat)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      callerProtocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings callerProtocol)
    (children : ∀ child, child < budget → PreservesAt (attachment := attachment) bridge context model index stages invocation expressionCertificate faults child)
    (armMeaning : ArmPreservesBelow (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context control resolution bodyCertificate expected type budget scope)
    (defaultMeaning : DefaultPreservesBelow (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context control resolution bodyCertificate expected type budget scope)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    {outcome : Staging.Recursive.BodyOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (ambient).definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (ambient).definitions)
    (runtime : Dynamic.SourceRuntimeValid program context index.source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = index.compilation.solvedRequirements)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At instances index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (trace : Staging.Recursive.Size.Match program stages size invocation context environment before resolution outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have expression : expressionCertificate scope resolution.scrutinee lowered := by
    cases certificate with
    | matchWith _ _ _ _ _ _ _ _ _ certified =>
      exact (uniqueExpression _ certified) ▸ certified
  have hiddenFresh := CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh physical.ownership statementFound statementForm
  cases trace with
  | @scrutineeFault exprSize _ _ _ _ _ _ failure fault =>
    have smaller : exprSize < budget := Nat.lt_of_lt_of_le
      (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨value, finalStore, finalMap, finalWorld, coreEval, related, heapRep, maps, worlds, preserved, metadata, effect,
      reached, relatedState, post⟩ :=
      children _ smaller expression found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation fault
    cases related with
    | fault represented =>
      exact ⟨_, finalStore, finalMap, finalWorld,
        CompatibleMatchScrutineeReflection.Certificate.failure_preserves certificate uniqueExpression coreEval,
        .fault represented, heapRep, maps, worlds, preserved, metadata, effect, reached, relatedState, post.at_fault_type⟩
  | patternFault contains evaluated allocated fault =>
    exact False.elim (CompatibleMatchSourceSelection.Certificate.not_pattern_fault_with_signatures certificate signatures _ fault)
  | @arm exprSize bodySize _ _ armContext innerFinal _ armEnvironment _ middle hidden bound _ _ sourceNode sourceValue
      location statements bindings innerOutcome contains sourceEval sourceHidden selected sourceExtended sourceAllocated sourceBody =>
    have exprSmaller : exprSize < budget := Nat.lt_of_lt_of_le
      (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have bodyWithin : bodySize ≤ budget := Nat.le_trans
      (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    have nodeEq : sourceNode = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst sourceNode
    obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
      firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
      children _ exprSmaller expression found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation sourceEval
    cases represented with
    | value represented =>
      obtain ⟨valueFacts, middleReady⟩ := firstPost.at_value
      let middlePhysical := physical.transport firstEffect firstFrame
      have reference := physical.reference
      have read := middlePhysical.read
      have unmapped := middlePhysical.unmapped
      obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
        secondFrame, selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩, secondEffect⟩ :=
        CellAwareMatchSelectedPrefix.selected_with_effect certificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid instances GeneralizedLocalDescriptorHeap.ordinary_cells callerProtocol producer stateBindings definitions registered extended compilerFound uniqueExpression (sameType.symm ▸ represented) (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference read unmapped coreEval middleState ready selected
      rw [sameType] at hiddenAllocated
      have hiddenEq := allocations_same hiddenAllocated sourceHidden
      subst hiddenHeap
      cases selectedBody with
      | arm binders allocated bodyCertified =>
        obtain ⟨sameEnvironment, sameHeap⟩ := binders_same allocated sourceAllocated
        subst selectedEnvironment
        subst selectedHeap
        obtain ⟨staticContext, staticFinal, facts, extended, typed, _⟩ :=
          DataMatchSourceScopes.MatchCasesSelect.arm_scope casesTyped selected
        have sameContext := extensions_same extended sourceExtended
        subst staticContext
        have selectedReady := (CallableIndexedOwnedMatchPrefixAdmission.after_arm_prefix bridge middleState selectedState middleReady valueFacts sourceHidden
          casesTyped selected sourceExtended sourceAllocated secondFrame).1
        have selectedMembers := selected_members statementFound statementForm (sourceEq ▸ casesTyped) selected
        let selectedPhysical := CellAwareInvocationMatchPhysical.arm middlePhysical hiddenFresh
          (by simpa only [binders] using selectedMembers) (by simpa only [binders, sourceEq] using sourceExtended)
          (by simpa only [binders] using allocated) secondEffect selectedReference selectedRead selectedUnmapped
        have selectedAuthority : CellAwareScopeAuthority.At instances index.owner index.active selectedMap selectedWorld bound selectedStore armEnvironment :=
          CellAwareInvocationMatchPhysical.allocated_authority (index := index) allocated
            (authority.transport (firstEffect.trans secondEffect))
        have fields := Dynamic.BindersExtend.runtimeContextFields sourceExtended
        obtain ⟨result, finalStore, finalMap, finalWorld, bodyEval, related, finalHeapRep,
          thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, thirdEffect, bodyState, bodyRelated, bodyReady⟩ :=
          armMeaning rfl selected (.arm binders allocated bodyCertified) sourceExtended typed _ bodyWithin selectedEnv selectedRelated
            (binders_agree sourceExtended (arm_monomorphic casesTyped selected)
              (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) sourceAllocated)
            selectedLayout selectedTyped (runtime.transport fields) (fields.covers covers) (fields.solvedRequirements.trans sameLedger)
            (by simpa only [sourceEq] using (show ProtectedStateImperativeTypedSourceSites.Statements invocation.source armContext statements from ⟨control, staticFinal, facts, typed⟩))
            selectedState selectedReady selectedAuthority selectedPhysical owner sameLocation ready sourceBody
        exact ⟨result, finalStore, finalMap, finalWorld, agreement.wrap bodyEval, restore_rep related environment,
          finalHeapRep, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame),
          firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation sourceHidden).trans
            ((binders_metadata sourceAllocated).trans thirdMetadata)),
          firstEffect.trans (secondEffect.trans thirdEffect),
          ⟨returnTo.restore bodyState, callerProtocol.trans firstRelated
            (callerProtocol.trans selectionRelated (callerProtocol.trans bodyRelated (returnTo.related bodyState))),
            restore_arm bridge returnTo sourceExtended bodyState environment bodyReady⟩⟩
  | @default exprSize bodySize _ _ innerFinal _ _ middle hidden _ _ sourceNode sourceValue location statements innerOutcome
      contains sourceEval sourceHidden selected sourceBody =>
    have exprSmaller : exprSize < budget := Nat.lt_of_lt_of_le
      (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have bodyWithin : bodySize ≤ budget := Nat.le_trans
      (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    have nodeEq : sourceNode = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst sourceNode
    obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
      firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
      children _ exprSmaller expression found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation sourceEval
    cases represented with
    | value represented =>
      obtain ⟨valueFacts, middleReady⟩ := firstPost.at_value
      let middlePhysical := physical.transport firstEffect firstFrame
      have reference := physical.reference
      have read := middlePhysical.read
      have unmapped := middlePhysical.unmapped
      obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
        secondFrame, selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩, secondEffect⟩ :=
        CellAwareMatchSelectedPrefix.selected_with_effect certificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid instances GeneralizedLocalDescriptorHeap.ordinary_cells callerProtocol producer stateBindings definitions registered extended compilerFound uniqueExpression (sameType.symm ▸ represented) (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference read unmapped coreEval middleState ready selected
      rw [sameType] at hiddenAllocated
      have hiddenEq := allocations_same hiddenAllocated sourceHidden
      subst hiddenHeap
      cases selectedBody with
      | default bodyCertified =>
        have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge middleState selectedState middleReady valueFacts sourceHidden secondFrame
        obtain ⟨staticFinal, facts, typed⟩ := defaultTyped (default_selected selected)
        let selectedPhysical := CellAwareInvocationMatchPhysical.parent middlePhysical hiddenFresh secondEffect selectedReference selectedRead selectedUnmapped
        have selectedAuthority : CellAwareScopeAuthority.At instances index.owner index.active selectedMap selectedWorld hidden selectedStore environment :=
          authority.transport (firstEffect.trans secondEffect)
        obtain ⟨result, finalStore, finalMap, finalWorld, bodyEval, related, finalHeapRep,
          thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, thirdEffect, bodyState, bodyRelated, bodyReady⟩ :=
          defaultMeaning (environment := environment) (heap := hidden) rfl selected (.default bodyCertified) typed _ bodyWithin selectedEnv selectedRelated
            (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) selectedLayout selectedTyped runtime covers sameLedger
            (by simpa only [sourceEq] using (show ProtectedStateImperativeTypedSourceSites.Statements invocation.source context statements from ⟨control, staticFinal, facts, typed⟩))
            selectedState selectedReady selectedAuthority selectedPhysical owner sameLocation ready sourceBody
        exact ⟨result, finalStore, finalMap, finalWorld, agreement.wrap bodyEval, restore_rep related environment,
          finalHeapRep, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame),
          firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation sourceHidden).trans thirdMetadata),
          firstEffect.trans (secondEffect.trans thirdEffect),
          ⟨returnTo.restore bodyState, callerProtocol.trans firstRelated
            (callerProtocol.trans selectionRelated (callerProtocol.trans bodyRelated (returnTo.related bodyState))),
            restore_parent bridge returnTo bodyState environment bodyReady⟩⟩
  | @noBranch exprSize _ _ _ _ middle hidden _ sourceNode sourceValue location contains sourceEval sourceHidden selected =>
    have exprSmaller : exprSize < budget := Nat.lt_of_lt_of_le
      (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have nodeEq : sourceNode = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst sourceNode
    obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
      firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
      children _ exprSmaller expression found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation sourceEval
    cases represented with
    | value represented =>
      obtain ⟨valueFacts, middleReady⟩ := firstPost.at_value
      let middlePhysical := physical.transport firstEffect firstFrame
      have reference := physical.reference
      have read := middlePhysical.read
      have unmapped := middlePhysical.unmapped
      obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
        secondFrame, selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩, secondEffect⟩ :=
        CellAwareMatchSelectedPrefix.selected_with_effect certificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid instances GeneralizedLocalDescriptorHeap.ordinary_cells callerProtocol producer stateBindings definitions registered extended compilerFound uniqueExpression (sameType.symm ▸ represented) (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference read unmapped coreEval middleState ready selected
      rw [sameType] at hiddenAllocated
      have hiddenEq := allocations_same hiddenAllocated sourceHidden
      subst hiddenHeap
      cases selectedBody
      have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge middleState selectedState middleReady valueFacts sourceHidden secondFrame
      exact ⟨_, selectedStore, selectedMap, selectedWorld, agreement.wrap (.inRight (.inLeft (.inLeft .unit))),
        .fallthrough environment (.inl rfl), selectedRelated, firstMaps.trans secondMaps, firstWorlds.trans secondWorlds,
        firstFrame.trans secondFrame, firstMetadata.trans (.of_allocation sourceHidden), firstEffect.trans secondEffect,
        ⟨returnTo.restore selectedState, callerProtocol.trans firstRelated
          (callerProtocol.trans selectionRelated (returnTo.related selectedState)),
          restore_parent bridge returnTo selectedState environment (outcome := .fallthrough environment) selectedReady⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchSequences
/-! Match heads restore the selected lexical scope before the actual suffix.
Returning and failing bypass that suffix; a genuine default-stopping receipt
justifies the compiler's unreachable continuation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchSequences
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

open CallableIndexedOwnedAdmittedStagedConditionalHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {administrative : Core.Context}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "instances" => GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

/-- A selected scoped arm's numeric reflection port, closed by the surrounding
compiler-tree induction. Its postcondition is at the original outer context. -/
def MatchReflects (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (resolution : MatchResolution) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_runtime : Dynamic.SourceRuntimeValid program context index.source)
    (_covers : invocation.evidence.Covers context)
    (_sameLedger : context.solvedRequirements = index.compilation.solvedRequirements)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_admitted : Admission bridge context initial)
    (_authority : CellAwareScopeAuthority.At instances index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (_sameLocation : owner.key.frameLocation = physical.location)
    (_ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native),
    EvaluationSize size actual store (code.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Match program stages sourceSize invocation context environment before
        resolution outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached

/-- The corresponding Source-to-native port retains successful branch typing,
fallthrough admission, and the same final heap for every admitted caller. -/
def MatchPreserves (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (resolution : MatchResolution) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_runtime : Dynamic.SourceRuntimeValid program context index.source)
    (_covers : invocation.evidence.Covers context)
    (_sameLedger : context.solvedRequirements = index.compilation.solvedRequirements)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_admitted : Admission bridge context initial)
    (_authority : CellAwareScopeAuthority.At instances index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (_sameLocation : owner.key.frameLocation = physical.location)
    (_ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native),
    ∀ {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap},
      Staging.Recursive.Size.Match program stages size invocation context environment before
        resolution outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached


private theorem fallthrough_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.fallthrough inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.fallthrough inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => exact Staging.Recursive.BodyOutcome.fallthrough.inj outcomeEq

private theorem breaking_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.breaking inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.breaking inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => cases outcomeEq

private theorem continuing_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.continuing inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.continuing inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => cases outcomeEq

private theorem stopped_not_fallthrough {program registry size invocation context before after resolution environment inner id statement}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (stopped : ReachableMatchContinuations.DefaultStopped invocation.source id resolution)
    (trace : Staging.Recursive.Size.Match program registry size invocation context environment before
      resolution (.fallthrough inner) after) : False := by
  have executed := trace.sound.plain id statement (lookupStatement?_sound found) form
  cases stopped.terminates unique executed

variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {innerCode : Expr}

variable {mode : Bool} {id : StatementId} {statement : StatementNode}
  {rest : List StatementId} {body : Expr}

include bridge functions index producer in
theorem reflects {budget : Nat}
    (sourceEq : invocation.source = index.source)
    (innerCorrect : MatchReflects (administrative := administrative) (receiving := receiving) (stages := stages) (invocation := invocation) (faults := faults) bridge functions index producer context scope resolution expected type innerCode budget)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (remaining : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer stages invocation faults administrative scope mode rest expected type body budget ∨
      (NodeOccurrencesUnique invocation.source ∧ ReachableMatchContinuations.DefaultStopped invocation.source id resolution))
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements index.source context (id :: rest))
    (runtime : Dynamic.SourceRuntimeValid program context index.source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = index.compilation.solvedRequirements)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At instances index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (completed : EvaluationSize size actual store ((LocalLoop.sequence type innerCode body).rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        (id :: rest) finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, headRelated, headPost⟩ :=
    innerCorrect (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready headEval
  cases represented with
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchReturned (lookupStatement?_sound statementFound) form headTrace,
        .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | breaking innerEnvironment =>
      have environmentEq := breaking_environment headTrace
      subst innerEnvironment
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchBreaking (lookupStatement?_sound statementFound) form headTrace,
        .breaking environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | continuing innerEnvironment =>
      have environmentEq := continuing_environment headTrace
      subst innerEnvironment
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchContinuing (lookupStatement?_sound statementFound) form headTrace,
        .continuing environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchFault (lookupStatement?_sound statementFound) form headTrace,
        .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      have environmentEq := fallthrough_environment headTrace
      subst innerEnvironment
      rcases remaining with remaining | ⟨unique, stopped⟩
      · obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
        obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
            finalHeaps, maps, worlds, framePreserved, metadata, effect, reached, tailRelated, post⟩ :=
          remaining _ (Nat.le_trans (Nat.le_of_lt smaller) within)
            (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) runtime covers sameLedger suffixTyped
            middleState headPost (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
            owner sameLocation ready
            (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
        exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
          .matchFallthrough (lookupStatement?_sound statementFound) form headTrace tailTrace,
          represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
          firstFrame.trans framePreserved, firstMetadata.trans metadata, firstEffect.trans effect, reached,
          callerProtocol.trans headRelated tailRelated, post⟩
      · exact False.elim (stopped_not_fallthrough unique statementFound form stopped headTrace)

include bridge functions index producer in
theorem preserves {budget : Nat}
    (sourceEq : invocation.source = index.source)
    (innerCorrect : MatchPreserves (administrative := administrative) (receiving := receiving) (stages := stages) (invocation := invocation) (faults := faults) bridge functions index producer context scope resolution expected type innerCode budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (remaining : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer stages invocation faults administrative scope mode rest expected type body budget ∨
      (ReachableMatchContinuations.DefaultStopped invocation.source id resolution))
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements index.source context (id :: rest))
    (runtime : Dynamic.SourceRuntimeValid program context index.source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = index.compilation.solvedRequirements)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At instances index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.sequence type innerCode body).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have finish {headSize : Nat}
      {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Staging.Recursive.Size.Match program stages headSize invocation context
        environment before resolution headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type innerCode body).rename ξ) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults headOutcome value ∧
        GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
        ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          callerProtocol.Relates initial reached ∧ Post bridge context expected headOutcome reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      innerCorrect bounded environments heaps locals agrees actualTyped
        runtime covers sameLedger initial admitted authority physical owner sameLocation ready headTrace
    cases represented with
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | breaking innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .breaking innerEnvironment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | continuing innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .continuing innerEnvironment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedMatchSourceInversion.match_and_tail unique statementFound form trace with
    ⟨innerSize, sourceValue, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, failure, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, tailSize, middle, sameSize, innerTrace, tailTrace⟩
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · rcases remaining with remaining | stopped
    · have headWithin : innerSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
          maps, worlds, preservation, metadata, effect, middleState, headRelated, headPost⟩ :=
        innerCorrect headWithin environments heaps locals agrees actualTyped
          runtime covers sameLedger initial admitted authority physical owner sameLocation ready innerTrace
      cases represented with
      | fallthrough innerEnvironment _ =>
          have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
            rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
          obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
              lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, tailRelated, post⟩ :=
            remaining _ tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
                (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
              (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) runtime covers sameLedger suffixTyped
              middleState headPost (authority.transport effect) (physical.transport effect preservation)
              owner sameLocation ready tailTrace
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
            maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
            metadata.trans lastMetadata, effect.trans lastEffect, reached, callerProtocol.trans headRelated tailRelated, post⟩
          rw [LoopRenaming.sequence]
          simp only [GenericExpressionMeaning.rename_prefix] at tailEval
          exact LocalLoop.sequence_fallthrough _ headEval tailEval
    · exact False.elim (stopped_not_fallthrough unique statementFound form stopped innerTrace)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchSequences
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchTreeHeads
/-! The actual finite compiler requests close the match head's selected branch
ports. Source contexts and numeric pattern evidence come from original pattern
typing; the genuine marked allocator supplies the actual hidden and arm cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchTreeHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedAdmittedStagedConditionalHeads
open CellAwareInvocationMatchSequences
universe u

private theorem arms_sites
    {compilation : SourceCoreCompatibleDataMatches.Context} {source semanticSource : TypedSource} {site scope expected bodyCertificate cases arms}
    (certificates : CompatibleMatchCertificates.Arms compilation source site scope expected bodyCertificate cases arms)
    {context : SourceSemantics.Context} {control : ControlContext} {caseFacts : List BodyFacts}
    (signatures : context.signatures = compilation.signatures)
    (typed : MatchCasesHaveType semanticSource control context expected cases caseFacts) :
    CompatibleMatchDecision.Arms.LiteralSites
      (fun numeric => RequirementProves context numeric.requirement numeric.predicate) certificates := by
  induction certificates generalizing caseFacts with
  | nil => exact .nil
  | cons pattern native body tail ih =>
      cases typed with
      | cons head remaining =>
          cases head with
          | intro patternTyped extended bodyTyped =>
              exact .cons (patternCertificate := pattern) (typed := native) (bodyCertified := body) (CompatibleMatchTypedLiteralSites.pattern_sites pattern signatures patternTyped) (ih remaining)

private theorem sites
    {compilation : SourceCoreCompatibleDataMatches.Context} {source semanticSource : TypedSource} {scope id resolution resultType internalReason expressionCertificate bodyCertificate code}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    {context : SourceSemantics.Context} {control : ControlContext} {node : ExpressionNode} {caseFacts : List BodyFacts}
    (signatures : context.signatures = compilation.signatures)
    (found : source.lookupExpression? resolution.scrutinee = some node)
    (typed : MatchCasesHaveType semanticSource control context node.type resolution.cases caseFacts) :
    CompatibleMatchDecision.Certificate.LiteralSites
      (fun numeric => RequirementProves context numeric.requirement numeric.predicate) certificate := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType arms fallback branches hiddenCompiled =>
      have same := Option.some.inj (scrutineeFound.symm.trans found)
      cases same
      exact .matchWith (read := read) (statementTypeValid := allowed) (form := form) (requirements := requirements)
        (hiddenOwned := hiddenOwned) (hiddenFresh := hiddenFresh) (scrutineeOwned := scrutineeOwned)
        (scrutineeFound := scrutineeFound) (projection := projection) (expression := expression) (sameType := sameType)
        (fallbackCertificate := fallback) (branchesCertified := branches) (hiddenCompiled := hiddenCompiled)
        (arms_sites arms signatures typed)


/-- No branch execution is assumed: each authentic finite request is supplied
by the surrounding compiler-tree induction at its exact Source context. -/
theorem reflects {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  {allocationSource : TypedSource}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
    (compiled.indexed.layouts.allocatorAt index.owner index.active onError)))
  (definitions : compiled.indexed.layouts.definitions = ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions) (registered : compiled.indexed.ancestry.layout.frame.Registered ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions)
  (extension : SourceCoreRawMetadata.Extends (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).values.registry receiving)
  {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate ((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)) allocationSource scope id resolution type reason
    expressionCertificate (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).signatures)
  (catalog : SignatureCatalogWellFormed (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).checked.signatures)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
  (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
  (sourceEq : invocation.source = index.source)
  {compilerNode : ExpressionNode}
  (compilerFound : allocationSource.lookupExpression? resolution.scrutinee = some compilerNode)
  (sameSourceType : compilerNode.type = node.type)
  {statement : StatementNode}
  (statementFound : index.source.lookupStatement? id = some statement)
  (statementForm : statement.form = .matchWith resolution)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
  (budget : Nat)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    callerProtocol compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

    (_children : ∀ childSize, childSize < budget →
      ReflectsAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index stages invocation expressionCertificate faults childSize)
    (_bodies : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor invocation.source context (resolution.hiddenScrutinee :: scope.map Prod.fst)
        node.type resolution.cases resolution.defaultBody request childContext →
      ProtectedStateImperativeTypedSourceSites.Statements invocation.source childContext request.statements →
      CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge childContext
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
        stages invocation faults administrative request.scope false request.statements expected type request.code budget) :
    MatchReflects (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context scope resolution expected type code budget := by
  obtain ⟨lowered, child, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
  intro size within mapping world actualContext environment canonical actual before store finalStore ξ value
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready completed
  refine CellAwareInvocationMatchReflection.reflects
    (expressionCertificate := GenericImperativeMatch.Singleton scope resolution.scrutinee lowered) (lowered := lowered) bridge functions index sourceEq onError allocator definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary)
    (fun numeric => RequirementProves context numeric.requirement numeric.predicate) signatures (fun _ proof => proof)
    (sites restricted signatures compilerFound (sameSourceType.symm ▸ casesTyped)) catalog found typed compilerFound sameSourceType statementFound statementForm
    (by intro other actual; exact actual.2.2) casesTyped (fun same => defaultTyped _ same) budget producer bindings
    ?_ ?_ ?_ within environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready completed
  · intro childSize smaller actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact _children childSize smaller child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      armContext staticFinal facts extended bodyTyped
    have scopeIds := selected_arm_ids bodySelected
    rw [sameScope] at scopeIds
    cases bodySelected with
    | arm binders allocated certified =>
      exact @_bodies ⟨_, statements, body⟩ certified armContext
        (ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended)
        ⟨control, staticFinal, facts, bodyTyped⟩
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      staticFinal facts bodyTyped
    have scopeIds := (selected_default_ids bodySelected).trans sameScope
    cases bodySelected with
    | default certified =>
      exact @_bodies ⟨_, statements, body⟩ certified context (.default selected.defaultBody_eq scopeIds) ⟨control, staticFinal, facts, bodyTyped⟩

theorem preserves {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  {allocationSource : TypedSource}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
    (compiled.indexed.layouts.allocatorAt index.owner index.active onError)))
  (definitions : compiled.indexed.layouts.definitions = ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions) (registered : compiled.indexed.ancestry.layout.frame.Registered ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions)
  (extension : SourceCoreRawMetadata.Extends (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).values.registry receiving)
  {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate ((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)) allocationSource scope id resolution type reason
    expressionCertificate (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).signatures)
  (catalog : SignatureCatalogWellFormed (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).checked.signatures)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
  (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
  (sourceEq : invocation.source = index.source)
  {compilerNode : ExpressionNode}
  (compilerFound : allocationSource.lookupExpression? resolution.scrutinee = some compilerNode)
  (sameSourceType : compilerNode.type = node.type)
  {statement : StatementNode}
  (statementFound : index.source.lookupStatement? id = some statement)
  (statementForm : statement.form = .matchWith resolution)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
  (budget : Nat)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    callerProtocol compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

    (_unique : NodeOccurrencesUnique invocation.source)
    (_children : ∀ childSize, childSize < budget →
      PreservesAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index stages invocation expressionCertificate faults childSize)
    (_bodies : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor invocation.source context (resolution.hiddenScrutinee :: scope.map Prod.fst)
        node.type resolution.cases resolution.defaultBody request childContext →
      ProtectedStateImperativeTypedSourceSites.Statements invocation.source childContext request.statements →
      CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge childContext
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
        stages invocation faults administrative request.scope false request.statements expected type request.code budget) :
    MatchPreserves (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context scope resolution expected type code budget := by
  obtain ⟨lowered, child, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
  intro size within mapping world actualContext environment canonical actual before store ξ
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready outcome after trace
  refine CellAwareInvocationMatchPreservation.preserves
    (expressionCertificate := GenericImperativeMatch.Singleton scope resolution.scrutinee lowered) (lowered := lowered) bridge functions index sourceEq onError allocator definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) _unique
    (fun numeric => RequirementProves context numeric.requirement numeric.predicate) signatures (fun _ proof => proof)
    (sites restricted signatures compilerFound (sameSourceType.symm ▸ casesTyped)) catalog found typed compilerFound sameSourceType statementFound statementForm
    (by intro other actual; exact actual.2.2) casesTyped (fun same => defaultTyped _ same) budget producer bindings
    ?_ ?_ ?_ within environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready trace
  · intro childSize smaller actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact _children childSize smaller child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      armContext staticFinal facts extended bodyTyped
    have scopeIds := selected_arm_ids bodySelected
    rw [sameScope] at scopeIds
    cases bodySelected with
    | arm binders allocated certified =>
      exact @_bodies ⟨_, statements, body⟩ certified armContext
        (ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended)
        ⟨control, staticFinal, facts, bodyTyped⟩
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      staticFinal facts bodyTyped
    have scopeIds := (selected_default_ids bodySelected).trans sameScope
    cases bodySelected with
    | default certified =>
      exact @_bodies ⟨_, statements, body⟩ certified context (.default selected.defaultBody_eq scopeIds) ⟨control, staticFinal, facts, bodyTyped⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchTreeHeads
end
