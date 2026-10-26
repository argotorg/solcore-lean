import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFlow

/-! The first expression closure of the accepted-body route. Meaning is proved
for exactly the expressions the actual compiler accepted for a named-row body
when they lie in the closed subset of `CellAwareInvocationAcceptedExpressionTrees`.
Each receipt is extracted from the compiler's own acceptance at its root fuel
and closed by structural recursion; no expression or body execution law is an
input. `Closed` discharges the `Expressions` premise of the body theorems.
Contextual closures and the remaining expression forms are not covered. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationAcceptedTerminals (children)
open CellAwareInvocationAcceptedFlow (Covered)

section Predicates
variable {whole : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : ActualBodyInvocation.BodyRelation}

/-- Compiler sites of the closed subset in a named-row body. Contextual
closures are not yet covered. -/
def InSubset : ActualBodyInvocation.Index whole bodyRelation → ExpressionId → Prop
  | @ActualBodyInvocation.Index.named _ _ named _ _ _ _ =>
      CellAwareInvocationAcceptedExpressionTrees.Subset whole.indexed named
        (CallableIndexedNamedGeneration.source named)
  | .contextual _ _ => fun _ => False

/-- The closed subset as a predicate on the actual accepted expression
receipts: the compiler accepted the expression at this fuel and scope, and it
is a site of the subset. -/
def Accepted (index : ActualBodyInvocation.Index whole bodyRelation) (fuel : Nat) :
    GenericExpressionMeaning.Certificate :=
  fun scope expression lowered => children index fuel scope expression lowered ∧ InSubset index expression

/-- Every expression the compiler accepts for this body, at any fuel and
scope, lies in the closed subset. -/
def Closed (index : ActualBodyInvocation.Index whole bodyRelation) : Prop :=
  ∀ fuel scope expression lowered, children index fuel scope expression lowered → InSubset index expression

/-- Fault interpretation of the body's read diagnostic words: an
uninitialized local read keeps the reason word of its own expression. -/
def Reads (index : ActualBodyInvocation.Index whole bodyRelation) (faults : RecursiveStageMeaning.FaultRep) : Prop :=
  ∀ id node name binder, index.source.lookupExpression? id = some node →
    node.form = .reference name (.local binder) →
    ∀ location, faults (.semantic (.uninitializedLocation location)) (index.reasonAt id)

private theorem found_of_lowered {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreBasic.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id
      reasonAt = .ok lowered) :
    ∃ node, source.lookupExpression? id = some node := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    cases found : source.lookupExpression? id with
    | some node => exact ⟨node, rfl⟩
    | none =>
      rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
      by_cases owner : id.occurrence.owner = source.owner
      · simp [owner, found, bind, Except.bind] at accepted
      · simp [owner, bind, Except.bind] at accepted

/-- The actual compiler accepts only expressions it finds in its own view. -/
theorem found_of_children (index : ActualBodyInvocation.Index whole bodyRelation)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} (generated : children index fuel scope expression lowered) :
    ∃ node, index.compilerSource.lookupExpression? expression = some node := by
  cases index with
  | named receipt selected =>
    change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
    cases fuel with
    | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
    | succ fuel =>
      rw [GeneralizedLocalInitializerCompilation.named_contextual receipt selected] at generated
      exact found_of_lowered generated
  | contextual material view =>
    change (GeneralizedLocalAcceptedBodyCompiler.policy material).lowerExpression _ _ _ _ _ = _ at generated
    rw [GeneralizedLocalAcceptedBodyCompiler.expression_reader] at generated
    exact found_of_lowered generated

/-- `Closed` follows from the body's expression nodes alone: a body whose
every expression node is a site of the subset is closed. -/
theorem closed_of_nodes (index : ActualBodyInvocation.Index whole bodyRelation)
    (nodes : ∀ expression node, index.compilerSource.lookupExpression? expression = some node →
      InSubset index expression) :
    Closed index := by
  intro fuel scope expression lowered generated
  obtain ⟨node, found⟩ := found_of_children index generated
  exact nodes expression node found

end Predicates

section Closure
variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  (index : ActualBodyInvocation.Index whole bodyRelation)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

private theorem reads_lowered {fuel : Nat} {context : SourceSemantics.Context}
    (sourceEq : invocation.source = index.source) (reads : Reads index faults) :
    ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead fuel
        (SourceCoreCompatibleValues.Context.initial whole.compatible.checked)
        invocation.source context index.reasonAt scope id lowered →
      ∀ location, faults (.semantic (.uninitializedLocation location)) (index.reasonAt id) := by
  intro scope id lowered receipt location
  obtain ⟨certificate, _type, _binding⟩ := receipt
  exact reads id certificate.node certificate.name certificate.binder
    (sourceEq ▸ certificate.metadata.found) certificate.form location

/-- Every accepted subset expression of a named-row body preserves its staged
Source execution at every grade. The receipt tree is extracted from the
compiler's own acceptance at the reached scope and Source context. -/
theorem preserves (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = index.source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : Reads index faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (runtime : Dynamic.SourceRuntimeValid program context index.source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = index.compilation.solvedRequirements) (size : Nat) :
    CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) bridge context model index
      registry invocation (Accepted index fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid program context invocation.source := sourceEq ▸ runtime
  have uninitialized := reads_lowered index invocation faults (fuel := whole.indexed.fuel) (context := context)
    sourceEq reads
  cases index with
  | contextual material view =>
    intro scope id lowered accepted
    exact accepted.2.elim
  | @named named diagnostics output receipt selected =>
    intro scope id lowered accepted node found typed mapping world administrative environment canonical
      actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped
      initial admitted authority physical
    obtain ⟨generated, subset⟩ := accepted
    have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
    change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
    cases fuel with
    | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
    | succ rootFuel =>
      rw [GeneralizedLocalInitializerCompilation.named_contextual receipt selected] at generated
      have unique := sourceRuntime.graph.nodeOccurrencesUnique
      rw [sourceNamed] at unique found typed
      have tree := CellAwareInvocationAcceptedExpressionTrees.of_subset receipt rootFuel subset unique
        physical.declarations found typed generated
      rw [← sourceNamed] at tree found typed
      exact CellAwareInvocationAcceptedExpressionBounds.preserves_tree bridge functions extension sameLedger
        faults uninitialized selectedBodies sourceRuntime covers tree size ⟨rfl, rfl, rfl⟩ found typed
        environments heaps locals agrees actualTyped initial admitted authority physical

/-- Every completed native run of an accepted subset expression of a named-row
body reconstructs an independent Source grade, outcome and reached heap. -/
theorem reflects (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = index.source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : Reads index faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (runtime : Dynamic.SourceRuntimeValid program context index.source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = index.compilation.solvedRequirements) (size : Nat) :
    CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) bridge context model index
      registry invocation (Accepted index fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid program context invocation.source := sourceEq ▸ runtime
  have uninitialized := reads_lowered index invocation faults (fuel := whole.indexed.fuel) (context := context)
    sourceEq reads
  cases index with
  | contextual material view =>
    intro scope id lowered accepted
    exact accepted.2.elim
  | @named named diagnostics output receipt selected =>
    intro scope id lowered accepted node found typed mapping world administrative environment canonical
      actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped
      initial admitted authority physical
    obtain ⟨generated, subset⟩ := accepted
    have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
    change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
    cases fuel with
    | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
    | succ rootFuel =>
      rw [GeneralizedLocalInitializerCompilation.named_contextual receipt selected] at generated
      have unique := sourceRuntime.graph.nodeOccurrencesUnique
      rw [sourceNamed] at unique found typed
      have tree := CellAwareInvocationAcceptedExpressionTrees.of_subset receipt rootFuel subset unique
        physical.declarations found typed generated
      rw [← sourceNamed] at tree found typed
      exact CellAwareInvocationAcceptedExpressionBounds.reflects_tree bridge functions extension sameLedger
        faults uninitialized selectedBodies sourceRuntime covers tree size ⟨rfl, rfl, rfl⟩ found typed
        environments heaps locals agrees actualTyped initial admitted authority physical

end Closure

section Discharge
variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

/-- A body whose accepted expressions all lie in the closed subset discharges
the accepted-expression input of the statement closure at every budget. -/
theorem expressions (closed : Closed index) (budget : Nat)
    (sourceEq : invocation.source = index.source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : Reads index faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry) :
    CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget := by
  intro fuel context runtime covers sameLedger
  refine ⟨?_, ?_⟩
  · intro size _ scope id lowered generated
    exact preserves bridge index registry invocation faults fuel sourceEq extension reads selectedBodies
      runtime covers sameLedger size ⟨generated, closed fuel scope id lowered generated⟩
  · intro size _ scope id lowered generated
    exact reflects bridge index registry invocation faults fuel sourceEq extension reads selectedBodies
      runtime covers sameLedger size ⟨generated, closed fuel scope id lowered generated⟩

end Discharge

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

include bindings transport registered in
/-- The complete accepted body of an actual invocation whose accepted
expressions all lie in the closed subset: `body_preserves` without the
accepted-expression premise. -/
theorem body_preserves (budget : Nat) (closed : Closed index) (reads : Reads index faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {control : ControlContext} {expected : TypeSystem.Ty} {context staticFinal : SourceSemantics.Context}
    {facts : BodyFacts} (result : control.returnType = expected) (depth : control.loopDepth = 0)
    (signatures : context.signatures = whole.compatible.checked.signatures)
    (sourceTyped : StatementsHaveType index.source control context index.statements staticFinal facts)
    (projection : whole.compatible.checked.catalog.project expected = .ok index.result)
    (body : AcceptedNamedBodyFlow.Body index.policy index.fuel index.compilerSource index.scope index.statements
      index.result index.reasonAt index.fellThrough index.escaped index.body)
    (covered : Covered index.source expected (CellAwareInvocationAcceptedMatches.Admitted index)
      (CellAwareInvocationAcceptedInputs.Generalized (attachment := attachment) index) body.tree)
    (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative) index.body
      nativeType whole.indexed.layouts.definitions) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative index.scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (index.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (index.source) context index.statements →
    ∀ initial : protocol.State ⟨index.scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context index.scope
      canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    Staging.Recursive.Size.Statements program registry size invocation context environment before
      index.statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (index.body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected index.result faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨index.scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge
          context expected (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached :=
  CellAwareInvocationAcceptedFlow.body_preserves bridge bindings transport index producer registered registry
    invocation faults administrative budget
    (expressions bridge index registry invocation faults closed budget sourceEq writes.extension reads selectedBodies)
    writes artifact checked sourceEq unique result depth signatures sourceTyped projection body covered native

include bindings transport registered in
/-- Native completion of the same complete accepted body reconstructs an
original Source execution: `body_reflects` without the accepted-expression
premise. -/
theorem body_reflects (budget : Nat) (closed : Closed index) (reads : Reads index faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {control : ControlContext} {expected : TypeSystem.Ty} {context staticFinal : SourceSemantics.Context}
    {facts : BodyFacts} (result : control.returnType = expected) (depth : control.loopDepth = 0)
    (signatures : context.signatures = whole.compatible.checked.signatures)
    (sourceTyped : StatementsHaveType index.source control context index.statements staticFinal facts)
    (projection : whole.compatible.checked.catalog.project expected = .ok index.result)
    (body : AcceptedNamedBodyFlow.Body index.policy index.fuel index.compilerSource index.scope index.statements
      index.result index.reasonAt index.fellThrough index.escaped index.body)
    (covered : Covered index.source expected (CellAwareInvocationAcceptedMatches.Admitted index)
      (CellAwareInvocationAcceptedInputs.Generalized (attachment := attachment) index) body.tree)
    (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative) index.body
      nativeType whole.indexed.layouts.definitions) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative index.scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (index.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (index.source) context index.statements →
    ∀ initial : protocol.State ⟨index.scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context index.scope
      canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {value finalStore}, EvaluationSize size actual store (index.body.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        index.statements finalContext outcome after ∧
      Staging.Recursive.BodyResult expected outcome (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected index.result faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨index.scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge
          context expected (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached :=
  CellAwareInvocationAcceptedFlow.body_reflects bridge bindings transport index producer registered registry
    invocation faults administrative budget
    (expressions bridge index registry invocation faults closed budget sourceEq writes.extension reads selectedBodies)
    writes artifact checked sourceEq unique result depth signatures sourceTyped projection body covered native

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressions
